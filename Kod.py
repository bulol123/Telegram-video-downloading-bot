import os
import re
import time
import html
import math
import json
import logging
import threading
import subprocess
import uuid
import glob
import queue
import contextlib
import datetime
from collections import deque
from urllib.parse import quote

import requests
import telebot
import yt_dlp
from telebot import apihelper
from telebot.types import (InlineKeyboardMarkup, InlineKeyboardButton,
                           InlineQueryResultArticle, InputTextMessageContent)
# ddgs (поиск по DuckDuckGo) — по вашим же словам, не дал нужного результата
# для фильтра по периоду (у DDG нет произвольных диапазонов дат, только
# пресеты день/неделя/месяц/год), но код всё ещё пытается его использовать
# как первый вариант в yt_search_with_period. Делаем импорт необязательным,
# как остальные опциональные зависимости в этом файле, — раньше отсутствие
# пакета ddgs роняло бота целиком ещё на старте, до входа в какой-либо код.
try:
    from ddgs import DDGS
    HAS_DDGS = True
except ImportError:
    HAS_DDGS = False


# youtube-transcript-api — отдельная, специализированная библиотека для
# субтитров/автоперевода YouTube. Она дёргает тот же браузерный механизм
# перевода, что и yt-dlp, но делает это надёжнее для автоматически
# переведённых дорожек (yt-dlp у нас иногда тихо возвращает пустой файл
# именно на этом сценарии). Используем её как основной путь, а
# generic-скачивание через yt-dlp оставляем запасным вариантом.
try:
    from youtube_transcript_api import YouTubeTranscriptApi
    from youtube_transcript_api.formatters import SRTFormatter
    from youtube_transcript_api.proxies import GenericProxyConfig
    from youtube_transcript_api._errors import (
        TranscriptsDisabled, NoTranscriptFound, VideoUnavailable,
        CouldNotRetrieveTranscript,
    )
    HAS_TRANSCRIPT_API = True
except ImportError:
    HAS_TRANSCRIPT_API = False

# requests_toolbelt — для настоящего прогресса ЗАГРУЗКИ в Telegram
# (сколько байт файла реально ушло по сети), а не просто "отправляю".
# requests сам по себе читает файл в память целиком при files=..., без
# колбэка на каждый чанк — а MultipartEncoderMonitor умеет это честно.
try:
    from requests_toolbelt.multipart.encoder import MultipartEncoder, MultipartEncoderMonitor
    HAS_TOOLBELT = True
except ImportError:
    HAS_TOOLBELT = False

# ---------- ЛОКАЛЬНЫЙ СЕРВЕР ----------
apihelper.API_URL  = "http://localhost:8081/bot{0}/{1}"
apihelper.FILE_URL = "http://localhost:8081/file/bot{0}/{1}"
apihelper.CONNECT_TIMEOUT = 30
apihelper.READ_TIMEOUT    = 600

# ---------- ПАТЧ: несовместимость версий локального Bot API сервера и
# библиотеки telebot (сервер не шлёт новое поле gifts_from_channels,
# библиотека требует его обязательно и роняет весь polling) ----------
try:
    from telebot.types import AcceptedGiftTypes as _AcceptedGiftTypes
    _orig_agt_init = _AcceptedGiftTypes.__init__
    def _patched_agt_init(self, unlimited_gifts, limited_gifts, unique_gifts,
                          premium_subscription, gifts_from_channels=False, **kwargs):
        _orig_agt_init(self, unlimited_gifts, limited_gifts, unique_gifts,
                       premium_subscription, gifts_from_channels, **kwargs)
    _AcceptedGiftTypes.__init__ = _patched_agt_init
except Exception:
    pass

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# === ОТЛАДКА ===
telebot.logger.setLevel(logging.DEBUG)

TOKEN = '[TOKEN]'

bot = telebot.TeleBot(TOKEN)

DOWNLOAD_DIR = 'downloads'
os.makedirs(DOWNLOAD_DIR, exist_ok=True)
user_data = {}

# ================================================================
#  ЗАЩИТА ОТ ФЛУДА/ДДОСА
# ================================================================
# 1) Тяжёлые задачи (получение инфы, скачивание, конвертация) идут не в
#    потоках telebot напрямую, а в ограниченный пул воркеров через очередь —
#    сколько бы сообщений ни прилетело разом, одновременно реально
#    выполняется не больше MAX_CONCURRENT_JOBS штук, остальное ждёт своей
#    очереди (или отбрасывается, если очередь переполнена).
# 2) Дедупликация: одна и та же задача (тот же чат + та же ссылка/тот же
#    выбор качества) не может быть запущена дважды, пока не закончится.
# 3) Антифлуд по чату: не чаще одного нового запроса раз в COOLDOWN_SEC
#    секунд и не больше RATE_MAX_REQUESTS запросов за RATE_WINDOW_SEC —
#    работает и в группах, так как считается по chat_id, а не по юзеру.
MAX_CONCURRENT_JOBS = 2
MAX_QUEUE_SIZE = 25
COOLDOWN_SEC = 3
RATE_WINDOW_SEC = 60
RATE_MAX_REQUESTS = 8

job_queue = queue.Queue(maxsize=MAX_QUEUE_SIZE)

def _job_worker():
    while True:
        func, args = job_queue.get()
        try:
            func(*args)
        except Exception as e:
            logger.error("Необработанная ошибка в фоновой задаче: %s", e)
        finally:
            job_queue.task_done()

for _ in range(MAX_CONCURRENT_JOBS):
    threading.Thread(target=_job_worker, daemon=True).start()

def enqueue_job(func, *args):
    """Пытается поставить задачу в очередь. False, если очередь забита."""
    try:
        job_queue.put_nowait((func, args))
        return True
    except queue.Full:
        return False

_active_jobs = set()
_active_jobs_lock = threading.Lock()

def try_start_job(key):
    with _active_jobs_lock:
        if key in _active_jobs:
            return False
        _active_jobs.add(key)
        return True

def finish_job(key):
    with _active_jobs_lock:
        _active_jobs.discard(key)

_rate_lock = threading.Lock()
_rate_history = {}   # chat_id -> deque[timestamps]
_last_request = {}   # chat_id -> timestamp последнего запроса

def rate_limited(chat_id):
    """True, если запрос нужно отклонить (слишком частые запросы)."""
    now = time.time()
    with _rate_lock:
        last = _last_request.get(chat_id, 0)
        if now - last < COOLDOWN_SEC:
            return True
        _last_request[chat_id] = now
        hist = _rate_history.setdefault(chat_id, deque())
        hist.append(now)
        while hist and now - hist[0] > RATE_WINDOW_SEC:
            hist.popleft()
        return len(hist) > RATE_MAX_REQUESTS

def safe_answer_callback(call, text=None, show_alert=False):
    """answer_callback_query может упасть, если на этот же callback уже
    ответили раньше (например, диспетчер уже отправил один ответ, пока
    задача стояла в очереди) — глушим эту ошибку, а не роняем обработчик."""
    try:
        bot.answer_callback_query(call.id, text, show_alert=show_alert)
    except Exception:
        pass

def dispatch_download(call, data, video_id, choice, func, *extra_args):
    """Проверяет дедуп + ставит тяжёлую задачу (скачивание/конвертацию) в
    ограниченную очередь воркеров, вместо того чтобы выполнять её сразу в
    потоке диспетчера telebot — это и есть защита от заддосивания."""
    chat_id = call.message.chat.id
    job_key = ('dl', chat_id, video_id, choice)

    if not try_start_job(job_key):
        safe_answer_callback(call, "⏳ Это уже скачивается, подождите.")
        return

    def _run():
        try:
            func(call, data, *extra_args)
        finally:
            finish_job(job_key)

    if not enqueue_job(_run):
        finish_job(job_key)
        safe_answer_callback(call, "🚦 Бот сейчас перегружен запросами, попробуйте через минуту.",
                             show_alert=True)
        return

    if job_queue.qsize() > 0:
        safe_answer_callback(call, f"⏳ Задача в очереди (~{job_queue.qsize()})...")

UA = ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 '
      '(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36')

# ---------- FFMPEG ИЗ ПАПКИ СО СКРИПТОМ ----------
_BASE_DIR = os.path.dirname(os.path.abspath(__file__))
FFMPEG_BIN = os.path.join(_BASE_DIR, 'ffmpeg.exe')
if not os.path.exists(FFMPEG_BIN):
    FFMPEG_BIN = 'ffmpeg'

# ---------- КУКИ (для обхода PO-token / возрастных ограничений YouTube) ----------
# Положите файл cookies.txt рядом со скриптом (экспортируется расширением
# вроде "Get cookies.txt LOCALLY" из браузера, где вы вошли в YouTube).
# Если файла нет — просто работаем без кук, как раньше.
COOKIES_FILE = os.path.join(_BASE_DIR, 'cookies.txt')

def cookies_opts():
    if os.path.exists(COOKIES_FILE):
        return {'cookiefile': COOKIES_FILE}
    return {}


# ---------- САМОДИАГНОСТИКА БОТА ----------
ADMIN_CHAT_ID = 1925781365

def _send_raw(chat_id, text):
    """Отправляет сообщение напрямую по HTTP, пробуя сначала локальный
    сервер (наш обычный путь для всего остального), а если не вышло —
    облако Telegram напрямую. Не завязано на bot.send_message, чтобы
    работать и при частичных сбоях самого бота."""
    try:
        local_url = apihelper.API_URL.format(TOKEN, 'sendMessage')
        r = requests.post(local_url, json={'chat_id': chat_id, 'text': text}, timeout=10)
        if r.ok and r.json().get('ok'):
            return True
    except Exception:
        pass
    try:
        r = requests.post(f"https://api.telegram.org/bot{TOKEN}/sendMessage",
                          json={'chat_id': chat_id, 'text': text}, timeout=10)
        return bool(r.ok and r.json().get('ok'))
    except Exception as e:
        logger.warning("Не удалось отправить уведомление в чат %s: %s", chat_id, e)
        return False

def notify_admin(text):
    _send_raw(ADMIN_CHAT_ID, text)

# ---------- СТАТУС БОТА — ЧЕРЕЗ ИМЯ, А НЕ РАССЫЛКУ ----------
# Раньше при падении/восстановлении бот слал сообщение КАЖДОМУ известному
# чату — раздражает и не нужно. Вместо этого просто переключаем
# отображаемое имя бота (то, что видно в шапке чата и в списке контактов):
# "Скачивание видео🟢" — работает, "Скачивание видео🛑" — не работает.
# Человек видит статус, просто открыв чат, без лишних пингов.
BOT_BASE_NAME = "Скачивание видео"
_bot_name_status = {'ok': None}

def _post_method(method, payload):
    try:
        r = requests.post(apihelper.API_URL.format(TOKEN, method),
                          json=payload, timeout=10)
        return bool(r.ok and r.json().get('ok')), r.text[:200]
    except Exception as e:
        return False, str(e)

def set_bot_status_name(ok):
    """Индикатор статуса дублируем в трёх каналах — у каждого своя
    видимость и свой лимит:
    1) кнопка меню слева от поля ввода — видна в каждом открытом чате,
       строгого лимита нет → основной индикатор;
    2) описание/короткое описание — профиль и стартовый экран, лимит
       отдельный;
    3) имя бота — самое заметное, но лимит жёсткий (пара смен в сутки),
       поэтому только бонусом; если 429 — не страшно, остальные каналы
       доработают, а имя дообновится при следующем перезапуске/флипе."""
    if _bot_name_status['ok'] == ok:
        return
    _bot_name_status['ok'] = ok
    mark = '🟢' if ok else '🔴'
    status = '🟢 работает' if ok else '🔴 не работает'

    ok_r, err = _post_method('setChatMenuButton',
                             {'menu_button': {'type': 'commands', 'text': status}})
    if not ok_r:
        logger.warning("setChatMenuButton не удался: %s", err)

    ok_r, err = _post_method('setMyShortDescription',
                             {'short_description': f"Статус: {status}"})
    if not ok_r:
        logger.warning("setMyShortDescription не удался: %s", err)

    ok_r, err = _post_method('setMyDescription',
                             {'description':
                              "Загрузчик видео/аудио (YouTube, TikTok и др.). "
                              f"Статус: {status}."})
    if not ok_r:
        logger.warning("setMyDescription не удался: %s", err)

    ok_r, err = _post_method('setMyName', {'name': f"{BOT_BASE_NAME}{mark}"})
    if not ok_r:
        logger.warning("setMyName не удался (не критично, см. комментарий): %s", err)

def local_server_ok():
    try:
        r = requests.get(f"http://localhost:8081/bot{TOKEN}/getMe", timeout=5)
        return bool(r.ok and r.json().get('ok'))
    except Exception:
        return False

def cloud_ok():
    try:
        r = requests.get(f"https://api.telegram.org/bot{TOKEN}/getMe", timeout=5)
        return bool(r.ok and r.json().get('ok'))
    except Exception:
        return False

_monitor = {'ok': True, 'down_since': None}

def monitor_loop(interval=30):
    while True:
        time.sleep(interval)
        try:
            if local_server_ok():
                reason = None
            elif cloud_ok():
                reason = 'локальный сервер не отвечает (localhost:8081)'
            else:
                reason = 'нет связи с Telegram (проверь VPN/интернет)'

            if reason and _monitor['ok']:
                _monitor['ok'] = False
                _monitor['down_since'] = time.time()
                set_bot_status_name(False)
            elif not reason and not _monitor['ok']:
                _monitor['ok'] = True
                _monitor['down_since'] = None
                set_bot_status_name(True)
        except Exception as e:
            logger.error("Ошибка монитора: %s", e)

# ---------- КАЧЕСТВО ВИДЕО ----------
def _video_spec(h):
    return (
        f"bestvideo[height<={h}][ext=mp4]+bestaudio[ext=m4a]"
        f"/bestvideo[width<={h}][ext=mp4]+bestaudio[ext=m4a]"
        f"/best[height<={h}][ext=mp4]"
        f"/best[width<={h}][ext=mp4]"
        f"/best[ext=mp4]/best"
    )

QUALITY_OPTIONS = {
    '144p':  _video_spec(144),
    '240p':  _video_spec(240),
    '360p':  _video_spec(360),
    '480p':  _video_spec(480),
    '720p':  _video_spec(720),
    '1080p': _video_spec(1080),
    'audio_128': 'bestaudio[abr<=128]/bestaudio',
    'audio_192': 'bestaudio[abr<=192]/bestaudio',
    'audio_320': 'bestaudio[abr<=320]/bestaudio',
}

YTDL_EXTRACTOR_ARGS = {
    'youtube': {
        'player_client': ['default', '-android_sdkless'],
        'skip': ['hls', 'dash'],
    }
}

VIDEO_QUALITIES = ('144p', '240p', '360p', '480p', '720p', '1080p')

# ---------- ВИДЕОФОРМАТЫ ----------
VIDEO_ORDER = ['mp4', 'm4v', 'mov', 'mkv', 'webm', 'avi', 'flv', 'wmv', 'asf', '3gp', '3g2', 'mpg', 'ogv', 'mxf', 'm2ts', 'vob', 'wtv', 'divx', 'amv', 'roq']

# Форматы, которые Telegram понимает как видео
VIDEO_TELEGRAM_OK = {'mp4', 'm4v', 'mov', 'mkv', 'webm', 'avi', '3gp', '3g2'}

# БАГ, который ломал превью на ПК для всего, кроме MP4: код слал видео через
# sendVideo с ЖЁСТКО прописанным Content-Type «video/mp4», даже если реально
# отправлялся .mov/.mkv/... Имя файла (расширение) говорило один формат,
# заголовок — другой. Telegram Desktop в такой ситуации пытается разобрать
# контейнер как MP4/QuickTime по заголовку, путается в структуре и получает
# неверные width/height/ориентацию — превью съезжает. Мобильные клиенты
# оказались терпимее и обычно определяют контейнер сами, поэтому там всё
# было нормально. Отсюда и совпадение: обложку меняли как угодно (жать,
# паддить, слать сырую) — а результат не менялся, ведь дело было не в
# картинке, а в том, что Desktop неверно парсил сам видеофайл.
VIDEO_MIME_MAP = {
    'mp4': 'video/mp4', 'm4v': 'video/x-m4v', 'mov': 'video/quicktime',
    'mkv': 'video/x-matroska', 'webm': 'video/webm', 'avi': 'video/x-msvideo',
    'flv': 'video/x-flv', 'wmv': 'video/x-ms-wmv', 'asf': 'video/x-ms-asf',
    '3gp': 'video/3gpp', '3g2': 'video/3gpp2', 'mpg': 'video/mpeg',
    'mpeg': 'video/mpeg', 'ogv': 'video/ogg', 'mxf': 'application/mxf',
    'm2ts': 'video/mp2t', 'vob': 'video/mpeg', 'wtv': 'video/x-ms-wtv',
}


VIDEO_FORMATS = {
    'mp4': {'label': 'MP4', 'ext': 'mp4',
        'args': [['-c', 'copy', '-movflags', '+faststart']]},
    'm4v': {'label': 'M4V', 'ext': 'm4v', 'args': [['-c', 'copy'], ['-c:v', 'libx264', '-preset', 'ultrafast', '-c:a', 'aac']]},
    'mov': {'label': 'MOV', 'ext': 'mov',
        'args': [['-c', 'copy', '-movflags', '+faststart'],
                 ['-c:v', 'libx264', '-preset', 'ultrafast', '-c:a', 'aac', '-movflags', '+faststart']]},
    'mkv':  {'label': 'MKV',  'ext': 'mkv',  'args': [['-c', 'copy'], ['-c:v', 'libx264', '-preset', 'ultrafast', '-c:a', 'aac']]},
    'webm': {'label': 'WEBM', 'ext': 'webm', 'args': [['-c', 'copy'], ['-c:v', 'libvpx-vp9', '-deadline', 'realtime', '-cpu-used', '8', '-c:a', 'libopus'], ['-c:v', 'libvpx', '-deadline', 'realtime', '-cpu-used', '8', '-c:a', 'libvorbis']]},
    'avi':  {'label': 'AVI',  'ext': 'avi',  'args': [['-c', 'copy'], ['-c:v', 'mpeg4', '-q:v', '5', '-c:a', 'libmp3lame']]},
    'flv':  {'label': 'FLV',  'ext': 'flv',  'args': [['-c', 'copy'], ['-c:v', 'flv1', '-c:a', 'libmp3lame']]},
    'wmv':  {'label': 'WMV',  'ext': 'wmv',  'args': [['-c:v', 'wmv2', '-q:v', '5', '-c:a', 'wmav2']]},
    'asf':  {'label': 'ASF',  'ext': 'asf',  'args': [['-c:v', 'wmv2', '-q:v', '5', '-c:a', 'wmav2']]},
    '3gp':  {'label': '3GP',  'ext': '3gp',  'args': [['-c', 'copy'], ['-c:v', 'mpeg4', '-c:a', 'aac']]},
    '3g2':  {'label': '3G2',  'ext': '3g2',  'args': [['-c', 'copy'], ['-c:v', 'mpeg4', '-c:a', 'aac']]},
    'mpg':  {'label': 'MPEG', 'ext': 'mpg', 'fext': 'mpeg', 'args': [['-c:v', 'mpeg2video', '-q:v', '5', '-c:a', 'mp2']]},
    'ogv':  {'label': 'OGV',  'ext': 'ogv',  'args': [['-vf', "scale='min(iw,360)':-2", '-r', '24', '-c:v', 'libtheora', '-q:v', '3', '-c:a', 'libvorbis']]},
    'mxf':  {'label': 'MXF',  'ext': 'mxf',  'args': [['-c:v', 'mpeg2video', '-q:v', '5', '-c:a', 'pcm_s16le']]},
    'm2ts': {'label': 'M2TS', 'ext': 'm2ts', 'args': [['-c', 'copy'], ['-c:v', 'libx264', '-preset', 'ultrafast', '-c:a', 'aac']]},
    'vob':  {'label': 'VOB',  'ext': 'vob',  'args': [['-c:v', 'mpeg2video', '-q:v', '5', '-c:a', 'ac3']]},
    'wtv':  {'label': 'WTV',  'ext': 'wtv',  'args': [['-c:v', 'mpeg2video', '-q:v', '5', '-c:a', 'mp2']]},
    'divx': {'label': 'DIVX', 'ext': 'avi', 'fext': 'divx', 'args': [['-c:v', 'mpeg4', '-q:v', '5', '-c:a', 'libmp3lame']]},
    'amv':  {'label': 'AMV',  'ext': 'amv',  'args': [
        ['-vf', 'scale=320:240', '-r', '15', '-b:v', '300k', '-c:v', 'amv', '-c:a', 'adpcm_ima_amv', '-ar', '22050', '-ac', '1'],
        ['-vf', 'scale=160:120', '-r', '10', '-b:v', '150k', '-c:v', 'amv', '-c:a', 'adpcm_ima_amv', '-ar', '22050', '-ac', '1'],
    ]},
    'roq':  {'label': 'ROQ',  'ext': 'roq',  'args': [
        ['-vf', "scale='min(iw,512)':-2,pad=ceil(iw/8)*8:ceil(ih/8)*8", '-r', '30', '-c:v', 'roqvideo', '-c:a', 'roq_dpcm', '-ar', '22050', '-ac', '1'],
        ['-vf', 'scale=256:256', '-r', '30', '-c:v', 'roqvideo', '-c:a', 'roq_dpcm', '-ar', '22050', '-ac', '1'],
    ]},
}


# ---------- АУДИО: ФОРМАТЫ И КАЧЕСТВА ----------
AUDIO_ORDER = ['mp2', 'mp3', 'wav', 'm4r', 'm4a', 'flac', 'ogg', 'amr']

AUDIO_FORMATS = {
    'mp2':  {'label': 'MP2',  'quals': [('64', '64k'), ('128', '128k'), ('160', '160k'), ('256', '256k')]},
    'mp3':  {'label': 'MP3',  'quals': [('64', '64k'), ('128', '128k'), ('192', '192k'), ('320', '320k')]},
    'wav':  {'label': 'WAV',  'quals': [('20', '20kHz'), ('44', '44.1kHz'), ('48', '48kHz'), ('96', '96kHz')]},
    'm4r':  {'label': 'M4R',  'quals': [('64', '64k'), ('128', '128k'), ('160', '160k'), ('256', '256k')]},
    'm4a':  {'label': 'M4A',  'quals': [('64', '64k'), ('128', '128k'), ('160', '160k'), ('256', '256k')]},
    'flac': {'label': 'FLAC', 'quals': []},
    'ogg':  {'label': 'OGG',  'quals': [('64', '64k'), ('128', '128k'), ('160', '160k'), ('256', '256k')]},
    'amr':  {'label': 'AMR',  'quals': []},
}

DOCUMENT_AUDIO = {'mp2', 'amr'}

WAV_RATES = {'20': '20000', '44': '44100', '48': '48000', '96': '96000'}

def ffmpeg_audio_args(key, q):
    if key == 'mp3':  return ['-codec:a', 'libmp3lame', '-b:a', f'{q}k']
    if key == 'mp2':  return ['-codec:a', 'mp2', '-b:a', f'{q}k']
    if key == 'wav':  return ['-codec:a', 'pcm_s16le', '-ar', WAV_RATES[q]]
    if key in ('m4a', 'm4r'): return ['-codec:a', 'aac', '-b:a', f'{q}k']
    if key == 'flac': return ['-codec:a', 'flac']
    if key == 'ogg':  return ['-codec:a', 'libvorbis', '-b:a', f'{q}k']
    if key == 'amr':  return ['-codec:a', 'libopencore_amrwb']
    raise Exception(f'Неизвестный аудиоформат: {key}')

def ffmpeg_audio_argsets(key, q):
    if key == 'amr':
        return [
            ['-c:a', 'amr_nb', '-ar', '8000', '-ac', '1'],
            ['-c:a', 'libopencore_amrnb', '-ar', '8000', '-ac', '1'],
            ['-c:a', 'libopencore_amrwb', '-ar', '16000', '-ac', '1'],
        ]
    return [ffmpeg_audio_args(key, q)]

def quality_label(key, q):
    label = AUDIO_FORMATS[key]['label']
    if not q:
        return label
    ql = dict(AUDIO_FORMATS[key]['quals']).get(q, q)
    return f"{label} {ql}"

# ---------- TIKTOK: КНОПКИ ----------
TT_CHOICES = {
    'tt_video': ('video', 'video', 'TIKTOK'),
    'tt_hd':    ('hd',    'video', 'TIKTOK HD'),
    'tt_audio': ('music', 'audio', 'MP3'),
}

PROXY = None
# Для requests/yt-dlp сокс-прокси задаётся как 'socks5h://host:port' (буква
# 'h' — резолвить DNS на стороне прокси, что важно для Tor). Playwright же
# понимает только 'socks5://' без 'h' — эта функция сама убирает разницу,
# чтобы PROXY можно было задать один раз в одном формате.
def playwright_proxy_server(proxy):
    if not proxy:
        return None
    return proxy.replace('socks5h://', 'socks5://')

# ---------- ПОИСК ССЫЛКИ ----------
URL_REGEX = re.compile(r'https?://[^\s]+')

def find_url(text):
    if not text:
        return None
    m = URL_REGEX.search(text)
    if not m:
        return None
    return m.group(0).rstrip('.,;:!?»')

# ---------- УТИЛИТЫ ----------
esc = html.escape

# ---------- ЯЗЫКОВЫЕ ДОРОЖКИ И СУБТИТРЫ: ФЛАГИ ----------
# base-код языка (без региона) -> (флаг страны, отображаемая метка)
LANG_INFO = {
    'ru': ('🇷🇺', 'RU'), 'en': ('🇺🇸', 'EN'), 'es': ('🇪🇸', 'ES'),
    'fr': ('🇫🇷', 'FR'), 'de': ('🇩🇪', 'DE'), 'it': ('🇮🇹', 'IT'),
    'pt': ('🇵🇹', 'PT'), 'ja': ('🇯🇵', 'JA'), 'ko': ('🇰🇷', 'KO'),
    'zh': ('🇨🇳', 'ZH'), 'ar': ('🇸🇦', 'AR'), 'hi': ('🇮🇳', 'HI'),
    'tr': ('🇹🇷', 'TR'), 'pl': ('🇵🇱', 'PL'), 'uk': ('🇺🇦', 'UK'),
    'nl': ('🇳🇱', 'NL'), 'sv': ('🇸🇪', 'SV'), 'cs': ('🇨🇿', 'CS'),
    'vi': ('🇻🇳', 'VI'), 'th': ('🇹🇭', 'TH'), 'id': ('🇮🇩', 'ID'),
    'ro': ('🇷🇴', 'RO'), 'hu': ('🇭🇺', 'HU'), 'el': ('🇬🇷', 'EL'),
    'he': ('🇮🇱', 'HE'), 'iw': ('🇮🇱', 'HE'), 'fa': ('🇮🇷', 'FA'),
    'bn': ('🇧🇩', 'BN'), 'ms': ('🇲🇾', 'MS'), 'fi': ('🇫🇮', 'FI'),
    'no': ('🇳🇴', 'NO'), 'da': ('🇩🇰', 'DA'), 'sk': ('🇸🇰', 'SK'),
    'bg': ('🇧🇬', 'BG'), 'hr': ('🇭🇷', 'HR'), 'sr': ('🇷🇸', 'SR'),
    'lt': ('🇱🇹', 'LT'), 'lv': ('🇱🇻', 'LV'), 'et': ('🇪🇪', 'ET'),
    'ka': ('🇬🇪', 'KA'), 'az': ('🇦🇿', 'AZ'), 'kk': ('🇰🇿', 'KK'),
    'uz': ('🇺🇿', 'UZ'), 'ur': ('🇵🇰', 'UR'), 'sw': ('🇹🇿', 'SW'),
}

def lang_display(code):
    """'ru' -> '🇷🇺 RU', 'en-US' -> '🇺🇸 EN', неизвестный код -> '🌐 XX'."""
    if not code:
        return '🌐 ?'
    # Особый случай: у китайского YouTube различает варианты письменности
    # (zh-Hans/zh-Hant) — если сворачивать их до общего 'zh', обе кнопки
    # выглядят одинаково и пользователь не может их различить.
    if code.lower() in ('zh-hans', 'zh-hant'):
        flag, _ = LANG_INFO.get('zh', ('🌐', 'ZH'))
        suffix = 'CN' if code.lower() == 'zh-hans' else 'TW'
        return f"{flag} ZH-{suffix}"
    base = code.split('-')[0].lower()
    flag, label = LANG_INFO.get(base, ('🌐', code.upper()))
    return f"{flag} {label}"

def arrow_link(href):
    return f'<a href="{html.escape(href, quote=True)}">↗</a>'

def sanitize_filename(name, max_len=60):
    name = re.sub(r'[\\/:*?"<>|\r\n]', ' ', name or '')
    name = re.sub(r'\s+', ' ', name).strip(' .')
    name = name[:max_len]
    # Защита от задвоенного расширения (Title.m4r.mp3): если конец
    # названия совпадает с одним из известных медиа-расширений — это
    # почти наверняка мусор, случайно прилипший к названию на одном из
    # предыдущих скачиваний в другом формате, а не часть настоящего
    # названия видео.
    for ext in ALL_EXTS:
        if name.lower().endswith(ext):
            name = name[:-len(ext)].rstrip(' .')
            break
    return name or 'video'

ALL_EXTS = ('.mp4', '.mp3', '.mkv', '.webm', '.m4a', '.opus', '.ogg',
            '.mp2', '.wav', '.m4r', '.flac', '.amr',
            '.m4v', '.mov', '.avi', '.flv', '.wmv', '.asf', '.3gp', '.3g2',
            '.mpg', '.mpeg', '.ogv', '.mxf', '.m2ts', '.vob', '.wtv', '.divx',
            '.amv', '.roq')

def base_path_for(title, video_id):
    return os.path.join(DOWNLOAD_DIR, f"{sanitize_filename(title)} [{video_id}]")

def find_downloaded_file(base_path):
    for ext in ALL_EXTS:
        p = base_path + ext
        if os.path.exists(p):
            return p
    return None

def cleanup_base(base_path):
    for ext in ALL_EXTS:
        p = base_path + ext
        if os.path.exists(p):
            try:
                os.remove(p)
            except OSError:
                pass

def format_file_size(n):
    if not n:
        return None
    n = float(n)
    for unit in ('Б', 'КБ', 'МБ', 'ГБ'):
        if n < 1024.0:
            return f"{n:.1f} {unit}"
        n /= 1024.0
    return f"{n:.1f} ТБ"

# ---------- ПРОГРЕСС: ПОЛОСКА + ТРОТТЛИНГ РЕДАКТИРОВАНИЯ СООБЩЕНИЯ ----------
def progress_bar(percent, width=12):
    percent = max(0, min(100, int(percent)))
    filled = round(width * percent / 100)
    return '🟩' * filled + '⬜' * (width - filled) + f' {percent}%'

class ProgressReporter:
    """Оборачивает edit_message_text с троттлингом: Telegram банит за
    слишком частые правки одного сообщения (flood control), поэтому
    обновляем не чаще раза в ~2.5 сек и только если процент заметно
    сдвинулся (или дошли до 100%)."""
    def __init__(self, chat_id, message_id, prefix, min_interval=2.5, min_delta=3):
        self.chat_id = chat_id
        self.message_id = message_id
        self.prefix = prefix
        self.min_interval = min_interval
        self.min_delta = min_delta
        self._last_time = 0
        self._last_percent = -100

    def update(self, percent, extra=''):
        now = time.time()
        percent = max(0, min(100, int(percent)))
        if (percent < 100 and percent - self._last_percent < self.min_delta
                and now - self._last_time < self.min_interval):
            return
        self._last_time = now
        self._last_percent = percent
        text = f"{self.prefix}\n{progress_bar(percent)}"
        if extra:
            text += f"\n{extra}"
        try:
            bot.edit_message_text(text, chat_id=self.chat_id, message_id=self.message_id)
        except Exception:
            pass  # "message is not modified" и подобное — не критично

def make_ytdlp_progress_hook(reporter, phase="⏳ Скачиваю"):
    def hook(d):
        if d.get('status') == 'downloading':
            total = d.get('total_bytes') or d.get('total_bytes_estimate')
            downloaded = d.get('downloaded_bytes') or 0
            if total:
                percent = downloaded * 100 / total
                speed = d.get('speed')
                extra = f"{format_file_size(downloaded)} / {format_file_size(total)}"
                if speed:
                    extra += f" · {format_file_size(speed)}/с"
                reporter.update(percent, extra)
        elif d.get('status') == 'finished':
            reporter.update(99, "Обрабатываю файл...")
    return hook

def make_ffmpeg_progress_hook(reporter, duration, phase="⏳ Конвертирую"):
    """duration — длительность исходника в секундах (см. probe_duration_ffmpeg).
    Возвращает функцию, которую нужно звать на каждой строке stdout ffmpeg,
    запущенного с флагом -progress pipe:1."""
    def on_line(line):
        if not duration or not line.startswith('out_time_ms='):
            return
        try:
            out_us = int(line.split('=', 1)[1].strip())
            percent = (out_us / 1_000_000) * 100 / duration
            reporter.update(percent)
        except (ValueError, ZeroDivisionError):
            pass
    return on_line

def format_duration(sec):
    if not sec:
        return None
    sec = int(sec)
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    return f"{h}h, {m}m, {s}s" if h else f"{m}m, {s}s"

def format_count(n):
    try:
        return f"{int(n):,}".replace(',', ' ')
    except Exception:
        return None

def format_date(d):
    if d and len(d) == 8 and d.isdigit():
        return f"{d[6:8]}.{d[4:6]}.{d[0:4]}"
    return None

def format_ts(ts):
    try:
        return time.strftime('%d.%m.%Y', time.localtime(int(ts)))
    except Exception:
        return None

def slug_from_url(url):
    try:
        parts = [p for p in url.split('?')[0].rstrip('/').split('/') if p]
        return parts[-1] or None
    except Exception:
        return None

def _eff_res(f):
    h = f.get('height') or 0
    w = f.get('width') or 0
    return min(h, w) if h and w else h

def exact_format_size(fmt, timeout=6):
    """Точный размер конкретного формата в байтах — без скачивания файла.
    Если yt-dlp уже знает filesize (не approx), используем его. Иначе
    спрашиваем у CDN заголовок Content-Length через HEAD (а если сервер
    не отвечает на HEAD нормально — через Range-запрос на 1 байт)."""
    fs = fmt.get('filesize')
    if fs:
        return fs
    url = fmt.get('url')
    if not url:
        return fmt.get('filesize_approx')
    headers = dict(fmt.get('http_headers') or {})
    headers.setdefault('User-Agent', UA)
    try:
        r = requests.head(url, headers=headers, timeout=timeout, allow_redirects=True)
        cl = r.headers.get('Content-Length')
        if cl and cl.isdigit():
            return int(cl)
    except Exception:
        pass
    try:
        r = requests.get(url, headers={**headers, 'Range': 'bytes=0-0'},
                         timeout=timeout, stream=True)
        cr = r.headers.get('Content-Range')  # формат: bytes 0-0/1234567
        if cr and '/' in cr:
            return int(cr.rsplit('/', 1)[-1])
    except Exception:
        pass
    return fmt.get('filesize_approx')

def _best_audio_pool(formats):
    audio = [f for f in formats
             if f.get('vcodec') in (None, 'none') and f.get('acodec') not in (None, 'none')]
    m4a = [f for f in audio if f.get('ext') == 'm4a']
    return m4a or audio

def estimate_quality_rows(info, exact=True):
    rows = []
    formats = info.get('formats') or []

    video = [f for f in formats if f.get('vcodec') not in (None, 'none')]
    apool = _best_audio_pool(formats)
    af = max(apool, key=lambda f: f.get('abr') or f.get('tbr') or 0) if apool else None

    prev = 0
    for h in (144, 240, 360, 480, 720, 1080):
        cand = [f for f in video if prev < _eff_res(f) <= h]
        prev = h
        if not cand:
            continue
        # Реальное скачивание (_video_spec) сначала пытается взять mp4 —
        # оцениваем размер по тому же приоритету, иначе оценка берётся из
        # более тяжёлого webm/vp9-потока, который на самом деле не скачается.
        mp4_cand = [f for f in cand if f.get('ext') == 'mp4']
        pool = mp4_cand or cand
        vf = max(pool, key=lambda f: (f.get('tbr') or f.get('vbr') or 0))

        has_audio = vf.get('acodec') not in (None, 'none')
        if exact:
            size = exact_format_size(vf)
            if size and not has_audio and af:
                a_size = exact_format_size(af)
                if a_size:
                    size += a_size
        else:
            size = vf.get('filesize') or vf.get('filesize_approx')

        size_str = format_file_size(size)
        res = (f"{vf['width']}×{vf['height']}"
               if vf.get('width') and vf.get('height') else None)
        rows.append((h, size_str, res, size))
    return rows

def get_audio_track_codes(info):
    """Список уникальных кодов языков аудиодорожек (для мультиязычных видео
    с дубляжом на YouTube). Порядок — по первому появлению в списке форматов."""
    codes = []
    for f in (info.get('formats') or []):
        if f.get('acodec') in (None, 'none'):
            continue
        code = f.get('language')
        if code and code not in codes:
            codes.append(code)
    return codes

def get_subtitle_tracks(info):
    """{код_языка: {'manual': bool, 'auto': bool}} — из yt-dlp info. Список
    automatic_captions тут содержит ВСЕ ~100+ языков, которые YouTube
    теоретически умеет переводить — не то же самое, что реально доступно
    для конкретного видео. Используется только как фолбэк, когда
    youtube-transcript-api недоступна (см. get_real_subtitle_tracks)."""
    tracks = {}
    for code in (info.get('subtitles') or {}):
        tracks[code] = {'manual': True, 'auto': False}
    for code in (info.get('automatic_captions') or {}):
        if code in tracks:
            tracks[code]['auto'] = True
        else:
            tracks[code] = {'manual': False, 'auto': True}
    return tracks

# Языки автоперевода, которые предлагаем в меню — реальную доступность
# каждого из них всё равно проверяем через translation_languages,
# так что список тут — просто разумный потолок, чтобы не заваливать
# пользователя полусотней кнопок для языков, которые он не читает.
POPULAR_SUB_LANGS = {'ru', 'en', 'uk', 'es', 'pt', 'fr', 'de', 'it', 'tr',
                     'ar', 'hi', 'ja', 'ko', 'zh-Hans', 'zh-Hant', 'pl', 'id'}

def get_real_subtitle_tracks(video_id):
    """Настоящий список языков субтитров для конкретного видео через
    youtube-transcript-api: {код: {'manual': bool, 'auto': bool}}.
    В отличие от yt-dlp, translation_languages тут — это то, что YouTube
    подтверждает как реально переводимое для ЭТОГО видео, а не общий
    список из ~100 языков «в теории». Возвращает None при ошибке/если
    библиотека не установлена — тогда используем старый фолбэк."""
    if not HAS_TRANSCRIPT_API:
        return None
    try:
        proxy_cfg = GenericProxyConfig(http_url=PROXY, https_url=PROXY) if PROXY else None
        ytt_api = YouTubeTranscriptApi(proxy_config=proxy_cfg) if proxy_cfg else YouTubeTranscriptApi()
        transcript_list = ytt_api.list(video_id)
    except Exception as e:
        logger.warning("youtube-transcript-api list() не удалась: %s", e)
        return None

    tracks = {}
    primary = None
    for t in transcript_list:
        tracks[t.language_code] = {'manual': not t.is_generated,
                                   'auto': t.is_generated}
        if primary is None or not t.is_generated:
            primary = t  # предпочитаем ручные субтитры как источник перевода

    if primary is not None and getattr(primary, 'is_translatable', False):
        for lang in primary.translation_languages:
            code = lang['language_code'] if isinstance(lang, dict) else lang.language_code
            if code in tracks:
                continue
            if code in POPULAR_SUB_LANGS:
                tracks[code] = {'manual': False, 'auto': True}
    return tracks

def audio_lang_filter(lang):
    return f"[language={lang}]" if lang else ""

def video_spec_lang(h, lang=None):
    lf = audio_lang_filter(lang)
    return (
        f"bestvideo[height<={h}][ext=mp4]+bestaudio[ext=m4a]{lf}"
        f"/bestvideo[width<={h}][ext=mp4]+bestaudio[ext=m4a]{lf}"
        f"/bestvideo[height<={h}][ext=mp4]+bestaudio{lf}"
        f"/best[height<={h}][ext=mp4]"
        f"/best[width<={h}][ext=mp4]"
        f"/best[ext=mp4]/best"
    )

def audio_spec_lang(abr, lang=None):
    lf = audio_lang_filter(lang)
    return f"bestaudio[abr<={abr}]{lf}/bestaudio{lf}/bestaudio[abr<={abr}]/bestaudio"

def format_selector_for(choice, lang=None):
    """Строит селектор формата yt-dlp для базового 'choice' (без учёта
    языка, если он не передан) — с фильтром по языку дорожки, когда lang
    указан. Если choice не про качество видео/аудио (напр. 'best'),
    возвращает статичный вариант из QUALITY_OPTIONS как есть."""
    if choice in VIDEO_QUALITIES:
        h = int(choice.rstrip('p'))
        return video_spec_lang(h, lang)
    if choice.startswith('audio_'):
        abr = choice.split('_', 1)[1]
        return audio_spec_lang(abr, lang)
    return QUALITY_OPTIONS.get(choice, choice)

def cache_key_for(choice, lang=None):
    """Кэш определённого качества/формата должен быть отдельным для каждой
    языковой дорожки — иначе после переключения языка бот мгновенно
    подсунет из кэша файл со старым языком под видом нового."""
    return f"{choice}@{lang}" if lang else choice

def download_thumbnail(url, video_id):
    if not url:
        return None
    try:
        r = requests.get(url, timeout=30, headers={'User-Agent': UA})
        if r.ok and r.content:
            path = os.path.join(DOWNLOAD_DIR, f"{video_id}_thumb.jpg")
            with open(path, 'wb') as f:
                f.write(r.content)
            return path
    except Exception as e:
        logger.warning("Не удалось скачать превью: %s", e)
    return None

def get_thumbnail_url(data):
    info = data.get('info') or {}
    tt = data.get('tiktok') or {}
    vc = data.get('vimeo_cobalt') or {}
    return info.get('thumbnail') or tt.get('cover') or vc.get('cover')

def make_telegram_video_thumb(src_thumb_path, video_id, target_w=None, target_h=None):
    """Превью для видео: JPEG ≤320×320 и <200 КБ.
    Главное: обложка кропается ПО ЦЕНТРУ под аспект реального видео.
    YouTube для шортсов отдаёт превью горизонтальной картинкой с серыми
    полями по бокам (вертикальный кадр вписан в центр) — если такую
    вписать целиком, телефон покажет серые столбы, а Desktop сам срежет
    их кавер-кропом (отсюда разница телефон/ПК). Центральный кроп под
    аспект видео чинит оба клиента сразу; для обычных горизонтальных
    видео превью и так 16:9 — кроп ничего не меняет."""
    if not src_thumb_path:
        return None
    out_path = os.path.join(DOWNLOAD_DIR, f"{video_id}_tgthumb.jpg")
    if target_w and target_h:
        ar = target_w / target_h
        # Центральный кроп под аспект видео (crop сам центрирует, если
        # x/y не указаны). Запятые внутри min() защищены одинарными
        # кавычками синтаксиса filtergraph.
        vf = (f"crop='min(iw,ih*{ar})':'min(ih,iw/{ar})',"
              f"scale='min(320,iw)':'min(320,ih)':force_original_aspect_ratio=decrease")
    else:
        vf = "scale='min(320,iw)':'min(320,ih)':force_original_aspect_ratio=decrease"
    try:
        subprocess.run(
            [FFMPEG_BIN, '-y', '-i', src_thumb_path,
             '-vf', vf,
             '-q:v', '5', out_path],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=15)
        if os.path.exists(out_path) and 0 < os.path.getsize(out_path) <= 200_000:
            return out_path
        if os.path.exists(out_path):
            try:
                os.remove(out_path)
            except OSError:
                pass
    except Exception as e:
        logger.warning("Не удалось подготовить превью для видео: %s", e)
    return None

def download_direct(url, dest_path):
    with requests.get(url, stream=True, timeout=120,
                      headers={'User-Agent': UA}) as r:
        r.raise_for_status()
        with open(dest_path, 'wb') as f:
            for chunk in r.iter_content(1024 * 1024):
                if chunk:
                    f.write(chunk)
    return dest_path

def download_direct_headers(url, dest_path, headers, proxies=None):
    with requests.get(url, stream=True, timeout=180, headers=headers,
                      proxies=proxies) as r:
        r.raise_for_status()
        with open(dest_path, 'wb') as f:
            for chunk in r.iter_content(1024 * 1024):
                if chunk:
                    f.write(chunk)
    return dest_path

def download_tiktok_url(url, dest_path, tt_data):
    """Качает файл по ссылке из tiktok-провайдера с учётом того, что для
    Playwright-провайдера (гео-блок) нужны свой Referer и, возможно, тот
    же прокси, что открывал страницу — иначе CDN отдаст 403/пустоту."""
    headers = tt_data.get('fetch_headers') or {'User-Agent': UA}
    proxies = None
    if tt_data.get('fetch_via_proxy') and PROXY:
        proxies = {'http': PROXY, 'https': PROXY}
    return download_direct_headers(url, dest_path, headers, proxies=proxies)

# ---------- КЛАВИАТУРЫ ----------
def build_video_kb(data):
    kb = InlineKeyboardMarkup()
    video_id = data.get('video_id')
    if data.get('source') == 'tiktok':
        d = data['tiktok']
        sizes = d.get('sizes') or {}
        vs = format_file_size(sizes.get('video'))
        v_icon = '🚀' if is_cached(video_id, 'tt_video') else '🎥'
        kb.row(InlineKeyboardButton(
            f"{v_icon} Видео" + (f": {vs}" if vs else ""), callback_data='tt_video'))
        if d['downloads'].get('hd'):
            hs = format_file_size(sizes.get('hd'))
            hd_icon = '🚀' if is_cached(video_id, 'tt_hd') else '✨'
            kb.row(InlineKeyboardButton(
                f"{hd_icon} HD" + (f": {hs}" if hs else ""), callback_data='tt_hd'))
        kb.row(InlineKeyboardButton("🎬 Формат видео", callback_data='vfmenu'))
        if d['downloads'].get('music'):
            kb.row(InlineKeyboardButton("🎵 Аудио", callback_data='amenu'))
        return kb

    if data.get('source') == 'bilibili':
        d = data['bilibili']
        q = d.get('quality')
        icon = '🚀' if is_cached(video_id, 'bili_dl') else '⬇️'
        label = f"{icon} Скачать" + (f" (q{q})" if q else "")
        kb.row(InlineKeyboardButton(label, callback_data='bili_dl'))
        return kb

    if data.get('source') == 'vimeo_cobalt':
        icon = '🚀' if is_cached(video_id, 'vimeo_cobalt_dl') else '⬇️'
        kb.row(InlineKeyboardButton(f"{icon} Скачать (через Cobalt)",
                                    callback_data='vimeo_cobalt_dl'))
        return kb

    if data.get('source') == 'vimeo_direct':
        d = data.get('vimeo_direct') or {}
        best = (d.get('files') or [{}])[0]
        q = best.get('quality') or best.get('height')
        icon = '🚀' if is_cached(video_id, 'vimeo_direct_dl') else '⬇️'
        label = f"{icon} Скачать" + (f" ({q}p)" if isinstance(q, int) else f" ({q})" if q else "")
        kb.row(InlineKeyboardButton(label, callback_data='vimeo_direct_dl'))
        return kb

    info = data.get('info') or {}
    lang = data.get('lang_sel')

    # ---- Языковые дорожки (дубляж) — только если их реально несколько ----
    lang_codes = get_audio_track_codes(info)
    if len(lang_codes) > 1:
        lb = []
        for code in lang_codes:
            mark = '✅ ' if code == lang else ''
            lb.append(InlineKeyboardButton(
                f"{mark}{lang_display(code)}", callback_data=f'setlang_{code}'))
        for i in range(0, len(lb), 4):
            kb.row(*lb[i:i + 4])

    rows = estimate_quality_rows(info)
    if rows:
        for h, size_str, res, size_bytes in rows:
            choice = f"{h}p"
            icon = '🚀' if is_cached(video_id, cache_key_for(choice, lang)) else '🎞'
            label = f"{icon} {h}p"
            if size_str:
                label += f": {size_str}"
            if res:
                label += f" ({res})"
            if size_bytes and size_bytes > MAX_PART_BYTES:
                n_parts = math.ceil(size_bytes / MAX_PART_BYTES)
                label += f"  ✂️{n_parts}"
            kb.row(InlineKeyboardButton(label, callback_data=choice))
    else:
        for q in ('720p', '480p', '360p'):
            icon = '🚀' if is_cached(video_id, cache_key_for(q, lang)) else '🎥'
            kb.row(InlineKeyboardButton(f"{icon} {q}", callback_data=q))
    kb.row(InlineKeyboardButton("🎬 Формат видео", callback_data='vfmenu'))
    kb.row(InlineKeyboardButton("🎵 Аудио", callback_data='amenu'))
    if get_subtitle_tracks(info):
        kb.row(InlineKeyboardButton("💬 Субтитры", callback_data='submenu'))
    if data.get('sniff_candidates') and len(data['sniff_candidates']) > 1:
        kb.row(InlineKeyboardButton("🔁 Это не то видео? Другой поток",
                                    callback_data='sniff_back'))
    return kb

def video_format_keyboard(sel, video_id=None, lang=None):
    kb = InlineKeyboardMarkup()
    btns = []
    for key in VIDEO_ORDER:
        label = VIDEO_FORMATS[key]['label']
        text = f"• {label}" if key == sel else label
        btns.append(InlineKeyboardButton(text, callback_data=f'vfmt_{key}'))
    for i in range(0, len(btns), 4):
        kb.row(*btns[i:i + 4])
    q_btns = []
    for q in VIDEO_QUALITIES:
        choice = f"vdl_{sel}_{q}"
        icon = '🚀' if is_cached(video_id, cache_key_for(choice, lang)) else ''
        q_btns.append(InlineKeyboardButton(f"{icon}{q}", callback_data=choice))
    kb.row(*q_btns)
    kb.row(InlineKeyboardButton("⬅️ Назад к карточке", callback_data='vback'))
    return kb

def audio_keyboard(sel, video_id=None, lang=None):
    kb = InlineKeyboardMarkup()
    btns = []
    for key in AUDIO_ORDER:
        label = AUDIO_FORMATS[key]['label']
        text = f"• {label}" if key == sel else label
        btns.append(InlineKeyboardButton(text, callback_data=f'afmt_{key}'))
    for i in range(0, len(btns), 4):
        kb.row(*btns[i:i + 4])
    fmt = AUDIO_FORMATS[sel]
    if fmt['quals']:
        a_btns = []
        for q, ql in fmt['quals']:
            choice = f"adl_{sel}_{q}"
            icon = '🚀 ' if is_cached(video_id, cache_key_for(choice, lang)) else ''
            a_btns.append(InlineKeyboardButton(f"{icon}{fmt['label']} {ql}", callback_data=choice))
        kb.row(*a_btns)
    else:
        choice = f"adl_{sel}"
        icon = '🚀 ' if is_cached(video_id, cache_key_for(choice, lang)) else '⬇️ '
        kb.row(InlineKeyboardButton(f"{icon}{fmt['label']}", callback_data=choice))
    kb.row(InlineKeyboardButton("⬅️ Назад к видео", callback_data='vmenu'))
    return kb

def sub_lang_keyboard(data):
    """Клавиатура выбора языка субтитров. None, если субтитров нет вообще.

    Сначала пробуем реальный, проверенный список через
    youtube-transcript-api (get_real_subtitle_tracks) — он не врёт про
    то, что действительно можно скачать для ЭТОГО видео. Если библиотека
    не установлена/недоступна — откатываемся на старый способ через
    yt-dlp info с обрезкой до популярных языков (менее точно, но лучше,
    чем ничего)."""
    video_id = data.get('video_id')
    tracks = get_real_subtitle_tracks(video_id) if video_id else None
    data['sub_tracks_verified'] = tracks is not None
    if tracks is None:
        info = data.get('info') or {}
        raw = get_subtitle_tracks(info)
        tracks = {code: f for code, f in raw.items()
                 if f['manual'] or code in POPULAR_SUB_LANGS} or raw
    if not tracks:
        return None
    kb = InlineKeyboardMarkup()
    btns = []
    for code, flags in tracks.items():
        ck = f"sub_{code}"
        icon = '🚀 ' if is_cached(video_id, ck) else ''
        label = f"{icon}{lang_display(code)}"
        if not flags['manual']:
            label += ' 🤖'  # только автосубтитры (автоперевод) для этого языка
        btns.append(InlineKeyboardButton(label, callback_data=ck))
    for i in range(0, len(btns), 3):
        kb.row(*btns[i:i + 3])
    kb.row(InlineKeyboardButton("⬅️ Назад к видео", callback_data='vmenu'))
    return kb

# ---------- ИТОГОВАЯ ПОДПИСЬ ----------
def channel_permalink(info):
    """Постоянная ссылка на YouTube-канал, которая не сломается, даже если
    владелец сменит @юзернейм — используем стабильный channel_id (UC...),
    а не uploader_url/channel_url (который может быть на основе хендла)."""
    cid = info.get('channel_id') or info.get('uploader_id')
    if cid and str(cid).startswith('UC'):
        return f"https://www.youtube.com/channel/{cid}"
    return info.get('channel_url') or info.get('uploader_url')

TG_CAPTION_LIMIT = 1024      # жёсткий лимit Telegram на подпись к файлу
DESC_MAX_QUOTE_LEN = 600     # не хотим, чтобы цитата растягивалась на пол-экрана

def format_description_block(description, remaining_budget):
    """Готовит HTML-цитату описания под оставшийся бюджет символов подписи.
    Возвращает (html_блок, поместилось_ли_описание_целиком). Если места
    почти нет — не впихиваем обрывок на 5 слов, лучше вообще без цитаты
    (полное описание всё равно уйдёт отдельным файлом)."""
    if not description:
        return '', True
    limit = max(0, min(remaining_budget, DESC_MAX_QUOTE_LEN))
    if limit < 40:
        return '', False
    text = description.strip()
    full_included = len(text) <= limit
    if not full_included:
        text = text[:limit - 1].rstrip() + '…'
    return f"\n<blockquote expandable=\"expandable\">📝 {esc(text)}</blockquote>", full_included

def needs_full_description_file(data):
    """True, если описание не поместилось целиком в подпись — только тогда
    имеет смысл слать его отдельным файлом (иначе это просто дублирование
    того же текста, который человек и так уже видит в подписи)."""
    info = data.get('info') or {}
    full_desc = (data.get('description') or info.get('description') or '').strip()
    return len(full_desc) > DESC_MAX_QUOTE_LEN

def build_final_caption(data, file_size, quality_text):
    info = data.get('info') or {}
    tt = data.get('tiktok') or {}
    cap = f"🎬 <b>{esc(data['title'])}</b> {arrow_link(data['url'])}\n"
    uploader = info.get('uploader') or info.get('channel') or tt.get('author')
    if uploader:
        line = f"📺 {esc(uploader)}"
        churl = channel_permalink(info) or tt.get('author_url')
        if churl:
            line += ' ' + arrow_link(churl)
        cap += line + '\n'
    site = info.get('extractor_key')
    if site and site.lower() != 'generic':
        cap += f"🌐 {esc(site)}\n"
    meta = []
    date = format_date(info.get('upload_date')) or tt.get('date_str')
    if date:
        meta.append(f"📅 {date}")
    dur = format_duration(info.get('duration') or tt.get('duration'))
    if dur:
        meta.append(f"⏱ {dur}")
    res = (f"{info['width']}×{info['height']}"
           if info.get('width') and info.get('height') else info.get('resolution'))
    if res:
        meta.append(f"🖥 {res}")
    if meta:
        cap += '  '.join(meta) + '\n'
    stats = []
    views = format_count(info.get('view_count') or tt.get('views'))
    if views:
        stats.append(f"👁 {views}")
    likes = format_count(info.get('like_count') or tt.get('likes'))
    if likes:
        stats.append(f"❤️ {likes}")
    comments = format_count(info.get('comment_count'))
    if comments:
        stats.append(f"💬 {comments}")
    if stats:
        cap += '  '.join(stats) + '\n'
    cap += f"📦 {format_file_size(file_size)}\n"
    cap += f"⚙️ {quality_text}"

    description = (data.get('description') or info.get('description') or '').strip()
    remaining = TG_CAPTION_LIMIT - len(cap) - 40  # запас на теги цитаты
    desc_block, _ = format_description_block(description, remaining)
    cap += desc_block
    return cap

# ================================================================
#  TIKTOK: ПРОВАЙДЕРЫ
# ================================================================
def abs_tikwm(u):
    if not u:
        return None
    return u if u.startswith('http') else 'https://www.tikwm.com' + u

def _proxies_dict():
    """Общий словарь для requests(proxies=...). ВАЖНО: сертификатные ошибки
    и у tiklydown (Hostname mismatch), и у cobalt (self-signed) на двух
    независимых доменах одновременно — это не "у них сломан сертификат",
    это классический признак того, что провайдер/сеть между вами и этими
    серверами подменяет TLS-сертификат (DPI/перехват трафика на уровне
    провайдера — в России такое практикуется для части зарубежных
    доменов). Через прокси/Tor этот перехват остаётся СНАРУЖИ
    зашифрованного туннеля и не может подменить сертификат внутри него —
    поэтому имеет смысл гнать через PROXY вообще все обращения к TikTok
    провайдерам, а не только Playwright."""
    return {'http': PROXY, 'https': PROXY} if PROXY else None

def prov_tikwm(url):
    api = 'https://www.tikwm.com/api/?url=' + quote(url, safe='')
    r = requests.get(api, timeout=30, headers={'User-Agent': UA}, proxies=_proxies_dict())
    r.raise_for_status()
    j = r.json()
    if j.get('code') != 0 or not j.get('data'):
        raise Exception(f"code={j.get('code')} msg={j.get('msg')}")
    d = j['data']
    author = d.get('author') or {}
    unique_id = author.get('unique_id')
    return {
        'title': d.get('title'),
        'author': author.get('nickname'),
        'author_url': f"https://www.tiktok.com/@{unique_id}" if unique_id else None,
        'video_id': str(d.get('id') or slug_from_url(url) or 'tiktok'),
        'duration': d.get('duration'),
        'views': d.get('play_count'),
        'likes': d.get('digg_count'),
        'cover': abs_tikwm(d.get('cover')) or abs_tikwm(d.get('origin_cover')),
        'date_str': format_ts(d.get('create_time')),
        'downloads': {
            'video': abs_tikwm(d.get('play')),
            'hd':    abs_tikwm(d.get('hd')),
            'audio': abs_tikwm(d.get('music')),
            'music': abs_tikwm(d.get('music')),
        },
        'sizes': {
            'video': d.get('size'),
            'hd':    d.get('hd_size'),
            'audio': d.get('music_size'),
        },
    }

def prov_tiklydown(url):
    # api.tiklydown.me не резолвится (мёртвый домен) — оставляем только
    # живой eu.org (подтверждено его собственной статус-страницей). Раньше
    # цикл пробовал оба и запоминал ТОЛЬКО последнюю ошибку — то есть в
    # логах всегда была бы ошибка мёртвого .me, а настоящая причина отказа
    # живого eu.org терялась.
    host = 'https://api.tiklydown.eu.org'
    r = requests.get(host + '/api/download?url=' + quote(url, safe=''),
                     timeout=30, headers={'User-Agent': UA}, proxies=_proxies_dict())
    r.raise_for_status()
    j = r.json()
    video = (j.get('video') or {}).get('noWatermark')
    if not video:
        raise Exception(f'нет ссылки на видео (ответ: {str(j)[:200]})')
    author = j.get('author') or {}
    username = author.get('username')
    return {
        'title': j.get('title'),
        'author': author.get('name'),
        'author_url': f"https://www.tiktok.com/@{username}" if username else None,
        'video_id': str(slug_from_url(url) or 'tiktok'),
        'duration': None, 'views': None, 'likes': None,
        'cover': None, 'date_str': None,
        'downloads': {'video': video, 'hd': None,
                      'audio': j.get('music'), 'music': j.get('music')},
        'sizes': {},
    }

COBALT_INSTANCES = (
    'https://cobalt-api.meow.lol',
    'https://blossom.imput.net',
    'https://nachos.imput.net',
)

# instances.cobalt.best поддерживает community-инстансы Cobalt и регулярно
# сам их прогоняет тестами по сервисам (youtube/tiktok/vimeo/...), отдавая
# результат по каждому open API. Захардкоженные адреса выше со временем
# протухают (сертификаты, забаненные IP, исчерпанный трафик у хозяина) —
# независимо друг от друга. Плюс у Cobalt именно Vimeo нередко упирается в
# "blocked by cloudflare" даже на живых инстансах — это НЕ наша проблема
# с сертификатами, а ограничение на стороне конкретного инстанса. Поэтому
# для Vimeo спрашиваем сайт, какие инстансы прямо сейчас живые И у кого
# именно vimeo реально работает, вместо слепого перебора статического списка.
COBALT_DIRECTORY_API = 'https://instances.cobalt.best/api'
_cobalt_instance_cache = {'ts': 0, 'urls': []}
COBALT_INSTANCE_CACHE_TTL = 600  # 10 минут — не долбить каталог на каждое скачивание

def discover_cobalt_instances(service='vimeo', limit=6):
    """Живой список Cobalt-инстансов, у которых конкретно `service`
    (например 'vimeo') реально проходит тест на instances.cobalt.best —
    отсортированный по их score (чем выше — тем стабильнее инстанс).
    При любой ошибке просто возвращает [] — вызывающий код в этом случае
    откатывается на статический COBALT_INSTANCES."""
    now = time.time()
    cache_key = service
    cached = _cobalt_instance_cache.get(cache_key)
    if cached and now - cached[0] < COBALT_INSTANCE_CACHE_TTL:
        return cached[1]
    try:
        headers = {'User-Agent': f'{BOT_BASE_NAME}-bot/1.0 (Telegram downloader bot)'}
        r = requests.get(COBALT_DIRECTORY_API, headers=headers, timeout=15,
                         proxies=_proxies_dict())
        r.raise_for_status()
        items = r.json()
        good = []
        for inst in items:
            if not inst.get('online'):
                continue
            svc = (inst.get('services') or {}).get(service)
            if svc is not True:  # строка вида "blocked by cloudflare" — не годится
                continue
            api_host = inst.get('api')
            if not api_host:
                continue
            proto = inst.get('protocol') or 'https'
            good.append((inst.get('score') or 0, f"{proto}://{api_host}"))
        good.sort(key=lambda x: x[0], reverse=True)
        urls = [u for _, u in good[:limit]]
        _cobalt_instance_cache[cache_key] = (now, urls)
        return urls
    except Exception as e:
        logger.warning("Не удалось получить список Cobalt-инстансов для %s: %s", service, e)
        return []

def prov_cobalt(url):
    headers = {'Accept': 'application/json',
               'Content-Type': 'application/json',
               'User-Agent': UA}
    proxies = _proxies_dict()
    video_url = audio_url = None
    last = None
    for inst in COBALT_INSTANCES:
        try:
            rv = requests.post(inst, json={'url': url},
                               headers=headers, timeout=30, proxies=proxies).json()
            if rv.get('status') in ('tunnel', 'redirect') and rv.get('url'):
                video_url = rv['url']
            ra = requests.post(inst, json={'url': url, 'downloadMode': 'audio'},
                               headers=headers, timeout=30, proxies=proxies).json()
            if ra.get('status') in ('tunnel', 'redirect') and ra.get('url'):
                audio_url = ra['url']
            if video_url:
                return {
                    'title': None, 'author': None, 'author_url': None,
                    'video_id': str(slug_from_url(url) or 'tiktok'),
                    'duration': None, 'views': None, 'likes': None,
                    'cover': None, 'date_str': None,
                    'downloads': {'video': video_url, 'hd': None,
                                  'audio': audio_url, 'music': audio_url},
                    'sizes': {},
                }
        except Exception as e:
            last = e
    raise last or Exception('cobalt недоступен')

def cobalt_direct_url(url, audio=False, service_hint=None):
    """Общая (не завязанная на форму данных TikTok) обёртка над Cobalt —
    он умеет не только TikTok, но и YouTube, Vimeo, Twitter/X, Reddit,
    Twitch и другие. Используется как резервный API-загрузчик там, где
    у yt-dlp своя выгрузка спотыкается (приватные/встраиваемые только с
    определённого домена/запароленные видео) — Cobalt в таких случаях
    иногда справляется там, где обычный экстрактор — нет.

    Сначала пробует живые инстансы, найденные через instances.cobalt.best
    именно под service_hint (например 'vimeo') — они реально протестированы
    только что; если сайт-каталог недоступен или пуст, откатывается на
    статический COBALT_INSTANCES. Каждый инстанс пробуется дважды: сначала
    с проверкой сертификата, и только при явной SSLError — второй раз без
    неё (частая история для зарубежных доменов за DPI-перехватом; см.
    комментарий в _proxies_dict())."""
    headers = {'Accept': 'application/json',
               'Content-Type': 'application/json',
               'User-Agent': UA}
    proxies = _proxies_dict()
    payload = {'url': url}
    if audio:
        payload['downloadMode'] = 'audio'

    instances = list(COBALT_INSTANCES)
    if service_hint:
        discovered = discover_cobalt_instances(service_hint)
        # Сначала живые/протестированные под нужный сервис, потом статические
        # как подстраховка — без дублей.
        instances = discovered + [i for i in COBALT_INSTANCES if i not in discovered]

    last = None
    for inst in instances:
        for verify in (True, False):
            try:
                resp = requests.post(inst, json=payload, headers=headers, timeout=30,
                                     proxies=proxies, verify=verify)
                try:
                    r = resp.json()
                except ValueError:
                    # Не JSON — почти всегда значит, что это не настоящий
                    # ответ Cobalt, а какая-то заглушка/блокирующая страница
                    # по пути (тот же DPI-перехват, только не через сертификат,
                    # а через подмену тела ответа). Логируем сырой текст —
                    # без этого причина не видна вообще, только "Extra data".
                    snippet = resp.text[:200].replace('\n', ' ')
                    last = Exception(f"{inst}: не JSON, HTTP {resp.status_code}, "
                                    f"тело: {snippet!r}")
                    break
                if r.get('status') in ('tunnel', 'redirect') and r.get('url'):
                    if not verify:
                        logger.warning(
                            "Cobalt-инстанс %s принят без проверки TLS-сертификата "
                            "(похоже на DPI-перехват, см. _proxies_dict())", inst)
                    return r['url']
                last = Exception(f"{inst}: status={r.get('status')} error={r.get('error')}")
                break  # ответ пришёл (не SSL-ошибка) — второй раз тот же инстанс не пробуем
            except requests.exceptions.SSLError as e:
                last = e
                continue  # именно SSL — пробуем этот же инстанс без verify
            except Exception as e:
                last = e
                break
    raise last or Exception('Cobalt недоступен')


def prov_playwright_tiktok(url):
    """Резервный провайдер через настоящий headless-браузер — на случай,
    когда видео гео-заблокировано (та же причина, по которой человеку
    самому нужен VPN, чтобы его посмотреть). API-загрузчики (tikwm и
    остальные) сидят на своих фиксированных серверах — если сервер
    оказался в заблокированном для этого видео регионе, они просто
    вернут ошибку независимо от того, короткая ссылка или длинная
    (сами загрузчики одинаково понимают оба формата — дело не в этом).

    Playwright же можно пустить через PROXY (обычный прокси/VPN-адрес,
    который уже используется для yt-dlp) — тогда браузер физически
    заходит с IP другого региона, точно как это делает пользователь
    через свой VPN. Без настроенного PROXY этот провайдер, скорее всего,
    упрётся в ту же самую блокировку, что и остальные."""
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        raise Exception("Playwright не установлен")

    captured = {}
    page_json = {}

    with sync_playwright() as p:
        launch_kwargs = {'headless': True}
        if PROXY:
            launch_kwargs['proxy'] = {'server': playwright_proxy_server(PROXY)}
        browser = p.chromium.launch(**launch_kwargs)
        try:
            context = browser.new_context(user_agent=UA, locale='en-US',
                                          viewport={'width': 390, 'height': 844})

            def on_response(resp):
                try:
                    if (not captured.get('video')
                            and resp.request.resource_type == 'media'
                            and resp.status == 200):
                        captured['video'] = resp.url
                except Exception:
                    pass

            page = context.new_page()
            page.on('response', on_response)
            # Через Tor/медленный прокси установление цепочки + TLS может
            # занимать 10-20 сек само по себе — 30 сек мало, увеличиваем,
            # когда прокси вообще используется.
            nav_timeout = 60000 if PROXY else 30000
            page.goto(url, wait_until='domcontentloaded', timeout=nav_timeout)
            try:
                page.wait_for_selector('video', timeout=15000)
            except Exception:
                pass
            page.wait_for_timeout(3000)  # дать шанс медиа-запросу проскочить

            # Метаданные (автор, описание, музыка) достаём из встроенного
            # в страницу JSON — это надёжнее, чем парсить DOM.
            try:
                raw = page.evaluate(
                    "document.querySelector('#__UNIVERSAL_DATA_FOR_REHYDRATION__')?.textContent || null")
                if raw:
                    j = json.loads(raw)
                    scope = j.get('__DEFAULT_SCOPE__', {})
                    page_json = (scope.get('webapp.video-detail', {})
                                .get('itemInfo', {}).get('itemStruct', {}))
            except Exception as e:
                logger.warning("TikTok Playwright: JSON-состояние не прочитано: %s", e)

            if not captured.get('video'):
                video_info = page_json.get('video') or {}
                captured['video'] = video_info.get('playAddr') or video_info.get('downloadAddr')
        finally:
            browser.close()

    video_url = captured.get('video')
    if not video_url:
        raise Exception('Playwright не нашёл прямую ссылку на видео '
                        '(вероятно, гео-блок — настройте PROXY на нужный регион)')

    author = page_json.get('author') or {}
    music = page_json.get('music') or {}
    stats = page_json.get('stats') or {}
    video_meta = page_json.get('video') or {}
    # CDN TikTok отдаёт видео только с правильным Referer/UA — без них
    # прямое скачивание requests'ом за пределами браузера вернёт 403.
    # А если гео-блок именно на уровне CDN (не только страницы), скачивать
    # тоже придётся через тот же PROXY, что и саму страницу.
    fetch_headers = {'User-Agent': UA, 'Referer': 'https://www.tiktok.com/'}
    return {
        'title': page_json.get('desc'),
        'author': author.get('nickname'),
        'author_url': (f"https://www.tiktok.com/@{author.get('uniqueId')}"
                      if author.get('uniqueId') else None),
        'video_id': str(page_json.get('id') or slug_from_url(url) or 'tiktok'),
        'duration': video_meta.get('duration'),
        'views': stats.get('playCount'),
        'likes': stats.get('diggCount'),
        'cover': video_meta.get('cover'),
        'date_str': None,
        'downloads': {'video': video_url, 'hd': None,
                      'audio': music.get('playUrl'), 'music': music.get('playUrl')},
        'sizes': {},
        'fetch_headers': fetch_headers,
        'fetch_via_proxy': bool(PROXY),
    }

TIKTOK_PROVIDERS = (prov_tikwm, prov_tiklydown, prov_cobalt, prov_playwright_tiktok)

def get_tiktok_info(url):
    errors = []
    for prov in TIKTOK_PROVIDERS:
        try:
            data = prov(url)
            if data and data['downloads'].get('video'):
                logger.info("TikTok: сработал провайдер %s", prov.__name__)
                return data
        except Exception as e:
            logger.warning("TikTok: провайдер %s отвалился: %s", prov.__name__, e)
            errors.append(f"{prov.__name__}: {e}")
    raise Exception("Все провайдеры TikTok недоступны: " + "; ".join(errors))

# ================================================================
#  BILIBILI: ПРОВАЙДЕР (в обход yt-dlp)
# ================================================================
# yt-dlp сейчас падает на подписанном WBI-эндпоинте x/player/wbi/playurl
# (баг на стороне Bilibili/yt-dlp, см. GitHub issue #16571). Используем
# старый неподписанный API x/player/playurl — тот же приём, что у
# сторонних загрузчиков (you-get и др.). Он не требует логина/WBI-подписи,
# но всегда отдаёт лучшее качество, доступное анонимно (обычно 720p–1080p).
BILI_HEADERS = {'User-Agent': UA, 'Referer': 'https://www.bilibili.com/'}
BVID_REGEX = re.compile(r'(BV[0-9A-Za-z]{8,})')

def resolve_bilibili_url(url):
    """Разворачивает короткие ссылки b23.tv в полный URL с BVID."""
    if 'b23.tv' in url or 'bili2233.cn' in url:
        try:
            r = requests.head(url, headers=BILI_HEADERS, timeout=15, allow_redirects=True)
            return r.url
        except Exception:
            return url
    return url

def get_bilibili_view(bvid):
    api = f'https://api.bilibili.com/x/web-interface/view?bvid={bvid}'
    r = requests.get(api, headers=BILI_HEADERS, timeout=20)
    r.raise_for_status()
    j = r.json()
    if j.get('code') != 0 or not j.get('data'):
        raise Exception(f"view api: code={j.get('code')} msg={j.get('message')}")
    return j['data']

def get_bilibili_playinfo(aid, cid):
    """Сначала пробуем DASH (раздельные видео/аудио, лучше качество),
    при неудаче — старый progressive mp4 (durl, один файл)."""
    base = f'https://api.bilibili.com/x/player/playurl?avid={aid}&cid={cid}&qn=116&fourk=1&otype=json'
    for fnval in (16, 1):
        try:
            r = requests.get(base + f'&fnval={fnval}&fnver=0',
                             headers=BILI_HEADERS, timeout=20)
            r.raise_for_status()
            j = r.json()
            if j.get('code') != 0 or not j.get('data'):
                continue
            d = j['data']
            if fnval == 16 and d.get('dash'):
                videos = sorted(d['dash']['video'], key=lambda v: v.get('bandwidth') or 0, reverse=True)
                audios = sorted(d['dash'].get('audio') or [], key=lambda a: a.get('bandwidth') or 0, reverse=True)
                if videos:
                    return {'mode': 'dash',
                            'video_url': videos[0]['baseUrl'],
                            'audio_url': audios[0]['baseUrl'] if audios else None,
                            'quality': d.get('quality')}
            if fnval == 1 and d.get('durl'):
                return {'mode': 'durl', 'video_url': d['durl'][0]['url'],
                        'audio_url': None, 'quality': d.get('quality')}
        except Exception as e:
            logger.warning("Bilibili playurl (fnval=%s) не сработал: %s", fnval, e)
    raise Exception("Не удалось получить ссылку на видео (playurl)")

def get_bilibili_info(url):
    url = resolve_bilibili_url(url)
    m = BVID_REGEX.search(url)
    if not m:
        raise Exception("Не нашёл BV-идентификатор в ссылке")
    bvid = m.group(1)
    v = get_bilibili_view(bvid)
    cid = v.get('cid') or (v.get('pages') or [{}])[0].get('cid')
    if not cid:
        raise Exception("Не удалось определить cid ролика")
    play = get_bilibili_playinfo(v['aid'], cid)
    owner = v.get('owner') or {}
    stat = v.get('stat') or {}
    return {
        'title': v.get('title'),
        'author': owner.get('name'),
        'author_url': f"https://space.bilibili.com/{owner['mid']}" if owner.get('mid') else None,
        'video_id': bvid,
        'duration': v.get('duration'),
        'views': stat.get('view'),
        'likes': stat.get('like'),
        'cover': v.get('pic'),
        'date_str': format_ts(v.get('pubdate')),
        'quality': play.get('quality'),
        'play': play,
    }

# ---------- BOOSTY ----------
def get_boosty_meta(url):
    try:
        r = requests.get(url, headers={'User-Agent': UA}, timeout=30)
        h = r.text

        def grab(tag):
            patterns = [
                r'<meta[^>]*property=["\']og:' + tag + r'["\'][^>]*content=["\']([^"\']*)["\']',
                r'<meta[^>]*content=["\']([^"\']*)["\'][^>]*property=["\']og:' + tag + r'["\']',
            ]
            for p in patterns:
                mm = re.search(p, h, re.I)
                if mm:
                    return html.unescape(mm.group(1)).strip()
            return None

        return grab('title'), grab('description')
    except Exception as e:
        logger.warning("Не удалось получить метаданные Boosty: %s", e)
        return None, None

# ---------- YT-DLP ----------
def get_download_options(choice, video_id, title, lang=None, reporter=None):
    is_audio = choice.startswith('audio_')
    ydl_opts = {
        'format': format_selector_for(choice, lang),
        'outtmpl': base_path_for(title, video_id) + '.%(ext)s',
        'quiet': False,
        'no_warnings': False,
        'ignoreerrors': True,
        'nocheckcertificate': True,
        'extractor_retries': 10,
        'file_access_retries': 10,
        'fragment_retries': 10,
        'retry_sleep': 5,
        'continuedl': True,
        'buffersize': 1024 * 1024,
        'socket_timeout': 120,
        'extractor_args': YTDL_EXTRACTOR_ARGS,
        'user_agent': UA,
        'postprocessors': [],
    }
    if reporter:
        ydl_opts['progress_hooks'] = [make_ytdlp_progress_hook(reporter)]
    ydl_opts.update(cookies_opts())
    if PROXY:
        ydl_opts['proxy'] = PROXY
    if is_audio:
        ydl_opts['postprocessors'].append({
            'key': 'FFmpegExtractAudio',
            'preferredcodec': 'mp3',
            'preferredquality': choice.split('_')[1],
        })
    else:
        ydl_opts['merge_output_format'] = 'mp4'
    return ydl_opts

def get_video_info(url):
    ydl_opts = {
        'quiet': True,
        'no_warnings': True,
        'nocheckcertificate': True,
        'user_agent': UA,
        'extractor_retries': 5,
        'socket_timeout': 60,
        'extractor_args': YTDL_EXTRACTOR_ARGS,
    }
    ydl_opts.update(cookies_opts())
    if PROXY:
        ydl_opts['proxy'] = PROXY
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        return ydl.extract_info(url, download=False)

# ---------- ПОЙМАТЬ ПОТОК ВРУЧНУЮ (для сайтов, которых yt-dlp не знает) ----------
# Открывает страницу в headless-браузере и слушает сетевые запросы на
# .m3u8/.mp4 — так же, как это делают расширения вроде Video DownloadHelper.
# Требует: pip install playwright && playwright install chromium
_STREAM_URL_RE = re.compile(r'\.m3u8(\?|$)|\.mp4(\?|$)')

_AD_DOMAIN_RE = re.compile(
    r'doubleclick\.net|googlesyndication|google-analytics|googletagmanager|'
    r'adservice|adsystem|amazon-adsystem|scorecardresearch|moatads|'
    r'taboola|outbrain|criteo|pubmatic|rubiconproject', re.I)

# Некоторые сайты грузят декоративные/интерфейсные ролики (лого-анимация,
# заглушка плеера, фон логин-окна) — они физически являются .mp4-файлами и
# попадают под _STREAM_URL_RE, но это не контент, который просил человек.
# У TikTok конкретно есть свой статический CDN именно для такого мусора —
# отдельный от CDN настоящих видео.
_JUNK_ASSET_RE = re.compile(
    r'ttwstatic\.com|/webapp-desktop/playback\d*\.mp4|/static/.*loading|'
    r'placeholder|spinner|preloader', re.I)

def sniff_media_candidates(url, wait_seconds=25):
    """Ловит видеопотоки через headless-браузер — как Video DownloadHelper.
    Возвращает список [{'url':, 'size':}, ...] БЕЗ угадывания — если на
    странице несколько разных видео (виджеты, рекомендации), возвращаем их
    все, а выбор отдаём человеку, а не эвристике."""
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        logger.warning("Playwright не установлен — sniff-фолбэк недоступен "
                       "(pip install playwright && playwright install chromium)")
        return []

    candidates = []
    seen_urls = set()
    state = {'clicked': False}
    direct_src = None

    def _add(u, size=0):
        if u in seen_urls:
            return
        seen_urls.add(u)
        candidates.append({'url': u, 'size': size})

    try:
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            context = browser.new_context(user_agent=UA,
                                           viewport={'width': 1280, 'height': 800})
            page = context.new_page()

            def on_response(response):
                req_url = response.url
                if (_AD_DOMAIN_RE.search(req_url) or _JUNK_ASSET_RE.search(req_url)
                        or not _STREAM_URL_RE.search(req_url)):
                    return
                try:
                    size = int(response.headers.get('content-length') or 0)
                except Exception:
                    size = 0
                _add(req_url, size)

            page.on('response', on_response)
            try:
                page.goto(url, timeout=15000, wait_until='domcontentloaded')
            except Exception:
                pass

            # Кликаем именно по <video>, а не наугад в центр страницы — так
            # реже задеваем соседние/автоплей-превью на страницах-лентах.
            video_el = None
            try:
                video_el = page.query_selector('video')
                if video_el:
                    video_el.scroll_into_view_if_needed(timeout=3000)
                    video_el.click(timeout=3000)
            except Exception:
                pass
            if not video_el:
                try:
                    page.mouse.click(640, 360)
                except Exception:
                    pass
            state['clicked'] = True

            for _ in range(max(1, wait_seconds // 2)):
                if video_el and not direct_src:
                    try:
                        src = video_el.evaluate("el => el.currentSrc || el.src || ''")
                    except Exception:
                        src = ''
                    if (src and src.startswith('http') and not src.startswith('blob:')
                            and not _JUNK_ASSET_RE.search(src)):
                        direct_src = src
                page.wait_for_timeout(2000)

            browser.close()
    except Exception as e:
        logger.warning("Sniff-фолбэк упал: %s", e)
        return []

    if direct_src and direct_src in seen_urls:
        candidates.sort(key=lambda c: 0 if c['url'] == direct_src else 1)
    elif direct_src:
        candidates.insert(0, {'url': direct_src, 'size': 0})
    else:
        candidates.sort(key=lambda c: c['size'], reverse=True)

    return candidates



# ---------- КОНВЕРТАЦИЯ ----------
def run_ffmpeg_with_progress(cmd_no_output, tmp_out, timeout, on_line=None):
    """Запускает ffmpeg с '-progress pipe:1 -nostats' и опционально зовёт
    on_line(строка) на каждой строке прогресса — так конвертация может
    показывать реальный процент вместо просто «подожди». stderr читается
    в отдельном потоке, чтобы не словить дедлок на переполнении пайпа."""
    cmd = cmd_no_output + ['-progress', 'pipe:1', '-nostats', tmp_out]
    logger.info("ffmpeg: %s", ' '.join(cmd))
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, bufsize=1, errors='replace')
    stderr_buf = []
    def _drain_stderr():
        try:
            for line in proc.stderr:
                stderr_buf.append(line)
        except Exception:
            pass
    t = threading.Thread(target=_drain_stderr, daemon=True)
    t.start()
    start = time.time()
    timed_out = False
    try:
        for line in proc.stdout:
            if on_line:
                try:
                    on_line(line.strip())
                except Exception:
                    pass
            if time.time() - start > timeout:
                timed_out = True
                proc.kill()
                break
        proc.wait(timeout=15)
    except Exception:
        proc.kill()
    t.join(timeout=5)
    if timed_out:
        raise subprocess.TimeoutExpired(cmd, timeout)
    return proc.returncode, ''.join(stderr_buf)[-600:]

def convert_src_to(src, key, q, reporter=None):
    tmp_ext = 'm4a' if key == 'm4r' else key
    tmp_out = os.path.join(DOWNLOAD_DIR, f"tmp_out_{uuid.uuid4().hex}.{tmp_ext}")
    duration = probe_duration_ffmpeg(src) if reporter else None
    on_line = make_ffmpeg_progress_hook(reporter, duration) if (reporter and duration) else None
    last_err = None
    for args in ffmpeg_audio_argsets(key, q):
        cmd = [FFMPEG_BIN, '-y', '-i', src] + args
        try:
            rc, stderr_tail = run_ffmpeg_with_progress(cmd, tmp_out, timeout=600, on_line=on_line)
        except subprocess.TimeoutExpired:
            last_err = 'таймаут ffmpeg (10 мин)'
            continue
        if rc == 0 and os.path.exists(tmp_out):
            if reporter:
                reporter.update(100)
            return tmp_out
        last_err = stderr_tail
    if os.path.exists(tmp_out):
        try:
            os.remove(tmp_out)
        except OSError:
            pass
    raise Exception(f'ffmpeg не смог конвертировать: {last_err}')

def convert_video_to(src, key, reporter=None):
    fmt = VIDEO_FORMATS[key]
    tmp_out = os.path.join(DOWNLOAD_DIR, f"tmp_vout_{uuid.uuid4().hex}.{fmt['ext']}")
    duration = probe_duration_ffmpeg(src) if reporter else None
    on_line = make_ffmpeg_progress_hook(reporter, duration) if (reporter and duration) else None
    last_err = None
    for args in fmt['args']:
        cmd = [FFMPEG_BIN, '-y', '-i', src] + args
        try:
            rc, stderr_tail = run_ffmpeg_with_progress(cmd, tmp_out, timeout=600, on_line=on_line)
        except subprocess.TimeoutExpired:
            last_err = 'таймаут ffmpeg (10 мин)'
            continue
        if rc == 0 and os.path.exists(tmp_out):
            if reporter:
                reporter.update(100)
            return tmp_out
        last_err = stderr_tail
    if os.path.exists(tmp_out):
        try:
            os.remove(tmp_out)
        except OSError:
            pass
    raise Exception(f'ffmpeg не смог конвертировать видео: {last_err}')

def finish_file(tmp_out, title, video_id, key):
    out = base_path_for(title, video_id) + '.' + key
    os.replace(tmp_out, out)
    return out

def download_and_convert_audio(url, video_id, title, key, q, lang=None, reporter=None):
    base = base_path_for(title, video_id)
    cleanup_base(base)

    tmp_src = os.path.join(DOWNLOAD_DIR, f"tmp_src_{uuid.uuid4().hex}")
    if lang:
        attempts = [f'bestaudio[language={lang}]', 'bestaudio/best',
                   'best', 'bestvideo+bestaudio/best']
    else:
        attempts = ['bestaudio/best', 'best', 'bestvideo+bestaudio/best']

    src = None
    last_err = None
    for fmt in attempts:
        ydl_opts = {
            'format': fmt,
            'outtmpl': tmp_src + '.%(ext)s',
            'quiet': True,
            'no_warnings': True,
            'ignoreerrors': False,
            'nocheckcertificate': True,
            'fragment_retries': 10,
            'socket_timeout': 120,
            'user_agent': UA,
            'extractor_args': YTDL_EXTRACTOR_ARGS,
        }
        if reporter:
            ydl_opts['progress_hooks'] = [make_ytdlp_progress_hook(reporter)]
        ydl_opts.update(cookies_opts())
        if PROXY:
            ydl_opts['proxy'] = PROXY
        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.extract_info(url, download=True)
            matches = glob.glob(tmp_src + '.*')
            if matches:
                src = matches[0]
                logger.info("yt-dlp скачал с форматом: %s -> %s", fmt, src)
                break
        except Exception as e:
            last_err = str(e)
            logger.warning("yt-dlp не смог с форматом %s: %s", fmt, e)
            for p in glob.glob(tmp_src + '.*'):
                try:
                    os.remove(p)
                except OSError:
                    pass

    if not src:
        raise Exception(f'аудио не скачалось: {last_err}')

    if reporter:
        reporter.prefix = "🎛 Конвертирую"
    try:
        tmp_out = convert_src_to(src, key, q, reporter=reporter)
    finally:
        try:
            os.remove(src)
        except OSError:
            pass
    return finish_file(tmp_out, title, video_id, key)

def download_and_convert_from_url(dl_url, title, video_id, key, q, tt_data=None):
    base = base_path_for(title, video_id)
    cleanup_base(base)
    tmp_src = os.path.join(DOWNLOAD_DIR, f"tmp_src_{uuid.uuid4().hex}.mp3")
    if tt_data:
        download_tiktok_url(dl_url, tmp_src, tt_data)
    else:
        download_direct(dl_url, tmp_src)
    try:
        tmp_out = convert_src_to(tmp_src, key, q)
    finally:
        try:
            os.remove(tmp_src)
        except OSError:
            pass
    return finish_file(tmp_out, title, video_id, key)

# ---------- ОТПРАВКА ----------
def _api_field(v):
    """Булевы значения Bot API понимает только как строчные 'true'/'false'.
    str(True) даёт 'True' — такое сервер может трактовать как вздор/true,
    поэтому сериализуем булевы явно."""
    if isinstance(v, bool):
        return 'true' if v else 'false'
    return str(v)

def send_media_with_progress(chat_id, file_path, tg_method, field_name, mime,
                             caption=None, reply_markup=None, extra_fields=None,
                             reporter=None, timeout=1800, thumb_path=None):
    """Заливает файл в Telegram сырым multipart-POST'ом напрямую (в обход
    telebot), чтобы получить настоящий прогресс по факту отправленных байт
    через requests_toolbelt (обычный requests с files=... читает файл в
    память целиком, без колбэка на каждый чанк). Всегда возвращает
    telebot.types.Message — а не сырой dict, — чтобы store_cached() и всё
    остальное, что ждёт .video/.audio/.document, продолжало работать."""
    total = os.path.getsize(file_path)
    str_fields = {'chat_id': str(chat_id)}
    if caption:
        str_fields['caption'] = caption
        str_fields['parse_mode'] = 'HTML'
    if reply_markup:
        str_fields['reply_markup'] = reply_markup.to_json()
    if extra_fields:
        str_fields.update({k: _api_field(v) for k, v in extra_fields.items()})
    if thumb_path and os.path.exists(thumb_path):
        # Именуем thumbnail через attach://, как того требует Bot API,
        # когда основной файл и превью идут вместе одним multipart-запросом.
        str_fields['thumbnail'] = 'attach://tg_thumb'

    url = apihelper.API_URL.format(TOKEN, tg_method)
    with open(file_path, 'rb') as f, \
         (open(thumb_path, 'rb') if (thumb_path and os.path.exists(thumb_path)) else _null_ctx()) as tf:
        if HAS_TOOLBELT and reporter:
            fields = dict(str_fields)
            fields[field_name] = (os.path.basename(file_path), f, mime)
            if tf:
                fields['tg_thumb'] = (os.path.basename(thumb_path), tf, 'image/jpeg')
            encoder = MultipartEncoder(fields=fields)
            def _cb(monitor):
                percent = monitor.bytes_read * 100 / total if total else 100
                reporter.update(percent, format_file_size(total))
            monitor = MultipartEncoderMonitor(encoder, _cb)
            r = requests.post(url, data=monitor,
                              headers={'Content-Type': monitor.content_type}, timeout=timeout)
        else:
            files = {field_name: (os.path.basename(file_path), f, mime)}
            if tf:
                files['tg_thumb'] = (os.path.basename(thumb_path), tf, 'image/jpeg')
            r = requests.post(url, data=str_fields, files=files, timeout=timeout)
    j = r.json()
    if not j.get('ok'):
        raise Exception(f"{tg_method}: {j.get('description')}")
    return telebot.types.Message.de_json(j['result'])

@contextlib.contextmanager
def _null_ctx():
    yield None

_UPLOAD_KIND = {
    'video':    ('sendVideo', 'video', 'video/mp4', {'supports_streaming': 'true'}),
    'audio':    ('sendAudio', 'audio', 'audio/mpeg', {}),
    'document': ('sendDocument', 'document', 'application/octet-stream',
                 {'disable_content_type_detection': 'true'}),
}

def send_file_with_retry(chat_id, file_path, file_type,
                         caption=None, timeout=None, retries=3, reply_markup=None,
                         reporter=None, thumb_path=None):
    method, field, mime, extra = _UPLOAD_KIND.get(file_type, _UPLOAD_KIND['document'])
    extra = dict(extra)
    if file_type == 'video':
        # mime по настоящему расширению файла (см. комментарий у VIDEO_MIME_MAP)
        real_ext = os.path.splitext(file_path)[1].lstrip('.').lower()
        mime = VIDEO_MIME_MAP.get(real_ext, mime)
        # Явная геометрия — тот самый «секрет» чужих ботов: без width/height/
        # duration Desktop рисует пузырь дефолтным размером и растягивает
        # обложку под него (сплющенное превью + 00:00), а телефон терпит.
        # Теперь безопасно: probe_video_meta больше не падает на Windows
        # (errors='replace' чинит UnicodeDecodeError на выводе ffmpeg).
        w, h, dur = probe_video_meta(file_path)
        if w and h:
            extra['width'], extra['height'] = w, h
        if dur:
            extra['duration'] = int(dur)

    # Таймаут по размеру файла, а не фиксированные 10 минут на всё подряд:
    # на нестабильном/медленном ВПН большой файл может честно грузиться
    # дольше, и слишком короткий таймаут как раз провоцирует то, что ниже —
    # повторную заливку уже фактически принятого сервером файла.
    if timeout is None:
        size_mb = os.path.getsize(file_path) / (1024 * 1024)
        timeout = max(600, int(size_mb * 8))  # ~8 сек/МБ, но не меньше 10 минут

    # Сбрасываем процент на случай, если этот reporter уже использовался для
    # ДРУГОЙ, не связанной попытки отправки (например для видео перед этим
    # самым фолбэком на документ) — иначе унаследованный высокий процент
    # ниже ошибочно заблокирует самую первую попытку этого вызова.
    if reporter:
        reporter._last_percent = -100

    for attempt in range(1, retries + 1):
        try:
            return send_media_with_progress(
                chat_id, file_path, method, field, mime, caption=caption,
                reply_markup=reply_markup, extra_fields=extra,
                reporter=reporter, timeout=timeout, thumb_path=thumb_path)
        except Exception as e:
            # Если к моменту сбоя прогресс уже был близок к 100% — файл,
            # скорее всего, ДОШЁЛ до сервера целиком, а упало именно
            # ожидание подтверждения (например ВПН зашатался на секунду).
            # Автоматический повтор в этом случае — прямой риск задвоить
            # отправку (ровно так получилось 7 одинаковых видео подряд:
            # каждый "неудавшийся" повтор на деле уже был принят Telegram).
            # Поэтому здесь НЕ повторяем, а сразу честно сообщаем.
            late_stage = bool(reporter) and getattr(reporter, '_last_percent', -1) >= 90
            if late_stage:
                logger.error(
                    "Обрыв на %d%% загрузки — файл мог реально дойти до Telegram, "
                    "не повторяю отправку во избежание дублей: %s",
                    reporter._last_percent, e)
                raise Exception(
                    "загрузка не подтвердилась вовремя, но файл, скорее всего, "
                    "всё равно дошёл до Telegram — проверьте чат, прежде чем "
                    f"пробовать ещё раз ({e})")
            logger.warning("Попытка %d/%d не удалась: %s", attempt, retries, e)
            if attempt < retries:
                time.sleep(5)
            else:
                raise

def send_document_octet(chat_id, file_path, caption=None, timeout=600,
                        reply_markup=None, reporter=None, thumb_path=None):
    # Раньше возвращал сырой dict — из-за этого store_cached() не мог
    # прочитать message.document и мгновенное кэширование НИКОГДА не
    # срабатывало для форматов, отправляемых этим путём (FLV/WMV/ASF/
    # MPEG/OGV/M2TS/VOB/WTV/DIVX/AMV/ROQ/MXF и подобные — все они не входят
    # в VIDEO_TELEGRAM_OK и шлются через эту функцию как документ).
    method, field, mime, extra = _UPLOAD_KIND['document']
    return send_media_with_progress(
        chat_id, file_path, method, field, mime, caption=caption,
        reply_markup=reply_markup, extra_fields=extra,
        reporter=reporter, timeout=timeout, thumb_path=thumb_path)

# ---------- КЭШ ДЛЯ «МГНОВЕННОГО ВИДЕО» ----------
# Ключ: (video_id, callback_data выбора качества/формата) -> уже отправленный
# в Telegram file_id. Если качество уже скачивалось раньше — Telegram
# позволяет переслать его мгновенно, без повторного скачивания/загрузки.
# Хранится и на диске (sent_cache.json рядом со скриптом), чтобы кэш не
# пропадал при перезапуске бота.
SENT_CACHE = {}
CACHE_FILE = os.path.join(_BASE_DIR, 'sent_cache.json')
_cache_lock = threading.Lock()

def _cache_key_str(video_id, choice):
    return f"{video_id}\x1f{choice}"

def load_sent_cache():
    if not os.path.exists(CACHE_FILE):
        return
    try:
        with open(CACHE_FILE, 'r', encoding='utf-8') as f:
            raw = json.load(f)
        for k, v in raw.items():
            video_id, choice = k.split('\x1f', 1)
            SENT_CACHE[(video_id, choice)] = v
        logger.info("Кэш «мгновенного видео» загружен: %d записей", len(SENT_CACHE))
    except Exception as e:
        logger.warning("Не удалось загрузить кэш: %s", e)

def save_sent_cache():
    try:
        with _cache_lock:
            raw = {_cache_key_str(k[0], k[1]): v for k, v in SENT_CACHE.items()}
        tmp_path = CACHE_FILE + '.tmp'
        with open(tmp_path, 'w', encoding='utf-8') as f:
            json.dump(raw, f, ensure_ascii=False)
        os.replace(tmp_path, CACHE_FILE)  # атомарно, не побьём файл при падении
    except Exception as e:
        logger.warning("Не удалось сохранить кэш: %s", e)

def is_cached(video_id, choice):
    return bool(video_id) and (video_id, choice) in SENT_CACHE

def store_cached(video_id, choice, message, file_type, caption):
    if not video_id or not message:
        return
    fid = None
    actual_type = file_type
    # Telegram не всегда возвращает то поле, которое мы ожидаем по методу
    # отправки — например OGG/OPUS через sendAudio Telegram-клиент иногда
    # рендерит как voice-сообщение. Проверяем все варианты, а не только
    # ожидаемый file_type, иначе кэш молча не запишется.
    if getattr(message, 'video', None):
        fid, actual_type = message.video.file_id, 'video'
    elif getattr(message, 'audio', None):
        fid, actual_type = message.audio.file_id, 'audio'
    elif getattr(message, 'voice', None):
        fid, actual_type = message.voice.file_id, 'voice'
    elif getattr(message, 'document', None):
        fid, actual_type = message.document.file_id, 'document'
    if fid:
        with _cache_lock:
            SENT_CACHE[(video_id, choice)] = {'file_id': fid, 'type': actual_type, 'caption': caption}
        save_sent_cache()

def send_from_cache(chat_id, video_id, choice):
    c = SENT_CACHE.get((video_id, choice))
    if not c:
        return None
    try:
        if c['type'] == 'video':
            return bot.send_video(chat_id, c['file_id'], caption=c['caption'],
                                  parse_mode='HTML', supports_streaming=True)
        elif c['type'] == 'audio':
            return bot.send_audio(chat_id, c['file_id'], caption=c['caption'], parse_mode='HTML')
        elif c['type'] == 'voice':
            return bot.send_voice(chat_id, c['file_id'], caption=c['caption'], parse_mode='HTML')
        else:
            return bot.send_document(chat_id, c['file_id'], caption=c['caption'], parse_mode='HTML')
    except Exception as e:
        # file_id мог протухнуть (Telegram иногда инвалидирует старые file_id
        # спустя долгое время) — убираем из кэша и просим скачать заново.
        logger.warning("Не удалось отправить из кэша (%s), убираю запись: %s", choice, e)
        with _cache_lock:
            SENT_CACHE.pop((video_id, choice), None)
        save_sent_cache()
        return None

# ---------- ПОИСК ВИДЕО НА YOUTUBE ----------
SEARCH_HISTORY = {}  # chat_id -> [query, ...], новые в начале
SEARCH_HISTORY_FILE = os.path.join(_BASE_DIR, 'search_history.json')
SEARCH_HISTORY_LIMIT = 15
_search_history_lock = threading.Lock()

def load_search_history():
    if not os.path.exists(SEARCH_HISTORY_FILE):
        return
    try:
        with open(SEARCH_HISTORY_FILE, 'r', encoding='utf-8') as f:
            raw = json.load(f)
        for k, v in raw.items():
            SEARCH_HISTORY[int(k)] = v
        logger.info("История поиска загружена: %d чатов", len(SEARCH_HISTORY))
    except Exception as e:
        logger.warning("Не удалось загрузить историю поиска: %s", e)

def save_search_history():
    try:
        with _search_history_lock:
            raw = {str(k): v for k, v in SEARCH_HISTORY.items()}
        tmp_path = SEARCH_HISTORY_FILE + '.tmp'
        with open(tmp_path, 'w', encoding='utf-8') as f:
            json.dump(raw, f, ensure_ascii=False)
        os.replace(tmp_path, SEARCH_HISTORY_FILE)
    except Exception as e:
        logger.warning("Не удалось сохранить историю поиска: %s", e)

def remember_search(chat_id, query):
    query_norm = query.strip()
    if not query_norm:
        return
    with _search_history_lock:
        hist = SEARCH_HISTORY.setdefault(chat_id, [])
        hist[:] = [q for q in hist if q.lower() != query_norm.lower()]
        hist.insert(0, query_norm)
        del hist[SEARCH_HISTORY_LIMIT:]
    save_search_history()

# chat_id -> {'query': str} — что следующее ТЕКСТОВОЕ сообщение из этого
# чата надо понимать не как новый поисковый запрос, а как ответ на вопрос
# "за какой период искать". Специально не сохраняем на диск: если бот
# перезапустится посреди диалога, проще попросить начать заново, чем
# тащить недоделанный сценарий через файл между запусками.
SEARCH_STATE = {}
_search_state_lock = threading.Lock()

DATE_RANGE_RE = re.compile(
    r'^\s*(\d{1,2}\.\d{1,2}\.\d{4}|\d{4})\s*-\s*(\d{1,2}\.\d{1,2}\.\d{4}|\d{4})\s*$'
)

def _parse_search_date(s, is_end=False):
    """'дд.мм.гггг' или просто 'гггг'. Для голого года: если это начало
    периода — считаем 1 января, если конец — 31 декабря (иначе диапазон
    вида '2012-2013' почти не захватывал бы 2013-й)."""
    s = s.strip()
    if '.' in s:
        return datetime.datetime.strptime(s, '%d.%m.%Y').date()
    year = int(s)
    return datetime.date(year, 12, 31) if is_end else datetime.date(year, 1, 1)

def _fmt_duration(seconds):
    if not seconds:
        return ''
    seconds = int(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f" [{h}:{m:02d}:{s:02d}]" if h else f" [{m}:{s:02d}]"

def yt_search(query, limit=8):
    """Быстрый (плоский) поиск по YouTube через встроенный поисковый
    экстрактор yt-dlp — без стороннего API-ключа. ВАЖНО: в этом flat-режиме
    YouTube НЕ отдаёт дату загрузки видео (только id/title/duration/канал) —
    для точной фильтрации по периоду дату приходится дозапрашивать отдельно
    по каждому видео, см. yt_search_with_period."""
    opts = {
        'quiet': True, 'no_warnings': True, 'skip_download': True,
        'extract_flat': 'in_playlist', 'noplaylist': True,
        'socket_timeout': 20,
    }
    with yt_dlp.YoutubeDL(opts) as ydl:
        info = ydl.extract_info(f'ytsearch{limit}:{query}', download=False)
    entries = (info or {}).get('entries') or []
    results = []
    for e in entries:
        if not e or not e.get('id'):
            continue
        results.append({
            'id': e['id'],
            'title': e.get('title') or '(без названия)',
            'duration': e.get('duration'),
            'channel': e.get('channel') or e.get('uploader'),
            'url': e.get('url') or f"https://www.youtube.com/watch?v={e['id']}",
        })
    return results

def yt_search_with_period(query, date_from, date_to, pool=30, need=8):
    """
    Гибридный поиск: сначала DuckDuckGo (отлично ищет старые видео по точным датам), 
    затем добиваем через yt-dlp (если не набрали нужное количество).
    """
    matched = []
    
    # 1. Попытка найти через DuckDuckGo (работает для старых дат)
    if HAS_DDGS:
        start_str = date_from.strftime('%Y-%m-%d')
        end_str = date_to.strftime('%Y-%m-%d')
        ddg_query = f"{query} site:youtube.com/watch"

        try:
            with DDGS() as ddgs:
                results = list(ddgs.text(ddg_query, timelimit=f"{start_str}..{end_str}", max_results=need * 2))
                for r in results:
                    if len(matched) >= need:
                        break
                    url = r.get('href', '')
                    match = re.search(r'(?:v=|\/)([0-9A-Za-z_-]{11}).*', url)
                    if match:
                        # Проверка на дубликаты
                        if not any(m['id'] == match.group(1) for m in matched):
                            matched.append({
                                'id': match.group(1),
                                'title': r.get('title') or '(без названия)',
                                'duration': None,
                                'channel': None,
                                'url': url,
                                'upload_date': None
                            })
        except Exception as e:
            logger.warning("DuckDuckGo поиск не удался: %s", e)

    # 2. Если не набрали нужное количество, добиваем через yt-dlp (для свежих видео)
    if len(matched) < need:
        remaining_need = need - len(matched)
        opts = {
            'quiet': True, 'no_warnings': True, 'skip_download': True,
            'extract_flat': False,  # ВАЖНО: собираем даты сразу, без зависаний
            'noplaylist': True, 'socket_timeout': 15
        }
        try:
            with yt_dlp.YoutubeDL(opts) as ydl:
                info = ydl.extract_info(f'ytsearch{remaining_need * 3}:{query}', download=False)
                entries = (info or {}).get('entries') or []
                
                for c in entries:
                    if len(matched) >= need:
                        break
                    if not c or not c.get('id'):
                        continue
                    
                    upload_date = c.get('upload_date')
                    if upload_date and len(upload_date) == 8:
                        d = datetime.date(int(upload_date[:4]), int(upload_date[4:6]), int(upload_date[6:8]))
                        if date_from <= d <= date_to:
                            if not any(m['id'] == c['id'] for m in matched):
                                matched.append({
                                    'id': c['id'],
                                    'title': c.get('title') or '(без названия)',
                                    'duration': c.get('duration'),
                                    'channel': c.get('channel') or c.get('uploader'),
                                    'url': c.get('url') or f"https://www.youtube.com/watch?v={c['id']}",
                                    'upload_date': upload_date
                                })
        except Exception as e:
            logger.warning("yt-dlp поиск не удался: %s", e)

    return matched

def build_search_prompt_kb():
    kb = InlineKeyboardMarkup()
    kb.row(InlineKeyboardButton("🔍 Искать сейчас", callback_data='search_now'))
    kb.row(InlineKeyboardButton("📅 Указать период", callback_data='search_period'))
    kb.row(InlineKeyboardButton("🕘 История поиска", callback_data='search_hist'))
    kb.row(InlineKeyboardButton("❌ Отмена", callback_data='search_cancel'))
    return kb

def start_search_flow(message, query):
    chat_id = message.chat.id
    sent = bot.reply_to(message, f"🔎 Искать «{esc(query)}» на YouTube?",
                        parse_mode='HTML', reply_markup=build_search_prompt_kb())
    user_data[(chat_id, sent.message_id)] = {'source': 'search_prompt', 'query': query}

def build_results_kb(items):
    kb = InlineKeyboardMarkup()
    for i, it in enumerate(items):
        label = it['title']
        if len(label) > 50:
            label = label[:50] + '…'
        kb.row(InlineKeyboardButton(f"{i + 1}. {label}{_fmt_duration(it.get('duration'))}",
                                    callback_data=f'search_pick_{i}'))
    return kb

def send_search_results(chat_id, query, items, message_id=None, note=None):
    if not items:
        text = f"😕 По запросу «{esc(query)}» ничего не нашлось."
        kb = None
    else:
        text = f"🔎 Результаты по «{esc(query)}»:"
        kb = build_results_kb(items)
    if note:
        text += f"\n{note}"
    msg_id = message_id
    if msg_id:
        try:
            bot.edit_message_text(text, chat_id=chat_id, message_id=msg_id,
                                  parse_mode='HTML', reply_markup=kb)
        except Exception:
            sent = bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=kb)
            msg_id = sent.message_id
    else:
        sent = bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=kb)
        msg_id = sent.message_id
    if items:
        user_data[(chat_id, msg_id)] = {'source': 'search_results', 'query': query, 'items': items}

def build_history_kb(hist):
    kb = InlineKeyboardMarkup()
    for i, q in enumerate(hist):
        label = (q[:55] + '…') if len(q) > 55 else q
        kb.row(InlineKeyboardButton(label, callback_data=f'search_hist_{i}'))
    kb.row(InlineKeyboardButton("❌ Закрыть", callback_data='search_cancel'))
    return kb

# ================================================================
#  INLINE-РЕЖИМ (@бот запрос — в любом чате)
# ================================================================
# Результат — это просто текст со ссылкой на видео. Как только человек
# выбирает вариант, Telegram публикует сообщение с этой ссылкой в текущем
# чате — а её тут же подхватывает уже существующий handle_url (он реагирует
# на любое сообщение со ссылкой) и строит обычную карточку с качествами.
# Ничего не приходится дублировать: inline — это просто ещё один способ
# доставить ссылку в чат.
# Специальная метка: когда человек выбирает "Расширенный поиск" из
# inline-результатов, Telegram публикует в чат именно этот текст (с
# префиксом + запросом) — отдельный обработчик ниже его ловит и сразу
# переводит в режим ввода периода, без обычного меню "искать сейчас/...".
ADV_SEARCH_PREFIX = "🔎 Расширенный поиск:"

_inline_cache = {}          # query (в нижнем регистре) -> (timestamp, results)
_inline_cache_lock = threading.Lock()
INLINE_CACHE_TTL = 120      # сек — не бьём YouTube поиском на каждую букву
INLINE_MIN_LEN = 2

def _inline_thumb(video_id):
    return f"https://i.ytimg.com/vi/{video_id}/hqdefault.jpg"

@bot.inline_handler(func=lambda q: True)
def handle_inline_search(inline_query):
    query = (inline_query.query or '').strip()

    if len(query) < INLINE_MIN_LEN:
        try:
            bot.answer_inline_query(
                inline_query.id, [], cache_time=1, is_personal=True,
                switch_pm_text="Введите название видео для поиска",
                switch_pm_parameter="inline_help")
        except Exception as e:
            logger.warning("Не удалось ответить на пустой inline-запрос: %s", e)
        return

    key = query.lower()
    now = time.time()
    with _inline_cache_lock:
        cached = _inline_cache.get(key)
    if cached and now - cached[0] < INLINE_CACHE_TTL:
        items = cached[1]
    else:
        try:
            items = yt_search(query, limit=10)
        except Exception as e:
            logger.warning("Inline-поиск не удался: %s", e)
            items = []
        with _inline_cache_lock:
            _inline_cache[key] = (now, items)

    results = [InlineQueryResultArticle(
        id='adv_search',
        title="🔎 Расширенный поиск",
        description=f"«{query}» — с фильтром по периоду загрузки",
        input_message_content=InputTextMessageContent(f"{ADV_SEARCH_PREFIX} {query}"),
    )]
    for it in items[:10]:
        parts = []
        if it.get('channel'):
            parts.append(it['channel'])
        dur = _fmt_duration(it.get('duration')).strip(' []')
        if dur:
            parts.append(dur)
        try:
            results.append(InlineQueryResultArticle(
                id=str(it['id']),
                title=it['title'],
                description=' • '.join(parts) if parts else None,
                thumbnail_url=_inline_thumb(it['id']),
                input_message_content=InputTextMessageContent(it['url']),
            ))
        except Exception as e:
            logger.warning("Пропускаю результат inline-поиска %s: %s", it.get('id'), e)

    try:
        bot.answer_inline_query(inline_query.id, results, cache_time=30, is_personal=True)
    except Exception as e:
        logger.warning("Не удалось ответить на inline-запрос '%s': %s", query, e)

# ---------- РАЗБИВКА БОЛЬШИХ ФАЙЛОВ (> 2 ГБ) НА ЧАСТИ ----------
MAX_PART_BYTES = 1_900_000_000  # с запасом от лимита в 2 ГБ

def probe_video_meta(filename):
    """Реальные ширина/высота/длительность файла. В sendVideo эти поля
    больше не передаются (см. send_file_with_retry), функция оставлена
    как справка и для будущих нужд."""
    try:
        proc = subprocess.run([FFMPEG_BIN, '-i', filename],
                              capture_output=True, text=True,
                              errors='replace', timeout=30)
        out = proc.stderr or ''
        duration = None
        m = re.search(r'Duration:\s*(\d+):(\d+):(\d+\.\d+)', out)
        if m:
            h, mnt, s = m.groups()
            duration = int(h) * 3600 + int(mnt) * 60 + float(s)
        width = height = None
        m2 = re.search(r'Video:.*?(\d{2,5})x(\d{2,5})', out)
        if m2:
            width, height = int(m2.group(1)), int(m2.group(2))
        rot = re.search(r'rotate\s*:\s*(-?\d+)', out)
        rot_deg = int(rot.group(1)) if rot else None
        if rot_deg is None:
            dm = re.search(r'rotation of\s*(-?\d+(?:\.\d+)?)\s*degrees', out)
            if dm:
                rot_deg = round(float(dm.group(1)))
        if width and height and rot_deg is not None and rot_deg % 180 == 90:
            width, height = height, width
        return width, height, duration
    except Exception as e:
        logger.warning("Не удалось определить параметры видео: %s", e)
        return None, None, None

def probe_duration_ffmpeg(filename):
    try:
        proc = subprocess.run([FFMPEG_BIN, '-i', filename],
                            capture_output=True, text=True,
                            errors='replace', timeout=30)
        m = re.search(r'Duration:\s*(\d+):(\d+):(\d+\.\d+)', proc.stderr or '')
        if m:
            h, mnt, s = m.groups()
            return int(h) * 3600 + int(mnt) * 60 + float(s)
    except Exception as e:
        logger.warning("Не удалось определить длительность для разбивки: %s", e)
    return None

def split_video_file(filename, max_bytes=MAX_PART_BYTES):
    total_size = os.path.getsize(filename)
    if total_size <= max_bytes:
        return [filename]
    duration = probe_duration_ffmpeg(filename)
    if not duration:
        logger.warning("Не удалось разбить файл (нет длительности), отправлю как есть")
        return [filename]
    n_parts = math.ceil(total_size / max_bytes)
    seg_time = max(5, int(duration / n_parts))
    base, ext = os.path.splitext(filename)
    pattern = f"{base}_part%03d{ext}"
    cmd = [FFMPEG_BIN, '-y', '-i', filename, '-c', 'copy', '-map', '0',
           '-f', 'segment', '-segment_time', str(seg_time),
           '-reset_timestamps', '1', pattern]
    try:
        subprocess.run(cmd, check=True, capture_output=True, timeout=1800)
    except Exception as e:
        logger.error("ffmpeg-разбивка не удалась: %s", e)
        return [filename]
    parts = sorted(glob.glob(f"{base}_part*{ext}"))
    return parts if parts else [filename]

def send_video_smart(chat_id, filename, file_type, base_caption,
                     video_id=None, cache_choice=None, reply_markup=None, reporter=None,
                     thumb_path=None):
    """Отправляет файл; если видео > 2 ГБ — режет на части через ffmpeg
    (без перекодирования) и шлёт по очереди. Кэширует file_id для
    «мгновенного видео», только если файл уместился в одну часть."""
    parts = split_video_file(filename) if file_type == 'video' else [filename]
    sent_last = None
    try:
        if len(parts) == 1:
            sent_last = send_file_with_retry(chat_id, parts[0], file_type, caption=base_caption,
                                             reply_markup=reply_markup, reporter=reporter,
                                             thumb_path=thumb_path)
            store_cached(video_id, cache_choice, sent_last, file_type, base_caption)
        else:
            for i, part in enumerate(parts, 1):
                part_cap = f"{base_caption}\n📀 Часть {i}/{len(parts)}"
                is_last = (i == len(parts))
                if reporter:
                    reporter.prefix = f"📤 Отправляю в Telegram (часть {i}/{len(parts)})"
                sent_last = send_file_with_retry(chat_id, part, file_type, caption=part_cap,
                                                 reply_markup=reply_markup if is_last else None,
                                                 reporter=reporter, thumb_path=thumb_path)
        return sent_last
    finally:
        if len(parts) > 1:
            for p in parts:
                if p != filename and os.path.exists(p):
                    os.remove(p)

# ---------- FALLBACK ----------
def download_with_fallback(url, video_id, title, chat_id, status_msg, lang=None):
    for q in ('480p', '360p'):
        try:
            reporter = ProgressReporter(chat_id, status_msg.message_id, f"⏳ Пробую {q}")
            with yt_dlp.YoutubeDL(get_download_options(q, video_id, title, lang,
                                                        reporter=reporter)) as ydl:
                ydl.extract_info(url, download=True)
            filename = find_downloaded_file(base_path_for(title, video_id))
            if filename and os.path.getsize(filename) > 0:
                return filename, q
        except Exception as e:
            logger.warning("Не удалось скачать %s: %s", q, e)
    try:
        reporter = ProgressReporter(chat_id, status_msg.message_id, "⏳ Пробую аудио")
        with yt_dlp.YoutubeDL(get_download_options('audio_192', video_id, title, lang,
                                                    reporter=reporter)) as ydl:
            ydl.extract_info(url, download=True)
        filename = find_downloaded_file(base_path_for(title, video_id))
        if filename and os.path.getsize(filename) > 0:
            return filename, 'audio_192'
    except Exception as e:
        logger.error("Не удалось скачать аудио: %s", e)

    # Последняя попытка: без фильтров по ext/height вообще (Coub и подобные
    # сайты иногда отдают формат без нужных полей, из-за чего сложный
    # селектор из QUALITY_OPTIONS не матчится ни на что).
    try:
        bot.edit_message_text("⏳ Пробую без ограничений по качеству...",
                              chat_id=chat_id, message_id=status_msg.message_id)
        opts = get_download_options('720p', video_id, title)
        opts['format'] = 'best'
        with yt_dlp.YoutubeDL(opts) as ydl:
            ydl.extract_info(url, download=True)
        filename = find_downloaded_file(base_path_for(title, video_id))
        if filename and os.path.getsize(filename) > 0:
            return filename, 'best'
    except Exception as e:
        logger.error("Не удалось скачать даже с form=best: %s", e)

    # Совсем последний шанс: Cobalt как внешний API-загрузчик. Полезно
    # именно для сайтов вроде Vimeo — приватные/встраиваемые только с
    # определённого домена/запароленные ролики иногда отдаются через
    # Cobalt там, где родной экстрактор yt-dlp спотыкается.
    try:
        bot.edit_message_text("⏳ Пробую через внешний API-загрузчик (Cobalt)...",
                              chat_id=chat_id, message_id=status_msg.message_id)
        direct_url = cobalt_direct_url(url, service_hint='vimeo' if 'vimeo.com' in url else None)
        dest = base_path_for(title, video_id) + '.mp4'
        download_direct_headers(direct_url, dest, {'User-Agent': UA})
        if os.path.exists(dest) and os.path.getsize(dest) > 0:
            return dest, 'cobalt'
    except Exception as e:
        logger.error("Cobalt тоже не смог скачать: %s", e)

    return None, None

# ---------- TIKTOK: КАРТОЧКА ----------
def send_tiktok_card(message, url, placeholder):
    d = get_tiktok_info(url)
    chat_id = message.chat.id
    title = (d.get('title') or 'TikTok видео').strip()

    lines = []
    if d.get('author'):
        line = f"📺 {esc(d['author'])}"
        if d.get('author_url'):
            line += ' ' + arrow_link(d['author_url'])
        lines.append(line)
        lines.append('')
    lines.append(f"<b>{esc(title)}</b> {arrow_link(url)}")
    lines.append('')

    meta = []
    if d.get('date_str'):
        meta.append(f"📅 {d['date_str']}")
    dur = format_duration(d.get('duration'))
    if dur:
        meta.append(f"⏱ {dur}")
    if meta:
        lines.append('  '.join(meta))

    stats = []
    views = format_count(d.get('views'))
    if views:
        stats.append(f"👁 {views}")
    likes = format_count(d.get('likes'))
    if likes:
        stats.append(f"❤️ {likes}")
    if stats:
        lines.append('  '.join(stats))

    caption = "\n".join(lines)
    if len(caption) > 1000:
        caption = caption[:1000] + '…'

    data = {
        'source': 'tiktok',
        'url': url,
        'title': title,
        'video_id': d.get('video_id') or 'tiktok',
        'tiktok': d,
    }
    kb = build_video_kb(data)

    bot.delete_message(chat_id, placeholder.message_id)
    thumb_path = download_thumbnail(d.get('cover'), d.get('video_id') or 'tiktok')
    try:
        if thumb_path:
            with open(thumb_path, 'rb') as f:
                sent = bot.send_photo(chat_id, f, caption=caption,
                                      parse_mode='HTML', reply_markup=kb)
        else:
            sent = bot.send_message(chat_id, caption, parse_mode='HTML', reply_markup=kb)
        user_data[(sent.chat.id, sent.message_id)] = data
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)

# ---------- TIKTOK: СКАЧИВАНИЕ ----------
def handle_tiktok(call, data):
    choice = call.data
    chat_id = call.message.chat.id
    field, ftype, qlabel = TT_CHOICES[choice]
    dl_url = data['tiktok']['downloads'].get(field)
    if not dl_url:
        bot.answer_callback_query(call.id, "❌ Этот вариант недоступен.")
        return

    bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
    safe_answer_callback(call, "⏳ Загрузка...")
    status_msg = bot.send_message(chat_id, "⏳ Начинаю загрузку...")
    ext = '.mp3' if ftype == 'audio' else '.mp4'
    filename = base_path_for(data['title'], data['video_id']) + ext
    sent = None
    thumb_path = None

    try:
        download_tiktok_url(dl_url, filename, data['tiktok'])
        file_size = os.path.getsize(filename)
        cap = build_final_caption(data, file_size, f"Качество: {qlabel}")
        raw_thumb = download_thumbnail(get_thumbnail_url(data), data['video_id'])
        vid_w, vid_h, _ = probe_video_meta(filename) if ftype == 'video' else (None, None, None)
        thumb_path = make_telegram_video_thumb(raw_thumb, data['video_id'], vid_w, vid_h)
        if raw_thumb and os.path.exists(raw_thumb):
            os.remove(raw_thumb)
        sent = send_video_smart(chat_id, filename, ftype, cap,
                                video_id=data['video_id'], cache_choice=choice,
                                thumb_path=thumb_path)
        bot.delete_message(chat_id, status_msg.message_id)
    except Exception as e:
        logger.error("Ошибка TikTok: %s", e)
        bot.send_message(chat_id, f"❌ Ошибка: {e}")
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)
        if os.path.exists(filename):
            if sent:
                os.remove(filename)
            else:
                logger.warning("Файл %s не подтверждён как отправленный — оставляю на диске", filename)

# ---------- BILIBILI: КАРТОЧКА ----------
def send_bilibili_card(message, url, placeholder):
    d = get_bilibili_info(url)
    chat_id = message.chat.id
    title = (d.get('title') or 'Bilibili видео').strip()

    lines = []
    if d.get('author'):
        line = f"📺 {esc(d['author'])}"
        if d.get('author_url'):
            line += ' ' + arrow_link(d['author_url'])
        lines.append(line)
        lines.append('')
    lines.append(f"<b>{esc(title)}</b> {arrow_link(url)}")
    lines.append('')

    meta = []
    if d.get('date_str'):
        meta.append(f"📅 {d['date_str']}")
    dur = format_duration(d.get('duration'))
    if dur:
        meta.append(f"⏱ {dur}")
    if meta:
        lines.append('  '.join(meta))

    stats = []
    views = format_count(d.get('views'))
    if views:
        stats.append(f"👁 {views}")
    likes = format_count(d.get('likes'))
    if likes:
        stats.append(f"❤️ {likes}")
    if stats:
        lines.append('  '.join(stats))

    caption = "\n".join(lines)
    if len(caption) > 1000:
        caption = caption[:1000] + '…'

    data = {
        'source': 'bilibili',
        'url': url,
        'title': title,
        'video_id': d.get('video_id') or 'bilibili',
        'bilibili': d,
    }
    kb = build_video_kb(data)

    bot.delete_message(chat_id, placeholder.message_id)
    thumb_path = download_thumbnail(d.get('cover'), d.get('video_id') or 'bilibili')
    try:
        if thumb_path:
            with open(thumb_path, 'rb') as f:
                sent = bot.send_photo(chat_id, f, caption=caption,
                                      parse_mode='HTML', reply_markup=kb)
        else:
            sent = bot.send_message(chat_id, caption, parse_mode='HTML', reply_markup=kb)
        user_data[(sent.chat.id, sent.message_id)] = data
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)

# ---------- VIMEO: прямой запрос конфига плеера (в обход Cobalt) ----------
def vimeo_extract_id(url):
    """ID видео (и, если есть, приватный хэш для unlisted-ссылок) из
    произвольной ссылки на Vimeo — vimeo.com/{id}, vimeo.com/{id}/{hash},
    vimeo.com/channels/.../{id}, player.vimeo.com/video/{id} и т.д."""
    m = re.search(r'vimeo\.com/(?:.*?/)?(\d+)(?:/([0-9a-f]+))?(?:[/?].*)?$', url)
    if not m:
        return None, None
    return m.group(1), m.group(2)

def vimeo_embed_url(url):
    """vimeo.com/{id} → player.vimeo.com/video/{id} — отдельный embed-URL,
    созданный специально для показа видео на чужих сайтах (тот же, что
    лежит в коде для встраивания — Share → Embed на самом Vimeo). Он не
    завязан на проверку авторизации полноценного сайта vimeo.com, и yt-dlp
    через него нередко спокойно достаёт HLS/DASH там, где обычная ссылка
    падает с «The web client only works when logged-in»."""
    vid, h = vimeo_extract_id(url)
    if not vid:
        return None
    return f'https://player.vimeo.com/video/{vid}' + (f'?h={h}' if h else '')

def get_vimeo_progressive(url):
    """Тот же способ, которым пользуется сам официальный плеер Vimeo (и,
    судя по всему, yt-dlp внутри себя): конфиг плеера отдаёт прямые ссылки
    на файл в request.files.progressive — но ТОЛЬКО если автор ролика сам
    включил разрешение на скачивание. Не зависит от Cobalt/сторонних
    сайтов вообще — идём напрямую к Vimeo. Ссылки в ответе временные
    (с expires/signature), поэтому не кэшируем их между вызовами, а всегда
    запрашиваем свежие непосредственно перед скачиванием."""
    vid, h = vimeo_extract_id(url)
    if not vid:
        raise Exception('Не удалось извлечь ID видео из ссылки Vimeo')
    config_url = f'https://player.vimeo.com/video/{vid}/config'
    if h:
        config_url += f'?h={h}'
    headers = {'User-Agent': UA, 'Referer': f'https://vimeo.com/{vid}'}
    r = requests.get(config_url, headers=headers, timeout=20, proxies=_proxies_dict())
    r.raise_for_status()
    cfg = r.json()
    files = ((cfg.get('request') or {}).get('files') or {})
    progressive = files.get('progressive') or []
    if not progressive:
        raise Exception('У этого видео отключено скачивание автором '
                        '(нет progressive-файлов в конфиге плеера)')
    progressive = sorted(progressive, key=lambda f: f.get('height') or 0, reverse=True)

    vinfo = cfg.get('video') or {}
    thumbs = vinfo.get('thumbs') or {}
    cover = None
    if thumbs:
        try:
            cover = thumbs[max(thumbs, key=lambda k: int(k))]
        except Exception:
            cover = next(iter(thumbs.values()), None)

    return {
        'video_id': vid,
        'title': vinfo.get('title'),
        'duration': vinfo.get('duration'),
        'cover': cover,
        'files': [{'quality': f.get('quality'), 'width': f.get('width'),
                   'height': f.get('height'), 'url': f.get('url')}
                  for f in progressive],
    }

def send_vimeo_card(chat_id, url, placeholder_message_id):
    """Основная карточка для Vimeo, когда yt-dlp не смог получить
    метаданные обычным способом (приватное/встраиваемое-только-с-домена/
    запароленное видео). Сначала пробуем официальный конфиг плеера — он
    даёт настоящие title/cover/duration и список качеств, в отличие от
    Cobalt-варианта, у которого метаданных почти нет. Если и это не
    сработало (автор выключил скачивание, видео действительно приватное) —
    откатываемся на Cobalt."""
    try:
        info = get_vimeo_progressive(url)
        video_id = info['video_id']
        title = info.get('title') or f"Vimeo видео [{video_id}]"
        best = info['files'][0]
        data = {
            'source': 'vimeo_direct',
            'url': url,
            'title': title,
            'video_id': video_id,
            'vimeo_direct': info,
        }
        kb = build_video_kb(data)
        dur_str = f"⏱ {int(info['duration'])//60}:{int(info['duration'])%60:02d}\n" if info.get('duration') else ""
        caption = (f"<b>{esc(title)}</b> {arrow_link(url)}\n"
                  f"{dur_str}"
                  f"🖥 Лучшее доступное: {best.get('width')}x{best.get('height')}")
        try:
            bot.edit_message_text(caption, chat_id=chat_id, message_id=placeholder_message_id,
                                  parse_mode='HTML', reply_markup=kb, disable_web_page_preview=True)
            msg_id = placeholder_message_id
        except Exception:
            sent = bot.send_message(chat_id, caption, parse_mode='HTML', reply_markup=kb,
                                    disable_web_page_preview=True)
            msg_id = sent.message_id
        user_data[(chat_id, msg_id)] = data
        return
    except Exception as e:
        logger.warning("Прямой конфиг Vimeo не сработал (%s), пробую Cobalt-карточку", e)
    send_vimeo_cobalt_card(chat_id, url, placeholder_message_id)

def handle_vimeo_direct_download(call, data):
    chat_id = call.message.chat.id
    url = data['url']
    video_id = data['video_id']

    bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
    safe_answer_callback(call, "⏳ Загрузка с Vimeo...")
    status_msg = bot.send_message(chat_id, "⏳ Запрашиваю свежую прямую ссылку у Vimeo...")
    filename = base_path_for(data['title'], video_id) + '.mp4'
    sent = None
    thumb_path = None

    try:
        # Ссылки временные — запрашиваем свежий конфиг прямо перед скачиванием,
        # а не переиспользуем то, что было в карточке (могло протухнуть).
        info = get_vimeo_progressive(url)
        direct_url = info['files'][0]['url']
        bot.edit_message_text("⏳ Скачиваю...", chat_id=chat_id, message_id=status_msg.message_id)
        download_direct_headers(direct_url, filename, {'User-Agent': UA})

        file_size = os.path.getsize(filename)
        if file_size == 0:
            raise Exception('Vimeo вернул пустой файл')
        cap = build_final_caption(data, file_size, "Источник: Vimeo (официальный, скачивание разрешено автором)")
        vid_w, vid_h, _ = probe_video_meta(filename)
        raw_thumb = download_thumbnail(info.get('cover'), video_id) if info.get('cover') else None
        thumb_path = make_telegram_video_thumb(raw_thumb, video_id, vid_w, vid_h)
        sent = send_video_smart(chat_id, filename, 'video', cap,
                                video_id=video_id, cache_choice='vimeo_direct_dl',
                                thumb_path=thumb_path)
        bot.delete_message(chat_id, status_msg.message_id)
    except Exception as e:
        logger.error("Ошибка прямого скачивания с Vimeo: %s", e)
        bot.send_message(chat_id, f"❌ Не удалось скачать напрямую с Vimeo: {e}\n"
                                  f"Пробую через Cobalt...")
        return handle_vimeo_cobalt_download(call, {**data, 'source': 'vimeo_cobalt'})
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)
        if os.path.exists(filename):
            if sent:
                os.remove(filename)
            else:
                logger.warning("Файл %s не подтверждён как отправленный — оставляю на диске", filename)

# ---------- VIMEO (через Cobalt, если yt-dlp не справился с инфой) ----------
def send_vimeo_cobalt_card(chat_id, url, placeholder_message_id):
    """Резервная карточка для Vimeo, когда даже get_video_info() (только
    метаданные, без скачивания) не смог достучаться до ролика — например,
    видео приватное или встраивается только с определённого домена.
    Метаданных у нас в этом случае почти нет (Cobalt не отдаёт title/cover
    для одиночного запроса без реального скачивания), так что карточка
    получается скромной — просто с кнопкой «Скачать»."""
    video_id = slug_from_url(url) or 'vimeo'
    title = f"Vimeo видео [{video_id}]"
    data = {
        'source': 'vimeo_cobalt',
        'url': url,
        'title': title,
        'video_id': video_id,
        'vimeo_cobalt': {'cover': None},
    }
    kb = build_video_kb(data)
    caption = (f"<b>{esc(title)}</b> {arrow_link(url)}\n"
              f"⚠️ yt-dlp не смог получить обычные метаданные (приватное/"
              f"запароленное/встраиваемое видео) — пробуем скачать через "
              f"внешний API-загрузчик (Cobalt), без превью и статистики.")
    try:
        bot.edit_message_text(caption, chat_id=chat_id, message_id=placeholder_message_id,
                              parse_mode='HTML', reply_markup=kb, disable_web_page_preview=True)
        msg_id = placeholder_message_id
    except Exception:
        sent = bot.send_message(chat_id, caption, parse_mode='HTML', reply_markup=kb,
                                disable_web_page_preview=True)
        msg_id = sent.message_id
    user_data[(chat_id, msg_id)] = data

def handle_vimeo_cobalt_download(call, data):
    chat_id = call.message.chat.id
    url = data['url']
    video_id = data['video_id']

    bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
    safe_answer_callback(call, "⏳ Загрузка через Cobalt...")
    status_msg = bot.send_message(chat_id, "⏳ Запрашиваю прямую ссылку у Cobalt...")
    filename = base_path_for(data['title'], video_id) + '.mp4'
    sent = None
    thumb_path = None

    try:
        direct_url = cobalt_direct_url(url, service_hint='vimeo')
        bot.edit_message_text("⏳ Скачиваю...", chat_id=chat_id, message_id=status_msg.message_id)
        download_direct_headers(direct_url, filename, {'User-Agent': UA})

        file_size = os.path.getsize(filename)
        if file_size == 0:
            raise Exception('Cobalt вернул пустой файл')
        cap = build_final_caption(data, file_size, "Источник: Cobalt (API-загрузчик)")
        vid_w, vid_h, _ = probe_video_meta(filename)
        thumb_path = make_telegram_video_thumb(None, video_id, vid_w, vid_h)
        sent = send_video_smart(chat_id, filename, 'video', cap,
                                video_id=video_id, cache_choice='vimeo_cobalt_dl',
                                thumb_path=thumb_path)
        bot.delete_message(chat_id, status_msg.message_id)
    except Exception as e:
        logger.error("Ошибка Vimeo/Cobalt: %s", e)
        bot.send_message(chat_id, f"❌ Не удалось скачать через Cobalt: {e}")
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)
        if os.path.exists(filename):
            if sent:
                os.remove(filename)
            else:
                logger.warning("Файл %s не подтверждён как отправленный — оставляю на диске", filename)

# ---------- BILIBILI: СКАЧИВАНИЕ ----------
def handle_bilibili_download(call, data):
    chat_id = call.message.chat.id
    play = data['bilibili']['play']

    bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
    safe_answer_callback(call, "⏳ Загрузка...")
    status_msg = bot.send_message(chat_id, "⏳ Начинаю загрузку...")
    filename = base_path_for(data['title'], data['video_id']) + '.mp4'
    tmp_video = filename + '.v.tmp'
    tmp_audio = filename + '.a.tmp'
    sent = None
    thumb_path = None

    try:
        if play['mode'] == 'dash' and play.get('audio_url'):
            download_direct_headers(play['video_url'], tmp_video, BILI_HEADERS)
            download_direct_headers(play['audio_url'], tmp_audio, BILI_HEADERS)
            cmd = [FFMPEG_BIN, '-y', '-i', tmp_video, '-i', tmp_audio,
                   '-c', 'copy', filename]
            subprocess.run(cmd, check=True, capture_output=True)
        else:
            download_direct_headers(play['video_url'], filename, BILI_HEADERS)

        file_size = os.path.getsize(filename)
        q = play.get('quality')
        cap = build_final_caption(data, file_size, f"Качество: q{q}" if q else "")
        raw_thumb = download_thumbnail(get_thumbnail_url(data), data['video_id'])
        vid_w, vid_h, _ = probe_video_meta(filename)
        thumb_path = make_telegram_video_thumb(raw_thumb, data['video_id'], vid_w, vid_h)
        if raw_thumb and os.path.exists(raw_thumb):
            os.remove(raw_thumb)
        sent = send_video_smart(chat_id, filename, 'video', cap,
                                video_id=data['video_id'], cache_choice='bili_dl',
                                thumb_path=thumb_path)
        bot.delete_message(chat_id, status_msg.message_id)
    except Exception as e:
        logger.error("Ошибка Bilibili: %s", e)
        bot.send_message(chat_id, f"❌ Ошибка: {e}")
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)
        for p in (tmp_video, tmp_audio):
            if os.path.exists(p):
                os.remove(p)
        if os.path.exists(filename):
            if sent:
                os.remove(filename)
            else:
                logger.warning("Файл %s не подтверждён как отправленный — оставляю на диске", filename)

# ---------- ВИДЕОФОРМАТ: СКАЧИВАНИЕ ----------
def handle_video_format_download(call, data, key, q, lang=None):
    chat_id = call.message.chat.id
    bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
    safe_answer_callback(call, "⏳ Загрузка...")
    status_msg = bot.send_message(
        chat_id, f"⏳ Скачиваю видео: {VIDEO_FORMATS[key]['label']} {q}...")
    reporter = ProgressReporter(chat_id, status_msg.message_id,
                                f"⏳ Скачиваю видео: {VIDEO_FORMATS[key]['label']} {q}")
    filename = None
    sent = None
    tmp_src_final = None
    thumb_path = None

    try:
        title = data['title']
        video_id = data['video_id']
        base = base_path_for(title, video_id)
        cleanup_base(base)
        tmp_src = os.path.join(DOWNLOAD_DIR, f"tmp_vsrc_{uuid.uuid4().hex}")

        if data.get('source') == 'tiktok':
            dl_url = data['tiktok']['downloads'].get('video')
            if not dl_url:
                raise Exception('TikTok: нет ссылки на видео')
            tmp_src_final = tmp_src + '.mp4'
            download_tiktok_url(dl_url, tmp_src_final, data['tiktok'])
        else:
            ydl_opts = get_download_options(q, video_id, title, lang, reporter=reporter)
            ydl_opts['outtmpl'] = tmp_src + '.%(ext)s'
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.extract_info(data['url'], download=True)
            matches = glob.glob(tmp_src + '.*')
            if not matches:
                raise Exception('видео не скачалось')
            tmp_src_final = matches[0]

        if key != 'mp4':
            reporter.prefix = f"🎞 Конвертирую в {VIDEO_FORMATS[key]['label']}"
            tmp_out = convert_video_to(tmp_src_final, key, reporter=reporter)
            try:
                os.remove(tmp_src_final)
            except OSError:
                pass
            tmp_src_final = None
            try:
                filename = finish_file(tmp_out, title, video_id,
                                       VIDEO_FORMATS[key].get('fext', key))
            except Exception:
                if os.path.exists(tmp_out):
                    os.remove(tmp_out)
                raise
        else:
            filename = finish_file(tmp_src_final, title, video_id, 'mp4')
            tmp_src_final = None

        file_size = os.path.getsize(filename)
        if file_size == 0:
            raise Exception('получился пустой файл')

        fmt_text = f"Формат: {VIDEO_FORMATS[key]['label']} {q}"
        if lang:
            fmt_text += f" | Дорожка: {lang_display(lang)}"
        cap = build_final_caption(data, file_size, fmt_text)

        vdl_choice = cache_key_for(f"vdl_{key}_{q}", lang)
        sent = None
        reporter.prefix = "📤 Отправляю в Telegram"
        raw_thumb = download_thumbnail(get_thumbnail_url(data), video_id)
        vid_w, vid_h, _ = probe_video_meta(filename)
        thumb_path = make_telegram_video_thumb(raw_thumb, video_id, vid_w, vid_h)
        if raw_thumb and os.path.exists(raw_thumb):
            os.remove(raw_thumb)
        if key in VIDEO_TELEGRAM_OK:
            try:
                sent = send_video_smart(chat_id, filename, 'video', cap,
                                        video_id=video_id, cache_choice=vdl_choice,
                                        reporter=reporter, thumb_path=thumb_path)
            except Exception as e:
                logger.warning("Видео не прошло как video, шлю документом: %s", e)
                sent = send_document_octet(chat_id, filename, caption=cap, reporter=reporter,
                                           thumb_path=thumb_path)
                store_cached(video_id, vdl_choice, sent, 'document', cap)
        else:
            sent = send_document_octet(chat_id, filename, caption=cap, reporter=reporter,
                                       thumb_path=thumb_path)
            store_cached(video_id, vdl_choice, sent, 'document', cap)

        if sent and data.get('source') != 'tiktok':
            if needs_full_description_file(data):
                send_full_description(chat_id, data, video_id=video_id, title=title)

        bot.delete_message(chat_id, status_msg.message_id)
    except Exception as e:
        logger.error("Ошибка видеоформата: %s", e)
        bot.send_message(chat_id, f"❌ Ошибка: {e}")
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)
        if tmp_src_final and os.path.exists(tmp_src_final):
            try:
                os.remove(tmp_src_final)
            except OSError:
                pass
        # Удаляем итоговый файл только если реально подтверждена отправка
        # в Telegram (есть ответ от API) — иначе рискуем потерять файл,
        # который на самом деле не дошёл до пользователя.
        if filename and os.path.exists(filename):
            if sent:
                os.remove(filename)
            else:
                logger.warning("Файл %s не подтверждён как отправленный — оставляю на диске", filename)

# ---------- АУДИО: СКАЧИВАНИЕ ----------
def handle_audio_download(call, data, key, q, lang=None):
    chat_id = call.message.chat.id
    bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
    safe_answer_callback(call, "⏳ Загрузка...")
    status_msg = bot.send_message(chat_id, f"⏳ Скачиваю аудио: {quality_label(key, q)}...")
    reporter = ProgressReporter(chat_id, status_msg.message_id,
                                f"⏳ Скачиваю аудио: {quality_label(key, q)}")
    filename = None
    sent = None
    thumb_path = None

    try:
        if data.get('source') == 'tiktok':
            music_url = data['tiktok']['downloads'].get('music')
            if not music_url:
                raise Exception('TikTok: нет ссылки на аудио')
            filename = download_and_convert_from_url(
                music_url, data['title'], data['video_id'], key, q, tt_data=data['tiktok'])
        else:
            filename = download_and_convert_audio(
                data['url'], data['video_id'], data['title'], key, q, lang, reporter=reporter)
        file_size = os.path.getsize(filename)
        fmt_text = f"Формат: {quality_label(key, q)}"
        if lang:
            fmt_text += f" | Дорожка: {lang_display(lang)}"
        cap = build_final_caption(data, file_size, fmt_text)
        adl_choice = cache_key_for(f"adl_{key}_{q}" if q else f"adl_{key}", lang)
        reporter.prefix = "📤 Отправляю в Telegram"
        raw_thumb = download_thumbnail(get_thumbnail_url(data), data['video_id'])
        thumb_path = make_telegram_video_thumb(raw_thumb, data['video_id'])
        if raw_thumb and os.path.exists(raw_thumb):
            os.remove(raw_thumb)
        if key in DOCUMENT_AUDIO:
            sent = send_document_octet(chat_id, filename, caption=cap, reporter=reporter,
                                       thumb_path=thumb_path)
            store_cached(data['video_id'], adl_choice, sent, 'document', cap)
        else:
            sent = send_file_with_retry(chat_id, filename, 'audio', caption=cap, reporter=reporter,
                                        thumb_path=thumb_path)
            store_cached(data['video_id'], adl_choice, sent, 'audio', cap)
        if sent and data.get('source') != 'tiktok':
            if needs_full_description_file(data):
                send_full_description(chat_id, data)
        bot.delete_message(chat_id, status_msg.message_id)
    except Exception as e:
        logger.error("Ошибка аудио: %s", e)
        bot.send_message(chat_id, f"❌ Ошибка: {e}")
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)
        if filename and os.path.exists(filename):
            if sent:
                os.remove(filename)
            else:
                logger.warning("Файл %s не подтверждён как отправленный — оставляю на диске", filename)

def fetch_subtitles_via_transcript_api(video_id, lang_code, prefer_manual):
    """Пытается получить субтитры через youtube-transcript-api — она честнее
    yt-dlp обрабатывает автоперевод YouTube. Возвращает (srt_text, is_generated)
    или бросает исключение, если не получилось (тогда вызывающий код
    откатывается на старый способ через yt-dlp)."""
    if not HAS_TRANSCRIPT_API:
        raise RuntimeError("youtube-transcript-api не установлена")

    proxy_cfg = GenericProxyConfig(http_url=PROXY, https_url=PROXY) if PROXY else None
    ytt_api = YouTubeTranscriptApi(proxy_config=proxy_cfg) if proxy_cfg else YouTubeTranscriptApi()
    tlist = ytt_api.list(video_id)

    try:
        # Точное совпадение — реальная дорожка (не синтетический перевод)
        tr = tlist.find_transcript([lang_code])
    except Exception:
        # Нет такой дорожки напрямую — переводим с исходной через
        # официальный механизм автоперевода YouTube (Transcript.translate).
        candidates = list(tlist)
        if not candidates:
            raise
        base = next((c for c in candidates if not c.is_generated), candidates[0])
        if not base.is_translatable:
            raise RuntimeError(f"Перевод на '{lang_code}' недоступен для этого видео")
        tr = base.translate(lang_code)

    fetched = tr.fetch()
    srt_text = SRTFormatter().format_transcript(fetched)
    return srt_text, tr.is_generated

def handle_subtitle_download(call, data, lang_code):
    """Скачивает субтитры отдельным файлом (.srt) — обычные, если автор их
    залил, иначе автосгенерированные YouTube для того же языка.

    Сначала пробуем youtube-transcript-api (надёжнее для автоперевода),
    и только если она недоступна или не справилась — старый способ
    через yt-dlp как запасной вариант."""
    chat_id = call.message.chat.id
    bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
    safe_answer_callback(call, "⏳ Скачиваю субтитры...")

    video_id = data['video_id']
    title = data['title']
    url = data['url']
    tracks = get_subtitle_tracks(data.get('info') or {})
    flags = tracks.get(lang_code, {'manual': True, 'auto': True})
    tmp_base = os.path.join(DOWNLOAD_DIR, f"tmp_sub_{uuid.uuid4().hex}")
    filename = None
    sent = None
    transcript_api_error = None
    is_generated = not flags.get('manual', True)

    try:
        srt_text, is_generated = fetch_subtitles_via_transcript_api(
            video_id, lang_code, flags.get('manual', False))
        filename = tmp_base + '.srt'
        with open(filename, 'w', encoding='utf-8') as f:
            f.write(srt_text)
    except Exception as e:
        transcript_api_error = str(e)
        logger.warning("youtube-transcript-api не справилась (%s), пробую yt-dlp: %s",
                       lang_code, e)
        filename = None

    if not filename:
        # ---- Запасной путь: старое поведение через yt-dlp ----
        captured = []
        class _CaptureLogger:
            def debug(self, msg): pass
            def info(self, msg): captured.append(msg)
            def warning(self, msg): captured.append(msg)
            def error(self, msg): captured.append(msg)

        ydl_opts = {
            'skip_download': True,
            'writesubtitles': flags.get('manual', False),
            'writeautomaticsubs': not flags.get('manual', False),
            'subtitleslangs': [lang_code],
            'subtitlesformat': 'srt/best',
            'outtmpl': tmp_base + '.%(ext)s',
            'quiet': True,
            'no_warnings': False,
            'logger': _CaptureLogger(),
            'nocheckcertificate': True,
            'socket_timeout': 60,
            'user_agent': UA,
            'extractor_args': YTDL_EXTRACTOR_ARGS,
        }
        ydl_opts.update(cookies_opts())
        if PROXY:
            ydl_opts['proxy'] = PROXY

        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                ydl.extract_info(url, download=True)
            matches = glob.glob(tmp_base + '.*')
            if matches:
                filename = matches[0]
        except Exception as e:
            logger.error("Ошибка субтитров (yt-dlp): %s", e)

        if not filename:
            if not flags.get('manual'):
                msg = ("❌ У YouTube для этого языка не оказалось реального "
                      "автоперевода субтитров (это машинный перевод, и для "
                      "редких языков он часто просто пуст).")
            else:
                msg = "❌ Не удалось скачать субтитры для этого языка."
            if transcript_api_error:
                msg += f"\n\nПодробности: {esc(transcript_api_error)}"
            bot.send_message(chat_id, msg, parse_mode='HTML')
            return

    try:
        auto_mark = '' if not is_generated else ' (авто)'
        cap = f"💬 Субтитры: {lang_display(lang_code)}{auto_mark}\n{esc(title)}"
        with open(filename, 'rb') as f:
            sent = bot.send_document(chat_id, f, caption=cap, parse_mode='HTML')
        store_cached(video_id, f"sub_{lang_code}", sent, 'document', cap)
    except Exception as e:
        logger.error("Ошибка отправки субтитров: %s", e)
        bot.send_message(chat_id, f"❌ Ошибка: {e}")
    finally:
        if filename and os.path.exists(filename):
            os.remove(filename)

# ---------- ОБРАБОТЧИКИ ----------
@bot.message_handler(commands=['start', 'help'])
def send_welcome(message):
    logger.info(">>> /start или /help от %s", message.from_user.id)
    bot.reply_to(
        message,
        "🎬 Бот-загрузчик (файлы до 2 ГБ через локальный сервер).\n"
        "Отправь ссылку с YouTube, Boosty, Instagram, TikTok и др.\n"
        "При ошибках бот автоматически попробует понизить качество.\n\n"
        "🔎 Можно и без ссылки: просто напиши, что искать (например "
        "«roblox»), и бот найдёт видео на YouTube. Команда /search "
        "работает так же явно: /search roblox.",
    )

@bot.message_handler(commands=['search'])
def cmd_search(message):
    parts = (message.text or '').split(maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        bot.reply_to(message, "Использование: <code>/search запрос</code>\n"
                              "Например: <code>/search roblox</code>", parse_mode='HTML')
        return
    start_search_flow(message, parts[1].strip())

@bot.message_handler(func=lambda m: (m.text or '').startswith(ADV_SEARCH_PREFIX))
def handle_adv_search_marker(message):
    """Ловит служебное сообщение от кнопки «🔎 Расширенный поиск» из
    inline-режима и сразу переводит в режим ввода периода — без обычного
    меню «искать сейчас / указать период / история», раз человек уже явно
    выбрал именно расширенный (по датам) поиск."""
    chat_id = message.chat.id
    query = message.text[len(ADV_SEARCH_PREFIX):].strip()
    if not query:
        bot.reply_to(message, "❌ Не понял запрос для расширенного поиска.")
        return
    with _search_state_lock:
        SEARCH_STATE[chat_id] = {'query': query}
    bot.reply_to(
        message,
        f"🔎 Расширенный поиск «{esc(query)}»\n"
        f"Укажите период загрузки видео в формате "
        f"<code>01.01.2012-01.01.2013</code> (или просто годами: "
        f"<code>2012-2013</code>):",
        parse_mode='HTML')

@bot.message_handler(func=lambda m: find_url(m.text) is not None)
def handle_url(message):
    url = find_url(message.text)
    chat_id = message.chat.id
    logger.info(">>> Ссылка от %s: %s", message.from_user.id, url)

    if rate_limited(chat_id):
        bot.reply_to(message, "🚦 Слишком много запросов подряд, подождите немного.")
        return

    job_key = ('url', chat_id, url)
    if not try_start_job(job_key):
        bot.reply_to(message, "⏳ Эта ссылка уже обрабатывается, подождите.")
        return

    placeholder = bot.reply_to(message, "🔍 Получаю информацию...")

    def _run():
        try:
            process_url_message(message, url, placeholder)
        finally:
            finish_job(job_key)

    if not enqueue_job(_run):
        finish_job(job_key)
        try:
            bot.edit_message_text("🚦 Бот сейчас перегружен запросами, попробуйте через минуту.",
                                  chat_id=chat_id, message_id=placeholder.message_id)
        except Exception:
            pass
        return

    if job_queue.qsize() > 0:
        try:
            bot.edit_message_text(f"⏳ В очереди (~{job_queue.qsize()})...",
                                  chat_id=chat_id, message_id=placeholder.message_id)
        except Exception:
            pass

def build_and_send_ytdlp_card(chat_id, url, info, placeholder_message_id=None,
                              sniff_candidates=None, sniff_orig_url=None):
    """Строит и отправляет обычную карточку видео по уже полученному info.
    Общая для обычного потока и для случая, когда URL пришёл из sniff-пикера
    (тогда sniff_candidates/sniff_orig_url прокидываются дальше, чтобы на
    карточке была кнопка «попробовать другой поток» без повторного скана)."""
    chat_id_int = chat_id
    video_id = info.get('id') or slug_from_url(url) or 'unknown'
    title = info.get('title') or ''
    description = info.get('description') or ''
    if 'boosty.to' in url:
        b_title, b_desc = get_boosty_meta(url)
        if b_title and title.strip().lower() in ('', 'video'):
            title = b_title
        if b_desc and not description:
            description = b_desc
    if not title or title.strip().lower() == 'video':
        title = slug_from_url(url) or title or 'video'

    data = {
        'source': 'ytdlp',
        'url': url, 'title': title, 'video_id': video_id, 'info': info,
        'description': description,
    }
    if sniff_candidates and len(sniff_candidates) > 1:
        data['sniff_candidates'] = sniff_candidates
        data['sniff_orig_url'] = sniff_orig_url or url
    kb = build_video_kb(data)

    lines = []
    uploader = info.get('uploader') or info.get('channel')
    channel_url = channel_permalink(info)
    if uploader:
        line = f"📺 {esc(uploader)}"
        if channel_url:
            line += ' ' + arrow_link(channel_url)
        lines.append(line)
    followers = format_count(info.get('channel_follower_count'))
    if followers:
        lines.append(f"👥 {followers}")
    site = info.get('extractor_key')
    if site and site.lower() != 'generic':
        lines.append(f"🌐 {esc(site)}")
    if lines:
        lines.append('')

    lines.append(f"<b>{esc(title)}</b> {arrow_link(url)}")
    lines.append('')

    meta = []
    date = format_date(info.get('upload_date'))
    if date:
        meta.append(f"📅 {date}")
    dur = format_duration(info.get('duration'))
    if dur:
        meta.append(f"⏱ {dur}")
    res = (f"{info['width']}×{info['height']}"
           if info.get('width') and info.get('height') else info.get('resolution'))
    if res:
        meta.append(f"🖥 {res}")
    if meta:
        lines.append('  '.join(meta))

    stats = []
    views = format_count(info.get('view_count'))
    if views:
        stats.append(f"👁 {views}")
    likes = format_count(info.get('like_count'))
    if likes:
        stats.append(f"❤️ {likes}")
    comments = format_count(info.get('comment_count'))
    if comments:
        stats.append(f"💬 {comments}")
    if stats:
        lines.append('  '.join(stats))

    caption = "\n".join(lines)
    remaining = TG_CAPTION_LIMIT - len(caption) - 40
    desc_block, _ = format_description_block(description, remaining)
    caption += desc_block
    if len(caption) > TG_CAPTION_LIMIT:
        caption = caption[:TG_CAPTION_LIMIT - 1] + '…'

    if placeholder_message_id:
        try:
            bot.delete_message(chat_id_int, placeholder_message_id)
        except Exception:
            pass
    thumb_path = download_thumbnail(info.get('thumbnail'), video_id)
    try:
        if thumb_path:
            with open(thumb_path, 'rb') as f:
                sent = bot.send_photo(chat_id_int, f, caption=caption,
                                      parse_mode='HTML', reply_markup=kb)
        else:
            sent = bot.send_message(chat_id_int, caption,
                                    parse_mode='HTML', reply_markup=kb)
        user_data[(sent.chat.id, sent.message_id)] = data
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)
    return sent

def send_sniff_picker(chat_id, orig_url, candidates, placeholder_message_id):
    """Несколько разных потоков найдено на странице — не гадаем, а даём
    выбрать вручную (см. пожелание пользователя: точность важнее магии)."""
    kb = InlineKeyboardMarkup()
    for i, c in enumerate(candidates[:8]):
        size_str = format_file_size(c['size']) if c.get('size') else '?'
        kb.row(InlineKeyboardButton(f"▶️ Вариант {i + 1} — {size_str}",
                                    callback_data=f"sniffpick_{i}"))
    text = (f"🔎 Нашёл {len(candidates)} разных потоков на странице — "
           f"не могу однозначно понять, какой нужен. Выберите:\n"
           f"{arrow_link(orig_url)}")
    try:
        bot.edit_message_text(text, chat_id=chat_id, message_id=placeholder_message_id,
                              parse_mode='HTML', reply_markup=kb, disable_web_page_preview=True)
        msg_id = placeholder_message_id
    except Exception:
        sent = bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=kb,
                                disable_web_page_preview=True)
        msg_id = sent.message_id
    user_data[(chat_id, msg_id)] = {
        'source': 'sniff_pick',
        'url': orig_url,
        'candidates': candidates,
    }

def resolve_sniff_pick(chat_id, chosen_url, all_candidates=None, orig_url=None):
    status = bot.send_message(chat_id, "🔍 Получаю информацию о выбранном потоке...")
    try:
        info = get_video_info(chosen_url) or {}
        build_and_send_ytdlp_card(chat_id, chosen_url, info, status.message_id,
                                  sniff_candidates=all_candidates,
                                  sniff_orig_url=orig_url or chosen_url)
    except Exception as e:
        logger.error("Не удалось получить инфо о выбранном потоке: %s", e)
        err_text = re.sub(r'\x1b\[[0-9;]*m', '', str(e))
        try:
            bot.edit_message_text(f"❌ Ошибка: {err_text}",
                                  chat_id=chat_id, message_id=status.message_id)
        except Exception:
            pass

def process_url_message(message, url, placeholder):
    chat_id = message.chat.id
    # У TikTok/Bilibili уже есть собственный, куда более точный пайплайн
    # провайдеров. Общий sniff-фолбэк ниже создавался для сайтов, которые
    # yt-dlp вообще не знает, и слепо хватает первый попавшийся .mp4 в
    # сетевых запросах — а у известных площадок так можно поймать декоративный
    # мусор интерфейса (лого-анимация, заглушка плеера) вместо настоящего
    # видео и отправить его пользователю как будто это успех. Поэтому для
    # этих доменов, если специализированный путь не сработал, сразу
    # показываем настоящую ошибку, а не гадаем через generic sniff.
    known_platform = ('tiktok.com' in url or 'bilibili.com' in url
                      or 'b23.tv' in url or 'bili2233.cn' in url)

    try:
        if 'tiktok.com' in url:
            try:
                send_tiktok_card(message, url, placeholder)
                return
            except Exception as e:
                logger.warning("Провайдеры TikTok не справились, пробую yt-dlp: %s", e)

        if 'bilibili.com' in url or 'b23.tv' in url or 'bili2233.cn' in url:
            try:
                send_bilibili_card(message, url, placeholder)
                return
            except Exception as e:
                logger.warning("Провайдер Bilibili не справился, пробую yt-dlp: %s", e)

        # Vimeo: ссылка вида vimeo.com/{id} у yt-dlp иногда упирается в
        # «The web client only works when logged-in» — это проверка именно
        # полноценного сайта vimeo.com. А вот player.vimeo.com/video/{id} —
        # отдельный embed-URL, специально созданный для показа видео на
        # чужих сайтах (тот, что лежит в коде для встраивания, Share →
        # Embed) — он не завязан на тот же чек авторизации, и yt-dlp через
        # него нередко спокойно достаёт HLS/DASH-манифесты там, где обычная
        # ссылка не сработала. Подменяем ссылку заранее и по-тихому — не
        # заставляем пользователя вручную копировать embed-код.
        if 'vimeo.com' in url and 'player.vimeo.com' not in url:
            embed_url = vimeo_embed_url(url)
            if embed_url:
                try:
                    info = get_video_info(embed_url) or {}
                    build_and_send_ytdlp_card(chat_id, embed_url, info, placeholder.message_id)
                    return
                except Exception as e:
                    logger.info("Embed-URL Vimeo тоже не помог (%s), пробую обычную ссылку", e)

        try:
            info = get_video_info(url) or {}
            build_and_send_ytdlp_card(chat_id, url, info, placeholder.message_id)
            return
        except Exception as e:
            orig_err = str(e)

        # Vimeo: yt-dlp обычно и сам справляется (у него зрелый родной
        # экстрактор), но если конкретное видео приватное/встраиваемое
        # только с определённого домена/запароленное — get_video_info()
        # выше упадёт. Прежде чем скатываться в общий sniff (который
        # ловит .mp4/.m3u8 вслепую через headless-браузер и на видеохостингах
        # рискует поймать декоративный мусор плеера), пробуем прямой конфиг
        # плеера Vimeo (send_vimeo_card — тот же метод, что использует сам
        # официальный плеер), а если и он не сработал — Cobalt как посредник.
        if 'vimeo.com' in url:
            try:
                send_vimeo_card(chat_id, url, placeholder.message_id)
                return
            except Exception as ce:
                logger.warning("Vimeo-карточка (прямая и через Cobalt) тоже не собралась: %s", ce)

        if known_platform:
            raise Exception(orig_err)

        # Обычный способ не сработал — пробуем поймать поток вручную.
        try:
            bot.edit_message_text(
                "🔎 Не получилось обычным способом, ищу потоки вручную "
                "(может занять ~20 сек)...",
                chat_id=chat_id, message_id=placeholder.message_id)
        except Exception:
            pass

        candidates = sniff_media_candidates(url)

        if not candidates:
            raise Exception(orig_err)

        if len(candidates) == 1:
            sniffed_url = candidates[0]['url']
            logger.info("Sniff-фолбэк поймал один поток для %s: %s", url, sniffed_url)
            info = get_video_info(sniffed_url) or {}
            build_and_send_ytdlp_card(chat_id, sniffed_url, info,
                                      placeholder.message_id,
                                      sniff_candidates=candidates, sniff_orig_url=url)
        else:
            logger.info("Sniff-фолбэк нашёл %d потоков для %s", len(candidates), url)
            send_sniff_picker(chat_id, url, candidates, placeholder.message_id)

    except Exception as e:
        logger.error("Ошибка получения информации: %s", e)
        err_text = str(e)
        # ANSI-коды из вывода yt-dlp (например "\x1b[0;31mERROR:\x1b[0m") в
        # Telegram выглядят как мусор — вырезаем их.
        err_text = re.sub(r'\x1b\[[0-9;]*m', '', err_text)

        if 'Unsupported URL' in err_text:
            friendly = ("❌ Этот сайт не поддерживается загрузчиком (yt-dlp "
                        "не знает, как его скачивать).")
        elif 'impersonation' in err_text.lower():
            friendly = ("❌ Сайт блокирует бота по TLS-отпечатку браузера. "
                        "На сервере нужно установить пакет curl_cffi "
                        "(pip install curl_cffi) и перезапустить бота.")
        else:
            friendly = f"❌ Ошибка: {err_text}"

        try:
            bot.edit_message_text(friendly,
                                  chat_id=chat_id, message_id=placeholder.message_id)
        except Exception:
            pass

@bot.callback_query_handler(func=lambda call: True)
def handle_quality_choice(call):
    logger.info(">>> Кнопка '%s' от %s", call.data, call.from_user.id)
    chat_id = call.message.chat.id
    choice = call.data

    # ---- ПОИСК: эти кнопки живут в своей собственной небольшой машине
    # состояний (search_prompt/search_results/search_history) и не имеют
    # отношения к video_id/download-логике ниже, поэтому разбираем их
    # отдельно, сразу после чтения choice/chat_id.
    if choice in ('search_now', 'search_period', 'search_hist', 'search_cancel') \
            or choice.startswith('search_pick_') or choice.startswith('search_hist_'):
        data = user_data.get((chat_id, call.message.message_id))
        if not data:
            safe_answer_callback(call, "❌ Устарело, начните поиск заново.")
            return

        if choice == 'search_cancel':
            safe_answer_callback(call, "Отменено.")
            with _search_state_lock:
                SEARCH_STATE.pop(chat_id, None)
            try:
                bot.edit_message_text("Отменено.", chat_id=chat_id,
                                      message_id=call.message.message_id)
            except Exception:
                pass
            return

        if choice == 'search_now':
            query = data.get('query')
            safe_answer_callback(call, "⏳ Ищу...")
            bot.edit_message_text(f"⏳ Ищу «{esc(query)}»...", chat_id=chat_id,
                                  message_id=call.message.message_id, parse_mode='HTML')
            remember_search(chat_id, query)
            def _run(q=query, mid=call.message.message_id):
                try:
                    items = yt_search(q)
                    send_search_results(chat_id, q, items, message_id=mid)
                except Exception as e:
                    logger.error("Ошибка поиска: %s", e)
                    try:
                        bot.edit_message_text(f"❌ Ошибка поиска: {e}",
                                              chat_id=chat_id, message_id=mid)
                    except Exception:
                        pass
            if not enqueue_job(_run):
                bot.edit_message_text("🚦 Бот перегружен, попробуйте позже.",
                                      chat_id=chat_id, message_id=call.message.message_id)
            return

        if choice == 'search_period':
            query = data.get('query')
            safe_answer_callback(call)
            bot.edit_message_text(
                f"📅 За какой период искать «{esc(query)}»?\n"
                f"Напишите в формате <code>01.01.2012-01.01.2013</code> "
                f"(или просто годами: <code>2012-2013</code>).\n\n"
                f"⚠️ Учтите: YouTube не отдаёт дату видео в общей выдаче, поэтому "
                f"даты проверяются по одному видео за раз в пределах ограниченного "
                f"пула — это не мгновенно и не гарантирует все подходящие видео "
                f"из всей истории YouTube, только из первых результатов поиска.",
                chat_id=chat_id, message_id=call.message.message_id, parse_mode='HTML')
            with _search_state_lock:
                SEARCH_STATE[chat_id] = {'query': query}
            return

        if choice == 'search_hist':
            hist = SEARCH_HISTORY.get(chat_id, [])
            if not hist:
                safe_answer_callback(call, "История поиска пуста.")
                return
            safe_answer_callback(call)
            bot.edit_message_text("🕘 Ваши последние запросы:", chat_id=chat_id,
                                  message_id=call.message.message_id,
                                  reply_markup=build_history_kb(hist))
            user_data[(chat_id, call.message.message_id)] = {
                'source': 'search_history', 'items': hist}
            return

        if choice.startswith('search_hist_'):
            idx = int(choice.split('_')[-1])
            items = data.get('items') or []
            if idx >= len(items):
                safe_answer_callback(call, "❌ Устарело.")
                return
            query = items[idx]
            safe_answer_callback(call)
            bot.edit_message_text(f"🔎 Искать «{esc(query)}» на YouTube?", chat_id=chat_id,
                                  message_id=call.message.message_id, parse_mode='HTML',
                                  reply_markup=build_search_prompt_kb())
            user_data[(chat_id, call.message.message_id)] = {
                'source': 'search_prompt', 'query': query}
            return

        if choice.startswith('search_pick_'):
            idx = int(choice.split('_')[-1])
            items = data.get('items') or []
            if idx >= len(items):
                safe_answer_callback(call, "❌ Устарело, ищите заново.")
                return
            picked_url = items[idx]['url']
            safe_answer_callback(call, "⏳ Загружаю...")
            try:
                bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
            except Exception:
                pass
            job_key = ('url', chat_id, picked_url)
            if not try_start_job(job_key):
                safe_answer_callback(call, "⏳ Уже обрабатывается, подождите.")
                return
            def _run(u=picked_url, m=call.message):
                try:
                    process_url_message(m, u, call.message)
                finally:
                    finish_job(job_key)
            if not enqueue_job(_run):
                finish_job(job_key)
                safe_answer_callback(call, "🚦 Бот перегружен, попробуйте позже.", show_alert=True)
            return

    data = user_data.get((call.message.chat.id, call.message.message_id))
    if not data:
        bot.answer_callback_query(call.id, "❌ Данные устарели, отправьте ссылку заново.")
        return

    video_id = data.get('video_id')

    if choice.startswith('sniffpick_'):
        idx = int(choice.split('_', 1)[1])
        cands = data.get('candidates') or []
        if idx >= len(cands):
            safe_answer_callback(call, "❌ Такого варианта уже нет, отправьте ссылку заново.")
            return
        chosen_url = cands[idx]['url']
        safe_answer_callback(call, "⏳ Загружаю...")
        try:
            bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
        except Exception:
            pass
        job_key = ('dl', chat_id, 'sniffpick', chosen_url)
        if not try_start_job(job_key):
            safe_answer_callback(call, "⏳ Это уже обрабатывается, подождите.")
            return
        def _run_pick(cu=chosen_url, cands_=cands, orig_=data.get('url')):
            try:
                resolve_sniff_pick(chat_id, cu, all_candidates=cands_, orig_url=orig_)
            finally:
                finish_job(job_key)
        if not enqueue_job(_run_pick):
            finish_job(job_key)
            safe_answer_callback(call, "🚦 Бот перегружен, попробуйте позже.", show_alert=True)
        return

    if choice == 'sniff_back':
        cands = data.get('sniff_candidates') or []
        orig = data.get('sniff_orig_url') or data.get('url')
        if len(cands) < 2:
            safe_answer_callback(call, "Других вариантов не найдено.")
            return
        safe_answer_callback(call)
        send_sniff_picker(chat_id, orig, cands, None)
        return

    lang = data.get('lang_sel')

    if choice.startswith('setlang_'):
        code = choice[len('setlang_'):]
        data['lang_sel'] = code
        bot.answer_callback_query(call.id, f"Дорожка: {lang_display(code)}")
        bot.edit_message_reply_markup(
            chat_id, call.message.message_id, reply_markup=build_video_kb(data))
        return

    if choice == 'submenu':
        kb = sub_lang_keyboard(data)
        if not kb:
            safe_answer_callback(call, "Субтитры для этого видео не найдены.")
            return
        bot.answer_callback_query(call.id)
        bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=kb)
        return

    if choice.startswith('sub_'):
        code = choice[len('sub_'):]
        if is_cached(video_id, choice):
            bot.answer_callback_query(call.id, "⚡ Мгновенно из кэша!")
            bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
            send_from_cache(chat_id, video_id, choice)
            return
        dispatch_download(call, data, video_id, choice, handle_subtitle_download, code)
        return

    if choice == 'amenu':
        data.setdefault('audio_sel', 'mp3')
        bot.answer_callback_query(call.id)
        bot.edit_message_reply_markup(
            chat_id, call.message.message_id,
            reply_markup=audio_keyboard(data['audio_sel'], video_id, lang))
        return
    if choice == 'vmenu':
        bot.answer_callback_query(call.id)
        bot.edit_message_reply_markup(
            chat_id, call.message.message_id, reply_markup=build_video_kb(data))
        return
    if choice.startswith('afmt_'):
        data['audio_sel'] = choice[5:]
        bot.answer_callback_query(call.id)
        bot.edit_message_reply_markup(
            chat_id, call.message.message_id,
            reply_markup=audio_keyboard(data['audio_sel'], video_id, lang))
        return
    if choice.startswith('adl_'):
        ck = cache_key_for(choice, lang)
        if is_cached(video_id, ck):
            bot.answer_callback_query(call.id, "⚡ Мгновенно из кэша!")
            bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
            send_from_cache(chat_id, video_id, ck)
            if needs_full_description_file(data):
                send_full_description(chat_id, data, video_id=video_id)
            return
        parts = choice.split('_')
        key = parts[1]
        q = parts[2] if len(parts) > 2 else None
        dispatch_download(call, data, video_id, ck, handle_audio_download, key, q, lang)
        return

    if choice == 'vfmenu':
        data.setdefault('video_fmt_sel', 'mp4')
        bot.answer_callback_query(call.id)
        bot.edit_message_reply_markup(
            chat_id, call.message.message_id,
            reply_markup=video_format_keyboard(data['video_fmt_sel'], video_id, lang))
        return
    if choice == 'vback':
        bot.answer_callback_query(call.id)
        bot.edit_message_reply_markup(
            chat_id, call.message.message_id, reply_markup=build_video_kb(data))
        return
    if choice.startswith('vfmt_'):
        data['video_fmt_sel'] = choice[5:]
        bot.answer_callback_query(call.id)
        bot.edit_message_reply_markup(
            chat_id, call.message.message_id,
            reply_markup=video_format_keyboard(data['video_fmt_sel'], video_id, lang))
        return
    if choice.startswith('vdl_'):
        ck = cache_key_for(choice, lang)
        if is_cached(video_id, ck):
            bot.answer_callback_query(call.id, "⚡ Мгновенно из кэша!")
            bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
            send_from_cache(chat_id, video_id, ck)
            if needs_full_description_file(data):
                send_full_description(chat_id, data, video_id=video_id)
            return
        parts = choice.split('_')
        key = parts[1]
        q = parts[2] if len(parts) > 2 else '720p'
        dispatch_download(call, data, video_id, ck, handle_video_format_download, key, q, lang)
        return

    if data.get('source') == 'tiktok':
        if is_cached(video_id, choice):
            bot.answer_callback_query(call.id, "⚡ Мгновенно из кэша!")
            bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
            send_from_cache(chat_id, video_id, choice)
            if needs_full_description_file(data):
                send_full_description(chat_id, data, video_id=video_id)
            return
        dispatch_download(call, data, video_id, choice, handle_tiktok)
        return

    if choice == 'bili_dl':
        if is_cached(video_id, choice):
            bot.answer_callback_query(call.id, "⚡ Мгновенно из кэша!")
            bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
            send_from_cache(chat_id, video_id, choice)
            if needs_full_description_file(data):
                send_full_description(chat_id, data, video_id=video_id)
            return
        dispatch_download(call, data, video_id, choice, handle_bilibili_download)
        return

    if choice == 'vimeo_cobalt_dl':
        if is_cached(video_id, choice):
            bot.answer_callback_query(call.id, "⚡ Мгновенно из кэша!")
            bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
            send_from_cache(chat_id, video_id, choice)
            return
        dispatch_download(call, data, video_id, choice, handle_vimeo_cobalt_download)
        return

    if choice == 'vimeo_direct_dl':
        if is_cached(video_id, choice):
            bot.answer_callback_query(call.id, "⚡ Мгновенно из кэша!")
            bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
            send_from_cache(chat_id, video_id, choice)
            return
        dispatch_download(call, data, video_id, choice, handle_vimeo_direct_download)
        return

    ck = cache_key_for(choice, lang)
    if is_cached(video_id, ck):
        bot.answer_callback_query(call.id, "⚡ Мгновенно из кэша!")
        bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
        send_from_cache(chat_id, video_id, ck)
        if needs_full_description_file(data):
            send_full_description(chat_id, data, video_id=video_id)
        return

    dispatch_download(call, data, video_id, ck, process_main_download, choice, lang)

def send_full_description(chat_id, data, video_id=None, title=None, url=None):
    """Отправляет отдельным файлом полное описание видео, если оно есть.
    Используется после любого способа доставки видео — обычное скачивание,
    аудио/формат-видео меню и мгновенная отдача из кэша."""
    info = data.get('info') or {}
    full_desc = data.get('description') or info.get('description') or ''
    if not full_desc:
        return
    video_id = video_id or data.get('video_id') or 'video'
    title = title or data.get('title') or ''
    url = url or data.get('url') or ''
    desc_path = os.path.join(DOWNLOAD_DIR, f"{video_id}_description.txt")
    try:
        with open(desc_path, 'w', encoding='utf-8') as df:
            df.write(f"Название: {title}\nСсылка: {url}\n")
            df.write("=" * 40 + "\n" + full_desc)
        with open(desc_path, 'rb') as df:
            bot.send_document(chat_id, df, caption="📄 Полное описание")
    except Exception as e:
        logger.warning("Не удалось отправить описание: %s", e)
    finally:
        if os.path.exists(desc_path):
            os.remove(desc_path)

def process_main_download(call, data, choice, lang=None):
    chat_id = call.message.chat.id
    url      = data['url']
    title    = data['title']
    video_id = data['video_id']
    info     = data['info']

    bot.edit_message_reply_markup(chat_id, call.message.message_id, reply_markup=None)
    safe_answer_callback(call, "⏳ Загрузка...")

    status_msg = bot.send_message(chat_id, "⏳ Начинаю загрузку...")
    reporter = ProgressReporter(chat_id, status_msg.message_id, f"⏳ Скачиваю: {choice}")
    filename = None
    sent = None
    thumb_path = None

    try:
        cleanup_base(base_path_for(title, video_id))
        try:
            with yt_dlp.YoutubeDL(get_download_options(choice, video_id, title, lang,
                                                        reporter=reporter)) as ydl:
                ydl.extract_info(url, download=True)
            filename = find_downloaded_file(base_path_for(title, video_id))
            used_quality = choice
        except Exception:
            bot.edit_message_text("⚠️ Выбранное качество не скачалось, пробую другие...",
                                  chat_id=chat_id, message_id=status_msg.message_id)
            filename, used_quality = download_with_fallback(
                url, video_id, title, chat_id, status_msg, lang)

        if not filename or os.path.getsize(filename) == 0:
            bot.edit_message_text("❌ Не удалось скачать. Проверьте ссылку или интернет.",
                                  chat_id=chat_id, message_id=status_msg.message_id)
            return

        file_size = os.path.getsize(filename)
        quality_text = f"Качество: {used_quality.replace('_', ' ').upper()}"
        if lang:
            quality_text += f" | Дорожка: {lang_display(lang)}"
        cap = build_final_caption(data, file_size, quality_text)

        file_type = 'audio' if used_quality.startswith('audio_') else 'video'
        sent = None
        result_kb = None
        # Если фолбэк подставил другое качество, чем было нажато (например
        # 720p не скачался, а 480p — да), кэшировать нужно под РЕАЛЬНО
        # доставленным качеством, а не под нажатой кнопкой — иначе в
        # следующий раз клик по «720p» мгновенно подсунет 480p-файл под
        # видом 720p. Плюс дорожка языка — часть кэш-ключа (см. cache_key_for).
        if used_quality == choice:
            cache_choice = cache_key_for(choice, lang)
        elif used_quality in QUALITY_OPTIONS:
            cache_choice = cache_key_for(used_quality, lang)
        else:
            cache_choice = None  # 'best' и т.п. — ни одной кнопке не соответствует
        if data.get('sniff_candidates') and len(data['sniff_candidates']) > 1:
            result_kb = InlineKeyboardMarkup()
            result_kb.row(InlineKeyboardButton(
                "🔁 Это не то видео? Попробовать другой поток",
                callback_data='sniff_back'))
        reporter.prefix = "📤 Отправляю в Telegram"
        if file_type == 'video':
            raw_thumb = download_thumbnail(get_thumbnail_url(data), video_id)
            vid_w, vid_h, _ = probe_video_meta(filename)
            thumb_path = make_telegram_video_thumb(raw_thumb, video_id, vid_w, vid_h)
            if raw_thumb and os.path.exists(raw_thumb):
                os.remove(raw_thumb)
        try:
            sent = send_video_smart(chat_id, filename, file_type, cap,
                                    video_id=video_id, cache_choice=cache_choice,
                                    reply_markup=result_kb, reporter=reporter,
                                    thumb_path=thumb_path)
            if result_kb and sent:
                user_data[(sent.chat.id, sent.message_id)] = data
        except Exception as e:
            logger.error("Ошибка отправки, пробую как документ: %s", e)
            try:
                sent = send_file_with_retry(chat_id, filename, 'document', caption=cap,
                                            reporter=reporter, thumb_path=thumb_path)
                store_cached(video_id, cache_choice, sent, 'document', cap)
            except Exception as e2:
                logger.error("Не удалось отправить: %s", e2)

        if sent is None:
            bot.edit_message_text("❌ Не удалось отправить файл.",
                                  chat_id=chat_id, message_id=status_msg.message_id)
            return

        if needs_full_description_file(data):
            send_full_description(chat_id, data, video_id=video_id, title=title, url=url)

        bot.delete_message(chat_id, status_msg.message_id)

    except Exception as e:
        logger.error("Ошибка: %s", e)
        clean_err = re.sub(r'\x1b\[[0-9;]*m', '', str(e))
        bot.send_message(chat_id, f"❌ Ошибка: {clean_err}")
    finally:
        if thumb_path and os.path.exists(thumb_path):
            os.remove(thumb_path)
        if filename and os.path.exists(filename):
            if sent:
                os.remove(filename)
            else:
                logger.warning("Файл %s не подтверждён как отправленный — оставляю на диске", filename)


@bot.message_handler(func=lambda m: True)
def handle_period_reply_only(message):
    """Больше НЕ реагирует на произвольный текст как на поисковый запрос —
    в группах это стреляло по любому случайному слову (см. историю с
    «Ферма»). Единственная оставшаяся задача этого перехватчика — поймать
    ответ с датами после того, как человек явно нажал «Указать период»
    (после /search или из inline «Расширенный поиск»). Обычный поиск теперь
    только через /search и через inline-режим (@бот запрос)."""
    chat_id = message.chat.id
    text = (message.text or '').strip()
    if not text:
        return

    with _search_state_lock:
        pending = SEARCH_STATE.pop(chat_id, None)
    if not pending:
        return  # не режим ожидания периода — просто игнорируем сообщение

    m = DATE_RANGE_RE.match(text)
    if not m:
        if text.lower() in ('отмена', 'cancel', 'стоп', 'stop'):
            bot.reply_to(message, "Отменено.")
            return
        # Не похоже даже на попытку ввести период (нет ни точки, ни
        # дефиса рядом с цифрами) — скорее всего человек просто передумал.
        # Раз свободный текст больше не стартует поиск сам по себе, просто
        # подсказываем воспользоваться /search заново, а не гадаем.
        looks_like_date_attempt = bool(re.search(r'\d', text)) and \
                                  ('-' in text or '.' in text)
        if not looks_like_date_attempt:
            bot.reply_to(message, "Отменил ожидание периода. Чтобы искать — "
                                  "используйте /search запрос или inline-режим "
                                  "(@имя_бота запрос).")
            return
        with _search_state_lock:
            SEARCH_STATE[chat_id] = pending  # не теряем запрос, даём исправиться
        bot.reply_to(message, "Не понял период. Формат: <code>01.01.2012-01.01.2013</code> "
                              "(или просто годами: <code>2012-2013</code>).\n"
                              "Напишите ещё раз, или «отмена».", parse_mode='HTML')
        return
    try:
        d_from = _parse_search_date(m.group(1))
        d_to = _parse_search_date(m.group(2), is_end=True)
    except Exception:
        with _search_state_lock:
            SEARCH_STATE[chat_id] = pending
        bot.reply_to(message, "Не удалось разобрать даты, проверьте формат и напишите ещё раз.")
        return
    if d_from > d_to:
        d_from, d_to = d_to, d_from
    query = pending['query']
    remember_search(chat_id, query)
    status = bot.reply_to(
        message,
        f"⏳ Ищу «{esc(query)}» за период {d_from.strftime('%d.%m.%Y')}–"
        f"{d_to.strftime('%d.%m.%Y')}...\n(проверяю даты видео по одному, "
        f"может занять до минуты)", parse_mode='HTML')

    def _run(q=query, df=d_from, dt=d_to, mid=status.message_id):
        try:
            items = yt_search_with_period(q, df, dt)
            note = None
            if not items:
                note = ("(проверено ограниченное число видео из выдачи — "
                        "попробуйте более широкий период или другой запрос)")
            send_search_results(chat_id, q, items, message_id=mid, note=note)
        except Exception as e:
            logger.error("Ошибка поиска с периодом: %s", e)
            try:
                bot.edit_message_text(f"❌ Ошибка поиска: {e}",
                                      chat_id=chat_id, message_id=mid)
            except Exception:
                pass
    if not enqueue_job(_run):
        try:
            bot.edit_message_text("🚦 Бот перегружен, попробуйте позже.",
                                  chat_id=chat_id, message_id=status.message_id)
        except Exception:
            pass

# ---------- ОЧИСТКА ОСИРОТЕВШИХ ВРЕМЕННЫХ ФАЙЛОВ ----------
def cleanup_stray_temp_files():
    """При старте бота чистим все tmp_* в папке загрузок — это файлы от
    прошлых запусков, которые не успели удалиться (например, если бот
    был закрыт/упал посреди скачивания или конвертации)."""
    if not os.path.isdir(DOWNLOAD_DIR):
        return
    removed, freed = 0, 0
    for name in os.listdir(DOWNLOAD_DIR):
        if name.startswith('tmp_'):
            path = os.path.join(DOWNLOAD_DIR, name)
            try:
                size = os.path.getsize(path)
                os.remove(path)
                removed += 1
                freed += size
            except OSError as e:
                logger.warning("Не удалось удалить осиротевший файл %s: %s", path, e)
    if removed:
        logger.info("Уборка при старте: удалено %d файлов (%s)",
                   removed, format_file_size(freed))

# ---------- ЗАПУСК ----------
if __name__ == '__main__':
    cleanup_stray_temp_files()
    load_sent_cache()
    load_search_history()
    try:
        me = bot.get_me()
        logger.info("Бот подключился как @%s", me.username)
        set_bot_status_name(True)
    except Exception as e:
        logger.error("Не удалось получить профиль бота: %s", e)

    threading.Thread(target=monitor_loop, daemon=True).start()
    print("Бот запущен (локальный сервер, файлы до 2 ГБ).")

    # Внешний while True не нужен и вреден: любые ошибки polling
    # infinity_polling переживает сам (внутри свой цикл перезапуска).
    # А после Ctrl+C telebot взводит внутренний флаг остановки, и каждый
    # повторный вызов infinity_polling() возвращался мгновенно — именно
    # поэтому внешний цикл устраивал бесконечный спам "Break infinity polling".
    try:
        bot.infinity_polling()
    except KeyboardInterrupt:
        pass  # если telebot когда-нибудь пробросит его наружу — выходим тихо
    finally:
        set_bot_status_name(False)
        logger.info("Бот остановлен.")