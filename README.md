# Setup

## Requirements

- **Python 3.9+**
- **ffmpeg** — required. Download a static build (e.g. from gyan.dev on Windows) and either:
  - place `ffmpeg.exe` in the same folder as the script, or
  - have `ffmpeg` available on your system `PATH`.
- **Telegram Bot API local server** ([telegram-bot-api](https://github.com/tdlib/telegram-bot-api)) — required. This bot talks to `http://localhost:8081` instead of `api.telegram.org` directly, so that files up to 2 GB can be sent/received (the default cloud Bot API caps at ~50 MB).

  The official repo does **not** publish prebuilt binaries — only C++ source. You have two options:

  **Option 1 (recommended): build it yourself.**
  ```
  git clone --recursive https://github.com/tdlib/telegram-bot-api.git
  cd telegram-bot-api
  mkdir build && cd build
  cmake -DCMAKE_BUILD_TYPE=Release ..
  cmake --build . --target install
  ```
  Requires a C++17 compiler, CMake 3.10+, OpenSSL, zlib, gperf. See the [official build instructions generator](https://tdlib.github.io/telegram-bot-api/build.html) for a step-by-step guide for your OS.

  **Option 2 (quick, but read this first): third-party prebuilt Windows binary.**
  This bot was developed/tested against a build from [Bezdarnost01/telegram-bot-api-windows](https://github.com/Bezdarnost01/telegram-bot-api-windows). It works, but:
  - it has essentially no community track record (0 stars, 1 watcher at time of writing) — nobody but the author has vetted it;
  - its one and only release is from **May 2025** and hasn't been updated since, meaning it's missing anything Telegram added to the Bot API after that date.

  This staleness is a real, recurring source of bugs, not a hypothetical one: the `AcceptedGiftTypes`/`gifts_from_channels` crash this bot works around (see the monkeypatch near the top of the script) exists *because* this exact binary predates a Bot API field that the `pyTelegramBotAPI` library now expects unconditionally. Expect more patches like that to be needed over time as Telegram's API keeps moving and this binary doesn't. Use it if you want to get running quickly and don't mind occasionally patching around API drift yourself; use Option 1 if you want something that stays current.

  Either way, once you have the binary, run it before starting the bot:
  ```
  telegram-bot-api.exe --api-id=<your_id> --api-hash=<your_hash> --local
  ```
  Get `api_id` / `api_hash` from <https://my.telegram.org> (free, just needs a phone number).

## Install Python packages

```
pip install pyTelegramBotAPI yt-dlp requests
```

### Optional packages (bot works fine without them, just with reduced features)

| Package | What it enables if installed |
|---|---|
| `requests_toolbelt` | Real upload progress bar (tracks bytes actually sent) instead of a generic "uploading..." message |
| `youtube_transcript_api` | Subtitle/transcript download feature |
| `playwright` (+ `playwright install chromium`) | Fallback "sniff the video stream" mode for sites yt-dlp doesn't support at all (opens a real headless browser and captures the video network request), and one of the TikTok fallback providers |
| `curl_cffi` | Needed by yt-dlp itself for some sites that require TLS/browser impersonation (e.g. Dailymotion) |
| `ddgs` | Present in the code as an experimental DuckDuckGo search path — **does not actually support custom date ranges** (DDG only has day/week/month/year presets), so it's effectively dead weight; safe to skip |

Install everything at once:
```
pip install pyTelegramBotAPI yt-dlp requests requests_toolbelt youtube_transcript_api playwright curl_cffi
playwright install chromium
```

## Configure before running

Open the script and set:

- `TOKEN` — your bot token from [@BotFather](https://t.me/BotFather).
- `ADMIN_CHAT_ID` — your own Telegram numeric user/chat ID (used for status/error notifications).
- `YOUTUBE_API_KEY` *(optional)* — a YouTube Data API v3 key from [Google Cloud Console](https://console.cloud.google.com/) (enable "YouTube Data API v3" for your project). Only needed for exact date-range search; without it, the bot falls back to a slower best-effort method.
- `cookies.txt` *(optional)* — place next to the script to let yt-dlp use a logged-in YouTube session (helps with age-restricted/blocked videos). Export it with a browser extension like "Get cookies.txt LOCALLY". **Never share this file — it's equivalent to your account login.**

## Run

1. Start the local Bot API server (see above).
2. Run the bot:
   ```
   python kod-pro.py
   ```

If you want it to start automatically on boot (Windows), use a `.bat` file that launches both the server and the script in separate windows, then schedule that `.bat` via Task Scheduler.

## Notes

- Everything is wired for **Windows-style paths** (`ffmpeg.exe`, batch files). It should still run on Linux/macOS if you swap `ffmpeg.exe` for a plain `ffmpeg` binary on PATH and adjust the local-server startup accordingly, but this hasn't been tested there.
- Inline mode (`@your_bot query`) must be enabled once via [@BotFather](https://t.me/BotFather) → `Bot Settings` → `Inline Mode` → `Turn on`, or the search feature's inline part won't work.
