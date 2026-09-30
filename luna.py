"""
LUNA UNIVERSE  -  personal AI voice assistant with a live cosmic-video interface (Windows)

Everything from your last version is still here (video wallpaper + spinning core,
HUD, power sounds, YouTube/Music playback, Instagram, VS Code, WhatsApp, shutdown...)
and this version ADDS:

  1. AI BRAIN   - ask anything: Luna searches the web, reads the websites, and
                  Claude (or ChatGPT) explains it to you in detail, out loud.
                  "explain how black holes form", "write a poem on a bird",
                  "i want to know how to learn Python", "who is APJ Abdul Kalam"
  2. LOCATIONS  - "where is Jaipur" opens Google Maps, tells you the address and
                  explains the place. "directions to Udaipur" opens the route.
  3. WHATSAPP CALLS - "call papa", "video call papa", "message papa saying hello"
  4. CONVERSATION - anything else you say in English is a normal chat with memory.
  5. VOICE FIX  - if the normal voice route fails, Luna automatically falls back
                  to two other Windows voice routes, and prints the exact reason.
  6. WALLPAPER FIX - the window opens instantly, the video loads in the background,
                  and any .mp4 in this folder is used if luna.mp4 is missing.

SETUP (once)
    python -m pip install SpeechRecognition pyttsx3 sounddevice numpy pillow opencv-python
    python -m pip install requests anthropic ddgs beautifulsoup4 geopy pyautogui

    Put your space video in the SAME folder as this file, named  luna.mp4
    Put your Anthropic key in API_KEY below (or run: setx ANTHROPIC_API_KEY "key"
    and reopen the terminal).  Do NOT share this file after adding your key.

RUN
    python luna_universe.py

KEYS   F11 = full screen   Esc = leave full screen   C = captions on/off
       S = stop Luna from reading a long answer   K = add / change the AI key
"""

import datetime
import difflib
import json
import math
import os
import queue
import random
import re
import subprocess
import tempfile
import threading
import time
import tkinter as tk
import urllib.parse
import urllib.request
import wave
import webbrowser
from concurrent.futures import ThreadPoolExecutor

import numpy as np
import pyttsx3
import sounddevice as sd
import speech_recognition as sr
from PIL import Image, ImageDraw, ImageFilter, ImageTk

try:
    import cv2
except Exception as _cv_err:            # video is optional - Luna still works without it
    cv2 = None
    print(f"[Video notice: OpenCV is not installed ({_cv_err}). "
          f"Run: python -m pip install opencv-python]")

_RES = getattr(Image, "Resampling", Image)
LANCZOS, BILINEAR = _RES.LANCZOS, _RES.BILINEAR

# ------------------------------------------------------------------
# SETTINGS
# ------------------------------------------------------------------
ASSISTANT_NAME = "Luna"
LANGUAGE = "en-IN"              # use "en-US" if recognition is poor
SAMPLE_RATE = 16000             # microphone sample rate

VOICE_REPLIES = True            # True = Luna talks back.  False = captions only
FUTURISTIC_VOICE = True         # False = plain natural voice
SOUND_FX = True                 # power-on / power-down / listening beeps
START_FULLSCREEN = False        # True = open in full screen
SHOW_SUBTITLES = True           # show what Luna / you said (toggle with C)

# ---- AI brain -----------------------------------------------------
API_KEY = ""                    # paste your Anthropic key here, e.g. "sk-ant-..."
OPENAI_API_KEY = ""             # optional ChatGPT backup key
GEMINI_API_KEY = ""             # optional FREE key from aistudio.google.com (starts with AIza)
# You can also leave all keys empty: Luna will ask for one in a box when she starts
# and remember it in luna_config.json.
GEMINI_MODEL = "gemini-3.8-flash"   # if this name stops working, Luna finds a new one herself
CLAUDE_MODEL = "claude-sonnet-5-5"
OPENAI_MODEL = "gpt-4o-mini"
ANSWER_TOKENS = 1000            # longer = more detailed spoken answers

# ---- Video wallpaper ---------------------------------------------
VIDEO_NAME = "luna.mp4"         # your background video, next to this file
BG_WORK_WIDTH = 560             # background is decoded at this width
VIDEO_FPS = 20                  # frames per second kept in memory
MAX_VIDEO_SECONDS = 15          # first N seconds of the video are looped

# WhatsApp contacts: say the name, Luna opens the chat with that number.
# 10-digit numbers get the country code below added automatically.
DEFAULT_COUNTRY_CODE = "91"
CONTACTS = {
    "papa": "9887538936",
    "gunna didi": "9929927043",
    "bade papa": "8559995927",
}

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(BASE_DIR, "luna_config.json")

if API_KEY:
    os.environ["ANTHROPIC_API_KEY"] = API_KEY
if OPENAI_API_KEY:
    os.environ["OPENAI_API_KEY"] = OPENAI_API_KEY
if GEMINI_API_KEY:
    os.environ["GEMINI_API_KEY"] = GEMINI_API_KEY


def blend(c1, c2, f):
    a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(int(a[i] * (1 - f) + b[i] * f) for i in range(3))


def load_config():
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def save_config(cfg):
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2)


CONFIG = load_config()
for _k, _env in (("anthropic_key", "ANTHROPIC_API_KEY"), ("gemini_key", "GEMINI_API_KEY"),
                 ("openai_key", "OPENAI_API_KEY")):
    if CONFIG.get(_k) and not os.environ.get(_env):
        os.environ[_env] = CONFIG[_k]

# ------------------------------------------------------------------
# SHARED STATE between the assistant thread and the window
# ------------------------------------------------------------------
ui_q = queue.Queue()
speech = {"clip": None}         # (envelope, seconds_per_step, start_time) while speaking
speech_stop = threading.Event()  # set by the S key to stop a long answer


def post(kind, *args):
    ui_q.put((kind, args))


# ------------------------------------------------------------------
# 1. SOUND EFFECTS - synthesised, no audio files needed
# ------------------------------------------------------------------
FX_RATE = 44100


def _play(samples, vol=1.0):
    if not SOUND_FX:
        return
    try:
        sd.play((samples * vol).astype(np.float32), FX_RATE)
        sd.wait()
    except Exception as e:
        print(f"[Sound effect notice: {e}]")


def tone(f_start, f_end, dur=0.12, vol=0.2):
    n = int(FX_RATE * dur)
    freq = np.linspace(f_start, f_end, n)
    phase = 2 * np.pi * np.cumsum(freq) / FX_RATE
    wav = (np.sin(phase) + 0.3 * np.sin(2 * phase)) * np.hanning(n) * vol
    _play(wav)


def fx_listen():
    tone(700, 1050, 0.09)


def fx_heard():
    tone(1300, 900, 0.07)


def _engine_body(rise, dur, rumble_f0, rumble_f1, chime):
    """Shared synth for the power-on / power-down sweep (rumble + noise + chime)."""
    n = int(FX_RATE * dur)
    t = np.arange(n) / FX_RATE
    prog = t / dur if rise else 1 - t / dur

    rumble_f = rumble_f0 + (rumble_f1 - rumble_f0) * prog
    rumble = np.sin(2 * np.pi * np.cumsum(rumble_f) / FX_RATE)
    rumble += 0.5 * np.sin(2 * np.pi * np.cumsum(rumble_f * 1.5) / FX_RATE)

    noise = np.random.uniform(-1, 1, n)
    noise_env = (prog ** 2) if rise else (prog ** 0.5)
    engine = rumble * (0.25 + 0.75 * prog) + noise * 0.18 * noise_env

    env = np.clip(np.minimum(t / 0.08, (dur - t) / 0.25), 0, 1)
    out = engine * env

    if chime:
        notes = [660, 880, 1320] if rise else [1320, 880, 660]
        seg = n // len(notes)
        for i, f in enumerate(notes):
            s, e = i * seg, min(n, (i + 1) * seg + int(0.05 * FX_RATE))
            k = np.arange(e - s)
            w = np.hanning(len(k))
            out[s:e] += 0.22 * np.sin(2 * np.pi * f * k / FX_RATE) * w

    peak = np.max(np.abs(out)) + 1e-6
    return out / peak


def fx_powerup():
    """Engine spinning up + a rising digital chime - Luna coming online."""
    _play(_engine_body(True, 1.6, 55, 260, chime=True), vol=0.55)


def fx_powerdown():
    """Engine winding down + a falling chime - Luna going offline."""
    _play(_engine_body(False, 1.4, 240, 40, chime=True), vol=0.5)


# ------------------------------------------------------------------
# 2. VOICE - three routes, so Luna always finds a way to talk
# ------------------------------------------------------------------
def pick_female_voice(engine):
    voices = engine.getProperty("voices")
    for v in voices:
        name = v.name.lower()
        if any(k in name for k in ("zira", "female", "hazel", "heera")):
            return v.id
    return voices[1].id if len(voices) > 1 else voices[0].id


def new_engine():
    engine = pyttsx3.init()
    engine.setProperty("voice", pick_female_voice(engine))
    engine.setProperty("rate", 175)
    return engine


def synthesize(text):
    path = os.path.join(tempfile.gettempdir(), f"luna_{os.getpid()}.wav")
    engine = new_engine()
    engine.save_to_file(text, path)
    engine.runAndWait()
    engine.stop()
    with wave.open(path, "rb") as w:
        channels, width, rate, n = (w.getnchannels(), w.getsampwidth(),
                                    w.getframerate(), w.getnframes())
        raw = w.readframes(n)
    try:
        os.remove(path)
    except OSError:
        pass
    if width != 2:
        raise ValueError("unsupported wav format")
    data = np.frombuffer(raw, dtype=np.int16).astype(np.float32) / 32768.0
    if channels > 1:
        data = data.reshape(-1, channels).mean(axis=1)
    return data, rate


def futuristic(data, rate):
    """Light echo + digital shimmer -> soft 'AI hologram' voice."""
    tail = int(0.25 * rate)
    dry = np.pad(data, (0, tail))
    t = np.arange(len(dry)) / rate
    out = dry + 0.08 * dry * np.sin(2 * np.pi * 180 * t)
    for delay, gain in ((0.045, 0.22), (0.11, 0.12)):
        d = int(delay * rate)
        out[d:] += gain * dry[:-d]
    peak = np.max(np.abs(out)) + 1e-6
    return (out / peak * 0.9).astype(np.float32)


def envelope(data, rate, hop):
    n = max(1, int(rate * hop))
    m = len(data) // n
    if m == 0:
        return np.zeros(1, dtype=np.float32)
    rms = np.sqrt(np.mean(data[:m * n].reshape(m, n) ** 2, axis=1))
    ref = np.percentile(rms, 95) + 1e-6
    return np.clip(rms / ref, 0, 1).astype(np.float32)


ENV_HOP = 0.03


def _speak_powershell(text):
    """Route 3: the built-in Windows speech engine, no Python audio needed."""
    safe = text.replace("'", "''").replace("\n", " ").replace("\r", " ")
    ps = ("Add-Type -AssemblyName System.Speech; "
          "$s = New-Object System.Speech.Synthesis.SpeechSynthesizer; "
          "try { $s.SelectVoice('Microsoft Zira Desktop') } catch { }; "
          "$s.Speak('" + safe + "')")
    subprocess.run(["powershell", "-NoProfile", "-Command", ps],
                   creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0), timeout=180)


def speak(text, final=True):
    print(f"{ASSISTANT_NAME}: {text}")

    if not VOICE_REPLIES:                       # captions-only mode
        post("chat", ASSISTANT_NAME, text)
        post("state", "speaking")
        time.sleep(min(8.0, 0.6 + len(text) / 16))
        if final:
            post("state", "idle")
        return

    post("state", "thinking")
    played = False

    # Route 1: synthesize -> play (lets the HUD react to her real voice)
    try:
        data, rate = synthesize(text)
        if len(data) < rate * 0.05:
            raise ValueError("the voice engine produced empty audio")
        if FUTURISTIC_VOICE:
            data = futuristic(data, rate)
        env = envelope(data, rate, ENV_HOP)
        post("chat", ASSISTANT_NAME, text)
        post("state", "speaking")
        speech["clip"] = (env, ENV_HOP, time.perf_counter())
        sd.play(data, rate)
        sd.wait()
        played = True
    except Exception as e:
        print(f"[VOICE PROBLEM - main voice route failed: {e}]")
    finally:
        speech["clip"] = None

    # Route 2: pyttsx3 speaks directly
    if not played:
        post("chat", ASSISTANT_NAME, text)
        post("state", "speaking")
        try:
            engine = new_engine()
            engine.say(text)
            engine.runAndWait()
            engine.stop()
            played = True
        except Exception as e:
            print(f"[VOICE PROBLEM - pyttsx3 direct route failed: {e}]")

    # Route 3: Windows built-in speech through PowerShell
    if not played:
        try:
            _speak_powershell(text)
            played = True
        except Exception as e:
            print(f"[VOICE PROBLEM - Windows speech route failed: {e}]")

    if not played:
        print("[VOICE PROBLEM - no voice route worked. Check Windows Settings > "
              "Sound > Output device, and Settings > Time & language > Speech.]")
    if final:
        post("state", "idle")


def clean_for_speech(text):
    text = re.sub(r"```.*?```", " ", text, flags=re.S)
    text = re.sub(r"https?://\S+", "", text)
    text = re.sub(r"[*#_`>|]+", "", text)
    text = re.sub(r"\s*\n+\s*", " ", text)
    return text.strip()


def split_chunks(text, limit=190):
    sentences = re.split(r"(?<=[.!?])\s+", text.strip())
    chunks, cur = [], ""
    for s in sentences:
        if not cur or len(cur) + len(s) + 1 <= limit:
            cur = (cur + " " + s).strip()
        else:
            chunks.append(cur)
            cur = s
    if cur:
        chunks.append(cur)
    return chunks


def say_long(text):
    """Speak a long answer in natural chunks; captions follow each chunk."""
    chunks = split_chunks(clean_for_speech(text))
    speech_stop.clear()
    for i, chunk in enumerate(chunks):
        if speech_stop.is_set():
            break
        speak(chunk, final=(i == len(chunks) - 1))
    if speech_stop.is_set():
        post("state", "idle")
    speech_stop.clear()


# ------------------------------------------------------------------
# 3. EARS - stops recording when you stop talking
# ------------------------------------------------------------------
recognizer = sr.Recognizer()


def _record(wait_seconds, max_phrase_seconds):
    block = int(SAMPLE_RATE * 0.1)
    frames, started = [], False
    silent_blocks = waited_blocks = 0

    with sd.InputStream(samplerate=SAMPLE_RATE, channels=1,
                        dtype="int16", blocksize=block) as stream:
        ambient = []
        for _ in range(5):
            data, _ = stream.read(block)
            ambient.append(np.sqrt(np.mean(data.astype(np.float32) ** 2)))
        threshold = max(np.mean(ambient) * 2.5, 400)

        while True:
            data, _ = stream.read(block)
            rms = np.sqrt(np.mean(data.astype(np.float32) ** 2))
            if rms > threshold:
                started = True
                silent_blocks = 0
                frames.append(data.copy())
            elif started:
                frames.append(data.copy())
                silent_blocks += 1
                if silent_blocks >= 10:
                    break
            else:
                waited_blocks += 1
                if waited_blocks > wait_seconds * 10:
                    return []
            if started and len(frames) > max_phrase_seconds * 10:
                break
    return frames


def listen(wait_seconds=6, max_phrase_seconds=10):
    post("state", "listening")
    print("\n[Listening... speak now]")
    fx_listen()
    text = ""
    try:
        frames = _record(wait_seconds, max_phrase_seconds)
        if frames:
            audio = sr.AudioData(np.concatenate(frames).tobytes(), SAMPLE_RATE, 2)
            text = recognizer.recognize_google(audio, language=LANGUAGE).lower()
    except sr.UnknownValueError:
        pass
    except sr.RequestError:
        print("[Speech service unavailable - check your internet]")
    except Exception as e:
        print(f"[Audio notice: {e}]")

    if text:
        print(f"You said: '{text}'")
        post("chat", "You", text)
        post("state", "thinking")
        fx_heard()
    else:
        post("state", "idle")
    return text


def ask(question, wait_seconds=7):
    speak(question)
    return listen(wait_seconds=wait_seconds)


def has(command, *phrases):
    """Whole-word match, so 'hi' does not trigger inside 'which'."""
    return any(re.search(r"\b" + re.escape(p) + r"\b", command) for p in phrases)


# ------------------------------------------------------------------
# 4. WEB + AI BRAIN
# ------------------------------------------------------------------
WEB_HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) LunaAssistant/2.0"}

SYSTEM_PROMPT = (
    "You are Luna, a warm, smart, friendly female personal AI assistant. "
    "The user speaks English and hears your reply through a speaker, so write "
    "plain spoken English: no markdown, no bullet symbols, no emojis, no URLs. "
    "Be clear, natural and encouraging. When the user wants to learn something, "
    "explain in detail, step by step, with simple examples. For casual chat, "
    "keep replies short, two to four sentences. If web notes are provided, use "
    "them and mention website names naturally, like 'according to Wikipedia'. "
    "If you are not sure about something, say so honestly."
)

history = []                     # chat memory: list of {"role", "content"}


SKIP = {"claude": False, "openai": False}     # set when a key has no credit / is rejected
KEY_PROMPTED = {"done": False}                # ask for a new key only once per session
DEAD_KEY_WORDS = ("credit balance", "billing", "insufficient", "authentication",
                  "invalid x-api-key", "invalid_api_key", "401", "403", "permission")


def have_ai():
    """True only if at least one key is present AND not known to be dead."""
    return bool((os.getenv("ANTHROPIC_API_KEY") and not SKIP["claude"])
                or (os.getenv("OPENAI_API_KEY") and not SKIP["openai"])
                or os.getenv("GEMINI_API_KEY"))


def web_search(query, n=6):
    try:
        try:
            from ddgs import DDGS
        except ImportError:
            from duckduckgo_search import DDGS
        return list(DDGS().text(query, max_results=n)) or []
    except Exception as e:
        print(f"[Search notice: {e}]")
        return []


def fetch_text(url, limit=2500):
    try:
        import requests
        from bs4 import BeautifulSoup
        r = requests.get(url, headers=WEB_HEADERS, timeout=6)
        if r.status_code != 200 or "text/html" not in r.headers.get("content-type", ""):
            return ""
        soup = BeautifulSoup(r.text, "html.parser")
        for tag in soup(["script", "style", "nav", "footer", "header", "aside", "form"]):
            tag.decompose()
        paras = [p.get_text(" ", strip=True) for p in soup.find_all("p")]
        return " ".join(p for p in paras if len(p) > 60)[:limit]
    except Exception:
        return ""


def domain_of(url):
    d = urllib.parse.urlparse(url).netloc.lower()
    return d[4:] if d.startswith("www.") else d


def research(question, pages=3):
    """Search the web and read the top pages. Returns (notes, [site names])."""
    results = web_search(question, 6)
    if not results:
        return "", []
    top = results[:pages]
    with ThreadPoolExecutor(max_workers=pages) as ex:
        texts = list(ex.map(lambda r: fetch_text(r.get("href", "")), top))
    notes, sites = [], []
    for r, txt in zip(top, texts):
        body = txt or r.get("body", "")
        if body:
            site = domain_of(r.get("href", ""))
            notes.append(f"Source: {site} | {r.get('title', '')}\n{body}")
            sites.append(site)
    for r in results[pages:]:
        if r.get("body"):
            notes.append(f"Source: {domain_of(r.get('href', ''))}\n{r['body']}")
    return "\n\n".join(notes), sites


def _ask_claude(messages, max_tokens):
    import anthropic
    client = anthropic.Anthropic()
    resp = client.messages.create(model=CLAUDE_MODEL, max_tokens=max_tokens,
                                  system=SYSTEM_PROMPT, messages=messages)
    return "".join(b.text for b in resp.content if b.type == "text")


def _ask_openai(messages, max_tokens):
    from openai import OpenAI
    client = OpenAI()
    resp = client.chat.completions.create(
        model=OPENAI_MODEL, max_tokens=max_tokens,
        messages=[{"role": "system", "content": SYSTEM_PROMPT}] + messages)
    return resp.choices[0].message.content


GEMINI_STATE = {"model": GEMINI_MODEL}
last_ai_error = {"msg": ""}


def _discover_gemini_model(headers):
    import requests
    r = requests.get("https://generativelanguage.googleapis.com/v1beta/models?pageSize=100",
                     headers=headers, timeout=15)
    names = []
    for m in r.json().get("models", []):
        n = m.get("name", "").replace("models/", "")
        if "generateContent" in m.get("supportedGenerationMethods", []) and "flash" in n \
                and not any(x in n for x in ("lite", "image", "tts", "live", "audio",
                                             "embedding", "vision", "thinking")):
            names.append(n)
    return sorted(names)[-1] if names else None


def _ask_gemini(messages, max_tokens):
    import requests
    headers = {"x-goog-api-key": os.getenv("GEMINI_API_KEY"), "Content-Type": "application/json"}
    body = {
        "system_instruction": {"parts": [{"text": SYSTEM_PROMPT}]},
        "contents": [{"role": "user" if m["role"] == "user" else "model",
                      "parts": [{"text": m["content"]}]} for m in messages],
        "generationConfig": {"maxOutputTokens": max_tokens * 2},
    }
    for attempt in range(2):
        url = ("https://generativelanguage.googleapis.com/v1beta/models/"
               f"{GEMINI_STATE['model']}:generateContent")
        r = requests.post(url, headers=headers, json=body, timeout=60)
        if r.status_code == 404 and attempt == 0:      # model name changed - find a current one
            found = _discover_gemini_model(headers)
            if found:
                GEMINI_STATE["model"] = found
                continue
        if r.status_code != 200:
            raise RuntimeError(f"Gemini HTTP {r.status_code}: {r.text[:300]}")
        parts = r.json()["candidates"][0]["content"]["parts"]
        return "".join(p.get("text", "") for p in parts)
    raise RuntimeError("Gemini model not found")


def ai_reply(user_text, notes="", max_tokens=ANSWER_TOKENS):
    global history
    prompt = user_text
    if notes:
        prompt = (f"{user_text}\n\n--- Notes from websites Luna just read ---\n"
                  f"{notes}\n--- End of notes ---")
    messages = history + [{"role": "user", "content": prompt}]
    answer = None
    if os.getenv("ANTHROPIC_API_KEY") and not SKIP["claude"]:
        try:
            answer = _ask_claude(messages, max_tokens)
        except Exception as e:
            last_ai_error["msg"] = str(e)
            print(f"[Claude error: {e}]")
            if any(x in str(e).lower() for x in DEAD_KEY_WORDS):
                SKIP["claude"] = True
    if not answer and os.getenv("OPENAI_API_KEY") and not SKIP["openai"]:
        try:
            answer = _ask_openai(messages, max_tokens)
        except Exception as e:
            last_ai_error["msg"] = str(e)
            print(f"[OpenAI error: {e}]")
            if any(x in str(e).lower() for x in DEAD_KEY_WORDS):
                SKIP["openai"] = True
    if not answer and os.getenv("GEMINI_API_KEY"):
        try:
            answer = _ask_gemini(messages, max_tokens)
        except Exception as e:
            last_ai_error["msg"] = str(e)
            print(f"[Gemini error: {e}]")
    if answer:
        history += [{"role": "user", "content": user_text},
                    {"role": "assistant", "content": answer}]
        history = history[-16:]
        while history and history[0]["role"] != "user":
            history.pop(0)
    return answer


def ask_key_once():
    if not KEY_PROMPTED["done"]:
        KEY_PROMPTED["done"] = True
        post("askkey")


def no_ai():
    err = last_ai_error["msg"].lower()
    if not have_ai() and not err:
        say_long("I do not have an AI key yet, so I can only read web results. "
                 "Press the K key to add a free Gemini key.")
    elif any(x in err for x in ("credit balance", "billing", "insufficient")):
        say_long("My AI account has no credit left. A box will open. Please paste a "
                 "free Gemini key there.")
        ask_key_once()
    elif any(x in err for x in ("401", "403", "authentication", "api key not valid",
                                "invalid x-api-key", "permission")):
        say_long("My AI key was rejected. A box will open. Please paste a working key.")
        ask_key_once()
    elif any(x in err for x in ("429", "quota", "rate", "resource_exhausted")):
        say_long("I have reached my AI limit for now. Please try again in a minute.")
    else:
        say_long("I could not reach my AI brain right now. Please check your "
                 "internet connection and try again.")


def topic_of(text):
    t = re.sub(r"^(?:i wanted to know|i want to know|i would like to know)\s+(?:about\s+)?", "", text)
    for w in sorted(RESEARCH_STARTS, key=len, reverse=True):
        if t.startswith(w + " "):
            t = t[len(w):].strip()
            break
    t = re.sub(r"^(?:about|the|a|an|is|are|does|do)\s+", "", t)
    return t or text


def wikipedia_summary(query):
    """Free, no key: returns (title, intro text) of the best Wikipedia match."""
    try:
        import requests
        r = requests.get("https://en.wikipedia.org/w/api.php", headers=WEB_HEADERS, timeout=8,
                         params={"action": "query", "generator": "search", "gsrsearch": query,
                                 "gsrlimit": 1, "prop": "extracts", "exintro": 1,
                                 "explaintext": 1, "format": "json"})
        for page in r.json().get("query", {}).get("pages", {}).values():
            text = (page.get("extract") or "").strip()
            if text:
                return page.get("title", ""), text
    except Exception as e:
        print(f"[Wikipedia notice: {e}]")
    return None


def free_answer(question, creative=False, notes="", sites=None):
    """No AI needed: read Wikipedia or the best website result aloud."""
    if not creative:
        wiki = wikipedia_summary(topic_of(question))
        if wiki:
            say_long(wiki[1][:1100])
            say_long("That was from Wikipedia.")
            return
    if not notes:
        notes, sites = research(question, pages=2)
    if notes:
        first = notes.split("\n\n")[0]
        body = first.split("\n", 1)[1] if "\n" in first else first
        say_long(body[:900])
        if sites:
            say_long("That was from " + sites[0] + ".")
    else:
        speak("I could not find anything about that right now.")


def explain(question, creative=False):
    """Learn from websites, then explain in detail."""
    if not have_ai():
        # No working AI key: answer for free from Wikipedia / websites.
        if creative:
            speak("I need an AI key to write that. Press K to add a free Gemini key. "
                  "For now, here is what I found.")
        else:
            speak("I have no working AI key, so I will read what I found. "
                  "Press K to add a free Gemini key.")
        post("state", "thinking")
        free_answer(question, creative)
        return
    speak("Sure. Let me learn about that from the internet for you.")
    post("state", "thinking")
    notes, sites = research(question + (" tips ideas examples" if creative else ""))
    if creative:
        instruction = (f"{question}\n\nWrite it for me, then briefly explain how "
                       "you wrote it and the technique used, so I can learn to do it myself.")
    else:
        instruction = (f"{question}\n\nExplain this in detail, step by step, in "
                       "simple spoken English.")
    post("state", "thinking")
    answer = ai_reply(instruction, notes)
    if not answer:
        no_ai()
        free_answer(question, creative, notes, sites)
        return
    say_long(answer)
    if sites:
        say_long("I learned this from " + ", ".join(dict.fromkeys(sites)) + ".")


JOKES = [
    "Why did the computer go to the doctor? Because it caught a virus.",
    "Why do programmers prefer dark mode? Because light attracts bugs.",
    "I told my computer I needed a break, and now it will not stop sending me vacation ads.",
]


def chat(text):
    if not have_ai():
        if has(text, "thanks", "thank you"):
            speak("You are welcome!")
        elif has(text, "joke"):
            speak(random.choice(JOKES))
        elif has(text, "love you", "good morning", "good night", "good evening"):
            speak("That is sweet. I am always here for you.")
        else:
            speak("To chat properly I need an AI key. Press the K key and paste a free "
                  "Gemini key. Meanwhile I can explain topics, show locations, play "
                  "songs, and call your contacts.")
        return
    post("state", "thinking")
    answer = ai_reply(text, max_tokens=500)
    if answer:
        say_long(answer)
    else:
        no_ai()


# ------------------------------------------------------------------
# 5. ACTIONS
# ------------------------------------------------------------------
def open_url(url):
    try:
        subprocess.Popen(["cmd", "/c", "start", "", "chrome", url])
    except Exception:
        webbrowser.open(url)


def q(text):
    return urllib.parse.quote_plus(text)


def youtube_first_video_id(query):
    """Look up the real first YouTube result for query and return its video id."""
    url = "https://www.youtube.com/results?search_query=" + q(query)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    html = urllib.request.urlopen(req, timeout=6).read().decode("utf-8", "ignore")
    m = re.search(r'"videoId":"(.*?)"', html)
    return m.group(1) if m else None


def play_on_youtube(query, context=""):
    speak(f"Playing {query}{context}.")
    video_id = None
    try:
        video_id = youtube_first_video_id(query)
    except Exception as e:
        print(f"[YouTube lookup notice: {e}]")
    if video_id:
        open_url(f"https://www.youtube.com/watch?v={video_id}&autoplay=1")
    else:
        speak("I could not fetch it directly, so here are the search results instead.")
        open_url(f"https://www.youtube.com/results?search_query={q(query)}")


def do_youtube_music():
    song = ask("Sure! Which song should I play?")
    if song:
        play_on_youtube(song, " on YouTube Music")
    else:
        speak("I did not hear a song name. Opening YouTube Music.")
        open_url("https://music.youtube.com")


def do_youtube():
    video = ask("Sure! Which video should I play?")
    if video:
        play_on_youtube(video)
    else:
        speak("I did not hear anything. Opening the YouTube homepage.")
        open_url("https://www.youtube.com")


def do_google():
    query = ask("What would you like me to search on Google?")
    if query:
        speak(f"Searching Google for {query}.")
        open_url(f"https://www.google.com/search?q={q(query)}")
    else:
        speak("Opening Google Chrome.")
        open_url("https://www.google.com")


def do_instagram():
    answer = ask("Opening Instagram. Do you want to visit a profile? "
                 "Say the username, or say no.")
    if answer and not has(answer, "no", "nope", "nothing", "skip"):
        username = answer.replace(" ", "").replace(".", "")
        speak(f"Opening the profile {username}.")
        open_url(f"https://www.instagram.com/{username}/")
    else:
        speak("Opening the Instagram homepage.")
        open_url("https://www.instagram.com")


def do_vscode():
    answer = ask("Opening Visual Studio Code. Should I open a specific folder? "
                 "Say yes or no.")
    if answer and has(answer, "yes", "yeah", "yep", "sure"):
        folder = ask("Tell me the folder name on your Desktop.")
        path = os.path.join(os.path.expanduser("~"), "Desktop", folder.strip())
        if folder and os.path.isdir(path):
            speak(f"Opening {folder} in Visual Studio Code.")
            subprocess.Popen(f'code "{path}"', shell=True)
            return
        speak("I could not find that folder. Opening Visual Studio Code normally.")
    else:
        speak("Launching Visual Studio Code.")
    subprocess.Popen("code", shell=True)


# ---------------- WhatsApp ----------------
def wa_number(raw):
    digits = re.sub(r"\D", "", raw)
    if len(digits) == 10:
        digits = DEFAULT_COUNTRY_CODE + digits
    return digits


def find_contact(name):
    name = name.lower().strip()
    if not name:
        return None
    if name in CONTACTS:
        return name
    match = difflib.get_close_matches(name, list(CONTACTS.keys()), n=1, cutoff=0.6)
    return match[0] if match else None


def open_whatsapp_chat(number, text=None):
    """Opens the chat in WhatsApp Desktop if installed, else WhatsApp Web."""
    try:
        url = f"whatsapp://send?phone={number}"
        if text:
            url += "&text=" + urllib.parse.quote(text)
        os.startfile(url)
        return True
    except Exception:
        url = f"https://wa.me/{number}"
        if text:
            url += "?text=" + q(text)
        open_url(url)
        return False


def do_whatsapp():
    name = ask("Opening WhatsApp. Who do you want to message? "
               "Say a contact name, or say nobody.").strip()
    contact = find_contact(name)
    if contact:
        message = ask(f"What should I say to {contact}?", wait_seconds=8)
        if message:
            speak(f"Opening the chat with {contact}. Just press send.")
        else:
            speak(f"Opening the chat with {contact}.")
        open_whatsapp_chat(wa_number(CONTACTS[contact]), message or None)
    else:
        if name and not has(name, "nobody", "no one", "none", "no"):
            speak("I do not have that contact saved yet.")
        speak("Opening WhatsApp Web.")
        open_url("https://web.whatsapp.com")


def do_whatsapp_message(name, message):
    contact = find_contact(name)
    if not contact:
        speak(f"I could not find {name} in your contacts.")
        return
    speak(f"Opening the chat with {contact}. Just press send.")
    open_whatsapp_chat(wa_number(CONTACTS[contact]), message)


def do_whatsapp_call(name, video=False):
    contact = find_contact(name)
    if not contact:
        speak(f"I could not find {name} in your contacts.")
        return
    kind = "video" if video else "voice"
    speak(f"Opening WhatsApp to {kind} call {contact}.")
    open_whatsapp_chat(wa_number(CONTACTS[contact]))
    time.sleep(6)
    pos = CONFIG.get(f"wa_{kind}_pos")
    if not pos:
        speak(f"I opened the chat, but I do not know where the {kind} call button is yet. "
              f"Say calibrate WhatsApp {kind} call, and I will learn it.")
        return
    try:
        import pyautogui
        pyautogui.click(pos[0], pos[1])
        speak(f"Calling {contact} now.")
    except Exception as e:
        print(f"[Call click notice: {e}]")
        speak("I could not press the call button. Please tap it yourself.")


def do_calibrate_whatsapp(video=False):
    kind = "video" if video else "voice"
    speak(f"Open a WhatsApp chat, then put your mouse on the {kind} call button. "
          "I will remember its position in six seconds.")
    time.sleep(6)
    try:
        import pyautogui
        p = pyautogui.position()
        CONFIG[f"wa_{kind}_pos"] = [int(p.x), int(p.y)]
        save_config(CONFIG)
        speak(f"Done. I learned the {kind} call button position.")
    except Exception as e:
        print(f"[Calibrate notice: {e}]")
        speak("I could not read the mouse position. Please install pyautogui.")


# ---------------- Maps ----------------
def geocode(place):
    try:
        from geopy.geocoders import Nominatim
        g = Nominatim(user_agent="luna_assistant_app", timeout=8)
        loc = g.geocode(place, language="en")
        if loc:
            return {"address": loc.address, "lat": loc.latitude, "lon": loc.longitude}
    except Exception as e:
        print(f"[Geocode notice: {e}]")
    return None


def place_without_ai(place, geo):
    """Free: speak the map address, then the Wikipedia introduction of the place."""
    if geo:
        say_long("According to the map, it is located at " + geo["address"] + ".")
    wiki = wikipedia_summary(place)
    if wiki:
        say_long(wiki[1][:900])
        say_long("That was from Wikipedia.")
    elif not geo:
        speak("I opened Google Maps for you, but I could not find more details.")


def do_locate(place):
    speak(f"Let me find {place} on Google Maps.")
    open_url("https://www.google.com/maps/search/?api=1&query=" + q(place))
    post("state", "thinking")
    geo = geocode(place)
    if not have_ai():
        place_without_ai(place, geo)
        return
    notes, _ = research(f"{place} location history what to know", pages=2)
    facts = ""
    if geo:
        facts = (f"Map lookup result: address is {geo['address']} "
                 f"(latitude {geo['lat']:.4f}, longitude {geo['lon']:.4f}).\n")
    prompt = (f"Tell me about the place '{place}': where exactly it is (area, city, "
              "state, country), what it is famous for, and useful tips for visiting "
              "or reaching it.")
    answer = ai_reply(prompt, facts + notes, max_tokens=900)
    if answer:
        say_long(answer)
    else:
        place_without_ai(place, geo)


def do_directions(destination, origin=None):
    speak(f"Opening directions to {destination}.")
    url = "https://www.google.com/maps/dir/?api=1&destination=" + q(destination)
    if origin:
        url += "&origin=" + q(origin)
    open_url(url)


# ---------------- small tools ----------------
def do_calculator():
    speak("Opening the Calculator.")
    subprocess.Popen("calc", shell=True)


def do_notepad():
    speak("Opening Notepad.")
    subprocess.Popen("notepad", shell=True)


def do_time():
    speak(f"The current time is {datetime.datetime.now().strftime('%I:%M %p')}.")


def do_date():
    speak(f"Today is {datetime.datetime.now().strftime('%A, %d %B %Y')}.")


def do_shutdown():
    """Shuts down the computer - always confirmed first, and cancellable."""
    answer = ask("Are you sure you want to shut down the computer? Say yes to confirm.")
    if not answer or not has(answer, "yes", "yeah", "confirm", "sure", "do it"):
        speak("Okay, cancelling. Your computer will stay on.")
        return
    speak("Shutting down in 10 seconds. Say cancel now to stop it.")
    try:
        subprocess.run(["shutdown", "/s", "/t", "10"], shell=True)
    except Exception as e:
        speak("I could not reach the shutdown command on this system.")
        print(f"[Shutdown error: {e}]")
        return
    cancel = listen(wait_seconds=8)
    if cancel and has(cancel, "cancel", "stop", "abort", "no"):
        try:
            subprocess.run(["shutdown", "/a"], shell=True)
            speak("Shutdown cancelled.")
        except Exception as e:
            speak("I could not cancel the shutdown, sorry.")
            print(f"[Shutdown cancel error: {e}]")
    else:
        speak("Goodbye. Powering down now.")
        fx_powerdown()


# ------------------------------------------------------------------
# 6. BRAIN - order matters (specific before general)
# ------------------------------------------------------------------
RESEARCH_STARTS = (
    "tell me about", "tell me", "explain", "what is", "what are", "what's", "what was",
    "what does", "who is", "who was", "who are", "why", "how does", "how do", "how did",
    "how to", "how can", "how much", "how many", "learn about", "teach me",
    "i want to know", "i wanted to know", "i would like to know", "information about",
    "history of", "difference between", "meaning of", "define", "describe",
    "when did", "when was", "latest news", "news about",
)
POLITE_PREFIX = re.compile(r"^(?:please|can you|could you|will you|would you|luna|hey luna|hi luna)[,\s]+")


def handle(command):
    """Returns False when the Luna app should close."""
    c = command.strip()
    while True:                                   # remove wake words / politeness
        stripped = POLITE_PREFIX.sub("", c)
        if stripped == c:
            break
        c = stripped
    if not c:
        speak("Yes, I am listening.")
        return True

    # --- system ---
    if has(c, "shutdown", "shut down", "turn off", "power off") and \
            has(c, "laptop", "computer", "pc", "system"):
        do_shutdown()
        return True
    if has(c, "goodbye", "bye luna", "exit", "shut down", "stop listening", "quit"):
        speak("Goodbye! Shutting down. Talk to you soon.")
        return False

    if has(c, "change key", "add key", "new key", "api key", "change my key"):
        speak("Opening the key box. Please paste your key there.")
        post("askkey")
        return True

    # --- WhatsApp calling / messaging ---
    if has(c, "calibrate") and has(c, "whatsapp"):
        do_calibrate_whatsapp(video=has(c, "video"))
        return True
    m = re.match(r"^(?:make\s+|start\s+|give\s+|do\s+)?(?:a\s+)?"
                 r"(?:(?:whatsapp|video|voice)\s+)*call\b\s*(?:to\s+)?(.*)$", c)
    if m:
        name = re.sub(r"\b(?:on whatsapp|whatsapp|please)\b", "", m.group(1)).strip()
        if not name:
            name = ask("Who do you want to call?")
        if name and (find_contact(name) or has(c, "whatsapp")):
            do_whatsapp_call(name, video=has(c, "video"))
            return True
        if name and not find_contact(name):
            pass                                  # not a contact: maybe a normal question
    m = re.match(r"^(?:send\s+)?(?:a\s+)?(?:whatsapp\s+)?message\s+(?:to\s+)?(.+?)\s+"
                 r"(?:saying|that says|say|that)\s+(.+)$", c)
    if m and find_contact(m.group(1)):
        do_whatsapp_message(m.group(1), m.group(2))
        return True

    # --- apps ---
    if has(c, "youtube music", "play music", "play song"):
        do_youtube_music()
    elif has(c, "youtube", "play video"):
        do_youtube()
    elif has(c, "instagram", "insta"):
        do_instagram()
    elif has(c, "visual studio", "vs code", "vscode"):
        do_vscode()
    elif has(c, "whatsapp", "whats app", "send message"):
        do_whatsapp()
    elif has(c, "calculator", "calculater"):
        do_calculator()
    elif has(c, "notepad"):
        do_notepad()
    elif has(c, "what time", "current time", "time is it", "tell me the time",
             "what is the time", "what's the time"):
        do_time()
    elif has(c, "today's date", "the date", "what date", "what day", "which day"):
        do_date()

    # --- Google Maps ---
    elif re.search(r"(?:directions?|route|how (?:to|do i) (?:go|get|reach))\s+"
                   r"(?:from\s+(.+?)\s+)?to\s+(.+)$", c):
        m = re.search(r"(?:directions?|route|how (?:to|do i) (?:go|get|reach))\s+"
                      r"(?:from\s+(.+?)\s+)?to\s+(.+)$", c)
        dest, origin = m.group(2), m.group(1)
        if " from " in dest and not origin:          # "to jaipur from delhi"
            dest, origin = [x.strip() for x in dest.split(" from ", 1)]
        do_directions(dest, origin)
    elif re.match(r"^(?:where is|where's|where are|location of|locate|show location of)\s+(.+)$", c):
        m = re.match(r"^(?:where is|where's|where are|location of|locate|show location of)\s+(.+)$", c)
        do_locate(m.group(1))
    elif re.match(r"^(?:show |find |open )?(?:me )?(.+?) on (?:google )?maps?$", c):
        m = re.match(r"^(?:show |find |open )?(?:me )?(.+?) on (?:google )?maps?$", c)
        do_locate(m.group(1))

    # --- small talk (fast, no internet) ---
    elif has(c, "how are you"):
        speak("I am doing great, thank you for asking. What should I do for you?")
    elif has(c, "your name", "who are you"):
        speak("I am Luna, your personal voice assistant.")
    elif len(c.split()) <= 3 and has(c, "hello", "hi", "hey"):
        speak("Hello! I am Luna. How can I help you?")

    # --- search / learn / write (AI + websites) ---
    elif re.match(r"^(?:search|google)\s+(?:for\s+|about\s+)?(.+)$", c) and \
            not has(c, "on google", "chrome"):
        m = re.match(r"^(?:search|google)\s+(?:for\s+|about\s+)?(.+)$", c)
        explain(m.group(1))
    elif re.match(r"^(?:write|compose|create)\b", c):
        explain(c, creative=True)
    elif any(c.startswith(w) for w in RESEARCH_STARTS):
        explain(c)

    # --- open Google / Chrome ---
    elif has(c, "chrome", "google", "search"):
        do_google()

    # --- everything else: normal conversation ---
    else:
        chat(c)
    return True


def run_assistant():
    fx_powerup()
    speak("System online. Hi, I am Luna. Tell me what you want me to do.")
    if not have_ai():
        print("\n[AI notice: no API key. Luna will only read web results. Restart and "
              "paste a free Gemini key (aistudio.google.com) in the box.]\n")
    idle_rounds = 0
    while True:
        command = listen()
        if not command:
            idle_rounds += 1
            if idle_rounds == 5:
                speak("I am still here. Say a command whenever you are ready.")
                idle_rounds = 0
            continue
        idle_rounds = 0
        if not handle(command):
            break


def assistant_thread():
    try:
        import comtypes
        comtypes.CoInitialize()          # Windows voice needs this in a thread
    except Exception:
        pass
    try:
        run_assistant()
    except Exception as e:
        print(f"[Assistant error: {e}]")
        post("chat", "System", f"Error: {e}")
    post("quit")


# ------------------------------------------------------------------
# 7. THE VIDEO BACKGROUND - decoded once (in the background), looped forever
# ------------------------------------------------------------------
def find_video():
    path = os.path.join(BASE_DIR, VIDEO_NAME)
    if os.path.exists(path):
        return path
    for name in sorted(os.listdir(BASE_DIR)):
        if name.lower().endswith((".mp4", ".mov", ".avi", ".mkv", ".webm")):
            return os.path.join(BASE_DIR, name)
    return None


class VideoLoop:
    """Decodes the video into memory and hands out frames by wall-clock time."""

    def __init__(self):
        self.frames = []
        self.fps = float(VIDEO_FPS)
        self.ok = False
        self.loading = True
        self.error = ""
        self.masks = {}

    def load(self):
        try:
            self._load()
        except Exception as e:
            self.error = str(e)
            print(f"[Video notice: could not load the video: {e}]")
        self.loading = False

    def _load(self):
        if cv2 is None:
            self.error = "OpenCV missing: run  python -m pip install opencv-python"
            return
        path = find_video()
        if not path:
            self.error = f"No video found. Put {VIDEO_NAME} next to this file."
            print(f"[Video notice: looked for a video in {BASE_DIR} - none found]")
            return
        print(f"[Video: loading {path}]")
        cap = cv2.VideoCapture(path)
        if not cap.isOpened():
            self.error = "The video file could not be opened."
            return
        src_fps = cap.get(cv2.CAP_PROP_FPS) or 30.0
        stride = max(1, round(src_fps / VIDEO_FPS))
        self.fps = src_fps / stride
        limit = int(MAX_VIDEO_SECONDS * self.fps)

        idx = 0
        frames = []
        while len(frames) < limit:
            ok, frame = cap.read()
            if not ok:
                break
            if idx % stride == 0:
                h, w = frame.shape[:2]
                scale = BG_WORK_WIDTH / w
                frame = cv2.resize(frame, (BG_WORK_WIDTH, max(1, int(h * scale))),
                                   interpolation=cv2.INTER_AREA)
                frames.append(Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)))
            idx += 1
        cap.release()
        if frames:
            self.frames = frames
            self.ok = True
            print(f"[Video: ready - {len(frames)} frames looping]")
        else:
            self.error = "The video had no readable frames."

    def frame_at(self, t):
        return self.frames[int(t * self.fps) % len(self.frames)]

    def core_at(self, t, diam):
        rgb = self.frame_at(t)
        side = min(rgb.size)
        x0, y0 = (rgb.size[0] - side) // 2, (rgb.size[1] - side) // 2
        zside = int(side * 0.75)
        zx0, zy0 = x0 + (side - zside) // 2, y0 + (side - zside) // 2
        return rgb.crop((zx0, zy0, zx0 + zside, zy0 + zside)).resize(
            (diam, diam), BILINEAR).convert("RGBA")

    def mask_for(self, diam):
        m = self.masks.get(diam)
        if m is None:
            m = Image.new("L", (diam, diam), 0)
            pad = max(1, int(diam * 0.02))
            ImageDraw.Draw(m).ellipse((pad, pad, diam - pad, diam - pad), fill=255)
            m = m.filter(ImageFilter.GaussianBlur(2))
            self.masks[diam] = m
        return m


# ------------------------------------------------------------------
# 8. THE WINDOW - full-screen video wallpaper + spinning core + HUD
# ------------------------------------------------------------------
BG = "#02060B"
CYAN, CYAN_HI, CYAN_DIM = "#35E0FF", "#B9F6FF", "#1D7C93"
STATE_COLOR = {"speaking": "#35E0FF", "listening": "#5CFFB0",
               "thinking": "#FFC857", "idle": "#4A9DB5"}
STATE_LABEL = {"speaking": "SPEAKING", "listening": "LISTENING",
               "thinking": "PROCESSING", "idle": "ONLINE"}


class LunaApp:
    NPART = 60

    def __init__(self, root):
        self.root = root
        self.closing = False
        self.state = "idle"
        self.vis = 0.0
        self.spin = 0.0
        self.t0 = time.perf_counter()
        self.mx = self.my = 0.0
        self.tmx = self.tmy = 0.0
        self.w = self.h = 0
        self.cx = self.cy = 0
        self.core_diam = 200
        self.subtitles = SHOW_SUBTITLES
        self.caption = ("", "")
        self.layout_job = None
        self.bg_photo = self.core_photo = None
        self.bg_item = self.core_item = None
        self.part_items = []
        self.parts = [dict(u=random.random(), v=random.random(),
                           depth=random.uniform(0.2, 1.0), size=random.uniform(0.8, 2.6),
                           speed=random.uniform(0.0015, 0.006), phase=random.uniform(0, 6.28),
                           color=random.choice(["#9DEBFF", "#35E0FF", "#7FB7C8", "#D8F8FF"]))
                      for _ in range(self.NPART)]

        self.video = VideoLoop()
        threading.Thread(target=self.video.load, daemon=True).start()

        root.title("Luna - Voice Assistant")
        root.geometry("1280x720")
        root.minsize(760, 430)
        root.configure(bg=BG)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.canvas = tk.Canvas(root, bg=BG, highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", self.on_configure)
        self.canvas.bind("<Motion>", self.on_motion)
        self.canvas.bind("<Double-Button-1>", lambda e: self.toggle_fullscreen())
        root.bind("<F11>", lambda e: self.toggle_fullscreen())
        root.bind("<Escape>", lambda e: root.attributes("-fullscreen", False))
        root.bind("<c>", lambda e: self.toggle_captions())
        root.bind("<C>", lambda e: self.toggle_captions())
        root.bind("<k>", lambda e: ask_for_key(self.root, force=True))
        root.bind("<K>", lambda e: ask_for_key(self.root, force=True))
        root.bind("<s>", lambda e: self.stop_reading())
        root.bind("<S>", lambda e: self.stop_reading())
        if START_FULLSCREEN:
            root.attributes("-fullscreen", True)

        root.lift()
        root.attributes("-topmost", True)
        root.after(800, lambda: root.attributes("-topmost", False))
        root.after(80, self.layout)
        self.animate()
        self.poll()

    # ---------- window events ----------
    def on_configure(self, event):
        if self.layout_job is not None:
            self.root.after_cancel(self.layout_job)
        self.layout_job = self.root.after(120, self.layout)

    def on_motion(self, event):
        if self.w:
            self.tmx = (event.x / self.w - 0.5) * 2
            self.tmy = (event.y / self.h - 0.5) * 2

    def toggle_fullscreen(self):
        self.root.attributes("-fullscreen", not self.root.attributes("-fullscreen"))

    def toggle_captions(self):
        self.subtitles = not self.subtitles

    def stop_reading(self):
        speech_stop.set()
        try:
            sd.stop()
        except Exception:
            pass

    def on_close(self):
        self.closing = True
        try:
            sd.stop()
        except Exception:
            pass
        fx_powerdown()
        self.root.destroy()

    # ---------- layout (on start and whenever the window is resized) ----------
    def layout(self):
        self.layout_job = None
        if self.closing:
            return
        c = self.canvas
        w, h = c.winfo_width(), c.winfo_height()
        if w < 100 or h < 100:
            self.root.after(100, self.layout)
            return
        self.w, self.h = w, h
        c.delete("static")

        self.bg_item = c.create_image(0, 0, anchor="nw", tags=("static", "bg"))
        self.core_diam = int(min(w, h) * 0.42)
        self.cx, self.cy = w // 2, h // 2
        r = self.core_diam / 2
        c.create_oval(self.cx - r, self.cy - r, self.cx + r, self.cy + r,
                      fill="#03121B", outline=CYAN_DIM, width=2, tags="static")
        self.core_item = c.create_image(self.cx, self.cy, tags=("static", "core"))
        self.build_hud()

    def build_hud(self):
        c, w, h = self.canvas, self.w, self.h
        m = 14
        L = max(30, int(min(w, h) * 0.06))
        for sx, sy in ((1, 1), (-1, 1), (1, -1), (-1, -1)):
            x = m if sx > 0 else w - m
            y = m if sy > 0 else h - m
            c.create_line(x, y + sy * L, x, y, x + sx * L, y, fill=CYAN, width=2, tags="static")
            c.create_line(x + sx * 6, y + sy * L * 0.55, x + sx * 6, y + sy * 6,
                          x + sx * L * 0.55, y + sy * 6, fill=CYAN_DIM, width=1, tags="static")
        self.t_title = c.create_text(m + 12, m + 12, anchor="nw", fill=CYAN,
                                     text="LUNA AI  //  ACTIVE INTERFACE",
                                     font=("Consolas", 11, "bold"), tags="static")
        self.t_clock = c.create_text(m + 12, m + 34, anchor="nw", fill="#7FD9EA", text="",
                                     font=("Consolas", 10), tags="static")
        self.t_status = c.create_text(w - m - 12, m + 12, anchor="ne", fill=CYAN, text="",
                                      font=("Consolas", 12, "bold"), tags="static")
        self.t_hint = c.create_text(w / 2, m + 60, fill="#FFC857", text="",
                                    font=("Consolas", 11, "bold"), tags="static")
        self.cap_bar = c.create_rectangle(w * 0.12, h - 104, w * 0.88, h - 24, fill="#031824",
                                          stipple="gray50", outline=CYAN_DIM, state="hidden",
                                          tags="static")
        self.cap_text = c.create_text(w / 2, h - 64, width=w * 0.74, fill="#E8FBFF", text="",
                                      font=("Segoe UI", 13), state="hidden", tags="static")
        self.part_items = [
            c.create_oval(0, 0, 1, 1, fill=p["color"], outline="", tags="static")
            for p in self.parts]

    # ---------- events from the assistant thread ----------
    def poll(self):
        if self.closing:
            return
        try:
            while True:
                kind, args = ui_q.get_nowait()
                if kind == "chat":
                    self.caption = (args[0], args[1])
                elif kind == "state":
                    self.state = args[0]
                    if self.state == "speaking" and self.root.state() == "iconic":
                        self.root.deiconify()
                elif kind == "askkey":
                    self.root.after(300, lambda: ask_for_key(self.root, force=True))
                elif kind == "quit":
                    self.closing = True
                    self.root.after(400, self.root.destroy)
                    return
        except queue.Empty:
            pass
        self.root.after(50, self.poll)

    # ---------- loudness ----------
    def current_level(self, now, t):
        clip = speech["clip"]
        if self.state == "speaking":
            if clip is not None:
                env, hop, start = clip
                i = int((now - start) / hop)
                return float(env[i]) if 0 <= i < len(env) else 0.0
            return max(0.0, 0.5 + 0.5 * math.sin(t * 11) * random.uniform(0.5, 1.0))
        if self.state == "listening":
            return 0.22 + 0.08 * math.sin(t * 3)
        if self.state == "thinking":
            return 0.12
        return 0.03

    # ---------- main frame ----------
    def animate(self):
        if self.closing:
            return
        t_start = time.perf_counter()
        try:
            self.frame(t_start)
        except Exception as e:
            print(f"[Animation notice: {e}]")
        ms = int((time.perf_counter() - t_start) * 1000)
        self.root.after(max(5, 40 - ms), self.animate)

    def frame(self, now):
        if not self.w:
            return
        t = now - self.t0
        level = self.current_level(now, t)
        self.vis += (level - self.vis) * 0.35
        self.spin += (1 / 25) * (18 + 340 * self.vis)     # faster spin while she talks
        self.mx += (self.tmx - self.mx) * 0.08
        self.my += (self.tmy - self.my) * 0.08

        if self.video.ok:
            bg = self.video.frame_at(t)
            bw, bh = bg.size
            scale = max(self.w / bw, self.h / bh)          # cover-fit
            resized = bg.resize((int(bw * scale) + 1, int(bh * scale) + 1), BILINEAR)
            rw, rh = resized.size
            x0, y0 = (rw - self.w) // 2, (rh - self.h) // 2
            cropped = resized.crop((x0, y0, x0 + self.w, y0 + self.h))
            self.bg_photo = ImageTk.PhotoImage(cropped)
            self.canvas.itemconfigure(self.bg_item, image=self.bg_photo)

            pulse = 1.0 + 0.05 * self.vis * (1 + math.sin(t * 6))
            diam = max(20, int(self.core_diam * pulse))
            core = self.video.core_at(t, diam).rotate(self.spin % 360, resample=BILINEAR)
            core.putalpha(self.video.mask_for(diam))
            self.core_photo = ImageTk.PhotoImage(core)
            self.canvas.itemconfigure(self.core_item, image=self.core_photo)

        self.draw_under(t)
        self.draw_over(t)

    # ---------- futuristic HUD ----------
    def draw_under(self, t):
        c = self.canvas
        c.delete("under")
        amp = 0.22 + 0.78 * self.vis
        color = STATE_COLOR.get(self.state, CYAN)
        cx, cy = self.cx, self.cy
        R = self.core_diam / 2

        for i in range(72):
            a = math.radians(i * 5)
            long_tick = i % 6 == 0
            r0, r1 = R + 12, R + (20 if long_tick else 15)
            c.create_line(cx + r0 * math.cos(a), cy + r0 * math.sin(a),
                          cx + r1 * math.cos(a), cy + r1 * math.sin(a),
                          fill=blend(color, BG, 0.35 if long_tick else 0.6),
                          width=2 if long_tick else 1, tags="under")

        r = R + 28
        for j in range(3):
            c.create_arc(cx - r, cy - r, cx + r, cy + r, start=(self.spin * 1.4 + j * 120) % 360,
                         extent=70, style="arc", outline=color, width=3, tags="under")
        r2 = R + 36
        for j in range(4):
            c.create_arc(cx - r2, cy - r2, cx + r2, cy + r2,
                         start=(-self.spin * 2.0 + j * 90) % 360, extent=22, style="arc",
                         outline=blend(color, BG, 0.4), width=2, tags="under")

        n = 80
        r0 = R + 46
        for i in range(n):
            a = math.radians(i * 360 / n - 90)
            wave = 0.5 + 0.5 * abs(math.sin(t * 4 + i * 0.55))
            length = 2 + amp * 30 * wave * random.uniform(0.6, 1.0)
            c.create_line(cx + r0 * math.cos(a), cy + r0 * math.sin(a),
                          cx + (r0 + length) * math.cos(a), cy + (r0 + length) * math.sin(a),
                          fill=color, width=3, capstyle="round", tags="under")

        bars, spacing = 34, max(6, int(self.w * 0.011))
        x0 = cx - (bars - 1) * spacing / 2
        y = self.h - 135
        for i in range(bars):
            wave = 0.5 + 0.5 * abs(math.sin(t * 5 + i * 0.6))
            hgt = 3 + amp * random.uniform(0.4, 1.0) * 26 * wave \
                + 1.5 * (math.sin(t * 2 + i) + 1) * (1 - amp)
            x = x0 + i * spacing
            c.create_line(x, y - hgt, x, y + hgt, width=5, capstyle="round",
                          fill=blend(color, BG, 0.1 + 0.4 * abs(i - bars / 2) / (bars / 2)),
                          tags="under")

    def draw_over(self, t):
        c = self.canvas
        w, h = self.w, self.h
        for p, item in zip(self.parts, self.part_items):
            p["v"] -= p["speed"]
            if p["v"] < -0.02:
                p["v"] = 1.02
                p["u"] = random.random()
            x = (p["u"] + 0.01 * math.sin(t * 0.5 + p["phase"])) * w + self.mx * p["depth"] * 22
            y = p["v"] * h + self.my * p["depth"] * 12
            s = p["size"] * (0.7 + 0.3 * math.sin(t * 3 + p["phase"]))
            c.coords(item, x - s, y - s, x + s, y + s)

        color = STATE_COLOR.get(self.state, CYAN)
        c.itemconfigure(self.t_status, text="\u25CF " + STATE_LABEL.get(self.state, ""),
                        fill=color)
        c.itemconfigure(self.t_clock, text=time.strftime("%H:%M:%S   %d %b %Y").upper())

        if self.video.loading:
            hint = "LOADING VIDEO WALLPAPER..."
        elif not self.video.ok:
            hint = self.video.error
        else:
            hint = ""
        c.itemconfigure(self.t_hint, text=hint)

        who, text = self.caption
        show = "normal" if (self.subtitles and text) else "hidden"
        c.itemconfigure(self.cap_bar, state=show)
        c.itemconfigure(self.cap_text, state=show, text=text,
                        fill="#E8FBFF" if who == ASSISTANT_NAME else "#9BFFD0")


# ------------------------------------------------------------------
def ask_for_key(parent=None, force=False):
    """Show a box to paste an AI key. It is remembered in luna_config.json."""
    if have_ai() and not force:
        return
    try:
        from tkinter import simpledialog
        box = None
        if parent is None:
            box = tk.Tk()
            box.withdraw()
            parent = box
        key = simpledialog.askstring(
            "Luna needs an AI key",
            "Paste your API key to unlock detailed answers.\n\n"
            "FREE:  aistudio.google.com -> Get API key   (starts with AIza)\n"
            "Or an Anthropic key (starts with sk-ant)\n\n"
            "Leave empty to cancel.", parent=parent)
        if box is not None:
            box.destroy()
    except Exception as e:
        print(f"[Key box notice: {e}]")
        return
    key = (key or "").strip().strip('"').strip("'")
    if not key:
        return
    if key.startswith("sk-ant"):
        name, env = "anthropic_key", "ANTHROPIC_API_KEY"
    elif key.startswith("AIza"):
        name, env = "gemini_key", "GEMINI_API_KEY"
    elif key.startswith("sk-"):
        name, env = "openai_key", "OPENAI_API_KEY"
    else:
        print("[Key notice: that does not look like an Anthropic, Gemini or OpenAI key]")
        return
    CONFIG[name] = key
    save_config(CONFIG)
    os.environ[env] = key
    SKIP["claude"] = SKIP["claude"] and env != "ANTHROPIC_API_KEY"
    SKIP["openai"] = SKIP["openai"] and env != "OPENAI_API_KEY"
    last_ai_error["msg"] = ""
    print("[Key saved. Luna will remember it next time.]")


def main():
    try:                                   # sharp picture on high-DPI screens
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    ask_for_key()
    root = tk.Tk()
    LunaApp(root)
    threading.Thread(target=assistant_thread, daemon=True).start()
    root.mainloop()


if __name__ == "__main__":
    main()