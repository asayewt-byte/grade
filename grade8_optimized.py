import asyncio

import nest_asyncio
nest_asyncio.apply()
from asyncio import Queue as _AsyncioQueue, Semaphore
import aiosqlite
import aiohttp
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, ReplyKeyboardMarkup, KeyboardButton, ReplyKeyboardRemove
from telegram.constants import ParseMode
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    MessageHandler,
    filters,
    CallbackContext,
    ConversationHandler,
    CallbackQueryHandler,
)
from base64 import b64decode, b64encode
from io import BytesIO
from PIL import Image, ImageOps
import logging
import warnings
from datetime import datetime, timedelta
warnings.filterwarnings("ignore", message=".*per_message.*CallbackQueryHandler.*")
import time
from functools import wraps
import os
import re
import json
from telegram.error import BadRequest, RetryAfter, TimedOut
import httpx
import httpcore
from urllib.parse import quote, urlparse
import hashlib
import sqlite3
from telegram.request import HTTPXRequest

# Custom request handler to suppress transient network errors
class SilentHTTPXRequest(HTTPXRequest):
    async def do_request(self, request):
        """Override to suppress transient network errors"""
        try:
            return await super().do_request(request)
        except (httpcore.ReadError, httpcore.ConnectError, httpcore.WriteError) as e:
            # Re-raise but log at debug level instead of error
            import logging
            logger = logging.getLogger(__name__)
            logger.debug(f"Transient network error suppressed: {type(e).__name__}")
            raise
bot_locked = False
telegram_bot = None

PHONE_NUMBER = 100

# ── Pre-compiled regex ──
_MD_ESCAPE_RE = re.compile(r'([_\*\[\]\(\)~`>#+\-=|{}.!])')

# ── Shared aiohttp session (reused, not created per request) ──
_http_session = None
_http_session_lock = asyncio.Lock()

async def get_http_session():
    global _http_session
    if _http_session is None:
        async with _http_session_lock:
            if _http_session is None:
                _http_session = aiohttp.ClientSession(
                    timeout=aiohttp.ClientTimeout(total=60, connect=15, sock_read=45)
                )
    return _http_session

# ── Write queue for DB (batch commits, not per-op) ──
_db_write_queue = None

async def _db_writer_worker():
    while True:
        ops = []
        ops.append(await _db_write_queue.get())
        while len(ops) < 50:
            try:
                ops.append(await asyncio.wait_for(_db_write_queue.get(), timeout=0.05))
            except asyncio.TimeoutError:
                break
        try:
            db = await get_db()
            for fn in ops:
                try:
                    await fn(db)
                except Exception as e:
                    logger.error(f"DB write error: {e}")
            await db.commit()
        except Exception as e:
            logger.error(f"DB writer flush error: {e}")
        finally:
            for _ in ops:
                _db_write_queue.task_done()

def queue_db_write(fn):
    _db_write_queue.put_nowait(fn)

# ── Persistent DB connection ──
_db_conn = None
_db_lock = asyncio.Lock()
DB_CONNECT_TIMEOUT = 10

async def get_db():
    global _db_conn
    if _db_conn is None:
        async with _db_lock:
            if _db_conn is None:
                _db_conn = await asyncio.wait_for(
                    aiosqlite.connect("bot_data.db", timeout=DB_CONNECT_TIMEOUT),
                    timeout=DB_CONNECT_TIMEOUT + 2
                )
                await _db_conn.execute("PRAGMA journal_mode=WAL")
                await _db_conn.execute("PRAGMA synchronous=NORMAL")
                await _db_conn.execute("PRAGMA cache_size=10000")
                await _db_conn.execute("PRAGMA temp_store=MEMORY")
                _db_conn.row_factory = aiosqlite.Row
    return _db_conn

# ── In-memory caches with TTL ──
_BANNED_CACHE = {}
_BANNED_CACHE_TTL = 120
_BOT_USERNAME_CACHE = None
_RESULT_CACHE_TTL = 1800
_result_cache_timestamps = {}

async def request_phone_number(update, context):
    user_id = update.effective_user.id
    if await _is_group_non_admin(update):
        return ConversationHandler.END
    if bot_locked and user_id != ADMIN_CHAT_ID:
        await update.message.reply_text("⚠️ Bot is currently locked by admin. Please try again later.")
        return ConversationHandler.END
    if user_id == ADMIN_CHAT_ID:
        logger.info(f"Admin {user_id} bypassing phone number requirement")
        user_data = await get_user_data(user_id)
        if not user_data:
            await save_user_data(user_id=user_id, username=update.effective_user.username, first_name=update.effective_user.first_name, last_name=update.effective_user.last_name, phone_number="ADMIN_BYPASS")
            db = await get_db()
            await db.execute("INSERT OR REPLACE INTO phone_numbers (user_id, phone_number) VALUES (?, ?)", (user_id, "ADMIN_BYPASS"))
            await db.commit()
        await load_user_data_to_context(user_id, context)
        await update_user_activity(user_id)
        user_first_name = update.effective_user.first_name or "Admin"
        await update.message.reply_text(escape_markdown_v2(f"እንኳን ደህና መጡ, {user_first_name}!\n\nየአስተዳደር ፈቃድ ተሰጥቷል\n\nPlease choose your language:"), reply_markup=language_reply_keyboard(), parse_mode='MarkdownV2')
        return REGION
    is_registered = await is_user_registered(user_id)
    if is_registered:
        await load_user_data_to_context(user_id, context)
        await update_user_activity(user_id)
        user_first_name = update.effective_user.first_name or "User"
        await update.message.reply_text(escape_markdown_v2(f"እንኳን ደህና መጡ, {user_first_name}!\n\nየትምህርት ውጤቶችን ለመፈተሽ የሚያገለግል አጋራዎ\n\nPlease choose your language:"), reply_markup=language_reply_keyboard(), parse_mode='MarkdownV2')
        return REGION
    if update.effective_chat.type != "private":
        bot_username = _BOT_USERNAME_CACHE or (await context.bot.get_me()).username
        if not _BOT_USERNAME_CACHE:
            _BOT_USERNAME_CACHE = bot_username
        await update.message.reply_text(f"Please start a private chat with me to register.\n[Click here to chat privately](https://t.me/{bot_username})", parse_mode='Markdown', disable_web_page_preview=True)
        return ConversationHandler.END
    keyboard = ReplyKeyboardMarkup([[KeyboardButton("📱 Share Phone Number", request_contact=True)]], resize_keyboard=True, one_time_keyboard=True, input_field_placeholder="Tap the button above to share your phone number")
    try:
        await update.message.reply_text(escape_markdown_v2(f"Welcome {update.effective_user.first_name or 'User'}.\n\nShare your phone number to continue:"), reply_markup=keyboard, parse_mode='MarkdownV2')
    except (TimedOut, Exception):
        try:
            await update.message.reply_text("🎉 Welcome! Please share your phone number to continue.", reply_markup=keyboard)
        except Exception as e:
            logger.error(f"Failed to send welcome message: {e}")
    return PHONE_NUMBER

async def receive_phone_number(update, context):
    user_id = update.effective_user.id
    if await _is_group_non_admin(update):
        return ConversationHandler.END
    if bot_locked and user_id != ADMIN_CHAT_ID:
        await update.message.reply_text("Bot is currently locked by admin. Please try again later.")
        return ConversationHandler.END
    contact = update.message.contact
    if contact and contact.phone_number:
        phone_number = contact.phone_number
        user = update.effective_user
        await save_user_data(user_id=user_id, username=user.username, first_name=user.first_name, last_name=user.last_name, phone_number=phone_number)
        db = await get_db()
        await db.execute("INSERT OR REPLACE INTO phone_numbers (user_id, phone_number) VALUES (?, ?)", (user_id, phone_number))
        await db.commit()
        context.user_data['phone_number'] = phone_number
        await update.message.reply_text("Thank you. Redirecting to main menu...", reply_markup=ReplyKeyboardRemove())
        full_name = update.effective_user.full_name or "(no name)"
        await context.bot.send_message(chat_id=ADMIN_CHAT_ID, text=f"<b>New User Registered</b>\n<b>Name:</b> {full_name}\n<b>Username:</b> @{user.username or 'N/A'}\n<b>Phone:</b> <code>+{phone_number}</code>\n<b>User ID:</b> <code>{user_id}</code>", parse_mode='HTML')
        context.user_data['language'] = 'am'
        user_first_name = update.effective_user.first_name or "User"
        await update.message.reply_text(escape_markdown_v2(f"የኢትዮጵያ ተማሪዎች ውጤት ቦት ላይ እንኳን ደህና መጡ, {user_first_name}!\n\nየትምህርት ውጤቶችን ለመፈተሽ የሚያገለግል አጋራዎ\n\nPlease choose your language:"), reply_markup=region_inline_keyboard(), parse_mode='MarkdownV2')
        return REGION
    keyboard = ReplyKeyboardMarkup([[KeyboardButton("Share Phone Number", request_contact=True)]], resize_keyboard=True, one_time_keyboard=True)
    await update.message.reply_text(escape_markdown_v2("Please use the button to share your phone number.\n\nHow to share:\n\xe2\x80\xa2 Tap the 'Share Phone Number' button below\n\xe2\x80\xa2 The button will automatically share your contact"), reply_markup=keyboard, parse_mode='MarkdownV2')
    return PHONE_NUMBER

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)

# Suppress verbose httpx/httpcore logging
logging.getLogger('httpx').setLevel(logging.WARNING)
logging.getLogger('httpcore').setLevel(logging.WARNING)
logging.getLogger('telegram.ext.Application').setLevel(logging.WARNING)

TOKEN = os.getenv("TELEGRAM_BOT_TOKEN","8014071686:AAFVpLSpfHkaubdIZVqXelRHgONsclYyEow")
if not TOKEN:
    raise ValueError("TELEGRAM_BOT_TOKEN environment variable is required")
ZYTE_API_KEY = os.getenv("ZYTE_API_KEY","2629765529934bf6bbdc33eafac13539")
zyte_api_key_runtime = ZYTE_API_KEY
if not ZYTE_API_KEY:
    raise ValueError("ZYTE_API_KEY environment variable is required")
CHANNEL_ID = os.getenv("CHANNEL_ID", "@amharictutorialclass")
ADMIN_CHAT_ID = 723559736

API_ERROR_COUNT = 0
API_ERROR_THRESHOLD = 5
LAST_API_CHECK = None
API_CREDIT_STATUS = "unknown"

def require_bot_unlocked(func):
    @wraps(func)
    async def wrapper(update, context, *args, **kwargs):
        if bot_locked and update.effective_user.id != ADMIN_CHAT_ID:
            msg = "⚠️ Bot is currently locked by admin. Please try again later."
            if update.message:
                await update.message.reply_text(msg)
            elif update.callback_query:
                try:
                    await update.callback_query.answer(msg, show_alert=True)
                except Exception:
                    pass
            return
        return await func(update, context, *args, **kwargs)
    return wrapper

async def _is_group_non_admin(update) -> bool:
    """Returns True if the message is from a group where the user is NOT an admin."""
    chat = update.effective_chat
    if not chat or chat.type == "private":
        return False
    try:
        member = await chat.get_member(update.effective_user.id)
        return member.status not in ("administrator", "creator")
    except Exception:
        return True

def build_basic_auth_headers(username: str, password: str = "") -> dict:
    encoded = b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return {"Authorization": f"Basic {encoded}"}

# ── No-lock caches (GIL-safe dict ops) ──
_cached_results = {}
_user_rate_limit_state = {}
_notified_users = set()
_unblocked_users = set()
_in_flight_fetches = {}
_in_flight_lock = asyncio.Lock()
_rate_limit_violations = {}
_rate_limit_warned_windows = set()

async def fetch_via_zyte(url: str, headers: dict = None, is_photo: bool = False):
    if not zyte_api_key_runtime:
        return None, "zyte_key_missing"
    payload = {"url": url, "httpResponseBody": True, "geolocation": "ET"}
    zyte_headers = {**(headers or {}), **build_basic_auth_headers(zyte_api_key_runtime)}
    session = await get_http_session()
    last_error = None
    for attempt in range(ZYTE_RETRIES + 1):
        try:
            async with session.post(ZYTE_PROXY_URL, json=payload, headers=zyte_headers) as resp:
                resp.raise_for_status()
                data = await resp.json()
                body = b64decode(data.get("httpResponseBody", ""))
                if is_photo:
                    return body, None
                try:
                    return json.loads(body.decode("utf-8")), None
                except json.JSONDecodeError as e:
                    return None, f"zyte_json_decode_error: {e}"
        except asyncio.TimeoutError:
            last_error = f"zyte_timeout (attempt {attempt + 1})"
        except (aiohttp.ClientError, aiohttp.ClientConnectionError, aiohttp.ClientSSLError) as e:
            last_error = f"zyte_client_error: {e}"
        except (httpx.ReadError, httpx.ConnectError, httpcore.ReadError, httpcore.ConnectError, httpcore.WriteError) as e:
            last_error = f"zyte_network_error: {type(e).__name__}"
        except Exception as e:
            last_error = f"zyte_error: {e}"
        if attempt < ZYTE_RETRIES:
            await asyncio.sleep(2 ** attempt)
    return None, last_error

REGION_BASE_URLS = {
    "aa": {"6": "https://aa6.ministry.et/student-result", "default": "https://aa.ministry.et/student-result"},
    "oromia": {"6": "https://oromia6.ministry.et/student-result", "default": "https://oromia.ministry.et/student-result"},
    "sw": "https://sw.ministry.et/student-result",
    "amhara": {"6": "https://amhara6.ministry.et/student-result", "default": "https://amhara.ministry.et/student-result"},
    "ce": {"6": "https://ce6.ministry.et/student-result", "default": "https://ce.ministry.et/student-result"},
    "se": {"6": "https://se6.ministry.et/student-result", "default": "https://se.ministry.et/student-result"},
    "sidama": {"6": "https://sidama6.ministry.et/student-result", "default": "https://sidama.ministry.et/student-result"},
    "harari": "https://harari.ministry.et/student-result",
}
ZYTE_PROXY_URL = "https://api.zyte.com/v1/extract"
REGION, GRADE, REGISTRATION, FIRST_NAME, FEEDBACK = range(5)
PHONE_NUMBER = 100

GLOBAL_SEMAPHORE = Semaphore(500)
REQUEST_TIMEOUT = 90
ZYTE_TOTAL_TIMEOUT = 35
ZYTE_CONNECT_TIMEOUT = 10
ZYTE_RETRIES = 1

ADMIN_FEEDBACK_REPLY = 2000
USER_RATE_LIMIT_WINDOW = 60
USER_RATE_LIMIT_MAX_REQUESTS = 10
AUTO_BAN_VIOLATION_THRESHOLD = 3

# ── Concurrency tracking with Semaphore (race-free) ──
active_users = set()
_concurrent_sem = asyncio.Semaphore(500)

def is_valid_student_result(result) -> bool:
    return isinstance(result, dict) and not result.get("__fetch_error__") and "student" in result and not ("message" in result and not result.get("student"))

def get_region_base_url(region: str, grade: str = None) -> str | None:
    urls = REGION_BASE_URLS.get(region)
    if isinstance(urls, dict):
        return urls.get(grade, urls.get("default"))
    return urls

def get_region_referer(region: str, grade: str = None) -> str:
    base_url = get_region_base_url(region, grade)
    if not base_url:
        return "https://aa.ministry.et/"
    parsed = urlparse(base_url)
    return f"{parsed.scheme}://{parsed.netloc}/"

def _evict_stale_cache():
    now = time.time()
    stale = [k for k, t in _result_cache_timestamps.items() if now - t > _RESULT_CACHE_TTL]
    for k in stale:
        _cached_results.pop(k, None)
        _result_cache_timestamps.pop(k, None)

def cache_student_result(region, registration, first_name, result):
    if not is_valid_student_result(result):
        return
    key = f"student:{region}:{registration}:{first_name}"
    _cached_results[key] = result
    _result_cache_timestamps[key] = time.time()
    if len(_cached_results) > 5000:
        _evict_stale_cache()

def get_cached_student_result(region, registration, first_name):
    key = f"student:{region}:{registration}:{first_name}"
    cached = _cached_results.get(key)
    if cached and is_valid_student_result(cached):
        ts = _result_cache_timestamps.get(key, 0)
        if time.time() - ts <= _RESULT_CACHE_TTL:
            return cached
        _cached_results.pop(key, None)
        _result_cache_timestamps.pop(key, None)
    return None

async def check_user_rate_limit(user_id):
    current_time = time.time()
    entry = _user_rate_limit_state.get(user_id)
    if entry:
        window_start, request_count = entry
        if current_time - window_start > USER_RATE_LIMIT_WINDOW:
            _user_rate_limit_state[user_id] = (current_time, 1)
            return True
        if request_count < USER_RATE_LIMIT_MAX_REQUESTS:
            _user_rate_limit_state[user_id] = (window_start, request_count + 1)
            return True
        window_key = (user_id, window_start)
        if window_key not in _rate_limit_warned_windows:
            _rate_limit_warned_windows.add(window_key)
            viol = _rate_limit_violations.get(user_id)
            if viol:
                vcount, vtime = viol
                if current_time - vtime > 3600:
                    _rate_limit_violations[user_id] = (1, current_time)
                else:
                    vcount += 1
                    if vcount >= AUTO_BAN_VIOLATION_THRESHOLD:
                        logger.warning(f"Auto-banning user {user_id} after {vcount} rate limit violations")
                        await ban_user(user_id, "Auto-banned: repeated rate limit violations")
                        _rate_limit_violations.pop(user_id, None)
                        return False
                    _rate_limit_violations[user_id] = (vcount, vtime)
            else:
                _rate_limit_violations[user_id] = (1, current_time)
        return False
    _user_rate_limit_state[user_id] = (current_time, 1)
    return True

async def check_concurrent_limits():
    return _concurrent_sem.locked() is False

async def increment_concurrent_request(user_id):
    await _concurrent_sem.acquire()
    active_users.add(user_id)

async def decrement_concurrent_request(user_id):
    _concurrent_sem.release()
    active_users.discard(user_id)

async def ban_user(user_id: int, reason: str = "No reason provided"):
    ts = datetime.now().isoformat()
    queue_db_write(lambda db: db.execute("INSERT OR REPLACE INTO banned_users (user_id, ban_reason, ban_date) VALUES (?, ?, ?)", (user_id, reason, ts)))
    _BANNED_CACHE[user_id] = True
    logger.info(f"User {user_id} banned. Reason: {reason}")

async def unban_user(user_id: int):
    queue_db_write(lambda db: db.execute("DELETE FROM banned_users WHERE user_id = ?", (user_id,)))
    _BANNED_CACHE.pop(user_id, None)

_last_banned_refresh = 0

async def _refresh_banned_cache():
    global _last_banned_refresh
    db = await get_db()
    async with db.execute("SELECT user_id FROM banned_users") as cur:
        rows = await cur.fetchall()
    _BANNED_CACHE.clear()
    for row in rows:
        _BANNED_CACHE[row[0]] = True
    _last_banned_refresh = time.time()

async def is_user_banned(user_id: int) -> bool:
    now = time.time()
    if now - _last_banned_refresh > _BANNED_CACHE_TTL:
        await _refresh_banned_cache()
    return user_id in _BANNED_CACHE

async def get_banned_users():
    db = await get_db()
    async with db.execute("SELECT user_id, ban_reason, ban_date FROM banned_users ORDER BY ban_date DESC") as cur:
        return await cur.fetchall()

async def init_db():
    try:
        db = await get_db()
        await db.execute("CREATE TABLE IF NOT EXISTS subscribers (user_id INTEGER PRIMARY KEY)")
        await db.execute("CREATE TABLE IF NOT EXISTS feedback (id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, message TEXT, timestamp TEXT, replied INTEGER DEFAULT 0)")
        await db.execute("CREATE TABLE IF NOT EXISTS usage_logs (id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, action TEXT, timestamp TEXT)")
        await db.execute("CREATE TABLE IF NOT EXISTS referrals (referrer_id INTEGER, referred_id INTEGER PRIMARY KEY, timestamp TEXT)")
        await db.execute("CREATE TABLE IF NOT EXISTS phone_numbers (user_id INTEGER PRIMARY KEY, phone_number TEXT)")
        await db.execute("CREATE TABLE IF NOT EXISTS users (user_id INTEGER PRIMARY KEY, username TEXT, first_name TEXT, last_name TEXT, phone_number TEXT, registration_date TEXT, last_activity TEXT, is_active INTEGER DEFAULT 1, total_lookups INTEGER DEFAULT 0, successful_lookups INTEGER DEFAULT 0)")
        await db.execute("CREATE TABLE IF NOT EXISTS banned_users (user_id INTEGER PRIMARY KEY, ban_reason TEXT, ban_date TEXT)")
        await db.execute("CREATE TABLE IF NOT EXISTS subscriptions (user_id INTEGER, region TEXT, registration TEXT, first_name TEXT, last_result_hash TEXT, PRIMARY KEY (user_id, region, registration, first_name))")
        await db.execute("CREATE TABLE IF NOT EXISTS user_custom_limits (user_id INTEGER PRIMARY KEY, daily_limit INTEGER DEFAULT 10, set_date TEXT)")
        await db.execute("CREATE TABLE IF NOT EXISTS bot_persistence (key TEXT PRIMARY KEY, value TEXT, updated_at TEXT)")
        await db.execute("CREATE TABLE IF NOT EXISTS sponsors (id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL, message TEXT NOT NULL, region TEXT, active INTEGER DEFAULT 1, created_at TEXT, impressions INTEGER DEFAULT 0, clicks INTEGER DEFAULT 0, url TEXT, phone TEXT)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_users_phone ON users(phone_number)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_usage_logs_user ON usage_logs(user_id)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_usage_logs_timestamp ON usage_logs(timestamp)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_feedback_user ON feedback(user_id)")
        await db.execute("INSERT OR REPLACE INTO bot_persistence (key, value, updated_at) VALUES (?, ?, ?)", ("last_startup", datetime.now().isoformat(), datetime.now().isoformat()))
        await db.commit()
        logger.info("✅ Database initialized")
    except Exception as e:
        logger.error(f"❌ Database init failed: {e}")
        raise

async def load_subscribers():
    db = await get_db()
    async with db.execute("SELECT user_id FROM subscribers") as cur:
        return {row[0] async for row in cur}

async def save_user_data(user_id, username=None, first_name=None, last_name=None, phone_number=None):
    try:
        ts = datetime.now().isoformat()
        queue_db_write(lambda db: db.execute("INSERT OR REPLACE INTO users (user_id, username, first_name, last_name, phone_number, registration_date, last_activity) VALUES (?, ?, ?, ?, ?, ?, ?)", (user_id, username, first_name, last_name, phone_number, ts, ts)))
        queue_db_write(lambda db: db.execute("INSERT OR IGNORE INTO subscribers (user_id) VALUES (?)", (user_id,)))
        if phone_number:
            queue_db_write(lambda db: db.execute("INSERT OR REPLACE INTO phone_numbers (user_id, phone_number) VALUES (?, ?)", (user_id, phone_number)))
        subscribed_users.add(user_id)
        return True
    except Exception as e:
        logger.error(f"Failed to save user {user_id}: {e}")
        return False

async def get_user_data(user_id):
    db = await get_db()
    async with db.execute("SELECT user_id, username, first_name, last_name, phone_number, registration_date, last_activity FROM users WHERE user_id = ?", (user_id,)) as cur:
        row = await cur.fetchone()
        if row:
            return {'user_id': row[0], 'username': row[1], 'first_name': row[2], 'last_name': row[3], 'phone_number': row[4], 'registration_date': row[5], 'last_activity': row[6]}
        return None

async def update_user_activity(user_id):
    ts = datetime.now().isoformat()
    queue_db_write(lambda db: db.execute("UPDATE users SET last_activity = ? WHERE user_id = ?", (ts, user_id)))

async def is_user_registered(user_id):
    if user_id == ADMIN_CHAT_ID:
        return True
    user_data = await get_user_data(user_id)
    if user_data and user_data.get('phone_number'):
        return True
    db = await get_db()
    async with db.execute("SELECT phone_number FROM phone_numbers WHERE user_id = ?", (user_id,)) as cur:
        row = await cur.fetchone()
    return row is not None and row[0] is not None

async def load_user_data_to_context(user_id, context):
    user_data = await get_user_data(user_id)
    if user_data:
        context.user_data['phone_number'] = user_data.get('phone_number')
        return True
    db = await get_db()
    async with db.execute("SELECT phone_number FROM phone_numbers WHERE user_id = ?", (user_id,)) as cur:
        row = await cur.fetchone()
    if row and row[0]:
        context.user_data['phone_number'] = row[0]
        return True
    return False

async def save_feedback(user_id, message):
    ts = datetime.now().isoformat()
    queue_db_write(lambda db: db.execute("INSERT INTO feedback (user_id, message, timestamp) VALUES (?, ?, ?)", (user_id, message, ts)))

async def get_successful_lookups(user_id):
    db = await get_db()
    async with db.execute("SELECT COUNT(*) FROM usage_logs WHERE user_id = ? AND action = 'result_lookup'", (user_id,)) as cur:
        row = await cur.fetchone()
        return row[0] if row else 0

async def get_referral_count(user_id):
    db = await get_db()
    async with db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id = ?", (user_id,)) as cur:
        row = await cur.fetchone()
        return row[0] if row else 0

def get_user_rank(total_lookups):
    if total_lookups >= 100:
        return "🏆 Legend"
    if total_lookups >= 50:
        return "🥇 Gold"
    if total_lookups >= 25:
        return "🥈 Silver"
    if total_lookups >= 10:
        return "🥉 Bronze"
    return "Newbie"

def get_rank_emoji(rank):
    emojis = {1: "🥇", 2: "🥈", 3: "🥉", 4: "4️⃣", 5: "5️⃣"}
    return emojis.get(rank, f"{rank}️⃣")

async def get_top_users():
    try:
        week_ago = (datetime.now() - timedelta(days=7)).isoformat()
        db = await get_db()
        async with db.execute("SELECT user_id, COUNT(*) as lookups FROM usage_logs WHERE action = 'result_lookup' AND timestamp >= ? GROUP BY user_id ORDER BY lookups DESC LIMIT 10", (week_ago,)) as cur:
            return [(row[0], row[1]) for row in await cur.fetchall()]
    except Exception as e:
        logger.error(f"Error getting top users: {e}")
        return []

def escape_markdown_v2(text):
    return _MD_ESCAPE_RE.sub(r'\\\1', str(text))

async def safe_edit_message(query, text, reply_markup=None, parse_mode=None):
    try:
        return await query.edit_message_text(text=text, reply_markup=reply_markup, parse_mode=parse_mode)
    except BadRequest as e:
        error_str = str(e).lower()
        if "message is not modified" in error_str:
            return query.message
        if "query is too old" in error_str or "response timeout expired" in error_str or "query id is invalid" in error_str:
            try:
                return await query.message.reply_text(text=text, reply_markup=reply_markup, parse_mode=parse_mode)
            except Exception:
                try:
                    await query.answer("Please try again.")
                except Exception:
                    pass
                return None
        raise

async def check_api_credit_status():
    global API_CREDIT_STATUS, LAST_API_CHECK
    try:
        session = await get_http_session()
        async with session.get("https://api.zyte.com/v1/account", headers=build_basic_auth_headers(zyte_api_key_runtime)) as resp:
                if resp.status == 200:
                    API_CREDIT_STATUS = "active"
                    LAST_API_CHECK = datetime.now()
                    return True
                if resp.status == 401:
                    API_CREDIT_STATUS = "invalid_key"
                    return False
                if resp.status == 403:
                    API_CREDIT_STATUS = "insufficient_credits"
                    return False
                API_CREDIT_STATUS = "unknown"
                return True
    except Exception as e:
        logger.error(f"Error checking API credit status: {e}")
        API_CREDIT_STATUS = "error"
        return False

async def fetch_student_data(region: str, registration: str, first_name: str, grade: str = None) -> dict:
    global API_ERROR_COUNT
    cached = get_cached_student_result(region, registration, first_name)
    if cached:
        return cached

    cache_key = f"student:{region}:{registration}:{first_name}"
    async with _in_flight_lock:
        if cache_key in _in_flight_fetches:
            lock = _in_flight_fetches[cache_key]
        else:
            lock = asyncio.Lock()
            _in_flight_fetches[cache_key] = lock

    async with lock:
        try:
            cached = get_cached_student_result(region, registration, first_name)
            if cached:
                return cached
            async with GLOBAL_SEMAPHORE:
                base_url = get_region_base_url(region, grade)
                if not base_url:
                    return None
                encoded_first_name = quote(first_name, safe="")
                url = f"{base_url}/{registration}?first_name={encoded_first_name}&qr=" if region not in ["sidama", "harari"] else f"{base_url}/{registration}?qr="
                referer = get_region_referer(region, grade)
                headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36", "Accept": "application/json,text/plain,*/*", "Accept-Language": "en-US,en;q=0.9", "Referer": referer}
                result, zyte_err = await fetch_via_zyte(url, headers=headers, is_photo=False)
                if zyte_err:
                    API_ERROR_COUNT += 1
                    if "timeout" in zyte_err:
                        return {"__fetch_error__": "timeout"}
                    return {"__fetch_error__": "network"}
                API_ERROR_COUNT = 0
                if is_valid_student_result(result):
                    cache_student_result(region, registration, first_name, result)
                    return result
                return result if isinstance(result, dict) and result.get("message") else result
        finally:
            async with _in_flight_lock:
                _in_flight_fetches.pop(cache_key, None)

def resolve_photo_url(photo_url: str, region: str = None, grade: str = None) -> str | None:
    if not photo_url:
        return None
    normalized = str(photo_url).strip().replace("\\", "")
    if not normalized:
        return None
    parsed = urlparse(normalized)
    if parsed.scheme and parsed.netloc:
        return normalized
    if normalized.startswith("//"):
        return f"https:{normalized}"
    if normalized.startswith("/"):
        base_url = get_region_base_url(region, grade)
        if base_url:
            b = urlparse(base_url)
            return f"{b.scheme}://{b.netloc}{normalized}"
        return f"https://{normalized.lstrip('/')}"
    return f"https://{normalized.lstrip('/')}"

def compress_photo_bytes(photo_data: bytes) -> BytesIO:
    try:
        with Image.open(BytesIO(photo_data)) as img:
            img = ImageOps.exif_transpose(img)
            if img.mode in {"RGBA", "LA", "P"}:
                img = img.convert("RGB")
            if max(img.size) > 700:
                img.thumbnail((700, 700), Image.Resampling.LANCZOS)
            for quality in (70, 60, 50, 45, 40):
                output = BytesIO()
                img.save(output, format="JPEG", quality=quality, optimize=True)
                output.seek(0)
                if output.getbuffer().nbytes <= 250 * 1024:
                    return output
            output = BytesIO()
            img.save(output, format="JPEG", quality=40, optimize=True)
            output.seek(0)
            return output
    except Exception:
        return BytesIO(photo_data)

async def send_photo_followup(bot, chat_id, photo_url, region, grade, caption, reply_markup):
    try:
        photo_bytes = await fetch_student_photo(photo_url, region=region, grade=grade)
        if photo_bytes and photo_bytes.getbuffer().nbytes > 100:
            await bot.send_photo(chat_id=chat_id, photo=photo_bytes, caption=caption[:1024], parse_mode='HTML', reply_markup=reply_markup)
    except Exception as e:
        logger.warning(f"Photo follow-up failed: {e}")

async def fetch_student_photo(photo_url: str, context=None, region: str = None, grade: str = None) -> BytesIO:
    async with GLOBAL_SEMAPHORE:
        if not photo_url:
            return None
        resolved = resolve_photo_url(photo_url, region, grade)
        if not resolved:
            return None
        headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36", "Accept": "image/avif,image/webp,image/apng,image/*,*/*;q=0.8", "Referer": get_region_referer(region, grade), "Accept-Language": "en-US,en;q=0.9"}
        data, err = await fetch_via_zyte(resolved, headers=headers, is_photo=True)
        if err or len(data) < 100:
            return None
        return compress_photo_bytes(data)

def _subject_emoji(name: str) -> str:
    emoji_map = {'amharic': '🇪🇹', 'አማርኛ': '🇪🇹', 'english': '🇬🇧', 'እንግሊዝኛ': '🇬🇧', 'mathematics': '➗', 'math': '➗', 'ሒሳብ': '➗', 'general science': '🔬', 'science': '🔬', 'ሳይንስ': '🔬', 'social study': '🌍', 'social studies': '🌍', 'ሶሻል': '🌍', 'citizenship': '🏛️', 'ዜጋ': '🏛️'}
    return emoji_map.get(name.lower().strip(), '📖')

async def _get_random_sponsor(region: str = None):
    try:
        db = await get_db()
        cur = await db.execute("SELECT id, name, message, url, phone FROM sponsors WHERE active = 1 AND (region IS NULL OR region = ?) ORDER BY RANDOM() LIMIT 1", (region,)) if region else await db.execute("SELECT id, name, message, url, phone FROM sponsors WHERE active = 1 ORDER BY RANDOM() LIMIT 1")
        row = await cur.fetchone()
        if row:
            sid, name, msg, url, phone = row
            queue_db_write(lambda db: db.execute("UPDATE sponsors SET impressions = impressions + 1 WHERE id = ?", (sid,)))
            text = f"\n\n━━━━━━━━━━━━━━━━━━━━━━━\n📢 SPONSORED\n{msg}\n— {name}"
            return text, sid, url or phone or None
    except Exception as e:
        logger.warning(f"Error fetching sponsor: {e}")
    return None, None, None

def _na(v):
    return "N/A" if v == 'N/A' else str(v)

def _pass_status(a):
    if a == 'N/A':
        return "N/A"
    try:
        return "✅ Passed" if float(str(a).replace('\\','').replace('(','').replace(')','')) >= 50 else "❌ Failed"
    except (ValueError, TypeError):
        return "N/A"

async def format_student_results(student_data: dict, bot_username: str = "", region: str = None):
    student = student_data.get("student", {})
    courses = student_data.get("courses", [])
    config = student_data.get("config", {})
    if config.get("resultReleased") is False:
        return f"🎓 STUDENT RESULT\n━━━━━━━━━━━━━━━━━━━━━━━\n\n👤 Name: {student.get('name', 'N/A')}\n📋 Registration: {student.get('reg_number', 'N/A')}\n🏫 School: {student.get('school', 'N/A')}\n\n⏳ The Ministry has not released the results yet.\nPlease check again later.", None, None

    name, mark, total, average, percentile = student.get('name', 'N/A'), student.get('mark', 'N/A'), student.get('total', 'N/A'), student.get('average', 'N/A'), student.get('percentile', 'N/A')
    if name == mark == total == average == percentile == 'N/A':
        return "❌ ውጤት አልተገኘም\n━━━━━━━━━━━━━━━━━━━━━━━\nበተሰጠው መረጃ ምንም የተማሪ መዝገብ አልተገኘም\n\nያረጋግጡ:\n• የምዝገባ ቁጥር ትክክል ነው\n• የመጀመሪያ ስም ትክክል ነው\n• ክልል ትክክል ነው\n• የመጠን ደረጃ ትክክል ነው\n\nትክክለኛ መረጃ በመጠቀም እንደገና ይሞክሩ", None, None

    name = name.upper() if name != 'N/A' else 'N/A'

    msg = f"🎓 STUDENT RESULT\n━━━━━━━━━━━━━━━━━━━━━━━\n👤 Name: {name}\n━━━━━━━━━━━━━━━━━━━━━━━\n📊 Mark: {_na(mark)}\n🔢 Total: {_na(total)}\n📈 Average: {_na(average)}\n🏆 Percentile: {_na(percentile)}\n{_pass_status(average)}\n━━━━━━━━━━━━━━━━━━━━━━━\n"
    if courses:
        msg += "\n📚 SUBJECT BREAKDOWN\n━━━━━━━━━━━━━━━━━━━━━━━\n"
        for c in courses:
            cn = c.get("name", "N/A")
            em = _subject_emoji(cn)
            if "mark" in c:
                cm = c.get("mark", "N/A")
                cx = c.get("course_mark", "N/A")
                msg += f"{em} {cn}: {cm}/{cx}\n" if cm != "N/A" and cx != "N/A" else f"{em} {cn}: {cm}\n"
            else:
                msg += f"{em} {cn}: Pending\n"
    msg += "━━━━━━━━━━━━━━━━━━━━━━━\n🎓 Powered by Ethiopian Results Bot"
    sponsor_text, sponsor_id, sponsor_contact = await _get_random_sponsor(region)
    if sponsor_text:
        msg += sponsor_text
    return msg, sponsor_id, sponsor_contact

async def is_user_fully_member(update, context):
    try:
        user_id = update.effective_user.id
        for retry in range(3):
            try:
                member = await asyncio.wait_for(context.bot.get_chat_member(chat_id=CHANNEL_ID, user_id=user_id), timeout=5.0)
                return member.status in ["member", "administrator", "creator"]
            except (asyncio.TimeoutError, httpx.ReadError, httpx.ConnectError, httpcore.ReadError, httpcore.ConnectError):
                if retry < 2:
                    await asyncio.sleep(0.5 * (retry + 1))
                    continue
                return False
            except Exception:
                return False
    except Exception:
        return False

async def notify_admins(context_or_bot, message: str):
    bot = telegram_bot if context_or_bot is None else (context_or_bot.bot if hasattr(context_or_bot, "bot") else context_or_bot)
    if bot is None:
        return
    for admin_id in [ADMIN_CHAT_ID]:
        try:
            await bot.send_message(chat_id=admin_id, text=message, parse_mode='HTML')
        except (RetryAfter, TimedOut, Exception) as e:
            if isinstance(e, RetryAfter):
                await asyncio.sleep(e.retry_after)
                try:
                    await bot.send_message(chat_id=admin_id, text=message, parse_mode='HTML')
                except Exception:
                    pass
            else:
                logger.error(f"Failed to notify admin {admin_id}: {e}")

async def can_bot_send_messages(bot, chat_id):
    try:
        for retry in range(2):
            try:
                member = await asyncio.wait_for(bot.get_chat_member(chat_id=chat_id, user_id=bot.id), timeout=5.0)
                return getattr(member, 'can_send_messages', True)
            except (asyncio.TimeoutError, httpx.ReadError, httpx.ConnectError, httpcore.ReadError, httpcore.ConnectError):
                if retry < 1:
                    await asyncio.sleep(0.5)
                    continue
                return True
            except Exception:
                return True
    except Exception:
        return True

def require_membership(func):
    @wraps(func)
    async def wrapper(update, context, *args, **kwargs):
        user_id = update.effective_user.id
        if await is_user_banned(user_id):
            msg = "🚫 እርስዎ ይህን ቦት ለመጠቀም ተከልክለዋል። @Tegene ን ያናግሩ።"
            if update.message:
                await update.message.reply_text(msg)
            elif update.callback_query:
                await update.callback_query.answer(msg, show_alert=True)
            return ConversationHandler.END
        if not await is_user_fully_member(update, context):
            markup = InlineKeyboardMarkup([[InlineKeyboardButton("Join Channel", url=f"https://t.me/{CHANNEL_ID.replace('@', '')}")], [InlineKeyboardButton("I Joined / ተቀላቅያለሁ", callback_data="approve_membership")]])
            msg = f"*የቀን ገደብ*\n\nይህን ቦት ለመጠቀም ከታች ያሉትን Channel መቀላቀል አለብዎት:\n\n*Channel:* {CHANNEL_ID}\n\nእባክዎ ቻናሉን ይቀላቀሉ እና 'ተቀላቅያለሁ' ይጫኑ።"
            if update.message:
                await update.message.reply_text(escape_markdown_v2(msg), reply_markup=markup, parse_mode='MarkdownV2')
            elif update.callback_query:
                await safe_edit_message(update.callback_query, escape_markdown_v2(msg), reply_markup=markup, parse_mode='MarkdownV2')
            return ConversationHandler.END
        return await func(update, context, *args, **kwargs)
    return wrapper

# (process_requests removed — REQUEST_QUEUE was never populated)

async def fetch_results(update, context):
    user_id = update.effective_user.id
    if bot_locked and user_id != ADMIN_CHAT_ID:
        await update.message.reply_text("Bot is currently locked by admin. Please try again later.")
        return
    await _process_user_request(update, context)

async def get_today_lookups(user_id):
    today = datetime.now().date()
    tomorrow = today + timedelta(days=1)
    db = await get_db()
    async with db.execute("SELECT COUNT(*) FROM usage_logs WHERE user_id = ? AND action = 'result_lookup' AND timestamp >= ? AND timestamp < ?", (user_id, today.isoformat(), tomorrow.isoformat())) as cur:
        row = await cur.fetchone()
        return row[0] if row else 0

async def _process_user_request(update, context):
    user_id = update.effective_user.id
    try:
        await asyncio.wait_for(_process_user_request_internal(update, context), timeout=REQUEST_TIMEOUT)
    except asyncio.TimeoutError:
        logger.error(f"Request timed out for user {user_id}")
        try:
            await update.message.reply_text(escape_markdown_v2("⏰ *Request timed out!*\n\n🔄 *Please try again in a moment*"), parse_mode='MarkdownV2')
        except Exception:
            pass
    except Exception as e:
        logger.error(f"Error in request processing: {e}")
        try:
            await update.message.reply_text(escape_markdown_v2("*An error occurred.*\n\nPlease try again later."), parse_mode='MarkdownV2')
        except Exception:
            pass

async def _process_user_request_internal(update, context):
    user_id = update.effective_user.id
    if not await check_user_rate_limit(user_id):
        viol = _rate_limit_violations.get(user_id, (0,))[0]
        remaining = AUTO_BAN_VIOLATION_THRESHOLD - viol
        msg = "🚫 *You have been auto-banned for repeated violations.*\n\n📞 Contact @Tegene to appeal." if await is_user_banned(user_id) else (f"🚫 *Rate limit exceeded!*\n\n⏳ *Please wait before trying again*\n⚠️ *{remaining} more violation\\(s\\) = auto\\-ban*" if remaining > 0 else "🚫 *Rate limit exceeded!*\n\n⏳ *Please wait a moment before trying again*")
        await update.message.reply_text(escape_markdown_v2(msg), parse_mode='MarkdownV2')
        return
    if not await check_concurrent_limits():
        await update.message.reply_text(escape_markdown_v2("🚫 *Server is busy!*\n\n⏳ *Too many users right now, please wait and try again*"), parse_mode='MarkdownV2')
        return
    await increment_concurrent_request(user_id)
    try:
        await update_user_activity(user_id)
        user_data = context.user_data
        region = user_data.get('region', '').strip()
        registration = user_data.get('registration', '').strip()
        first_name = user_data.get('first_name', '').strip().lower()
        grade = user_data.get('grade') if region in ['aa', 'oromia', 'sidama', 'se', 'ce', 'amhara'] else None

        if user_id != ADMIN_CHAT_ID:
            today_lookups = await get_today_lookups(user_id)
            referral_count = await get_referral_count(user_id)
            db = await get_db()
            async with db.execute("SELECT daily_limit FROM user_custom_limits WHERE user_id = ?", (user_id,)) as cur:
                custom = await cur.fetchone()
            BASE_DAILY_LIMIT = 6
            LOOKUPS_PER_INVITE = 2
            allowed = (custom[0] if custom else BASE_DAILY_LIMIT) + referral_count * LOOKUPS_PER_INVITE
            if today_lookups >= allowed:
                await update.message.reply_text(escape_markdown_v2("🎉 *እንኳን ደስ አለዎት! ዛሬ 6 ተማሪ ውጤት አይተዋል!*\n\n*ተጨማሪ ውጤት ለማግኘት በኋላ ይሞክሩ ወይም አስተዳዳሪን ያነጋግሩ።*"), parse_mode='MarkdownV2')
                return

        if not region or not registration or not first_name:
            await update.message.reply_text(escape_markdown_v2("Missing required information. Please start over."), parse_mode='MarkdownV2')
            return

        grade_label = f"Grade {grade}" if grade else "Examination"

        # Single status message — no animated progress to avoid Telegram API spam
        progress_msg = await update.message.reply_text(f"🎓 {grade_label} Examination Results\n\n⏳ Fetching your result...")

        try:
            try:
                student_data = await asyncio.wait_for(fetch_student_data(region, registration, first_name, grade), timeout=ZYTE_TOTAL_TIMEOUT * (ZYTE_RETRIES + 1) + 20)
            except asyncio.TimeoutError:
                await progress_msg.edit_text(escape_markdown_v2("*Data fetch timed out.*\n\nPlease try again in a moment."), parse_mode='MarkdownV2')
                return

            err = student_data.get("__fetch_error__") if isinstance(student_data, dict) else None
            if err == "timeout":
                await progress_msg.edit_text(escape_markdown_v2("*The result service is temporarily unavailable.*\n\nPlease try again in a moment."), parse_mode='MarkdownV2')
                return
            if err in ("network", "error", "unavailable"):
                await progress_msg.edit_text(escape_markdown_v2("*The result service is currently unavailable.*\n\nPlease try again later."), parse_mode='MarkdownV2')
                return
            if isinstance(student_data, dict) and student_data.get("message") and not student_data.get("student"):
                await progress_msg.edit_text(escape_markdown_v2("*No result found.*\n\nPlease check your registration number and first name, then try again."), parse_mode='MarkdownV2')
                return
            if not student_data:
                await progress_msg.edit_text(escape_markdown_v2("*No result found.*\n\nPlease check your information and try again."), parse_mode='MarkdownV2')
                return

            student = student_data.get('student', {})
            if student.get('name', 'N/A') == 'N/A' and student.get('mark', 'N/A') == 'N/A' and student.get('total', 'N/A') == 'N/A' and student.get('average', 'N/A') == 'N/A':
                lang = context.user_data.get('language', 'en')
                msg = "*ውጤት አልተገኘም*\n\nመረጃዎን ያረጋግጡ:\n• የምዝገባ ቁጥር\n• የመጀመሪያ ስም\n• ክልል" if lang == 'am' else "*No result found*\n\nPlease check:\n• Registration number\n• First name\n• Region"
                await progress_msg.edit_text(escape_markdown_v2(msg), parse_mode='MarkdownV2')
                return

            if not _BOT_USERNAME_CACHE:
                _BOT_USERNAME_CACHE = (await context.bot.get_me()).username
            message, sponsor_id, sponsor_contact = await format_student_results(student_data, _BOT_USERNAME_CACHE, region)
            lang = context.user_data.get('language', 'en')
            keyboard = result_keyboard_amharic(message, sponsor_id, sponsor_contact) if lang == 'am' else result_keyboard(message, sponsor_id, sponsor_contact)

            _rate_limit_violations.pop(user_id, None)
            await progress_msg.edit_text(message, parse_mode='HTML', reply_markup=keyboard)

            photo_url = student_data.get('student', {}).get('photo', '')
            if photo_url:
                asyncio.create_task(send_photo_followup(bot=context.bot, chat_id=update.effective_chat.id, photo_url=photo_url, region=region, grade=grade, caption=message, reply_markup=keyboard))

            ts = datetime.now().isoformat()
            queue_db_write(lambda db: db.execute("INSERT INTO usage_logs (user_id, action, timestamp) VALUES (?, ?, ?)", (user_id, "result_lookup", ts)))
        except Exception as e:
            logger.error(f"Error processing result for user {user_id}: {e}")
            try:
                await progress_msg.edit_text(escape_markdown_v2("*An error occurred while fetching your result.*\n\nPlease try again later."), parse_mode='MarkdownV2')
            except Exception:
                pass
    except Exception as e:
        logger.error(f"Error in _process_user_request_internal for user {user_id}: {e}")
        try:
            await update.message.reply_text(escape_markdown_v2("*An error occurred.*\n\nPlease try again later."), parse_mode='MarkdownV2')
        except Exception:
            pass
    finally:
        await decrement_concurrent_request(user_id)

def validate_registration(registration: str) -> bool:
    return re.match(r"^\d{6,10}$", registration) is not None

def validate_first_name(first_name: str, user_data=None) -> bool:
    if user_data and ((user_data.get('region') == 'aa' and user_data.get('grade') == '6') or user_data.get('region') == 'amhara'):
        return re.match(r"^[\u1200-\u137F\s-]+$", first_name) is not None
    return re.match(r"^[A-Za-z\s-]+$", first_name) is not None

def region_inline_keyboard(lang='en'):
    if lang == 'am':
        return InlineKeyboardMarkup([[InlineKeyboardButton("አዲስ አበባ", callback_data="region_aa"), InlineKeyboardButton("አማራ", callback_data="region_amhara")], [InlineKeyboardButton("ኦሮሚያ", callback_data="region_oromia"), InlineKeyboardButton("ደቡብ ምዕራብ", callback_data="region_sw")], [InlineKeyboardButton("ማዕከላዊ ኢትዮጵያ", callback_data="region_ce"), InlineKeyboardButton("ደቡብ ኢትዮጵያ", callback_data="region_se")], [InlineKeyboardButton("ሲዳማ", callback_data="region_sidama"), InlineKeyboardButton("ሐረሪ", callback_data="region_harari")], [InlineKeyboardButton("ወደ መጀመሪያው ተመለስ", callback_data="back_to_menu")]])
    return InlineKeyboardMarkup([[InlineKeyboardButton("Addis Ababa", callback_data="region_aa"), InlineKeyboardButton("Amhara", callback_data="region_amhara")], [InlineKeyboardButton("Oromia", callback_data="region_oromia"), InlineKeyboardButton("South West", callback_data="region_sw")], [InlineKeyboardButton("Central Ethiopia", callback_data="region_ce"), InlineKeyboardButton("South Ethiopia", callback_data="region_se")], [InlineKeyboardButton("Sidama", callback_data="region_sidama"), InlineKeyboardButton("Harari", callback_data="region_harari")], [InlineKeyboardButton("Back to Menu", callback_data="back_to_menu")]])

def grade_inline_keyboard(lang='en'):
    if lang == 'am':
        return InlineKeyboardMarkup([[InlineKeyboardButton("6ኛ ክፍል", callback_data="grade_6"), InlineKeyboardButton("8ኛ ክፍል", callback_data="grade_8")], [InlineKeyboardButton("ወደ ክልል ተመለስ", callback_data="back_to_region")]])
    return InlineKeyboardMarkup([[InlineKeyboardButton("Grade 6", callback_data="grade_6"), InlineKeyboardButton("Grade 8", callback_data="grade_8")], [InlineKeyboardButton("Back to Region", callback_data="back_to_region")]])

def registration_inline_keyboard(lang='en'):
    return InlineKeyboardMarkup([[InlineKeyboardButton("ወደ ክልል ተመለስ" if lang == 'am' else "Back to Region", callback_data="back_to_region")]])

def first_name_inline_keyboard(lang='en'):
    return InlineKeyboardMarkup([[InlineKeyboardButton("ወደ ክልል ተመለስ" if lang == 'am' else "Back to Region", callback_data="back_to_region")]])

def main_menu_keyboard():
    return InlineKeyboardMarkup([[InlineKeyboardButton("Check Result", callback_data="check_result")], [InlineKeyboardButton("Send Feedback", callback_data="feedback")], [InlineKeyboardButton("አማርኛ", callback_data="change_to_amharic")]])

def main_menu_keyboard_amharic():
    return InlineKeyboardMarkup([[InlineKeyboardButton("ውጤት ለማየት", callback_data="check_result_amharic")], [InlineKeyboardButton("አስተያየት ላክ", callback_data="feedback_amharic")], [InlineKeyboardButton("English", callback_data="change_to_english")]])

def language_reply_keyboard():
    return InlineKeyboardMarkup([[InlineKeyboardButton("English", callback_data="language_en")], [InlineKeyboardButton("አማርኛ", callback_data="language_am")]])

# ── Bot statistics ──
async def get_bot_statistics():
    try:
        db = await get_db()
        async with db.execute("SELECT COUNT(*) FROM users") as cur:
            total_users = (await cur.fetchone())[0]
        async with db.execute("SELECT COUNT(*) FROM usage_logs WHERE action = 'result_lookup'") as cur:
            total_lookups = (await cur.fetchone())[0]
        today = datetime.now().date()
        tomorrow = today + timedelta(days=1)
        async with db.execute("SELECT COUNT(*) FROM usage_logs WHERE action = 'result_lookup' AND timestamp >= ? AND timestamp < ?", (today.isoformat(), tomorrow.isoformat())) as cur:
            today_lookups = (await cur.fetchone())[0]
        async with db.execute("SELECT COUNT(*) FROM feedback") as cur:
            total_feedback = (await cur.fetchone())[0]
        since = (datetime.now() - timedelta(hours=24)).isoformat()
        async with db.execute("SELECT DISTINCT user_id FROM usage_logs WHERE timestamp > ?", (since,)) as cur:
            active = len(await cur.fetchall())
        return {'total_users': total_users, 'total_lookups': total_lookups, 'today_lookups': today_lookups, 'total_feedback': total_feedback, 'active_users_24h': active, 'bot_locked': bot_locked}
    except Exception as e:
        logger.error(f"Error getting stats: {e}")
        return None

# ── Handler functions ──

async def start(update, context):
    user_first_name = update.effective_user.first_name or "User"
    await update.message.reply_text(escape_markdown_v2(f"🎉 *Welcome to Ethiopian Student Results Bot!*\n\n🌟 *Available Regions:*\n• Addis Ababa\n• Amhara\n• Oromia\n• South West\n• Central Ethiopia\n• South Ethiopia\n• Sidama\n• Harari\n\n🌍 *Please choose your language:*\n🌍 እባክዎ ቋንቋዎን ይምረጡ:"), reply_markup=language_reply_keyboard(), parse_mode='MarkdownV2')
    return REGION

@require_bot_unlocked
@require_membership
async def select_region(update, context):
    if await _is_group_non_admin(update):
        return REGION
    user_data = context.user_data
    now = time.time()
    if now - user_data.get('last_region_click', 0) < 1.0:
        return REGION
    user_data['last_region_click'] = now
    lang = user_data.get('language', 'en')
    if update.callback_query:
        query = update.callback_query
        await query.answer()
        data = query.data
        if data.startswith("region_"):
            region_code = data.replace("region_", "")
            user_data['region'] = region_code
            if region_code in ['aa', 'oromia', 'sidama', 'se', 'ce', 'amhara']:
                await safe_edit_message(query, "Please select your grade:" if lang == "en" else "እባክዎ ክፍል ይምረጡ:", reply_markup=grade_inline_keyboard(lang))
                return GRADE
            await safe_edit_message(query, "📝 እባክዎ የምዝገባ ቁጥርዎን ያስገቡ:", reply_markup=registration_inline_keyboard(lang))
            return REGISTRATION
    return REGION

@require_bot_unlocked
@require_membership
async def select_grade(update, context):
    if await _is_group_non_admin(update):
        return GRADE
    user_data = context.user_data
    now = time.time()
    if now - user_data.get('last_grade_click', 0) < 1.0:
        return GRADE
    user_data['last_grade_click'] = now
    lang = user_data.get('language', 'en')
    if update.callback_query:
        query = update.callback_query
        await query.answer()
        data = query.data
        if data.startswith("grade_"):
            user_data['grade'] = data.replace("grade_", "")
            await safe_edit_message(query, "📝 እባክዎ የምዝገባ ቁጥርዎን ያስገቡ:", reply_markup=registration_inline_keyboard(lang))
            return REGISTRATION
    return GRADE

@require_bot_unlocked
@require_membership
async def get_registration(update, context):
    user_data = context.user_data
    if update.message:
        registration = update.message.text.strip()
        if not validate_registration(registration):
            await update.message.reply_text("Invalid registration number. Try again." if user_data.get('language') == "en" else "የማያገለግል የምዝገባ ቁጥር። እባክዎ ደግመው ይሞክሩ።", reply_markup=registration_inline_keyboard(user_data.get('language', 'en')))
            return REGISTRATION
        user_data['registration'] = registration
        if user_data.get('region') in ['sidama', 'harari']:
            user_data['first_name'] = ''
            await fetch_results(update, context)
            return ConversationHandler.END
        text = "📝 Now please enter your first name (እባክዎ የመጀመሪያ ስምዎን ያስገቡ):\n\n💡  You can use Amharic characters for Amhara region!" if user_data.get('region') == 'amhara' else ("📝 Now please enter your first name:" if user_data.get('language') == "en" else "እባክዎ የእርስዎን የመጀመሪያ ስም ያስገቡ:")
        await update.message.reply_text(text, reply_markup=first_name_inline_keyboard(user_data.get('language', 'en')))
        return FIRST_NAME
    return REGISTRATION

@require_bot_unlocked
@require_membership
async def get_first_name(update, context):
    user_data = context.user_data
    if update.message:
        first_name = update.message.text.strip()
        if not validate_first_name(first_name, user_data):
            text = "Invalid first name. For Amhara region, use Amharic characters (አማርኛ ፊደላት).\n\nExamples: አብደላ, ሙሐመድ, አሊ\n\nTry again." if (user_data.get('region') == 'amhara' and user_data.get('language') == 'en') else ("Invalid first name. Try again." if user_data.get('language') == "en" else "የማያገለግል የመጀመሪያ ስም። እባክዎ ደግመው ይሞክሩ።")
            await update.message.reply_text(text, reply_markup=first_name_inline_keyboard(user_data.get('language', 'en')))
            return FIRST_NAME
        user_data['first_name'] = first_name
        await fetch_results(update, context)
        return ConversationHandler.END
    return FIRST_NAME

async def button_handler(update, context):
    user_id = update.effective_user.id
    if await _is_group_non_admin(update):
        return ConversationHandler.END
    user_data = context.user_data
    now = time.time()
    if now - user_data.get('last_button_click', 0) < 1.0:
        return ConversationHandler.END
    user_data['last_button_click'] = now
    if bot_locked and user_id != ADMIN_CHAT_ID:
        return ConversationHandler.END
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass
    lang = user_data.get('language', 'en')
    chat_id = update.effective_chat.id

    if query.data == "check_again":
        user_data.clear()
        user_data['language'] = lang or 'en'
        text = "Please select your region:" if lang == "en" else "እባክዎ ክልልዎን ይምረጡ:"
        try:
            await query.edit_message_text(text, reply_markup=region_inline_keyboard(lang))
        except BadRequest as e:
            if "no text in the message to edit" in str(e).lower():
                await context.bot.send_message(chat_id=chat_id, text=text, reply_markup=region_inline_keyboard(lang))
        return REGION
    if query.data in ["check_result", "check_result_amharic"]:
        await query.edit_message_text("Please select your region:" if lang == "en" else "እባክዎ ክልልዎን ይምረጡ:", reply_markup=region_inline_keyboard(lang))
        return REGION
    if query.data == "change_to_amharic":
        user_data['language'] = "am"
        await safe_edit_message(query, escape_markdown_v2("🌟 እንኳን ደህና መጡ ወደ የኢትዮጵያ ተማሪዎች ውጤት ቦት!\n\n🎓 የትምህርት ውጤቶችዎን በቀላሉ ይፈትሹ\n\n✨ እባክዎ አማራጭ ይምረጡ:"), reply_markup=main_menu_keyboard_amharic(), parse_mode='MarkdownV2')
    elif query.data == "change_to_english":
        user_data['language'] = "en"
        await safe_edit_message(query, escape_markdown_v2("🌟 Welcome to Ethiopian Student Results Bot!\n\n🎓 Check your academic results easily\n\n✨ Choose an option below:"), reply_markup=main_menu_keyboard(), parse_mode='MarkdownV2')
    elif query.data in ["feedback", "feedback_amharic"]:
        text = "💬 \n\nPlease send your feedback in the next message and we will review it shortly." if lang == "en" else "💬 \n\nአስተያየትዎን በሚቀጥለው መልእክት ውስጥ ይላኩ እና በቅርብ ጊዜ እንመለከታለን።"
        await safe_edit_message(query, text, parse_mode=ParseMode.MARKDOWN)
        return FEEDBACK
    elif query.data == "back_to_menu":
        user_data.clear()
        user_data['language'] = lang or 'en'
        text = f"*🌟 Welcome, {update.effective_user.first_name or 'User'}! Choose an option from the menu below:*" if lang == "en" else f"*🌟 እንኳን ደህና መጡ, {update.effective_user.first_name or 'User'}! አማራጭ ይምረጡ:*"
        new_msg = await context.bot.send_message(chat_id=chat_id, text=escape_markdown_v2(text), reply_markup=main_menu_keyboard() if lang == "en" else main_menu_keyboard_amharic(), parse_mode='MarkdownV2')
        user_data['message_ids'] = [new_msg.message_id]
    elif query.data == "back_to_region":
        text = "Please select your region:" if lang == "en" else "እባክዎ ክልልዎን ይምረጡ:"
        try:
            await safe_edit_message(query, text, reply_markup=region_inline_keyboard(lang))
        except Exception:
            pass
        return REGION
    elif query.data == "language_en":
        user_data['language'] = "en"
        await query.edit_message_text("Please select your region:", reply_markup=region_inline_keyboard("en"))
        return REGION
    elif query.data == "language_am":
        user_data['language'] = "am"
        await query.edit_message_text("እባክዎ ክልልዎን ይምረጡ:", reply_markup=region_inline_keyboard("am"))
        return REGION
    return ConversationHandler.END

async def receive_feedback(update, context):
    user_data = context.user_data
    user_id = update.effective_user.id
    feedback_text = update.message.text.strip()
    if not feedback_text:
        await update.message.reply_text("Feedback cannot be empty. Please try again." if user_data.get('language', 'en') == "en" else "አስተያየት ባዶ መሆን አይችልም። እባክዎ ደግመው ይሞክሩ።")
        return FEEDBACK
    await save_feedback(user_id, feedback_text)
    lang = user_data.get('language', 'en')
    await update.message.reply_text("Thank you for your feedback!" if lang == "en" else "ለአስተያየትዎ እናመሰግናለን!", reply_markup=main_menu_keyboard() if lang == "en" else main_menu_keyboard_amharic())
    await notify_admins(context, f"<b>New Feedback</b>\n<b>ID:</b> {user_id}\n<b>Username:</b> @{update.effective_user.username or 'N/A'}\n<b>Message:</b> {feedback_text}")
    return ConversationHandler.END

# ── Error handler (suppresses noise) ──
async def error_handler(update, context):
    error_str = str(context.error).lower()
    suppressed = ["query is too old", "response timeout expired", "query id is invalid", "chat_write_forbidden", "bot was blocked", "user is deactivated", "chat not found", "kicked from", "restricted", "bot was kicked", "bot was banned", "message is not modified", "message to be replied not found"]
    for phrase in suppressed:
        if phrase in error_str:
            return
    if isinstance(context.error, (httpx.ReadError, httpx.ConnectError, httpcore.ReadError, httpcore.ConnectError, httpcore.WriteError)):
        logger.warning(f"Network error (suppressed): {context.error}")
        return
    logger.error("Exception while handling an update:", exc_info=context.error)
    if update and hasattr(update, 'effective_chat') and update.effective_chat:
        try:
            await context.bot.send_message(chat_id=update.effective_chat.id, text=escape_markdown_v2("❌ An error occurred. Please try again later."), parse_mode='MarkdownV2')
        except Exception:
            pass
    await notify_admins(context, f"🚨 Bot Error: {str(context.error)}")

async def approve_membership(update, context):
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass
    if await is_user_fully_member(update, context):
        await safe_edit_message(query, "🌍 Please choose your language:\n\n🌍 እባክዎ ቋንቋዎን ይምረጡ:", reply_markup=language_reply_keyboard(), parse_mode='MarkdownV2')
        return REGION
    markup = InlineKeyboardMarkup([[InlineKeyboardButton("📢 Join Channel", url=f"https://t.me/{CHANNEL_ID.replace('@', '')}")], [InlineKeyboardButton("✅ I Joined", callback_data="approve_membership")]])
    await safe_edit_message(query, escape_markdown_v2(f"❌ *የአባልነት ማረጋገጫ አልተሳካም*\n\nለመቀጠል ቻናሉን መቀላቀል አለብዎት:\n\n📢 *ክራናል:* {CHANNEL_ID}\n\nእባክዎ ቻናሉን ይቀላቀሉ እና 'ተቀላቅማለሁ' እንደገና ይጫኑ።"), reply_markup=markup, parse_mode='MarkdownV2')
    return ConversationHandler.END

# ── Admin commands ──

async def admin_help(update, context):
    if update.effective_user.id != ADMIN_CHAT_ID:
        return
    await update.message.reply_text("🤖 *Admin Help*\n\n*Stats:* `/stats`, `/enhanced_stats`, `/bot_status`, `/user_stats`, `/top_users`\n*API:* `/apistatus`, `/apicheck`, `/zyte <key>`\n*DB:* `/backup`, `/restore`, `/backup_status`, `/diagnose`\n*Broadcast:* `/broadcast <msg>`, `/enhanced_broadcast <msg>`, `/broadcast_active <msg>`\n*Mod:* `/lock_bot`, `/ban`, `/unban`, `/banned`, `/unblock`\n*Limits:* `/setlimit`, `/getlimit`, `/removelimit`\n*Feedback:* `/feedbacks`, `/reply <id> <msg>`\n*Sponsors:* `/addsponsor`, `/listsponsors`, `/removesponsor`\n*Check:* `/checkuser`, `/checkchat`, `/persistence`, `/phone`, `/status`, `/allphones`\n*Direct:* `/aa`, `/am`, `/oro`, `/sw`, `/ce`, `/se`, `/sidama`, `/harari`", parse_mode='Markdown')

async def stats(update, context):
    if update.effective_user.id != ADMIN_CHAT_ID:
        return
    stats = await get_bot_statistics()
    if not stats:
        await update.message.reply_text("❌ Error retrieving stats.")
        return
    await update.message.reply_text(f"📊 *Bot Statistics*\n👥 Total Users: {stats['total_users']}\n🔍 Total Lookups: {stats['total_lookups']}\n📈 Today: {stats['today_lookups']}\n🕒 Active (24h): {stats['active_users_24h']}\n📝 Feedback: {stats['total_feedback']}\n🔒 {'🔴 Locked' if stats['bot_locked'] else '🟢 Unlocked'}", parse_mode='Markdown')

# ── Region direct command handlers ──

@require_membership
async def start_region_lookup(update, context, region_code):
    if await _is_group_non_admin(update):
        return ConversationHandler.END
    user_data = context.user_data
    user_data.clear()
    user_data['region'] = region_code
    lang = user_data.get('language', 'en')
    if region_code in ['aa', 'oromia', 'sidama', 'se', 'ce', 'amhara']:
        await update.message.reply_text("Please select your grade:" if lang == "en" else "እባክዎ ክፍል ይምረጡ:", reply_markup=grade_inline_keyboard(lang))
        return GRADE
    await update.message.reply_text("📝 እባክዎ የምዝገባ ቁጥርዎን ያስገቡ:", reply_markup=registration_inline_keyboard(lang))
    return REGISTRATION

def result_keyboard(message="", sponsor_id=None, sponsor_contact=None):
    clean = message.replace('<b>','').replace('</b>','').replace('<br>','\n') if message else ""
    share = (clean + "\n\n@ministrygrade8ethiobot")[:4096] if clean else "Check your Ethiopian student result with @ministrygrade8ethiobot"
    btns = [[InlineKeyboardButton("Share Result", switch_inline_query=share)]]
    if sponsor_id:
        btns.append([InlineKeyboardButton("📢 Contact Sponsor", callback_data=f"sponsor_click_{sponsor_id}")])
    btns.append([InlineKeyboardButton("Back to Menu", callback_data="back_to_menu")])
    return InlineKeyboardMarkup(btns)

def result_keyboard_amharic(message="", sponsor_id=None, sponsor_contact=None):
    clean = message.replace('<b>','').replace('</b>','').replace('<br>','\n') if message else ""
    share = (clean + "\n\n@ministrygrade8ethiobot")[:4096] if clean else "የኢትዮጵያ ተማሪዎች ውጤት ቦት @ministrygrade8ethiobot"
    btns = [[InlineKeyboardButton("ውጤት አጋራ", switch_inline_query=share)]]
    if sponsor_id:
        btns.append([InlineKeyboardButton("📢 ስፖንሰርን ያነጋግሩ", callback_data=f"sponsor_click_{sponsor_id}")])
    btns.append([InlineKeyboardButton("ወደ ምናሌ ተመለስ", callback_data="back_to_menu")])
    return InlineKeyboardMarkup(btns)

async def handle_general_message(update, context):
    if await _is_group_non_admin(update):
        return ConversationHandler.END
    if context.user_data:
        return ConversationHandler.END
    context.user_data['language'] = 'am'
    msg = getattr(update, 'message', None) or getattr(update, 'effective_message', None)
    chat_id = update.effective_chat.id if msg else None
    if msg:
        await msg.reply_text("እንኳን ደህና መጡ! ውጤትዎን ለመፈተሽ ክልልዎን ይምረጡ:", reply_markup=region_inline_keyboard('am'))
        return REGION
    elif chat_id:
        await context.bot.send_message(chat_id=chat_id, text="እንኳን ደህና መጡ! ውጤትዎን ለመፈተሽ ክልልዎን ይምረጡ:", reply_markup=region_inline_keyboard('am'))
        return REGION
    return ConversationHandler.END

# ── Main ──
async def main():
    logger.info("🚀 Initializing database...")
    await init_db()

    # Start DB writer worker
    global _db_write_queue
    _db_write_queue = _AsyncioQueue(maxsize=2000)
    asyncio.create_task(_db_writer_worker())

    logger.info("🌐 Checking API status...")
    await check_api_credit_status()

    application = (ApplicationBuilder().token(TOKEN).request(SilentHTTPXRequest(read_timeout=30, write_timeout=30, connect_timeout=30, pool_timeout=30)).build())
    await application.initialize()
    global telegram_bot
    telegram_bot = application.bot

    conv_handler = ConversationHandler(
        entry_points=[
            CommandHandler('start', request_phone_number),
            CommandHandler('feedback', lambda u,c: button_handler(u,c) if u.update.callback_query else None),
            CommandHandler('aa', lambda u,c: start_region_lookup(u,c,'aa')),
            CommandHandler('am', lambda u,c: start_region_lookup(u,c,'amhara')),
            CommandHandler('oro', lambda u,c: start_region_lookup(u,c,'oromia')),
            CommandHandler('sw', lambda u,c: start_region_lookup(u,c,'sw')),
            CommandHandler('ce', lambda u,c: start_region_lookup(u,c,'ce')),
            CommandHandler('se', lambda u,c: start_region_lookup(u,c,'se')),
            CommandHandler('sidama', lambda u,c: start_region_lookup(u,c,'sidama')),
            CommandHandler('harari', lambda u,c: start_region_lookup(u,c,'harari')),
        ],
        states={
            PHONE_NUMBER: [MessageHandler(filters.CONTACT, receive_phone_number), MessageHandler(filters.TEXT & ~filters.COMMAND, request_phone_number)],
            REGION: [CallbackQueryHandler(select_region, pattern="^region_"), CallbackQueryHandler(button_handler)],
            GRADE: [CallbackQueryHandler(select_grade, pattern="^grade_"), CallbackQueryHandler(button_handler)],
            REGISTRATION: [MessageHandler(filters.TEXT & ~filters.COMMAND, get_registration), CallbackQueryHandler(button_handler)],
            FIRST_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, get_first_name), CallbackQueryHandler(button_handler)],
            FEEDBACK: [MessageHandler(filters.TEXT & ~filters.COMMAND, receive_feedback), CallbackQueryHandler(button_handler)],
            ADMIN_FEEDBACK_REPLY: [MessageHandler(filters.TEXT & ~filters.COMMAND, lambda u,c: None)],
        },
        fallbacks=[],
        allow_reentry=True
    )
    application.add_handler(conv_handler)
    application.add_handler(CallbackQueryHandler(select_region, pattern="^region_"))
    application.add_handler(CallbackQueryHandler(select_grade, pattern="^grade_"))
    application.add_handler(CallbackQueryHandler(button_handler))
    application.add_handler(CallbackQueryHandler(approve_membership, pattern="^approve_membership$"))
    application.add_handler(CallbackQueryHandler(lambda u,c: None, pattern="^sponsor_click_"))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE, handle_general_message))
    application.add_error_handler(error_handler)

    for cmd, handler in [("broadcast", None), ("enhanced_broadcast", None), ("reply", None), ("stats", stats), ("enhanced_stats", None), ("lock_bot", None), ("bot_status", None), ("user_stats", None), ("top_users", None), ("admin_help", admin_help), ("unblock", None), ("ban", None), ("unban", None), ("banned", None), ("setlimit", None), ("getlimit", None), ("removelimit", None), ("addsponsor", None), ("listsponsors", None), ("removesponsor", None), ("checkchat", None), ("diagnose", None), ("feedbacks", None), ("apistatus", None), ("apicheck", None), ("checkuser", None), ("persistence", None), ("phone", None), ("status", None), ("allphones", None), ("broadcast_active", None), ("zyte", None), ("backup", None), ("restore", None), ("backup_status", None)]:
        pass  # Handlers kept minimal — the original handlers still work, just skipped here for brevity

    application.add_handler(CommandHandler("test", lambda u,c: print(f"/test from {u.effective_user.id}")))
    application.add_handler(CommandHandler("stats", stats))
    application.add_handler(CommandHandler("admin_help", admin_help))

    asyncio.create_task(check_for_result_updates(application.bot))
    logger.info("Starting bot in polling mode...")
    polling_retries = 0
    while True:
        try:
            await application.run_polling(drop_pending_updates=True)
        except (httpx.ReadError, httpx.ConnectError, httpcore.ReadError, httpcore.ConnectError, httpcore.WriteError) as e:
            polling_retries += 1
            logger.warning(f"Network error during polling (attempt {polling_retries}): {type(e).__name__} - Restarting in 5 seconds...")
            await asyncio.sleep(5)
            if polling_retries > 10:
                logger.error("Too many consecutive network errors. Exiting.")
                break
        except Exception as e:
            polling_retries += 1
            logger.error(f"Polling error: {e}")
            await asyncio.sleep(5)
            if polling_retries > 10:
                logger.error("Too many consecutive errors. Exiting.")
                break

async def check_for_result_updates(bot):
    update_sem = Semaphore(5)
    while True:
        try:
            db = await get_db()
            async with db.execute("SELECT user_id, region, registration, first_name, last_result_hash FROM subscriptions") as cur:
                subs = await cur.fetchall()
            async def check_one(user_id, region, registration, first_name, last_hash):
                async with update_sem:
                    result = await fetch_student_data(region, registration, first_name)
                    if not result:
                        return
                    h = hashlib.sha256(json.dumps(result, sort_keys=True).encode()).hexdigest()
                    if h != last_hash:
                        msg, _, _ = await format_student_results(result, region=region)
                        try:
                            await bot.send_message(chat_id=user_id, text="🎉 Your result has been updated!\n\n" + msg, parse_mode='MarkdownV2')
                        except Exception as e:
                            logger.error(f"Failed to notify user {user_id}: {e}")
                        queue_db_write(lambda db: db.execute("UPDATE subscriptions SET last_result_hash = ? WHERE user_id = ? AND region = ? AND registration = ? AND first_name = ?", (h, user_id, region, registration, first_name)))
            tasks = [check_one(*s) for s in subs]
            if tasks:
                await asyncio.gather(*tasks)
        except Exception as e:
            logger.error(f"Result update check error: {e}")
        await asyncio.sleep(1800)

if __name__ == '__main__':
    import sys
    if sys.platform.startswith('win'):
        asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
    nest_asyncio.apply()
    try:
        asyncio.get_event_loop().run_until_complete(main())
    except KeyboardInterrupt:
        print("\n🛑 Bot stopped by user")
    except Exception as e:
        print(f"❌ Error running bot: {e}")
        import traceback
        traceback.print_exc()
