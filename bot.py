
import asyncio
import html
import json
import logging
import math
import os
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Optional
from zoneinfo import ZoneInfo

import matplotlib
matplotlib.use("Agg")
import mplfinance as mpf
import numpy as np
import pandas as pd
import requests
import sqlite3

try:
    import psycopg
except ImportError:
    psycopg = None
import feedparser
import xml.etree.ElementTree as ET
from bs4 import BeautifulSoup
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from dotenv import load_dotenv
from telegram import Update, ReplyKeyboardMarkup, ReplyKeyboardRemove
from telegram.constants import ParseMode
from telegram.ext import (
    Application, CommandHandler, ContextTypes, ConversationHandler,
    MessageHandler, filters
)

load_dotenv()
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s"
)
log = logging.getLogger("xau-signal-bot")

BOT_TOKEN = os.environ["TELEGRAM_BOT_TOKEN"]
DATABASE_URL = os.getenv("DATABASE_URL", "").strip()
CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()
GOLD_API_KEY = os.getenv("GOLD_API_KEY", "").strip()
GOLD_API_BASE_URL = os.getenv("GOLD_API_BASE_URL", "https://api.gold-api.com").rstrip("/")
TE_KEY = os.getenv("TRADING_ECONOMICS_API_KEY", "")
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY", "").strip()
OPENAI_MODEL = os.getenv("OPENAI_MODEL", "gpt-4.1-mini").strip()
OPENAI_ENABLED = os.getenv("OPENAI_ENABLED", "true").lower() == "true"
OPENAI_TIMEOUT = int(os.getenv("OPENAI_TIMEOUT_SECONDS", "35"))
AI_BLOCK_OPPOSITE = os.getenv("AI_BLOCK_OPPOSITE", "true").lower() == "true"
SYMBOL = os.getenv("MARKET_SYMBOL", "XAU/USD")
TZ = ZoneInfo(os.getenv("TZ", "Asia/Tashkent"))

SCAN_MINUTES = int(os.getenv("SCAN_MINUTES", "3"))
MIN_SIGNAL_SCORE = int(os.getenv("MIN_SIGNAL_SCORE", "6"))
RELAXED_SIGNAL_SCORE = int(os.getenv("RELAXED_SIGNAL_SCORE", "5"))
DAILY_SIGNAL_TARGET = int(os.getenv("DAILY_SIGNAL_TARGET", "2"))
MIN_RR = float(os.getenv("MIN_RR", "1.8"))
COOLDOWN_HOURS = int(os.getenv("SIGNAL_COOLDOWN_HOURS", "3"))
SIGNAL_MAX_HOURS = int(os.getenv("SIGNAL_MAX_HOURS", "36"))
INTRADAY_HOURS = int(os.getenv("INTRADAY_HOURS", "6"))
SWING_HOURS = int(os.getenv("SWING_HOURS", "24"))
POINT_SIZE = float(os.getenv("XAU_POINT_SIZE", "0.01"))
MAX_TP_POINTS = int(os.getenv("MAX_TP_POINTS", "300"))
MIN_SL_POINTS = int(os.getenv("MIN_SL_POINTS", "10"))
MAX_SL_POINTS = int(os.getenv("MAX_SL_POINTS", "50"))
ENTRY_VALID_MINUTES = int(os.getenv("ENTRY_VALID_MINUTES", "15"))
NEWS_BLOCK_BEFORE = int(os.getenv("NEWS_BLOCK_BEFORE_MINUTES", "45"))
NEWS_CONFIRM_AFTER = int(os.getenv("NEWS_CONFIRM_AFTER_MINUTES", "30"))
DRY_RUN = os.getenv("DRY_RUN", "false").lower() == "true"
SMC_LOOKBACK = int(os.getenv("SMC_LOOKBACK", "80"))
SMC_REQUIRE_CONFIRMATION = os.getenv("SMC_REQUIRE_CONFIRMATION", "true").lower() == "true"

OFFICIAL_NEWS_SCAN_MINUTES = int(os.getenv("OFFICIAL_NEWS_SCAN_MINUTES", "5"))
OFFICIAL_NEWS_SEND_EXISTING = os.getenv("OFFICIAL_NEWS_SEND_EXISTING", "false").lower() == "true"
OFFICIAL_NEWS_MAX_AGE_HOURS = int(os.getenv("OFFICIAL_NEWS_MAX_AGE_HOURS", "24"))

OFFICIAL_FEEDS = {
    "Federal Reserve — Monetary Policy": "https://www.federalreserve.gov/feeds/press_monetary.xml",
    "Federal Reserve — Speeches": "https://www.federalreserve.gov/feeds/speeches.xml",
    "BLS — Employment Situation": "https://www.bls.gov/feed/empsit.rss",
    "BLS — CPI": "https://www.bls.gov/feed/cpi.rss",
    "BLS — PPI": "https://www.bls.gov/feed/ppi.rss",
    "BEA — Economic Releases": "https://apps.bea.gov/rss/rss.xml",
}

OFFICIAL_NEWS_KEYWORDS = (
    "fomc", "federal funds", "interest rate", "monetary policy", "inflation",
    "consumer price", "producer price", "cpi", "ppi", "payroll", "employment",
    "unemployment", "job openings", "labor market", "wages", "average hourly",
    "gross domestic product", "gdp", "personal consumption", "pce",
    "personal income", "retail", "economic outlook", "treasury yield",
    "rate cut", "rate hike", "balance sheet", "quantitative tightening",
    "powell", "chair", "governor", "vice chair"
)

# Persistent storage. On Railway mount a Volume at /data.
# Without a persistent volume no program can keep subscribers after a full redeploy.
def _resolve_data_dir() -> Path:
    preferred = Path(os.getenv("BOT_DATA_DIR", "/data"))
    try:
        preferred.mkdir(parents=True, exist_ok=True)
        test_file = preferred / ".write_test"
        test_file.write_text("ok", encoding="utf-8")
        test_file.unlink(missing_ok=True)
        return preferred
    except Exception:
        fallback = Path(".bot_data")
        fallback.mkdir(parents=True, exist_ok=True)
        return fallback

DATA_DIR = _resolve_data_dir()
STATE_FILE = DATA_DIR / "state.json"
CHART_FILE = DATA_DIR / "latest_signal.png"
USER_STATE_FILE = DATA_DIR / "users.json"  # human-readable backup
USER_DB_FILE = DATA_DIR / "users.sqlite3"
ACTIVE_SIGNALS_FILE = DATA_DIR / "active_signals.json"
LEGACY_USER_STATE_FILE = Path("users.json")

SELECT_LANGUAGE, ENTER_CAPITAL = range(2)

LANG_KEYBOARD = ReplyKeyboardMarkup(
    [["🇷🇺 Русский", "🇺🇿 O‘zbekcha"]],
    resize_keyboard=True,
    one_time_keyboard=True,
)

RU_MENU = ReplyKeyboardMarkup(
    [
        ["📊 Анализ", "📰 Новости"],
        ["✅ Статус", "🧪 Тест-сигнал"],
        ["👤 Профиль", "🏛 Официальные новости"],
        ["⚙️ Изменить язык/капитал"],
    ],
    resize_keyboard=True,
)

UZ_MENU = ReplyKeyboardMarkup(
    [
        ["📊 Tahlil", "📰 Yangiliklar"],
        ["✅ Holat", "🧪 Test-signal"],
        ["👤 Profil", "🏛 Rasmiy yangiliklar"],
        ["⚙️ Til/kapitalni o‘zgartirish"],
    ],
    resize_keyboard=True,
)


def menu_for(lang: str) -> ReplyKeyboardMarkup:
    return UZ_MENU if lang == "uz" else RU_MENU

TEXTS = {
    "ru": {
        "welcome": "👋 Добро пожаловать! Выберите язык:",
        "ask_capital": "💵 Введите ваш торговый капитал в долларах, например: 100 или 2500",
        "bad_capital": "Введите корректную сумму от 1 до 1 000 000 долларов.",
        "saved": "✅ Готово! Капитал сохранён: ${capital:,.2f}\n📌 Рекомендованный минимальный лот: {lot:.2f}\n🔔 Теперь вы будете получать персональные сигналы.",
        "cancelled": "Настройка отменена.",
        "not_configured": "Сначала нажмите /start и настройте язык и капитал.",
        "profile": "Язык: Русский\nКапитал: ${capital:,.2f}\nРекомендованный минимальный лот: {lot:.2f}",
        "personal_plan": "👤 Персональный план\nКапитал: ${capital:,.2f}\nРекомендованный минимальный лот: {lot:.2f}\nРиск: минимальный",
    },
    "uz": {
        "welcome": "👋 Xush kelibsiz! Tilni tanlang:",
        "ask_capital": "💵 Savdo kapitalingizni dollarda kiriting, masalan: 100 yoki 2500",
        "bad_capital": "1 dan 1 000 000 dollargacha to‘g‘ri summa kiriting.",
        "saved": "✅ Tayyor! Kapital saqlandi: ${capital:,.2f}\n📌 Tavsiya etilgan minimal lot: {lot:.2f}\n🔔 Endi siz shaxsiy signallar olasiz.",
        "cancelled": "Sozlash bekor qilindi.",
        "not_configured": "Avval /start ni bosing va til hamda kapitalni sozlang.",
        "profile": "Til: O‘zbekcha\nKapital: ${capital:,.2f}\nTavsiya etilgan minimal lot: {lot:.2f}",
        "personal_plan": "👤 Shaxsiy reja\nKapital: ${capital:,.2f}\nTavsiya etilgan minimal lot: {lot:.2f}\nRisk: minimal",
    }
}

HIGH_IMPACT_WORDS = (
    "non farm", "non-farm", "nonfarm", "payroll", "nfp",
    "cpi", "core cpi", "consumer price", "inflation",
    "ppi", "core ppi", "producer price",
    "pce", "core pce", "personal consumption",
    "fomc", "fed interest", "interest rate", "powell", "federal reserve",
    "unemployment", "jobless", "initial claims", "continuing claims",
    "gdp", "retail sales", "employment", "average hourly", "adp", "jolts",
    "pmi", "services pmi", "manufacturing pmi", "composite pmi",
    "s&p global", "ism manufacturing", "ism services", "ism non-manufacturing",
    "consumer confidence", "michigan sentiment"
)

@dataclass
class NewsContext:
    blocked: bool
    bias: str
    title: str
    explanation: str
    upcoming: list
    recent: list

@dataclass
class SMCContext:
    bullish_bos: bool
    bearish_bos: bool
    bullish_choch: bool
    bearish_choch: bool
    bullish_sweep: bool
    bearish_sweep: bool
    bullish_fvg: Optional[tuple[float, float]]
    bearish_fvg: Optional[tuple[float, float]]
    bullish_ob: Optional[tuple[float, float]]
    bearish_ob: Optional[tuple[float, float]]
    summary: list[str]


@dataclass
class Signal:
    side: str
    score: int
    entry_low: float
    entry_high: float
    stop: float
    tp1: float
    tp2: float
    rr: float
    invalidation: str
    reasons: list[str]
    strategies: list[str]
    price: float
    fib_low: float
    fib_high: float
    news: NewsContext
    smc: SMCContext
    ai_verdict: str = "UNAVAILABLE"
    ai_confidence: int = 0
    ai_summary: str = "OpenAI-анализ не выполнялся."
    trade_style: str = "INTRADAY"
    expected_hold_hours: int = 8
    expires_at: str = ""
    entry_timeframe: str = "M15/M30"
    analysis_timeframes: str = "H1/H4/D1"
    entry_valid_minutes: int = 15


# Live XAU/USD price from GoldAPI. The free /price/XAU endpoint is used as
# the source of truth for the current spot price. Yahoo provides candle shape;
# candles are aligned to this live spot price so a delayed feed cannot produce
# an entry hundreds of points away from the real market.
_GOLD_PRICE_CACHE: tuple[datetime, float, str] | None = None

def goldapi_live_price() -> tuple[float, str]:
    global _GOLD_PRICE_CACHE
    now = datetime.now(timezone.utc)
    if _GOLD_PRICE_CACHE and (now - _GOLD_PRICE_CACHE[0]).total_seconds() < 25:
        return _GOLD_PRICE_CACHE[1], _GOLD_PRICE_CACHE[2]
    url = f"{GOLD_API_BASE_URL}/price/XAU"
    headers = {"Accept": "application/json", "User-Agent": "XAU-Signal-Bot/1.0"}
    if GOLD_API_KEY:
        headers["x-api-key"] = GOLD_API_KEY
    response = requests.get(url, headers=headers, timeout=20)
    if response.status_code >= 400:
        raise RuntimeError(f"GoldAPI HTTP {response.status_code}: {response.text[:200]}")
    payload = response.json()
    price = float(payload.get("price"))
    updated = str(payload.get("updatedAt") or payload.get("updatedAtReadable") or "")
    if not math.isfinite(price) or price <= 0:
        raise RuntimeError(f"GoldAPI returned invalid price: {payload}")
    _GOLD_PRICE_CACHE = (now, price, updated)
    return price, updated

# Real OHLC candles from Yahoo Finance chart data.
# Gold API is kept optional for the user's existing subscription, but it is not
# used to manufacture candles from max/min/avg aggregates.
_YAHOO_CACHE: dict[tuple[str, str], tuple[datetime, pd.DataFrame]] = {}


def _yahoo_chart(symbol: str, interval: str, range_: str) -> pd.DataFrame:
    cache_key = (symbol, interval)
    now = datetime.now(timezone.utc)
    ttl = 45 if interval in ("15m", "30m") else 180
    cached = _YAHOO_CACHE.get(cache_key)
    if cached and (now - cached[0]).total_seconds() < ttl:
        return cached[1].copy()

    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{symbol}"
    params = {
        "interval": interval,
        "range": range_,
        "includePrePost": "false",
        "events": "div,splits",
    }
    headers = {
        "User-Agent": "Mozilla/5.0 (compatible; XAU-Signal-Bot/1.0)",
        "Accept": "application/json",
    }
    response = requests.get(url, params=params, headers=headers, timeout=30)
    if response.status_code >= 400:
        raise RuntimeError(f"Yahoo Finance HTTP {response.status_code}: {response.text[:300]}")
    try:
        payload = response.json()
    except Exception as exc:
        raise RuntimeError(f"Yahoo Finance returned invalid JSON: {response.text[:300]}") from exc

    chart = payload.get("chart") or {}
    error = chart.get("error")
    if error:
        raise RuntimeError(f"Yahoo Finance error for {symbol}: {error}")
    results = chart.get("result") or []
    if not results:
        raise RuntimeError(f"Yahoo Finance returned no chart result for {symbol}/{interval}")

    result = results[0]
    timestamps = result.get("timestamp") or []
    indicators = result.get("indicators") or {}
    quotes = indicators.get("quote") or []
    if not timestamps or not quotes:
        raise RuntimeError(f"Yahoo Finance returned no OHLC data for {symbol}/{interval}")
    quote = quotes[0]

    frame = pd.DataFrame({
        "open": quote.get("open") or [],
        "high": quote.get("high") or [],
        "low": quote.get("low") or [],
        "close": quote.get("close") or [],
    }, index=pd.to_datetime(timestamps, unit="s", utc=True))
    frame = frame.apply(pd.to_numeric, errors="coerce").dropna()
    frame = frame[~frame.index.duplicated(keep="last")].sort_index()
    if frame.empty:
        raise RuntimeError(f"Yahoo Finance returned only empty candles for {symbol}/{interval}")
    _YAHOO_CACHE[cache_key] = (now, frame.copy())
    return frame


def _real_ohlc_base(interval: str) -> pd.DataFrame:
    settings = {
        "15min": ("15m", "60d"),
        "30min": ("30m", "60d"),
        "1h": ("60m", "730d"),
        "1day": ("1d", "5y"),
    }
    if interval not in settings:
        raise ValueError(f"Unsupported OHLC interval: {interval}")
    yahoo_interval, range_ = settings[interval]

    errors = []
    # Spot gold first; COMEX futures are a fallback when the spot feed is unavailable.
    for symbol in ("XAUUSD=X", "GC=F"):
        try:
            frame = _yahoo_chart(symbol, yahoo_interval, range_)
            frame.attrs["source_symbol"] = symbol
            return frame
        except Exception as exc:
            errors.append(f"{symbol}: {exc}")
    raise RuntimeError("Real OHLC feed unavailable. " + " | ".join(errors))


def real_ohlc_candles(interval: str, outputsize: int = 500) -> pd.DataFrame:
    if interval == "4h":
        base = _real_ohlc_base("1h")
        candles = base.resample("4h", label="right", closed="right").agg({
            "open": "first", "high": "max", "low": "min", "close": "last"
        }).dropna()
    else:
        candles = _real_ohlc_base(interval).copy()

    candles = candles.tail(outputsize).copy()
    minimum = min(80, outputsize)
    if len(candles) < minimum:
        raise RuntimeError(f"Real OHLC feed returned too few {interval} candles: {len(candles)}")

    # Yahoo spot/futures can lag or differ from the broker spot quote. Align the
    # whole series by a constant offset to the live GoldAPI XAU/USD price. This
    # preserves candle structure and indicators while making the latest price real.
    try:
        live_price, updated_at = goldapi_live_price()
        source_close = float(candles.iloc[-1]["close"])
        offset = live_price - source_close
        for col in ("open", "high", "low", "close"):
            candles[col] = candles[col].astype(float) + offset
        candles.attrs["live_price"] = live_price
        candles.attrs["live_updated_at"] = updated_at
        candles.attrs["alignment_offset"] = offset
        log.info("Aligned %s candles to GoldAPI: source=%.2f live=%.2f offset=%+.2f", interval, source_close, live_price, offset)
    except Exception as exc:
        # Do not silently claim the quote is live. Signal creation below checks
        # this attribute and refuses publication if GoldAPI validation failed.
        candles.attrs["live_price_error"] = str(exc)
        log.exception("GoldAPI live-price alignment failed for %s", interval)

    return candles[["open", "high", "low", "close"]]


# Backward-compatible name used throughout the existing bot.
def td_candles(interval: str, outputsize: int = 500) -> pd.DataFrame:
    return real_ohlc_candles(interval, outputsize)


def ema(s: pd.Series, length: int) -> pd.Series:
    return s.ewm(span=length, adjust=False).mean()


def rsi(s: pd.Series, length: int = 14) -> pd.Series:
    delta = s.diff()
    gain = delta.clip(lower=0).ewm(alpha=1/length, adjust=False).mean()
    loss = (-delta.clip(upper=0)).ewm(alpha=1/length, adjust=False).mean()
    rs = gain / loss.replace(0, np.nan)
    return 100 - (100 / (1 + rs))


def atr(df: pd.DataFrame, length: int = 14) -> pd.Series:
    prev = df["close"].shift(1)
    tr = pd.concat([
        df["high"] - df["low"],
        (df["high"] - prev).abs(),
        (df["low"] - prev).abs()
    ], axis=1).max(axis=1)
    return tr.ewm(alpha=1/length, adjust=False).mean()


def adx(df: pd.DataFrame, length: int = 14) -> pd.Series:
    up = df["high"].diff()
    down = -df["low"].diff()
    plus_dm = up.where((up > down) & (up > 0), 0.0)
    minus_dm = down.where((down > up) & (down > 0), 0.0)
    a = atr(df, length)
    plus_di = 100 * plus_dm.ewm(alpha=1/length, adjust=False).mean() / a
    minus_di = 100 * minus_dm.ewm(alpha=1/length, adjust=False).mean() / a
    dx = ((plus_di - minus_di).abs() / (plus_di + minus_di).replace(0, np.nan)) * 100
    return dx.ewm(alpha=1/length, adjust=False).mean()


def enrich(df: pd.DataFrame) -> pd.DataFrame:
    x = df.copy()
    x["ema20"] = ema(x["close"], 20)
    x["ema50"] = ema(x["close"], 50)
    x["ema200"] = ema(x["close"], 200)
    x["rsi"] = rsi(x["close"])
    x["atr"] = atr(x)
    x["adx"] = adx(x)
    fast = ema(x["close"], 12)
    slow = ema(x["close"], 26)
    x["macd"] = fast - slow
    x["macd_signal"] = ema(x["macd"], 9)
    mid = x["close"].rolling(20).mean()
    std = x["close"].rolling(20).std()
    x["bb_upper"] = mid + 2 * std
    x["bb_lower"] = mid - 2 * std
    return x.dropna()


def swing_range(df: pd.DataFrame, lookback: int = 80) -> tuple[float, float]:
    part = df.tail(lookback)
    low_i = part["low"].idxmin()
    high_i = part["high"].idxmax()
    low = float(part.loc[low_i, "low"])
    high = float(part.loc[high_i, "high"])
    return low, high


def parse_dt(value: str) -> datetime:
    dt = datetime.fromisoformat(value.replace("Z", "+00:00"))
    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)


def _parse_ff_datetime(date_text: str, time_text: str) -> Optional[datetime]:
    """Parse Forex Factory/FairEconomy calendar time as America/New_York."""
    date_text = (date_text or "").strip()
    time_text = (time_text or "").strip().lower().replace(" ", "")
    if not date_text or not time_text or time_text in {"all day", "tentative", ""}:
        return None
    parsed_date = None
    for fmt in ("%m-%d-%Y", "%m/%d/%Y", "%Y-%m-%d"):
        try:
            parsed_date = datetime.strptime(date_text, fmt).date()
            break
        except ValueError:
            continue
    if parsed_date is None:
        return None
    parsed_time = None
    for fmt in ("%I:%M%p", "%H:%M"):
        try:
            parsed_time = datetime.strptime(time_text, fmt).time()
            break
        except ValueError:
            continue
    if parsed_time is None:
        return None
    ny = ZoneInfo("America/New_York")
    return datetime.combine(parsed_date, parsed_time, tzinfo=ny).astimezone(timezone.utc)


def fetch_faireconomy_events() -> list[dict]:
    """No-key Forex Factory/FairEconomy calendar feed."""
    urls = (
        "https://nfs.faireconomy.media/ff_calendar_thisweek.xml",
        "https://nfs.faireconomy.media/ff_calendar_nextweek.xml",
    )
    headers = {
        "User-Agent": "Mozilla/5.0 (iPhone; CPU iPhone OS 18_0 like Mac OS X) AppleWebKit/605.1.15",
        "Accept": "application/xml,text/xml,*/*",
    }
    events: list[dict] = []
    for url in urls:
        try:
            response = requests.get(url, headers=headers, timeout=25)
            response.raise_for_status()
            root = ET.fromstring(response.content)
            for node in root.findall(".//event"):
                get = lambda tag: (node.findtext(tag) or "").strip()
                country = get("country").upper()
                if country not in {"USD", "US", "USA", "UNITED STATES"}:
                    continue
                dt = _parse_ff_datetime(get("date"), get("time"))
                if dt is None:
                    continue
                impact_text = get("impact").lower()
                importance = 3 if "high" in impact_text else 2 if "medium" in impact_text else 1
                title = get("title")
                events.append({
                    "Event": title,
                    "Category": title,
                    "Country": "United States",
                    "Date": dt.isoformat(),
                    "Importance": importance,
                    "Actual": get("actual"),
                    "Forecast": get("forecast"),
                    "Previous": get("previous"),
                    "Source": "FairEconomy",
                    "URL": get("url"),
                })
        except Exception as exc:
            log.warning("FairEconomy calendar failed: %s — %s", url, exc)
    return events


def _tv_importance(value) -> int:
    if isinstance(value, (int, float)):
        value = int(value)
        return 3 if value >= 3 else 2 if value == 2 else 1
    text = str(value or "").lower()
    return 3 if "high" in text else 2 if "medium" in text else 1


def _tv_datetime(value) -> Optional[datetime]:
    if isinstance(value, (int, float)):
        # TradingView may return seconds or milliseconds.
        stamp = float(value)
        if stamp > 10_000_000_000:
            stamp /= 1000
        return datetime.fromtimestamp(stamp, tz=timezone.utc)
    if not value:
        return None
    try:
        return parse_dt(str(value))
    except Exception:
        return None


def fetch_tradingview_events() -> list[dict]:
    """No-key TradingView economic-calendar fallback.

    The parser intentionally accepts several response shapes because the public
    endpoint has changed field names in the past.
    """
    now = datetime.now(timezone.utc)
    date_from = (now - timedelta(days=1)).strftime("%Y-%m-%dT00:00:00.000Z")
    date_to = (now + timedelta(days=8)).strftime("%Y-%m-%dT23:59:59.999Z")
    url = "https://economic-calendar.tradingview.com/events"
    params = {
        "from": date_from,
        "to": date_to,
        "countries": "US",
        "minImportance": "1",
    }
    headers = {
        "User-Agent": "Mozilla/5.0 (iPhone; CPU iPhone OS 18_0 like Mac OS X) AppleWebKit/605.1.15",
        "Origin": "https://www.tradingview.com",
        "Referer": "https://www.tradingview.com/markets/currencies/economic-calendar/",
        "Accept": "application/json,text/plain,*/*",
    }
    try:
        response = requests.get(url, params=params, headers=headers, timeout=25)
        response.raise_for_status()
        payload = response.json()
    except Exception as exc:
        log.warning("TradingView calendar failed: %s", exc)
        return []

    if isinstance(payload, list):
        rows = payload
    elif isinstance(payload, dict):
        rows = payload.get("result") or payload.get("events") or payload.get("data") or []
    else:
        rows = []

    events: list[dict] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        country = str(row.get("country") or row.get("countryCode") or row.get("currency") or "").upper()
        if country and country not in {"US", "USA", "USD", "UNITED STATES"}:
            continue
        title = str(row.get("title") or row.get("name") or row.get("event") or "").strip()
        dt = _tv_datetime(row.get("date") or row.get("time") or row.get("timestamp") or row.get("datetime"))
        if not title or dt is None:
            continue
        events.append({
            "Event": title,
            "Category": str(row.get("category") or title),
            "Country": "United States",
            "Date": dt.isoformat(),
            "Importance": _tv_importance(row.get("importance") or row.get("impact")),
            "Actual": row.get("actual") if row.get("actual") not in (None, "") else "",
            "Forecast": row.get("forecast") if row.get("forecast") not in (None, "") else "",
            "Previous": row.get("previous") if row.get("previous") not in (None, "") else "",
            "Source": "TradingView calendar",
            "URL": "",
        })
    return events



def _clean_calendar_value(value: str) -> str:
    text = BeautifulSoup(str(value or ""), "html.parser").get_text(" ", strip=True)
    return " ".join(text.replace("\xa0", " ").split())


def fetch_investing_events() -> list[dict]:
    """No-key Investing.com calendar fallback.

    This endpoint returns an HTML fragment inside JSON. The parser is deliberately
    defensive because class names and optional fields can vary.
    """
    now_local = datetime.now(TZ)
    start = now_local.date() - timedelta(days=1)
    end = now_local.date() + timedelta(days=7)
    url = "https://www.investing.com/economic-calendar/Service/getCalendarFilteredData"
    payload = [
        ("country[]", "5"),
        ("importance[]", "1"),
        ("importance[]", "2"),
        ("importance[]", "3"),
        ("dateFrom", start.strftime("%Y-%m-%d")),
        ("dateTo", end.strftime("%Y-%m-%d")),
        ("timeZone", "55"),
        ("timeFilter", "timeOnly"),
        ("currentTab", "custom"),
        ("limit_from", "0"),
    ]
    headers = {
        "User-Agent": "Mozilla/5.0 (iPhone; CPU iPhone OS 18_0 like Mac OS X) AppleWebKit/605.1.15",
        "Accept": "application/json, text/javascript, */*; q=0.01",
        "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
        "X-Requested-With": "XMLHttpRequest",
        "Origin": "https://www.investing.com",
        "Referer": "https://www.investing.com/economic-calendar/",
    }
    try:
        response = requests.post(url, data=payload, headers=headers, timeout=30)
        response.raise_for_status()
        body = response.json()
        html_fragment = body.get("data", "") if isinstance(body, dict) else ""
        if not html_fragment:
            log.warning("Investing calendar returned no HTML payload")
            return []
    except Exception as exc:
        log.warning("Investing calendar failed: %s", exc)
        return []

    soup = BeautifulSoup(html_fragment, "html.parser")
    events: list[dict] = []
    for row in soup.select("tr[id^='eventRowId_'], tr.js-event-item"):
        currency_cell = row.select_one("td.flagCur, td[class*='flagCur']")
        currency = _clean_calendar_value(currency_cell.get_text(" ", strip=True) if currency_cell else "")
        country_tag = row.select_one("span[title]")
        country = (country_tag.get("title", "") if country_tag else "").strip()
        if "USD" not in currency.upper() and "UNITED STATES" not in country.upper():
            continue

        title_node = row.select_one("td.event a, td.event, a.event")
        title = _clean_calendar_value(title_node.get_text(" ", strip=True) if title_node else "")
        if not title:
            continue

        raw_dt = row.get("event_timestamp") or row.get("data-event-datetime") or ""
        dt = None
        for fmt in ("%Y/%m/%d %H:%M:%S", "%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M"):
            try:
                dt = datetime.strptime(str(raw_dt).strip(), fmt).replace(tzinfo=timezone.utc)
                break
            except ValueError:
                continue
        if dt is None:
            try:
                dt = parse_dt(str(raw_dt))
            except Exception:
                continue

        actual_node = row.select_one("td[id^='eventActual_'], td.actual")
        forecast_node = row.select_one("td[id^='eventForecast_'], td.forecast")
        previous_node = row.select_one("td[id^='eventPrevious_'], td.previous")
        impact_icons = row.select("td.sentiment i.grayFullBullishIcon, td.sentiment i.full, td[class*='sentiment'] i[class*='Full']")
        importance = min(3, max(1, len(impact_icons)))
        if not impact_icons:
            sentiment = row.select_one("td.sentiment, td[class*='sentiment']")
            importance = _tv_importance(sentiment.get("title", "") if sentiment else "")

        events.append({
            "Event": title,
            "Category": title,
            "Country": "United States",
            "Date": dt.astimezone(timezone.utc).isoformat(),
            "Importance": importance,
            "Actual": _clean_calendar_value(actual_node.get_text(" ", strip=True) if actual_node else ""),
            "Forecast": _clean_calendar_value(forecast_node.get_text(" ", strip=True) if forecast_node else ""),
            "Previous": _clean_calendar_value(previous_node.get_text(" ", strip=True) if previous_node else ""),
            "Source": "Investing.com calendar",
            "URL": "https://www.investing.com/economic-calendar/",
        })
    return events

def economic_events() -> list[dict]:
    """Load and merge calendar events from all available sources."""
    events: list[dict] = []
    if TE_KEY:
        try:
            today = datetime.now(timezone.utc).date() - timedelta(days=1)
            end = today + timedelta(days=9)
            url = (
                "https://api.tradingeconomics.com/calendar/country/united%20states/"
                f"{today.isoformat()}/{end.isoformat()}"
            )
            params = {"c": TE_KEY, "importance": 1, "values": "true", "f": "json"}
            response = requests.get(url, params=params, timeout=25)
            response.raise_for_status()
            data = response.json()
            if isinstance(data, list):
                for item in data:
                    item.setdefault("Source", "Trading Economics")
                events.extend(data)
        except Exception as exc:
            log.warning("Trading Economics failed: %s", exc)

    # Do not depend on one provider: merge several independent calendars.
    source_results = {
        "FairEconomy": fetch_faireconomy_events(),
        "TradingView": fetch_tradingview_events(),
        "Investing.com": fetch_investing_events(),
    }
    for source_name, source_events in source_results.items():
        log.info("Calendar source %s returned %s events", source_name, len(source_events))
        events.extend(source_events)

    unique: dict[tuple[str, str], dict] = {}
    for event in events:
        try:
            dt = parse_dt(str(event.get("Date", ""))).replace(second=0, microsecond=0)
        except Exception:
            continue
        title = str(event.get("Event") or event.get("Category") or "").strip()
        if not title:
            continue
        key = (title.lower(), dt.isoformat())
        current = unique.get(key)
        # Prefer the copy containing actual/forecast/previous values.
        score = sum(bool(event.get(x) not in (None, "")) for x in ("Actual", "Forecast", "Previous"))
        current_score = sum(bool(current and current.get(x) not in (None, "")) for x in ("Actual", "Forecast", "Previous"))
        if current is None or score > current_score:
            event["Date"] = dt.isoformat()
            unique[key] = event
    result = sorted(unique.values(), key=lambda e: e.get("Date", ""))
    log.info("Economic calendar loaded %s events (%s relevant)", len(result), sum(event_relevant(e) for e in result))
    return result

def event_relevant(event: dict) -> bool:
    text = f"{event.get('Event','')} {event.get('Category','')}".lower()
    # Medium-impact releases are included when they are directly relevant to USD/XAU,
    # so S&P Global PMI is not silently discarded.
    return int(event.get("Importance", 0) or 0) >= 2 and any(w in text for w in HIGH_IMPACT_WORDS)


def value_num(event: dict, field: str) -> Optional[float]:
    direct = event.get(field + "Value")
    if isinstance(direct, (int, float)):
        return float(direct)
    raw = str(event.get(field, "")).replace(",", "").strip()
    mult = 1.0
    if raw.endswith("K"):
        mult, raw = 1_000.0, raw[:-1]
    elif raw.endswith("M"):
        mult, raw = 1_000_000.0, raw[:-1]
    elif raw.endswith("B"):
        mult, raw = 1_000_000_000.0, raw[:-1]
    raw = raw.replace("%", "")
    try:
        return float(raw) * mult
    except ValueError:
        return None


def news_direction(event: dict) -> tuple[str, str]:
    actual = value_num(event, "Actual")
    forecast = value_num(event, "Forecast")
    title = str(event.get("Event", "")).lower()
    if actual is None or forecast is None or forecast == 0:
        return "neutral", "нет достаточных числовых данных"

    surprise = (actual - forecast) / abs(forecast)
    if abs(surprise) < 0.02:
        return "neutral", "факт близок к прогнозу"

    lower_is_usd_positive = any(k in title for k in ("unemployment", "jobless", "claims"))
    usd_positive = surprise < 0 if lower_is_usd_positive else surprise > 0

    if usd_positive:
        return "bearish_gold", "данные сильнее ожиданий поддерживают USD и могут давить на золото"
    return "bullish_gold", "данные слабее ожиданий могут ослаблять USD и поддерживать золото"


def get_news_context() -> NewsContext:
    now = datetime.now(timezone.utc)
    events = [e for e in economic_events() if event_relevant(e)]
    upcoming, recent = [], []
    blocked = False
    biases = []
    title = "Нет важных новостей рядом"
    explanation = "Сигнал оценивается главным образом по цене."

    for e in events:
        dt = parse_dt(e["Date"])
        mins = (dt - now).total_seconds() / 60
        item = {**e, "_dt": dt}
        if 0 <= mins <= 360:
            upcoming.append(item)
        if -180 <= mins < 0:
            recent.append(item)
        if 0 <= mins <= NEWS_BLOCK_BEFORE:
            blocked = True
            title = e.get("Event", "Важная новость США")
            explanation = f"До новости около {int(mins)} мин. Новый сигнал заблокирован."
        if -NEWS_CONFIRM_AFTER <= mins < 0:
            blocked = True
            title = e.get("Event", "Важная новость США")
            explanation = "Новость только что вышла. Бот ждёт подтверждение закрытием H1."

    for e in recent:
        bias, reason = news_direction(e)
        biases.append(bias)
        if bias != "neutral":
            title = e.get("Event", "Новость США")
            explanation = reason

    bull = biases.count("bullish_gold")
    bear = biases.count("bearish_gold")
    bias = "bullish_gold" if bull > bear else "bearish_gold" if bear > bull else "neutral"
    return NewsContext(blocked, bias, title, explanation, upcoming, recent)


def pivot_highs(series: pd.Series, left: int = 3, right: int = 3) -> pd.Series:
    flags = pd.Series(False, index=series.index)
    for i in range(left, len(series) - right):
        window = series.iloc[i-left:i+right+1]
        if series.iloc[i] == window.max():
            flags.iloc[i] = True
    return flags


def pivot_lows(series: pd.Series, left: int = 3, right: int = 3) -> pd.Series:
    flags = pd.Series(False, index=series.index)
    for i in range(left, len(series) - right):
        window = series.iloc[i-left:i+right+1]
        if series.iloc[i] == window.min():
            flags.iloc[i] = True
    return flags


def latest_zone(df: pd.DataFrame, bullish: bool, lookback: int = 40) -> Optional[tuple[float, float]]:
    part = df.tail(lookback)
    for i in range(len(part) - 2, 1, -1):
        candle = part.iloc[i]
        nxt = part.iloc[i + 1]
        if bullish and candle["close"] < candle["open"] and nxt["close"] > candle["high"]:
            return float(candle["low"]), float(candle["high"])
        if not bullish and candle["close"] > candle["open"] and nxt["close"] < candle["low"]:
            return float(candle["low"]), float(candle["high"])
    return None


def latest_fvg(df: pd.DataFrame, bullish: bool, lookback: int = 50) -> Optional[tuple[float, float]]:
    part = df.tail(lookback)
    for i in range(len(part) - 1, 1, -1):
        first = part.iloc[i - 2]
        third = part.iloc[i]
        if bullish and third["low"] > first["high"]:
            return float(first["high"]), float(third["low"])
        if not bullish and third["high"] < first["low"]:
            return float(third["high"]), float(first["low"])
    return None


def analyze_smc(df: pd.DataFrame) -> SMCContext:
    part = df.tail(max(SMC_LOOKBACK, 30)).copy()
    highs = pivot_highs(part["high"])
    lows = pivot_lows(part["low"])
    swing_highs = part.loc[highs, "high"]
    swing_lows = part.loc[lows, "low"]

    last = part.iloc[-1]
    prev = part.iloc[-2]
    prev_high = float(swing_highs.iloc[-1]) if len(swing_highs) else float(part["high"].iloc[:-1].max())
    prev_low = float(swing_lows.iloc[-1]) if len(swing_lows) else float(part["low"].iloc[:-1].min())

    bullish_bos = float(last["close"]) > prev_high
    bearish_bos = float(last["close"]) < prev_low

    recent_trend_up = part["close"].iloc[-10:-1].mean() > part["close"].iloc[-20:-10].mean()
    bullish_choch = (not recent_trend_up) and bullish_bos
    bearish_choch = recent_trend_up and bearish_bos

    bullish_sweep = float(last["low"]) < prev_low and float(last["close"]) > prev_low
    bearish_sweep = float(last["high"]) > prev_high and float(last["close"]) < prev_high

    bullish_fvg = latest_fvg(part, True)
    bearish_fvg = latest_fvg(part, False)
    bullish_ob = latest_zone(part, True)
    bearish_ob = latest_zone(part, False)

    summary = []
    if bullish_bos:
        summary.append("BOS вверх: цена закрылась выше предыдущего swing high")
    if bearish_bos:
        summary.append("BOS вниз: цена закрылась ниже предыдущего swing low")
    if bullish_choch:
        summary.append("CHoCH вверх: возможная смена медвежьей структуры")
    if bearish_choch:
        summary.append("CHoCH вниз: возможная смена бычьей структуры")
    if bullish_sweep:
        summary.append("снята ликвидность под минимумом с возвратом выше")
    if bearish_sweep:
        summary.append("снята ликвидность над максимумом с возвратом ниже")
    if bullish_ob:
        summary.append(f"бычий Order Block {bullish_ob[0]:.2f}–{bullish_ob[1]:.2f}")
    if bearish_ob:
        summary.append(f"медвежий Order Block {bearish_ob[0]:.2f}–{bearish_ob[1]:.2f}")
    if bullish_fvg:
        summary.append(f"бычий FVG {bullish_fvg[0]:.2f}–{bullish_fvg[1]:.2f}")
    if bearish_fvg:
        summary.append(f"медвежий FVG {bearish_fvg[0]:.2f}–{bearish_fvg[1]:.2f}")

    return SMCContext(
        bullish_bos, bearish_bos, bullish_choch, bearish_choch,
        bullish_sweep, bearish_sweep, bullish_fvg, bearish_fvg,
        bullish_ob, bearish_ob, summary
    )


def price_in_zone(price: float, zone: Optional[tuple[float, float]], tolerance: float) -> bool:
    if not zone:
        return False
    return zone[0] - tolerance <= price <= zone[1] + tolerance


def _recent_swing(df: pd.DataFrame, side: str, lookback: int = 12) -> float:
    part = df.tail(lookback)
    return float(part["low"].min() if side == "BUY" else part["high"].max())


def _points(distance: float) -> int:
    return int(round(abs(distance) / max(POINT_SIZE, 1e-9)))


def build_signal(
    m15: pd.DataFrame,
    m30: pd.DataFrame,
    h1: pd.DataFrame,
    h4: pd.DataFrame,
    d1: pd.DataFrame,
    news: NewsContext,
    relaxed: bool = False,
) -> Optional[Signal]:
    """Multi-timeframe signal.

    D1/H4/H1 define direction and market structure. M30/M15 are used only
    for a fresh entry trigger, so a delayed user is not invited into an old move.
    """
    a15, a30, a, b, d = m15.iloc[-1], m30.iloc[-1], h1.iloc[-1], h4.iloc[-1], d1.iloc[-1]
    price = float(a15["close"])
    unit = float(a["atr"])
    entry_atr = float(a15["atr"])
    fib_low, fib_high = swing_range(h1)
    span = fib_high - fib_low
    if span <= 0 or not all(math.isfinite(x) and x > 0 for x in (unit, entry_atr)):
        return None

    smc = analyze_smc(h1)
    bull_score = bear_score = 0
    bull_reasons, bear_reasons = [], []
    bull_strategies, bear_strategies = [], []

    # 1) Higher-timeframe trend alignment.
    if d["close"] > d["ema50"] > d["ema200"]:
        bull_score += 2; bull_reasons.append("D1: основной тренд вверх"); bull_strategies.append("Multi-Timeframe Trend D1/H4/H1")
    elif d["close"] < d["ema50"] < d["ema200"]:
        bear_score += 2; bear_reasons.append("D1: основной тренд вниз"); bear_strategies.append("Multi-Timeframe Trend D1/H4/H1")

    if b["close"] > b["ema50"] > b["ema200"]:
        bull_score += 2; bull_reasons.append("H4 выше EMA50/EMA200"); bull_strategies.append("EMA Trend Following")
    elif b["close"] < b["ema50"] < b["ema200"]:
        bear_score += 2; bear_reasons.append("H4 ниже EMA50/EMA200"); bear_strategies.append("EMA Trend Following")

    if a["close"] > a["ema20"] > a["ema50"]:
        bull_score += 2; bull_reasons.append("H1 сохраняет бычью структуру EMA20/EMA50"); bull_strategies.append("H1 EMA Pullback")
    elif a["close"] < a["ema20"] < a["ema50"]:
        bear_score += 2; bear_reasons.append("H1 сохраняет медвежью структуру EMA20/EMA50"); bear_strategies.append("H1 EMA Pullback")

    # 2) Momentum and trend strength.
    if a["macd"] > a["macd_signal"] and a["rsi"] >= 50:
        bull_score += 1; bull_reasons.append("H1 MACD и RSI подтверждают импульс вверх"); bull_strategies.append("MACD + RSI Momentum")
    if a["macd"] < a["macd_signal"] and a["rsi"] <= 50:
        bear_score += 1; bear_reasons.append("H1 MACD и RSI подтверждают импульс вниз"); bear_strategies.append("MACD + RSI Momentum")
    if float(b["adx"]) >= 22:
        (bull_reasons if bull_score >= bear_score else bear_reasons).append(f"H4 ADX {b['adx']:.0f}: тренд имеет силу")

    # 3) Fibonacci pullback on H1.
    bull_fib_zone = (fib_high - 0.618 * span, fib_high - 0.382 * span)
    bear_fib_zone = (fib_low + 0.382 * span, fib_low + 0.618 * span)
    if price_in_zone(price, bull_fib_zone, unit * 0.12):
        bull_score += 2; bull_reasons.append("цена в зоне Fibonacci 0.382–0.618 для BUY"); bull_strategies.append("Fibonacci Pullback")
    if price_in_zone(price, bear_fib_zone, unit * 0.12):
        bear_score += 2; bear_reasons.append("цена в зоне Fibonacci 0.382–0.618 для SELL"); bear_strategies.append("Fibonacci Pullback")

    # 4) Smart Money structure on H1.
    if smc.bullish_bos or smc.bullish_choch:
        bull_score += 2; bull_reasons.append("H1 BOS/CHoCH подтверждает BUY"); bull_strategies.append("Smart Money BOS/CHoCH")
    if smc.bearish_bos or smc.bearish_choch:
        bear_score += 2; bear_reasons.append("H1 BOS/CHoCH подтверждает SELL"); bear_strategies.append("Smart Money BOS/CHoCH")
    if smc.bullish_sweep:
        bull_score += 2; bull_reasons.append("снята sell-side ликвидность"); bull_strategies.append("Liquidity Sweep Reversal")
    if smc.bearish_sweep:
        bear_score += 2; bear_reasons.append("снята buy-side ликвидность"); bear_strategies.append("Liquidity Sweep Reversal")
    if price_in_zone(price, smc.bullish_ob, unit * 0.20) or price_in_zone(price, smc.bullish_fvg, unit * 0.15):
        bull_score += 1; bull_reasons.append("цена тестирует бычий Order Block/FVG"); bull_strategies.append("Order Block + FVG Retest")
    if price_in_zone(price, smc.bearish_ob, unit * 0.20) or price_in_zone(price, smc.bearish_fvg, unit * 0.15):
        bear_score += 1; bear_reasons.append("цена тестирует медвежий Order Block/FVG"); bear_strategies.append("Order Block + FVG Retest")

    # 5) Breakout/retest and Bollinger squeeze on M30.
    prev30 = m30.iloc[-2]
    high20 = float(m30["high"].shift(1).rolling(20).max().iloc[-1])
    low20 = float(m30["low"].shift(1).rolling(20).min().iloc[-1])
    bb_width_now = float((a30["bb_upper"] - a30["bb_lower"]) / max(a30["close"], 0.01))
    bb_width_avg = float(((m30["bb_upper"] - m30["bb_lower"]) / m30["close"]).tail(30).mean())
    if a30["close"] > high20 and prev30["close"] <= high20:
        bull_score += 2; bull_reasons.append("M30 пробил 20-свечной максимум"); bull_strategies.append("Donchian Breakout + Retest")
    if a30["close"] < low20 and prev30["close"] >= low20:
        bear_score += 2; bear_reasons.append("M30 пробил 20-свечной минимум"); bear_strategies.append("Donchian Breakout + Retest")
    if bb_width_now > bb_width_avg and a30["close"] > a30["bb_upper"]:
        bull_score += 1; bull_reasons.append("M30 Bollinger expansion вверх"); bull_strategies.append("Bollinger Squeeze Breakout")
    if bb_width_now > bb_width_avg and a30["close"] < a30["bb_lower"]:
        bear_score += 1; bear_reasons.append("M30 Bollinger expansion вниз"); bear_strategies.append("Bollinger Squeeze Breakout")

    # 6) Fresh entry trigger on M15/M30. Includes trend continuation, EMA retest,
    # momentum reversal and engulfing candles to produce more executable setups.
    p15 = m15.iloc[-2]
    bull_engulf = a15["close"] > a15["open"] and p15["close"] < p15["open"] and a15["close"] >= p15["open"] and a15["open"] <= p15["close"]
    bear_engulf = a15["close"] < a15["open"] and p15["close"] > p15["open"] and a15["open"] >= p15["close"] and a15["close"] <= p15["open"]
    bull_retest = a15["low"] <= a15["ema20"] <= a15["close"] and a15["close"] > a15["open"]
    bear_retest = a15["high"] >= a15["ema20"] >= a15["close"] and a15["close"] < a15["open"]
    bull_rsi_turn = p15["rsi"] < 45 and a15["rsi"] > p15["rsi"] and a15["macd"] > p15["macd"]
    bear_rsi_turn = p15["rsi"] > 55 and a15["rsi"] < p15["rsi"] and a15["macd"] < p15["macd"]
    bull_trigger = (
        (a15["close"] > a15["ema20"] and a15["macd"] > a15["macd_signal"] and 45 <= a15["rsi"] <= 74 and a30["close"] >= a30["ema20"])
        or (bull_retest and (bull_engulf or bull_rsi_turn) and a30["close"] >= a30["ema50"])
    )
    bear_trigger = (
        (a15["close"] < a15["ema20"] and a15["macd"] < a15["macd_signal"] and 26 <= a15["rsi"] <= 55 and a30["close"] <= a30["ema20"])
        or (bear_retest and (bear_engulf or bear_rsi_turn) and a30["close"] <= a30["ema50"])
    )
    if bull_retest: bull_score += 1; bull_reasons.append("M15: бычий ретест EMA20"); bull_strategies.append("EMA20 Retest Scalp")
    if bear_retest: bear_score += 1; bear_reasons.append("M15: медвежий ретест EMA20"); bear_strategies.append("EMA20 Retest Scalp")
    if bull_engulf: bull_score += 1; bull_reasons.append("M15: бычье поглощение"); bull_strategies.append("Engulfing Price Action")
    if bear_engulf: bear_score += 1; bear_reasons.append("M15: медвежье поглощение"); bear_strategies.append("Engulfing Price Action")
    if bull_rsi_turn: bull_score += 1; bull_reasons.append("M15: RSI/MACD разворачиваются вверх"); bull_strategies.append("RSI-MACD Reversal")
    if bear_rsi_turn: bear_score += 1; bear_reasons.append("M15: RSI/MACD разворачиваются вниз"); bear_strategies.append("RSI-MACD Reversal")
    if bull_trigger:
        bull_score += 3; bull_reasons.append("M15/M30 дали свежий триггер входа BUY"); bull_strategies.append("M15/M30 Entry Timing")
    if bear_trigger:
        bear_score += 3; bear_reasons.append("M15/M30 дали свежий триггер входа SELL"); bear_strategies.append("M15/M30 Entry Timing")

    if news.bias == "bullish_gold":
        bull_score += 1; bull_reasons.append("новостной фон поддерживает золото"); bull_strategies.append("Fundamental News Filter")
    elif news.bias == "bearish_gold":
        bear_score += 1; bear_reasons.append("новостной фон поддерживает доллар"); bear_strategies.append("Fundamental News Filter")
    if news.blocked:
        return None

    side = "BUY" if bull_score > bear_score else "SELL"
    score = max(bull_score, bear_score)
    reasons = bull_reasons if side == "BUY" else bear_reasons
    strategies = bull_strategies if side == "BUY" else bear_strategies
    required_score = RELAXED_SIGNAL_SCORE if relaxed else MIN_SIGNAL_SCORE
    if score < required_score or (side == "BUY" and not bull_trigger) or (side == "SELL" and not bear_trigger):
        return None

    # Require at least one market-structure confirmation, not indicators alone.
    structure_ok = (
        smc.bullish_bos or smc.bullish_choch or smc.bullish_sweep
        or price_in_zone(price, smc.bullish_ob, unit * 0.20)
        or a30["close"] > high20
    ) if side == "BUY" else (
        smc.bearish_bos or smc.bearish_choch or smc.bearish_sweep
        or price_in_zone(price, smc.bearish_ob, unit * 0.20)
        or a30["close"] < low20
    )
    if SMC_REQUIRE_CONFIRMATION and not structure_ok and not relaxed:
        return None

    max_tp_distance = MAX_TP_POINTS * POINT_SIZE
    min_sl_distance = MIN_SL_POINTS * POINT_SIZE
    max_sl_distance = MAX_SL_POINTS * POINT_SIZE
    zone_half = min(max(entry_atr * 0.10, 12 * POINT_SIZE), 35 * POINT_SIZE)
    entry_low, entry_high = price - zone_half, price + zone_half
    mid_entry = (entry_low + entry_high) / 2

    # SL is based on M15 structure plus ATR buffer. If the structure needs a
    # wider stop than policy permits, reject the setup instead of forcing a tiny SL.
    if side == "BUY":
        structural_stop = _recent_swing(m15, "BUY", 12) - max(entry_atr * 0.12, 12 * POINT_SIZE)
        sl_distance = mid_entry - structural_stop
    else:
        structural_stop = _recent_swing(m15, "SELL", 12) + max(entry_atr * 0.12, 12 * POINT_SIZE)
        sl_distance = structural_stop - mid_entry
    sl_distance = max(sl_distance, min_sl_distance)
    if sl_distance > max_sl_distance:
        return None
    stop = mid_entry - sl_distance if side == "BUY" else mid_entry + sl_distance

    # Target is capped at the user's requested 300 points. Do not publish a
    # trade when the cap cannot still provide acceptable R:R.
    tp2_distance = min(max_tp_distance, max(sl_distance * MIN_RR, entry_atr * 1.4))
    if tp2_distance / sl_distance < max(1.35, MIN_RR):
        return None
    tp1_distance = min(tp2_distance * 0.60, max(sl_distance * 1.0, entry_atr * 0.8))
    if side == "BUY":
        tp1, tp2 = mid_entry + tp1_distance, mid_entry + tp2_distance
        invalidation = f"M15 закрывается ниже {stop:.2f} или цена вышла из зоны входа"
    else:
        tp1, tp2 = mid_entry - tp1_distance, mid_entry - tp2_distance
        invalidation = f"M15 закрывается выше {stop:.2f} или цена вышла из зоны входа"

    rr = tp2_distance / sl_distance
    d1_aligned = (side == "BUY" and d["close"] > d["ema50"]) or (side == "SELL" and d["close"] < d["ema50"])
    h4_strong = float(b["adx"]) >= 24
    trade_style = "INTRADAY 4–24 HOURS" if d1_aligned and h4_strong else "SCALP/INTRADAY 1–6 HOURS"
    expected_hold_hours = min(SIGNAL_MAX_HOURS, 24 if trade_style.startswith("INTRADAY") else 6)
    expires_at = (datetime.now(timezone.utc) + timedelta(hours=expected_hold_hours)).isoformat()

    return Signal(
        side=side, score=score, entry_low=entry_low, entry_high=entry_high,
        stop=stop, tp1=tp1, tp2=tp2, rr=rr, invalidation=invalidation,
        reasons=reasons[:10], strategies=list(dict.fromkeys(strategies)),
        price=price, fib_low=fib_low, fib_high=fib_high, news=news, smc=smc,
        trade_style=trade_style, expected_hold_hours=expected_hold_hours,
        expires_at=expires_at, entry_timeframe="M15/M30",
        analysis_timeframes="H1/H4/D1", entry_valid_minutes=ENTRY_VALID_MINUTES,
    )


def _extract_openai_text(payload: dict) -> str:
    text = payload.get("output_text")
    if isinstance(text, str) and text.strip():
        return text.strip()
    parts: list[str] = []
    for item in payload.get("output", []):
        for content in item.get("content", []):
            value = content.get("text")
            if isinstance(value, str):
                parts.append(value)
    return "\n".join(parts).strip()


def openai_json(instructions: str, user_input: str) -> Optional[dict]:
    """Call OpenAI only as a secondary analytical layer. Returns None on any failure."""
    if not OPENAI_ENABLED or not OPENAI_API_KEY:
        return None
    payload = {
        "model": OPENAI_MODEL,
        "instructions": instructions,
        "input": user_input,
        "temperature": 0.1,
        "max_output_tokens": 700,
    }
    try:
        response = requests.post(
            "https://api.openai.com/v1/responses",
            headers={
                "Authorization": f"Bearer {OPENAI_API_KEY}",
                "Content-Type": "application/json",
            },
            json=payload,
            timeout=OPENAI_TIMEOUT,
        )
        response.raise_for_status()
        raw = _extract_openai_text(response.json())
        if not raw:
            return None
        raw = raw.strip().removeprefix("```json").removeprefix("```").removesuffix("```").strip()
        return json.loads(raw)
    except Exception:
        log.exception("OpenAI analysis failed")
        return None


def market_snapshot(df: pd.DataFrame) -> dict:
    row = df.iloc[-1]
    return {
        "time_utc": df.index[-1].isoformat(),
        "close": round(float(row["close"]), 3),
        "ema20": round(float(row["ema20"]), 3),
        "ema50": round(float(row["ema50"]), 3),
        "ema200": round(float(row["ema200"]), 3),
        "rsi": round(float(row["rsi"]), 2),
        "macd": round(float(row["macd"]), 4),
        "macd_signal": round(float(row["macd_signal"]), 4),
        "atr": round(float(row["atr"]), 3),
        "adx": round(float(row["adx"]), 2),
        "bb_upper": round(float(row["bb_upper"]), 3),
        "bb_lower": round(float(row["bb_lower"]), 3),
    }


def ai_validate_signal(signal: Signal, m15: pd.DataFrame, m30: pd.DataFrame, h1: pd.DataFrame, h4: pd.DataFrame, d1: pd.DataFrame) -> dict:
    instructions = (
        "Ты независимый риск-фильтр для XAU/USD. Анализируй только переданные числовые данные, "
        "структуру рынка и подтвержденные новости. Не придумывай цены, факты или новости. "
        "Верни ТОЛЬКО корректный JSON без markdown: "
        '{"verdict":"BUY|SELL|WAIT","confidence":0,"summary":"до 350 символов",'
        '"risks":["..."],"news_conclusion":"до 250 символов"}. '
        "BUY/SELL означает согласие с направлением; WAIT — недостаточно подтверждений."
    )
    data = {
        "symbol": SYMBOL,
        "algorithm_signal": {
            "side": signal.side,
            "score": signal.score,
            "entry": [round(signal.entry_low, 3), round(signal.entry_high, 3)],
            "stop": round(signal.stop, 3),
            "tp1": round(signal.tp1, 3),
            "tp2": round(signal.tp2, 3),
            "rr": round(signal.rr, 2),
            "reasons": signal.reasons,
            "strategies": signal.strategies,
        },
        "M15_entry": market_snapshot(m15),
        "M30_entry": market_snapshot(m30),
        "H1": market_snapshot(h1),
        "H4": market_snapshot(h4),
        "D1": market_snapshot(d1),
        "holding_policy": {
            "style": signal.trade_style,
            "expected_hours": signal.expected_hold_hours,
            "absolute_max_hours": SIGNAL_MAX_HOURS,
        },
        "smart_money": signal.smc.summary,
        "news": {
            "blocked": signal.news.blocked,
            "bias": signal.news.bias,
            "title": signal.news.title,
            "explanation": signal.news.explanation,
        },
    }
    result = openai_json(instructions, json.dumps(data, ensure_ascii=False))
    if not result:
        return {"verdict": "UNAVAILABLE", "confidence": 0, "summary": "OpenAI временно недоступен; использован алгоритмический анализ.", "risks": []}
    verdict = str(result.get("verdict", "WAIT")).upper()
    if verdict not in {"BUY", "SELL", "WAIT"}:
        verdict = "WAIT"
    try:
        confidence = max(0, min(100, int(result.get("confidence", 0))))
    except (TypeError, ValueError):
        confidence = 0
    return {
        "verdict": verdict,
        "confidence": confidence,
        "summary": str(result.get("summary", ""))[:500],
        "risks": [str(x)[:180] for x in result.get("risks", [])[:3]],
        "news_conclusion": str(result.get("news_conclusion", ""))[:350],
    }


def ai_explain_news_item(item: dict) -> Optional[dict]:
    instructions = (
        "Ты анализируешь официальную макроэкономическую публикацию США для трейдера XAU/USD. "
        "Используй только переданный заголовок и текст. Не выдумывай отсутствующие цифры. "
        "Верни ТОЛЬКО JSON: "
        '{"impact":"BULLISH_GOLD|BEARISH_GOLD|NEUTRAL|UNCERTAIN",'
        '"conclusion":"краткий окончательный вывод до 400 символов",'
        '"usd_effect":"до 180 символов","gold_effect":"до 180 символов"}.'
    )
    data = {
        "source": item.get("source"),
        "title": item.get("title"),
        "summary": item.get("summary"),
        "published": item.get("published").isoformat() if item.get("published") else None,
    }
    return openai_json(instructions, json.dumps(data, ensure_ascii=False))

def chart_signal(h1: pd.DataFrame, signal: Signal, path: Path) -> None:
    plot = h1.tail(100).copy()
    plot.index = plot.index.tz_convert(TZ).tz_localize(None)
    renamed = plot.rename(columns={
        "open": "Open", "high": "High", "low": "Low", "close": "Close"
    })

    ap = [
        mpf.make_addplot(plot["ema20"], width=1),
        mpf.make_addplot(plot["ema50"], width=1),
        mpf.make_addplot(plot["ema200"], width=1),
    ]

    fig, axes = mpf.plot(
        renamed,
        type="candle",
        addplot=ap,
        volume=False,
        figsize=(13, 8),
        title=f"{SYMBOL} {signal.side} | ENTRY M15/M30 | ANALYSIS H1/H4/D1",
        ylabel="Price",
        datetime_format="%d %b %H:%M",
        xrotation=15,
        tight_layout=True,
        returnfig=True,
    )
    ax = axes[0]

    # Entry area and trade levels.
    ax.axhspan(signal.entry_low, signal.entry_high, alpha=0.18)
    labelled_levels = [
        (signal.entry_low, "ENTRY LOW"),
        (signal.entry_high, "ENTRY HIGH"),
        (signal.stop, "STOP LOSS"),
        (signal.tp1, "TAKE PROFIT 1"),
        (signal.tp2, "TAKE PROFIT 2"),
    ]
    for level, label in labelled_levels:
        ax.axhline(level, linestyle="--", linewidth=1.2)
        ax.text(
            0.995, level, f" {label}: {level:.2f}",
            transform=ax.get_yaxis_transform(),
            ha="right", va="bottom", fontsize=8,
            bbox=dict(boxstyle="round,pad=0.2", alpha=0.65)
        )

    # Fibonacci levels.
    span = signal.fib_high - signal.fib_low
    for ratio in (0.382, 0.5, 0.618):
        level = signal.fib_low + ratio * span
        ax.axhline(level, linestyle=":", linewidth=0.8)
        ax.text(
            0.01, level, f"FIB {ratio:.3f}  {level:.2f}",
            transform=ax.get_yaxis_transform(),
            ha="left", va="bottom", fontsize=7
        )

    # Smart Money areas.
    zone = signal.smc.bullish_ob if signal.side == "BUY" else signal.smc.bearish_ob
    fvg = signal.smc.bullish_fvg if signal.side == "BUY" else signal.smc.bearish_fvg
    if zone:
        ax.axhspan(zone[0], zone[1], alpha=0.10)
        ax.text(0.02, (zone[0] + zone[1]) / 2, "ORDER BLOCK",
                transform=ax.get_yaxis_transform(), fontsize=8, va="center")
    if fvg:
        ax.axhspan(fvg[0], fvg[1], alpha=0.08)
        ax.text(0.18, (fvg[0] + fvg[1]) / 2, "FAIR VALUE GAP",
                transform=ax.get_yaxis_transform(), fontsize=8, va="center")

    fig.savefig(path, dpi=170, bbox_inches="tight")


def caption(signal: Signal) -> str:
    emoji = "🟢⬆️" if signal.side == "BUY" else "🔴⬇️"
    reasons = "\n".join(f"• {x}" for x in signal.reasons)
    strategies = "\n".join(f"• {x}" for x in signal.strategies)
    news_line = f"{signal.news.title}: {signal.news.explanation}"
    ai_icon = "✅" if signal.ai_verdict == signal.side else "⏸" if signal.ai_verdict == "WAIT" else "⚠️"
    ai_line = html.escape(signal.ai_summary or "Нет комментария")
    return (
        f"{emoji} <b>XAU/USD — {signal.side}</b>\n"
        f"🧭 Анализ направления: {signal.analysis_timeframes}\n"
        f"🎯 Точка входа: {signal.entry_timeframe}\n"
        f"⌛ Формат: {signal.trade_style}; ожидаемо до {signal.expected_hold_hours} ч\n\n"
        f"<b>Зона входа:</b> {signal.entry_low:.2f}–{signal.entry_high:.2f}\n"
        f"<b>Stop Loss:</b> {signal.stop:.2f}\n"
        f"<b>Take Profit 1:</b> {signal.tp1:.2f}\n"
        f"<b>Take Profit 2:</b> {signal.tp2:.2f}\n"
        f"<b>Risk/Reward:</b> 1:{signal.rr:.1f}\n"
        f"<b>TP2:</b> {_points(signal.tp2-signal.price)} пунктов | <b>SL:</b> {_points(signal.price-signal.stop)} пунктов\n"
        f"<b>Сила сигнала:</b> {signal.score}/10+\n\n"
        f"🧠 <b>Стратегия сигнала:</b>\n{strategies}\n\n"
        f"<b>Почему бот дал сигнал:</b>\n{reasons}\n\n"
        f"📰 <b>Новостной фон:</b>\n{news_line}\n\n"
        f"🤖 <b>OpenAI-проверка:</b> {ai_icon} {signal.ai_verdict} ({signal.ai_confidence}%)\n{ai_line}\n\n"
        f"❌ <b>Отмена сценария:</b> {signal.invalidation}\n\n"
        f"⏳ <b>Сигнал для нового входа действует {signal.entry_valid_minutes} минут и только пока цена находится в зоне {signal.entry_low:.2f}–{signal.entry_high:.2f}.</b>\n"
        f"Если цена ушла из зоны — НЕ ВХОДИТЕ и ждите следующий сигнал.\n\n"
        f"⚠️ Алгоритмический сценарий не гарантирует прибыль. Соблюдайте риск-менеджмент."
    )


def clean_html(value: str) -> str:
    return " ".join(BeautifulSoup(value or "", "html.parser").get_text(" ").split())


def entry_datetime(entry) -> datetime:
    parsed = entry.get("published_parsed") or entry.get("updated_parsed")
    if parsed:
        return datetime(*parsed[:6], tzinfo=timezone.utc)
    return datetime.now(timezone.utc)


def official_news_relevant(title: str, summary: str) -> bool:
    text = f"{title} {summary}".lower()
    return any(word in text for word in OFFICIAL_NEWS_KEYWORDS)


def explain_official_news(title: str, summary: str) -> tuple[str, str]:
    text = f"{title} {summary}".lower()

    if any(x in text for x in ("rate hike", "higher interest", "inflation remains elevated",
                               "restrictive policy", "hawkish", "rates remain high")):
        return (
            "🔴 Возможное давление на золото",
            "Более жёсткая политика ФРС обычно поддерживает доходности и доллар, "
            "что может давить на золото. Направление нужно подтвердить движением цены."
        )
    if any(x in text for x in ("rate cut", "lower interest", "disinflation",
                               "inflation eased", "slower inflation", "dovish")):
        return (
            "🟢 Возможная поддержка золота",
            "Более мягкая политика или замедление инфляции может ослаблять доллар "
            "и доходности, что способно поддержать золото."
        )
    if any(x in text for x in ("payroll", "employment situation", "jobs", "unemployment", "wages")):
        return (
            "🟡 Важная новость по рынку труда",
            "Сильный рынок труда может поддержать доллар и давить на золото; "
            "слабые данные могут дать обратный эффект. Бот ждёт реакцию XAU/USD."
        )
    if any(x in text for x in ("consumer price", "producer price", "cpi", "ppi", "pce", "inflation")):
        return (
            "🟡 Важная инфляционная новость",
            "Инфляция выше ожиданий обычно уменьшает вероятность быстрого снижения ставок "
            "и может поддержать доллар. Более слабая инфляция чаще поддерживает золото."
        )
    if any(x in text for x in ("gross domestic product", "gdp", "personal income", "consumption")):
        return (
            "🟡 Важные данные по экономике США",
            "Сильные данные могут поддержать доллар; слабые — повысить ожидания смягчения ФРС "
            "и поддержать золото. Реакция рынка важнее одной цифры."
        )
    return (
        "⚪️ Новость может повлиять на USD и золото",
        "Влияние неоднозначное. Бот не объявляет BUY/SELL только по заголовку "
        "и ждёт подтверждение на H1."
    )


def fetch_official_news(max_age_hours: int | None = None, require_relevance: bool = True) -> list[dict]:
    """Fetch genuine publications directly from official US agency RSS feeds.

    Automatic monitoring uses the strict relevance filter. The manual button can
    request a wider date window and, as a last fallback, show the newest official
    publications even when no keyword matched.
    """
    items: list[dict] = []
    now = datetime.now(timezone.utc)
    hours = OFFICIAL_NEWS_MAX_AGE_HOURS if max_age_hours is None else max_age_hours
    max_age = timedelta(hours=max(1, hours))

    headers = {"User-Agent": "XAU-Signal-Bot/1.0 (+Telegram official-news monitor)"}
    for source, url in OFFICIAL_FEEDS.items():
        try:
            response = requests.get(url, headers=headers, timeout=25)
            response.raise_for_status()
            feed = feedparser.loads(response.content)
            for entry in feed.entries[:30]:
                title = clean_html(entry.get("title", ""))
                summary = clean_html(entry.get("summary", "") or entry.get("description", ""))
                link = entry.get("link", "")
                published = entry_datetime(entry)
                if now - published > max_age or published > now + timedelta(hours=2):
                    continue
                if require_relevance and not official_news_relevant(title, summary):
                    continue
                if not title or not link:
                    continue
                uid = entry.get("id") or entry.get("guid") or link or f"{source}:{title}:{published.isoformat()}"
                items.append({
                    "id": str(uid),
                    "source": source,
                    "title": title,
                    "summary": summary[:800],
                    "link": link,
                    "published": published,
                })
        except Exception:
            log.exception("Official feed failed: %s", source)

    unique = {}
    for item in items:
        unique[item["id"]] = item
    return sorted(unique.values(), key=lambda x: x["published"])


def official_news_post(item: dict) -> str:
    impact, explanation = explain_official_news(item["title"], item["summary"])
    ai = item.get("ai_analysis") or {}
    ai_conclusion = str(ai.get("conclusion", "")).strip()
    ai_block = (f"\n🤖 <b>Итог OpenAI:</b>\n{html.escape(ai_conclusion)}\n" if ai_conclusion else "")
    local = item["published"].astimezone(TZ)
    summary = item["summary"]
    if len(summary) > 500:
        summary = summary[:497].rstrip() + "…"

    return (
        f"📰 <b>ОФИЦИАЛЬНАЯ НОВОСТЬ США</b>\n\n"
        f"<b>{item['title']}</b>\n\n"
        f"{summary}\n\n"
        f"<b>Возможное влияние:</b>\n"
        f"{impact}\n{explanation}\n"
        f"{ai_block}\n"
        f"<b>Источник:</b> {item['source']}\n"
        f"<b>Время Ташкента:</b> {local:%d.%m.%Y %H:%M}\n"
        f'<a href="{item["link"]}">Открыть официальный источник</a>\n\n'
        f"⚠️ Это анализ возможного влияния, а не гарантия направления цены."
    )


async def broadcast_text_to_users(app: Application, text: str) -> int:
    """Send a text post to every configured subscriber."""
    users = load_users()
    sent = 0
    for user_id, profile in users.items():
        if not isinstance(profile, dict) or not profile.get("capital"):
            continue
        try:
            await app.bot.send_message(
                chat_id=int(user_id),
                text=text,
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=False,
            )
            sent += 1
        except Exception as exc:
            log.warning("Could not send text to user %s: %s", user_id, exc)
    return sent


async def scan_official_news(app: Application, manual: bool = False) -> str:
    items = await asyncio.to_thread(fetch_official_news)
    state = load_state()
    seen = set(state.get("seen_official_news", []))
    initialized = bool(state.get("official_news_initialized"))

    if not initialized and not OFFICIAL_NEWS_SEND_EXISTING and not manual:
        seen.update(item["id"] for item in items)
        state["seen_official_news"] = list(seen)[-1000:]
        state["official_news_initialized"] = True
        save_state(state)
        return f"Официальные ленты подключены. Запомнено текущих публикаций: {len(items)}."

    new_items = [item for item in items if item["id"] not in seen]
    sent = 0
    for item in new_items:
        if DRY_RUN and not manual:
            log.info("OFFICIAL NEWS DRY RUN\n%s", official_news_post(item))
        else:
            if OPENAI_ENABLED and OPENAI_API_KEY:
                item["ai_analysis"] = await asyncio.to_thread(ai_explain_news_item, item) or {}
            post = official_news_post(item)
            if CHAT_ID:
                await app.bot.send_message(
                    chat_id=CHAT_ID,
                    text=post,
                    parse_mode=ParseMode.HTML,
                    disable_web_page_preview=False,
                )
            await broadcast_text_to_users(app, post)
        seen.add(item["id"])
        sent += 1

    state["seen_official_news"] = list(seen)[-1000:]
    state["official_news_initialized"] = True
    save_state(state)
    return f"Новых официальных публикаций отправлено: {sent}."


async def officialnews_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    try:
        # 1) Important official publications from the last 24 hours.
        items = await asyncio.to_thread(fetch_official_news, 24, True)
        period_note = "за последние 24 часа"

        # 2) If today is quiet, show important official publications from 7 days.
        if not items:
            items = await asyncio.to_thread(fetch_official_news, 24 * 7, True)
            period_note = "за последние 7 дней"

        # 3) Last fallback: newest genuine publications from official feeds,
        # even when their titles did not match the gold-impact keyword list.
        if not items:
            items = await asyncio.to_thread(fetch_official_news, 24 * 7, False)
            period_note = "последние публикации официальных ведомств США"

        if not items:
            await update.message.reply_text(
                "⚠️ Не удалось получить публикации из официальных лент ФРС, BLS и BEA. "
                "Проверьте подключение Railway и повторите позже."
            )
            return

        selected = items[-3:][::-1]
        await update.message.reply_text(
            f"🏛 Последние официальные новости {period_note}:"
        )
        for item in selected:
            if OPENAI_ENABLED and OPENAI_API_KEY:
                item["ai_analysis"] = await asyncio.to_thread(ai_explain_news_item, item) or {}
            await update.message.reply_text(
                official_news_post(item),
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=False,
            )
    except Exception as exc:
        log.exception("official news command failed")
        await update.message.reply_text(f"Ошибка официальных новостей: {exc}")


def _sqlite_users_db() -> sqlite3.Connection:
    conn = sqlite3.connect(USER_DB_FILE, timeout=30)
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=FULL")
    conn.execute(
        """CREATE TABLE IF NOT EXISTS users (
            user_id TEXT PRIMARY KEY,
            chat_id INTEGER NOT NULL,
            language TEXT NOT NULL DEFAULT 'ru',
            capital REAL NOT NULL DEFAULT 0,
            lot REAL NOT NULL DEFAULT 0.01,
            username TEXT NOT NULL DEFAULT '',
            first_name TEXT NOT NULL DEFAULT '',
            updated_at TEXT NOT NULL DEFAULT ''
        )"""
    )
    return conn


def _postgres_connection():
    if not DATABASE_URL:
        raise RuntimeError("DATABASE_URL is not configured")
    if psycopg is None:
        raise RuntimeError('PostgreSQL driver is missing: install psycopg[binary]')
    conn = psycopg.connect(DATABASE_URL, connect_timeout=15)
    with conn.cursor() as cur:
        cur.execute(
            """CREATE TABLE IF NOT EXISTS users (
                user_id TEXT PRIMARY KEY,
                chat_id BIGINT NOT NULL,
                language TEXT NOT NULL DEFAULT 'ru',
                capital DOUBLE PRECISION NOT NULL DEFAULT 0,
                lot DOUBLE PRECISION NOT NULL DEFAULT 0.01,
                username TEXT NOT NULL DEFAULT '',
                first_name TEXT NOT NULL DEFAULT '',
                updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )"""
        )
    conn.commit()
    return conn


def _read_json_users(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        log.exception("Failed to read users backup from %s", path)
        return {}


def _write_users_backup(users: dict) -> None:
    try:
        tmp = USER_STATE_FILE.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(users, ensure_ascii=False, indent=2), encoding="utf-8")
        tmp.replace(USER_STATE_FILE)
    except Exception:
        log.exception("Failed to write local users backup")


def _load_users_postgres() -> dict:
    with _postgres_connection() as conn:
        with conn.cursor() as cur:
            cur.execute(
                "SELECT user_id, chat_id, language, capital, lot, username, first_name, updated_at FROM users"
            )
            rows = cur.fetchall()
    return {
        str(r[0]): {
            "chat_id": int(r[1]),
            "language": r[2],
            "capital": float(r[3]),
            "lot": float(r[4]),
            "username": r[5] or "",
            "first_name": r[6] or "",
            "updated_at": r[7].isoformat() if hasattr(r[7], "isoformat") else str(r[7]),
        }
        for r in rows
    }


def _load_users_sqlite() -> dict:
    with _sqlite_users_db() as conn:
        rows = conn.execute(
            "SELECT user_id, chat_id, language, capital, lot, username, first_name, updated_at FROM users"
        ).fetchall()
    return {
        str(r[0]): {
            "chat_id": r[1], "language": r[2], "capital": r[3], "lot": r[4],
            "username": r[5], "first_name": r[6], "updated_at": r[7]
        } for r in rows
    }


def load_users() -> dict:
    try:
        if DATABASE_URL:
            users = _load_users_postgres()
            if users:
                return users

            # First PostgreSQL start: migrate existing local SQLite/JSON profiles once.
            migrated = _load_users_sqlite()
            if not migrated:
                migrated = _read_json_users(USER_STATE_FILE) or _read_json_users(LEGACY_USER_STATE_FILE)
            if migrated:
                save_users(migrated)
                log.info("Migrated %s subscriber profiles into PostgreSQL", len(migrated))
                return migrated
            return {}

        users = _load_users_sqlite()
        if users:
            return users
        migrated = _read_json_users(USER_STATE_FILE) or _read_json_users(LEGACY_USER_STATE_FILE)
        if migrated:
            save_users(migrated)
            return migrated
        return {}
    except Exception:
        log.exception("Failed to load primary users database; trying local fallback")
        try:
            return _load_users_sqlite() or _read_json_users(USER_STATE_FILE) or _read_json_users(LEGACY_USER_STATE_FILE)
        except Exception:
            log.exception("Local user fallback also failed")
            return {}


def _save_users_postgres(users: dict) -> None:
    now = datetime.now(timezone.utc)
    with _postgres_connection() as conn:
        with conn.cursor() as cur:
            for user_id, profile in users.items():
                updated = profile.get("updated_at") or now
                cur.execute(
                    """INSERT INTO users
                       (user_id, chat_id, language, capital, lot, username, first_name, updated_at)
                       VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                       ON CONFLICT (user_id) DO UPDATE SET
                         chat_id=EXCLUDED.chat_id, language=EXCLUDED.language, capital=EXCLUDED.capital,
                         lot=EXCLUDED.lot, username=EXCLUDED.username, first_name=EXCLUDED.first_name,
                         updated_at=EXCLUDED.updated_at""",
                    (
                        str(user_id), int(profile.get("chat_id", user_id)),
                        str(profile.get("language", "ru")), float(profile.get("capital", 0)),
                        float(profile.get("lot", 0.01)), str(profile.get("username", "")),
                        str(profile.get("first_name", "")), updated,
                    ),
                )
        conn.commit()


def _save_users_sqlite(users: dict) -> None:
    now = datetime.now(timezone.utc).isoformat()
    with _sqlite_users_db() as conn:
        conn.execute("BEGIN IMMEDIATE")
        for user_id, profile in users.items():
            conn.execute(
                """INSERT INTO users
                   (user_id, chat_id, language, capital, lot, username, first_name, updated_at)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                   ON CONFLICT(user_id) DO UPDATE SET
                     chat_id=excluded.chat_id, language=excluded.language, capital=excluded.capital,
                     lot=excluded.lot, username=excluded.username, first_name=excluded.first_name,
                     updated_at=excluded.updated_at""",
                (
                    str(user_id), int(profile.get("chat_id", user_id)),
                    str(profile.get("language", "ru")), float(profile.get("capital", 0)),
                    float(profile.get("lot", 0.01)), str(profile.get("username", "")),
                    str(profile.get("first_name", "")), str(profile.get("updated_at", now)),
                ),
            )
        conn.commit()


def save_users(users: dict) -> None:
    # PostgreSQL is the durable source of truth when DATABASE_URL exists.
    if DATABASE_URL:
        _save_users_postgres(users)
    else:
        log.warning("DATABASE_URL is absent; subscriber storage is local and may be lost on redeploy")
        _save_users_sqlite(users)
    _write_users_backup(users)

def lot_for_capital(capital: float) -> float:
    if capital < 1000:
        return 0.01
    if capital < 10000:
        return 0.03
    if capital < 25000:
        return 0.05
    if capital < 50000:
        return 0.10
    return 0.20


def user_language(user_id: int) -> str:
    users = load_users()
    return users.get(str(user_id), {}).get("language", "ru")


def localized_caption(signal: Signal, lang: str, capital: float, lot: float) -> str:
    if lang == "uz":
        emoji = "🟢⬆️" if signal.side == "BUY" else "🔴⬇️"
        side = "SOTIB OLISH" if signal.side == "BUY" else "SOTISH"
        reasons = "\n".join(f"• {x}" for x in signal.reasons)
        strategies = "\n".join(f"• {x}" for x in signal.strategies)
        return (
            f"{emoji} <b>XAU/USD — {side}</b>\n"
            f"🧭 Yo‘nalish tahlili: {signal.analysis_timeframes}\n"
            f"🎯 Kirish taymfreymi: {signal.entry_timeframe}\n"
            f"⌛ Format: {signal.trade_style}; taxminan {signal.expected_hold_hours} soatgacha\n\n"
            f"<b>Kirish zonasi:</b> {signal.entry_low:.2f}–{signal.entry_high:.2f}\n"
            f"<b>Stop Loss:</b> {signal.stop:.2f}\n"
            f"<b>Take Profit 1:</b> {signal.tp1:.2f}\n"
            f"<b>Take Profit 2:</b> {signal.tp2:.2f}\n"
            f"<b>Risk/Reward:</b> 1:{signal.rr:.1f}\n"
        f"<b>TP2:</b> {_points(signal.tp2-signal.price)} пунктов | <b>SL:</b> {_points(signal.price-signal.stop)} пунктов\n"
            f"<b>Signal kuchi:</b> {signal.score}/10+\n\n"
            f"👤 <b>Shaxsiy reja:</b>\n"
            f"Kapital: ${capital:,.2f}\n"
            f"Tavsiya etilgan minimal lot: <b>{lot:.2f}</b>\n"
            f"Risk: minimal\n\n"
            f"🧠 <b>Signal strategiyasi:</b>\n{strategies}\n\n"
            f"<b>Nima uchun signal berildi:</b>\n{reasons}\n\n"
            f"📰 <b>Yangiliklar foni:</b>\n"
            f"{signal.news.title}: {signal.news.explanation}\n\n"
            f"❌ <b>Stsenariy bekor bo‘ladi:</b> {signal.invalidation}\n\n"
            f"⏳ <b>Yangi kirish uchun signal {signal.entry_valid_minutes} daqiqa va narx {signal.entry_low:.2f}–{signal.entry_high:.2f} zonasida turguncha amal qiladi.</b>\n"
            f"Narx zonadan chiqsa — SAVDOGA KIRMANG, yangi signalni kuting.\n\n"
            f"⚠️ Bu foyda kafolati emas. Lot hajmi broker shartlari va stop masofasiga qarab farq qilishi mumkin."
        )

    base = caption(signal)
    personal = (
        f"\n\n👤 <b>Персональный план:</b>\n"
        f"Капитал: ${capital:,.2f}\n"
        f"Рекомендованный минимальный лот: <b>{lot:.2f}</b>\n"
        f"Риск: минимальный"
    )
    return base + personal


async def start_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    await update.message.reply_text(
        TEXTS["ru"]["welcome"],
        reply_markup=LANG_KEYBOARD
    )
    return SELECT_LANGUAGE


async def language_choice(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = (update.message.text or "").strip()
    if text in {"O‘zbekcha", "🇺🇿 O‘zbekcha"}:
        lang = "uz"
    else:
        lang = "ru"
    context.user_data["language"] = lang
    await update.message.reply_text(
        TEXTS[lang]["ask_capital"],
        reply_markup=ReplyKeyboardRemove()
    )
    return ENTER_CAPITAL


async def capital_entry(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    lang = context.user_data.get("language", "ru")
    raw = (update.message.text or "").replace(",", ".").replace("$", "").strip()
    try:
        capital = float(raw)
    except ValueError:
        await update.message.reply_text(TEXTS[lang]["bad_capital"])
        return ENTER_CAPITAL

    if not 1 <= capital <= 1_000_000:
        await update.message.reply_text(TEXTS[lang]["bad_capital"])
        return ENTER_CAPITAL

    lot = lot_for_capital(capital)
    users = load_users()
    user_id = str(update.effective_user.id)
    users[user_id] = {
        "language": lang,
        "capital": capital,
        "lot": lot,
        "chat_id": update.effective_chat.id,
        "username": update.effective_user.username or "",
        "first_name": update.effective_user.first_name or "",
        "updated_at": datetime.now(timezone.utc).isoformat(),
    }
    save_users(users)

    await update.message.reply_text(
        TEXTS[lang]["saved"].format(capital=capital, lot=lot),
        reply_markup=menu_for(lang),
    )
    return ConversationHandler.END


async def cancel_setup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    lang = context.user_data.get("language", "ru")
    await update.message.reply_text(
        TEXTS[lang]["cancelled"],
        reply_markup=ReplyKeyboardRemove()
    )
    return ConversationHandler.END


async def profile_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    users = load_users()
    profile = users.get(str(update.effective_user.id))
    if not profile:
        await update.message.reply_text(TEXTS["ru"]["not_configured"])
        return
    lang = profile.get("language", "ru")
    await update.message.reply_text(
        TEXTS[lang]["profile"].format(
            capital=float(profile["capital"]),
            lot=float(profile["lot"])
        )
    )


async def broadcast_personal_signal(app: Application, signal: Signal, chart_path: Path) -> int:
    users = load_users()
    sent = 0
    for profile in users.values():
        chat_id = profile.get("chat_id")
        if not chat_id:
            continue
        lang = profile.get("language", "ru")
        capital = float(profile.get("capital", 0))
        lot = float(profile.get("lot", lot_for_capital(capital)))
        try:
            with chart_path.open("rb") as photo:
                await app.bot.send_photo(
                    chat_id=chat_id,
                    photo=photo,
                    caption=localized_caption(signal, lang, capital, lot),
                    parse_mode=ParseMode.HTML,
                )
            sent += 1
        except Exception:
            log.exception("Failed to send personal signal to %s", chat_id)
    return sent


def load_active_signals() -> list[dict]:
    if not ACTIVE_SIGNALS_FILE.exists():
        return []
    try:
        data = json.loads(ACTIVE_SIGNALS_FILE.read_text(encoding="utf-8"))
        return data if isinstance(data, list) else []
    except Exception:
        return []


def save_active_signals(signals: list[dict]) -> None:
    ACTIVE_SIGNALS_FILE.write_text(
        json.dumps(signals, ensure_ascii=False, indent=2),
        encoding="utf-8"
    )


def register_active_signal(signal: Signal) -> None:
    signals = load_active_signals()
    signal_id = f"{int(datetime.now(timezone.utc).timestamp())}-{signal.side}-{signal.price:.2f}"
    signals.append({
        "id": signal_id,
        "side": signal.side,
        "entry_low": signal.entry_low,
        "entry_high": signal.entry_high,
        "stop": signal.stop,
        "tp1": signal.tp1,
        "tp2": signal.tp2,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "expires_at": signal.expires_at,
        "trade_style": signal.trade_style,
        "expected_hold_hours": signal.expected_hold_hours,
        "status": "active",
        "tp1_hit": False,
        "tp2_hit": False,
        "stop_hit": False,
        "tp1_notified": False,
        "final_notified": False,
    })
    save_active_signals(signals)


def outcome_text(lang: str, outcome: str, signal_data: dict, hit_price: float) -> str:
    side = signal_data["side"]
    entry_mid = (float(signal_data["entry_low"]) + float(signal_data["entry_high"])) / 2
    signed_move = (hit_price - entry_mid) if side == "BUY" else (entry_mid - hit_price)
    result_points = _points(signed_move)

    if lang == "uz":
        if outcome == "tp1":
            headline = "✅ SIGNAL TAKE PROFIT 1 GA YETDI"
            detail = "Birinchi maqsad bajarildi. Qolgan pozitsiya uchun riskni kamaytirish mumkin."
            result_line = f"Natija: +{abs(result_points)} punkt"
        elif outcome == "tp2":
            headline = "🏆 SIGNAL MUVAFFAQIYATLI YAKUNLANDI"
            detail = "Bizning signal Take Profit 2 ga yetdi. Pozitsiya to‘liq yopildi."
            result_line = f"Natija: +{abs(result_points)} punkt"
        elif outcome == "expired":
            headline = "⏳ SIGNAL VAQTI TUGADI"
            detail = "Maqsad yoki Stop Loss ishlamadi. Bozor narxida yopish yoki yangi tahlil kutish kerak."
            result_line = f"Yakuniy narx: {hit_price:.2f}"
        else:
            headline = "❌ SIGNAL STOP LOSS BILAN YAKUNLANDI"
            detail = "Signal Stop Loss oldi. Risk oldindan cheklangan edi; keyingi tasdiqlangan signalni kuting."
            result_line = f"Natija: -{abs(result_points)} punkt"
        return (
            f"{headline}\n\n"
            f"Yo‘nalish: {side}\n"
            f"Kirish zonasi: {signal_data['entry_low']:.2f}–{signal_data['entry_high']:.2f}\n"
            f"Hisobiy kirish: {entry_mid:.2f}\n"
            f"Chiqish zonasi/narxi: {hit_price:.2f}\n"
            f"TP1: {signal_data['tp1']:.2f}\n"
            f"TP2: {signal_data['tp2']:.2f}\n"
            f"Stop Loss: {signal_data['stop']:.2f}\n"
            f"{result_line}\n\n"
            f"{detail}\n"
            f"⚠️ Har bir signal foyda kafolati emas."
        )

    if outcome == "tp1":
        headline = "✅ СИГНАЛ ДОШЁЛ ДО TAKE PROFIT 1"
        detail = "Первая цель достигнута. Для оставшейся части позиции можно уменьшить риск."
        result_line = f"Результат: +{abs(result_points)} пунктов"
    elif outcome == "tp2":
        headline = "🏆 НАШ СИГНАЛ ЗАВЕРШИЛСЯ УСПЕШНО"
        detail = "Цена достигла Take Profit 2. Сигнал полностью завершён."
        result_line = f"Результат: +{abs(result_points)} пунктов"
    elif outcome == "expired":
        headline = "⏳ СРОК СИГНАЛА ЗАВЕРШЁН"
        detail = "Цена не достигла цели или Stop Loss. Следует закрыть по рынку либо дождаться нового анализа."
        result_line = f"Цена завершения: {hit_price:.2f}"
    else:
        headline = "❌ СИГНАЛ ЗАВЕРШИЛСЯ ПО STOP LOSS"
        detail = "Сработал Stop Loss. Риск был заранее ограничен; ждём следующий подтверждённый сигнал."
        result_line = f"Результат: -{abs(result_points)} пунктов"

    return (
        f"{headline}\n\n"
        f"Направление: {side}\n"
        f"Зона входа: {signal_data['entry_low']:.2f}–{signal_data['entry_high']:.2f}\n"
        f"Расчётный вход: {entry_mid:.2f}\n"
        f"Зона/цена выхода: {hit_price:.2f}\n"
        f"Take Profit 1: {signal_data['tp1']:.2f}\n"
        f"Take Profit 2: {signal_data['tp2']:.2f}\n"
        f"Stop Loss: {signal_data['stop']:.2f}\n"
        f"{result_line}\n\n"
        f"{detail}\n"
        f"⚠️ Один результат не гарантирует будущую прибыль."
    )


def outcome_chart(h1: pd.DataFrame, signal_data: dict, outcome: str, hit_price: float, path: Path) -> None:
    plot = h1.tail(100).copy()
    plot.index = plot.index.tz_convert(TZ).tz_localize(None)
    renamed = plot.rename(columns={
        "open": "Open", "high": "High", "low": "Low", "close": "Close"
    })

    fig, axes = mpf.plot(
        renamed,
        type="candle",
        volume=False,
        figsize=(13, 8),
        title=f"XAU/USD {signal_data['side']} | {outcome.upper()} HIT",
        ylabel="Price",
        datetime_format="%d %b %H:%M",
        xrotation=15,
        tight_layout=True,
        returnfig=True,
    )
    ax = axes[0]

    ax.axhspan(signal_data["entry_low"], signal_data["entry_high"], alpha=0.18)
    levels = [
        (signal_data["entry_low"], "ENTRY LOW"),
        (signal_data["entry_high"], "ENTRY HIGH"),
        (signal_data["stop"], "STOP LOSS"),
        (signal_data["tp1"], "TAKE PROFIT 1"),
        (signal_data["tp2"], "TAKE PROFIT 2"),
        (hit_price, "HIT PRICE"),
    ]
    for level, label in levels:
        ax.axhline(level, linestyle="--", linewidth=1.2)
        ax.text(
            0.995, level, f" {label}: {level:.2f}",
            transform=ax.get_yaxis_transform(),
            ha="right", va="bottom", fontsize=8,
            bbox=dict(boxstyle="round,pad=0.2", alpha=0.65)
        )

    fig.savefig(path, dpi=170, bbox_inches="tight")


async def broadcast_outcome(app: Application, signal_data: dict, outcome: str, hit_price: float, chart_path: Path) -> int:
    users = load_users()
    sent = 0
    for profile in users.values():
        chat_id = profile.get("chat_id")
        if not chat_id:
            continue
        lang = profile.get("language", "ru")
        try:
            with chart_path.open("rb") as photo:
                await app.bot.send_photo(
                    chat_id=chat_id,
                    photo=photo,
                    caption=outcome_text(lang, outcome, signal_data, hit_price),
                )
            sent += 1
        except Exception:
            log.exception("Failed to send outcome to %s", chat_id)
    return sent


async def monitor_active_signals(app: Application) -> None:
    signals = load_active_signals()
    if not signals:
        return

    h1 = enrich(await asyncio.to_thread(td_candles, "1h", 300))
    latest = h1.iloc[-1]
    high = float(latest["high"])
    low = float(latest["low"])
    current_price = float(latest["close"])
    changed = False

    for s in signals:
        if s.get("status") != "active":
            continue

        outcome = None
        hit_price = None
        expires_raw = s.get("expires_at")
        if expires_raw:
            try:
                expires = datetime.fromisoformat(expires_raw)
                if expires.tzinfo is None:
                    expires = expires.replace(tzinfo=timezone.utc)
                if datetime.now(timezone.utc) >= expires:
                    s["status"] = "expired"
                    outcome = "expired"
                    hit_price = current_price
            except Exception:
                log.warning("Invalid expires_at for signal %s", s.get("id"))

        if outcome != "expired":
            if s["side"] == "BUY":
                if not s.get("tp1_hit") and high >= s["tp1"]:
                    s["tp1_hit"] = True
                    outcome = "tp1"
                    hit_price = s["tp1"]
                if high >= s["tp2"]:
                    s["tp2_hit"] = True
                    s["status"] = "closed_tp"
                    outcome = "tp2"
                    hit_price = s["tp2"]
                elif low <= s["stop"]:
                    s["stop_hit"] = True
                    s["status"] = "closed_sl"
                    outcome = "sl"
                    hit_price = s["stop"]
            else:
                if not s.get("tp1_hit") and low <= s["tp1"]:
                    s["tp1_hit"] = True
                    outcome = "tp1"
                    hit_price = s["tp1"]
                if low <= s["tp2"]:
                    s["tp2_hit"] = True
                    s["status"] = "closed_tp"
                    outcome = "tp2"
                    hit_price = s["tp2"]
                elif high >= s["stop"]:
                    s["stop_hit"] = True
                    s["status"] = "closed_sl"
                    outcome = "sl"
                    hit_price = s["stop"]

        if outcome:
            # TP1 is an intermediate update. TP2, SL and expiry are final updates.
            if outcome == "tp1" and s.get("tp1_notified"):
                continue
            if outcome in {"tp2", "sl", "expired"} and s.get("final_notified"):
                continue
            if outcome == "tp1":
                s["tp1_notified"] = True
            else:
                s["final_notified"] = True
            changed = True
            chart_path = DATA_DIR / f"outcome_{s['id']}_{outcome}.png"
            await asyncio.to_thread(outcome_chart, h1, s, outcome, hit_price, chart_path)

            if CHAT_ID:
                with chart_path.open("rb") as photo:
                    await app.bot.send_photo(
                        chat_id=CHAT_ID,
                        photo=photo,
                        caption=outcome_text("ru", outcome, s, hit_price),
                    )

            count = await broadcast_outcome(app, s, outcome, hit_price, chart_path)
            log.info("Outcome sent: %s to %s users", outcome, count)
            try:
                chart_path.unlink(missing_ok=True)
            except Exception:
                log.exception("Could not remove outcome chart %s", chart_path)

    if changed:
        save_active_signals(signals)


def load_state() -> dict:
    if not STATE_FILE.exists():
        return {}
    try:
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except Exception:
        return {}


def save_state(state: dict) -> None:
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")


def duplicate(signal: Signal) -> bool:
    state = load_state()
    last = state.get("last_signal")
    if not last:
        return False
    dt = datetime.fromisoformat(last["time"])
    too_soon = datetime.now(timezone.utc) - dt < timedelta(hours=COOLDOWN_HOURS)
    same_side = last.get("side") == signal.side
    close_entry = abs(float(last.get("entry", 0)) - signal.price) < max(1.0, abs(signal.price) * 0.001)
    return too_soon and same_side and close_entry


def remember(signal: Signal) -> None:
    save_state({"last_signal": {
        "time": datetime.now(timezone.utc).isoformat(),
        "side": signal.side,
        "entry": signal.price
    }})


async def create_analysis(relaxed: bool = False) -> tuple[Optional[Signal], Optional[pd.DataFrame], NewsContext]:
    # H1/H4/D1 build the scenario; M30/M15 confirm a fresh, executable entry.
    m15 = enrich(await asyncio.to_thread(td_candles, "15min", 500))
    if "live_price" not in m15.attrs:
        raise RuntimeError(f"Live GoldAPI price unavailable: {m15.attrs.get('live_price_error', 'unknown error')}")
    m30 = enrich(await asyncio.to_thread(td_candles, "30min", 500))
    h1 = enrich(await asyncio.to_thread(td_candles, "1h", 500))
    h4 = enrich(await asyncio.to_thread(td_candles, "4h", 500))
    d1 = enrich(await asyncio.to_thread(td_candles, "1day", 500))
    news = await asyncio.to_thread(get_news_context)
    signal = build_signal(m15, m30, h1, h4, d1, news, relaxed=relaxed)
    if signal and OPENAI_ENABLED and OPENAI_API_KEY:
        review = await asyncio.to_thread(ai_validate_signal, signal, m15, m30, h1, h4, d1)
        signal.ai_verdict = review["verdict"]
        signal.ai_confidence = review["confidence"]
        signal.ai_summary = review["summary"]
        if review.get("news_conclusion"):
            signal.ai_summary += " Новостной итог: " + review["news_conclusion"]
        opposite = signal.ai_verdict in {"BUY", "SELL"} and signal.ai_verdict != signal.side
        if AI_BLOCK_OPPOSITE and opposite and signal.ai_confidence >= 65:
            log.warning("Signal blocked by OpenAI: algo=%s ai=%s confidence=%s", signal.side, signal.ai_verdict, signal.ai_confidence)
            return None, m15, news
    elif signal:
        signal.ai_summary = "OPENAI_API_KEY не добавлен; использован алгоритмический анализ."
    return signal, m15, news


def signals_sent_today() -> int:
    state = load_state()
    day = datetime.now(TZ).date().isoformat()
    return int(state.get("daily_counts", {}).get(day, 0))

def increment_daily_signal_count() -> None:
    state = load_state()
    day = datetime.now(TZ).date().isoformat()
    counts = state.setdefault("daily_counts", {})
    counts[day] = int(counts.get(day, 0)) + 1
    # retain only recent entries
    state["daily_counts"] = dict(list(sorted(counts.items()))[-14:])
    save_state(state)

async def publish_signal(app: Application, force: bool = False) -> str:
    # After midday, use a controlled relaxed mode when the daily target has not
    # been reached. It still requires a live M15 trigger, RR and SL <= 50 points.
    now_local = datetime.now(TZ)
    relaxed = signals_sent_today() < DAILY_SIGNAL_TARGET and now_local.hour >= 12
    signal, entry_df, news = await create_analysis(relaxed=relaxed)
    if not signal:
        if news.blocked:
            return f"Сигнал заблокирован: {news.title}. {news.explanation}"
        return "Сейчас подтверждённого сетапа H1/H4/D1 нет."

    if duplicate(signal) and not force:
        return "Похожий сигнал уже публиковался недавно."

    await asyncio.to_thread(chart_signal, entry_df, signal, CHART_FILE)
    text = caption(signal)

    if DRY_RUN:
        log.info("DRY RUN\n%s", text)
        return "DRY_RUN: карточка создана, но не опубликована."

    channel_sent = False
    if CHAT_ID:
        with CHART_FILE.open("rb") as photo:
            await app.bot.send_photo(
                chat_id=CHAT_ID,
                photo=photo,
                caption=text,
                parse_mode=ParseMode.HTML,
            )
        channel_sent = True

    personal_count = await broadcast_personal_signal(app, signal, CHART_FILE)
    register_active_signal(signal)
    remember(signal)
    increment_daily_signal_count()
    return f"Сигнал опубликован. Канал: {channel_sent}. Личных сообщений: {personal_count}. Сегодня: {signals_sent_today()}/{DAILY_SIGNAL_TARGET}."


def build_market_preview(m15: pd.DataFrame, m30: pd.DataFrame, h1: pd.DataFrame, h4: pd.DataFrame) -> dict:
    a15, a30, a1, a4 = m15.iloc[-1], m30.iloc[-1], h1.iloc[-1], h4.iloc[-1]
    price = float(a15["close"])
    bull_votes = sum([a15["close"] > a15["ema20"], a30["close"] > a30["ema20"], a1["close"] > a1["ema50"], a4["close"] > a4["ema50"]])
    side = "BUY" if bull_votes >= 3 else "SELL" if bull_votes <= 1 else "WAIT"
    unit = POINT_SIZE
    zone_half = min(10, MAX_SL_POINTS // 3) * unit
    if side == "BUY":
        anchor = min(price, float(a15["ema20"]))
        zone = (anchor-zone_half, anchor+zone_half)
        missing = []
        if not (a15["close"] > a15["ema20"]): missing.append("закрытие M15 выше EMA20")
        if not (a15["macd"] > a15["macd_signal"]): missing.append("бычье пересечение MACD")
        if not (45 <= a15["rsi"] <= 70): missing.append("RSI в рабочем диапазоне 45–70")
        trigger = "бычья свеча M15 и удержание выше зоны"
    elif side == "SELL":
        anchor = max(price, float(a15["ema20"]))
        zone = (anchor-zone_half, anchor+zone_half)
        missing = []
        if not (a15["close"] < a15["ema20"]): missing.append("закрытие M15 ниже EMA20")
        if not (a15["macd"] < a15["macd_signal"]): missing.append("медвежье пересечение MACD")
        if not (30 <= a15["rsi"] <= 55): missing.append("RSI в рабочем диапазоне 30–55")
        trigger = "медвежья свеча M15 и удержание ниже зоны"
    else:
        anchor = float(a15["ema20"])
        zone = (anchor-zone_half, anchor+zone_half)
        missing = ["совпадение направления M15, M30, H1 и H4", "импульс MACD/RSI"]
        trigger = "дождаться выхода из боковика и ретеста"
    return {"price": price, "side": side, "zone_low": zone[0], "zone_high": zone[1], "missing": missing or ["финальное закрытие подтверждающей свечи M15"], "trigger": trigger}

async def analysis_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Show a live watchlist preview, never a manual trade command.

    Confirmed signals are broadcast automatically to every saved subscriber.
    The button only explains the likely direction/zone and missing confirmation.
    """
    lang = user_language(update.effective_user.id) if update.effective_user else "ru"
    try:
        m15 = enrich(await asyncio.to_thread(td_candles, "15min", 250))
        m30 = enrich(await asyncio.to_thread(td_candles, "30min", 250))
        h1 = enrich(await asyncio.to_thread(td_candles, "1h", 250))
        h4 = enrich(await asyncio.to_thread(td_candles, "4h", 250))
        if "live_price" not in m15.attrs:
            raise RuntimeError(m15.attrs.get("live_price_error", "GoldAPI price not validated"))
        preview = build_market_preview(m15, m30, h1, h4)
        missing = "\n".join(f"• {x}" for x in preview["missing"][:4])
        direction = preview["side"]
        if lang == "uz":
            text = (
                "🔎 <b>XAU/USD JONLI TAHLIL — TASDIQLANMAGAN</b>\n\n"
                f"💵 GoldAPI joriy narxi: <b>{preview['price']:.2f}</b>\n"
                f"🧭 Kutilayotgan yo‘nalish: <b>{direction}</b>\n"
                f"📍 Kuzatuv zonasi: <b>{preview['zone_low']:.2f}–{preview['zone_high']:.2f}</b>\n"
                f"🎯 Tasdiqlash triggeri: {preview['trigger']}\n\n"
                f"⏳ Hali yetishmayapti:\n{missing}\n\n"
                "🚫 <b>SIGNAL TASDIQLANMAGAN — SAVDOGA KIRMANG.</b>\n"
                "Tasdiq paydo bo‘lsa, bot barcha obunachilarga avtomatik yuboradi."
            )
        else:
            text = (
                "🔎 <b>XAU/USD — ЖИВОЙ АНАЛИЗ, НЕ ПОДТВЕРЖДЕНО</b>\n\n"
                f"💵 Текущая цена GoldAPI: <b>{preview['price']:.2f}</b>\n"
                f"🧭 Ожидаемое направление: <b>{direction}</b>\n"
                f"📍 Зона наблюдения: <b>{preview['zone_low']:.2f}–{preview['zone_high']:.2f}</b>\n"
                f"🎯 Что подтвердит вход: {preview['trigger']}\n\n"
                f"⏳ Пока не хватает:\n{missing}\n\n"
                "🚫 <b>СИГНАЛ НЕ ПОДТВЕРЖДЁН — СДЕЛКУ НЕ ОТКРЫВАТЬ.</b>\n"
                "Когда подтверждение появится, бот автоматически отправит сигнал всем подписчикам."
            )
        await update.message.reply_text(text, parse_mode=ParseMode.HTML)
    except Exception as exc:
        log.exception("manual analysis failed")
        await update.message.reply_text(f"❌ Не удалось получить живую цену/анализ: {type(exc).__name__}: {exc}")


async def news_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    try:
        all_events = await asyncio.to_thread(economic_events)
        relevant = [e for e in all_events if event_relevant(e)]
        now_local = datetime.now(TZ)
        today = now_local.date()
        tomorrow = today + timedelta(days=1)

        today_events = []
        next_events = []
        for e in relevant:
            try:
                dt_utc = parse_dt(str(e.get("Date", "")))
            except Exception:
                continue
            item = {**e, "_dt": dt_utc}
            local_date = dt_utc.astimezone(TZ).date()
            if local_date == today:
                today_events.append(item)
            elif today < local_date <= tomorrow:
                next_events.append(item)

        def render_event(e: dict) -> str:
            local = e["_dt"].astimezone(TZ)
            actual = e.get("Actual", "—") or "—"
            forecast = e.get("Forecast", "—") or "—"
            previous = e.get("Previous", "—") or "—"
            released = local <= now_local
            icon = "✅" if released and actual != "—" else "⏳" if not released else "⚪️"
            line = (
                f"{icon} {local:%H:%M} — {e.get('Event','')}\n"
                f"   Факт: {actual} | Прогноз: {forecast} | Пред.: {previous}\n"
                f"   Источник: {e.get('Source','Календарь')}"
            )
            if released and actual != "—":
                bias, conclusion = news_direction(e)
                xau = "поддержка золоту" if bias == "bullish_gold" else "давление на золото" if bias == "bearish_gold" else "нейтрально"
                line += f"\n   Вывод XAU/USD: {xau}. {conclusion}"
            return line

        rows = [f"🇺🇸 Важные новости США на {today:%d.%m.%Y} (Ташкент):"]
        if today_events:
            rows.extend(render_event(e) for e in sorted(today_events, key=lambda x: x["_dt"]))
        elif next_events:
            rows.append("Сегодня важных событий не найдено. Ближайшие:")
            rows.extend(render_event(e) for e in sorted(next_events, key=lambda x: x["_dt"])[:8])
        else:
            rows.append(
                "Все подключённые календарные источники проверены, но важных событий США не получено. "
                "Открой Railway → Console и найди строки 'Calendar source ... returned ...'."
            )
        await update.message.reply_text("\n\n".join(rows)[:4000])
    except Exception as exc:
        log.exception("news command failed")
        await update.message.reply_text(f"Ошибка календаря: {exc}")


async def status_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(
        f"✅ Бот запущен\n"
        f"Инструмент: {SYMBOL}\n"
        f"Анализ: H1/H4/D1 | Вход: M15/M30\n"
        f"Стратегии: MTF + EMA Retest + SMC + Fibonacci + Breakout + RSI/MACD + Engulfing + OpenAI\n"
        f"Цель: до {DAILY_SIGNAL_TARGET} качественных сигналов в день (без принудительных входов)\n"
        f"Сегодня отправлено: {signals_sent_today()}\n"
        f"Подписчиков в базе: {len(load_users())}\n"
        f"Цена: GoldAPI live; свечи выровнены по живой XAU/USD цене\n"
        f"Авторассылка: всем подписчикам без нажатия кнопки\n"
        f"Срок сигнала: 4–8 часов или максимум {SIGNAL_MAX_HOURS} часов\n"
        f"Проверка: каждые {SCAN_MINUTES} мин\n"
        f"Stop Loss: {MIN_SL_POINTS}–{MAX_SL_POINTS} пунктов\n"
        f"DRY_RUN: {DRY_RUN}\n"
        f"OpenAI: {'подключён' if OPENAI_ENABLED and OPENAI_API_KEY else 'не подключён'}"
    )


async def testsignal_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Pure Telegram delivery test: no fake market price and no BUY/SELL."""
    try:
        users = load_users()
        saved = len(users)
        live_price, updated = await asyncio.to_thread(goldapi_live_price)
        await update.message.reply_text(
            "🧪 <b>ТЕСТ СИСТЕМЫ — ЭТО НЕ СИГНАЛ</b>\n\n"
            "✅ Telegram-бот отвечает\n"
            f"✅ Живая цена GoldAPI: <b>{live_price:.2f}</b>\n"
            f"✅ Сохранено подписчиков: <b>{saved}</b>\n"
            f"✅ Автопроверка рынка: каждые {SCAN_MINUTES} мин\n"
            f"✅ Максимальный Stop Loss: {MAX_SL_POINTS} пунктов\n\n"
            "Подтверждённый BUY/SELL будет автоматически отправлен всем подписчикам. "
            "Тест не создаёт торговую карточку и не показывает выдуманную точку входа.",
            parse_mode=ParseMode.HTML,
        )
    except Exception as exc:
        log.exception("test signal failed")
        await update.message.reply_text(f"❌ Ошибка теста: {type(exc).__name__}: {exc}")


async def scheduled_scan(app: Application) -> None:
    try:
        result = await publish_signal(app)
        log.info(result)
    except Exception:
        log.exception("scheduled scan failed")


async def post_init(app: Application) -> None:
    scheduler = AsyncIOScheduler(timezone=TZ)
    scheduler.add_job(
        scheduled_scan,
        "interval",
        minutes=SCAN_MINUTES,
        args=[app],
        max_instances=1,
        coalesce=True,
    )
    scheduler.add_job(
        scan_official_news,
        "interval",
        minutes=OFFICIAL_NEWS_SCAN_MINUTES,
        args=[app],
        max_instances=1,
        coalesce=True,
    )
    scheduler.add_job(
        monitor_active_signals,
        "interval",
        minutes=SCAN_MINUTES,
        args=[app],
        max_instances=1,
        coalesce=True,
    )
    scheduler.start()
    app.bot_data["scheduler"] = scheduler
    log.info("Scheduler started")
    asyncio.create_task(scheduled_scan(app))
    asyncio.create_task(monitor_active_signals(app))


async def post_shutdown(app: Application) -> None:
    scheduler = app.bot_data.get("scheduler")
    if scheduler:
        scheduler.shutdown(wait=False)


async def menu_button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    text = (update.message.text or "").strip()
    routes = {
        "📊 Анализ": analysis_cmd,
        "📊 Tahlil": analysis_cmd,
        "📰 Новости": news_cmd,
        "📰 Yangiliklar": news_cmd,
        "✅ Статус": status_cmd,
        "✅ Holat": status_cmd,
        "🧪 Тест-сигнал": testsignal_cmd,
        "🧪 Test-signal": testsignal_cmd,
        "👤 Профиль": profile_cmd,
        "👤 Profil": profile_cmd,
        "🏛 Официальные новости": officialnews_cmd,
        "🏛 Rasmiy yangiliklar": officialnews_cmd,
    }
    if text in {"⚙️ Изменить язык/капитал", "⚙️ Til/kapitalni o‘zgartirish"}:
        await start_cmd(update, context)
        return
    handler = routes.get(text)
    if handler:
        await handler(update, context)



def main() -> None:
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )
    setup_handler = ConversationHandler(
        entry_points=[CommandHandler("start", start_cmd)],
        states={
            SELECT_LANGUAGE: [MessageHandler(filters.TEXT & ~filters.COMMAND, language_choice)],
            ENTER_CAPITAL: [MessageHandler(filters.TEXT & ~filters.COMMAND, capital_entry)],
        },
        fallbacks=[CommandHandler("cancel", cancel_setup)],
    )
    app.add_handler(setup_handler)
    app.add_handler(CommandHandler("profile", profile_cmd))
    app.add_handler(CommandHandler("analysis", analysis_cmd))
    app.add_handler(CommandHandler("news", news_cmd))
    app.add_handler(CommandHandler("status", status_cmd))
    app.add_handler(CommandHandler("testsignal", testsignal_cmd))
    app.add_handler(CommandHandler("officialnews", officialnews_cmd))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, menu_button_handler))
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
