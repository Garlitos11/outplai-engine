"""OutplAI Engine - Live NBA Betting Engine (website edition).

Run:   python outplai_web.py            (opens http://localhost:8000)
Serve: gunicorn outplai_web:application   |   waitress-serve outplai_web:application
Same data + model code as the desktop app; the dashboard is rendered in the browser.
"""
from __future__ import annotations

import difflib
import io
import json
import logging
import math
import os
import queue
import re
import threading
import time
import unicodedata
import webbrowser
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field, replace
from email.utils import parsedate_to_datetime
from datetime import date, datetime, timedelta, timezone
from functools import lru_cache
from types import SimpleNamespace
from typing import Callable, Optional

import numpy as np
import pandas as pd
import requests
from nba_api.stats.endpoints import (leaguedashptstats, leaguedashteamstats, leaguegamelog,
                                     playergamelog, playerindex, scoreboardv2, commonteamroster)
from nba_api.stats.static import players, teams
from scipy.stats import norm

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
log = logging.getLogger("outplai")


NBA_TIMEOUT = 15
NBA_RETRIES = 2
CACHE_TTL = 600
INDEX_TTL = 6 * 3600
LEAGUE_TTL = 1800

WEB_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36",
    "Referer": "https://www.nba.com/",
    "Accept": "application/json",
}
SCOREBOARD_LOOKAHEAD_DAYS = 7
NON_OFFICIAL_PREFIXES = ("001", "003")

HEADSHOT_URLS = (
    "https://cdn.nba.com/headshots/nba/latest/260x190/{pid}.png",
    "https://ak-static.cms.nba.com/resources/prod/3.0/pipeline/gamezip/stats/actionshot/{pid}.png",
)
HEADSHOT_SIZE = 76

# Team logos (PNG) and free live game lines come from ESPN's public endpoints.
LOGO_URL = "https://a.espncdn.com/i/teamlogos/nba/500/{code}.png"
NBA_TO_ESPN_LOGO = {"GSW": "gs", "NYK": "ny", "NOP": "no", "SAS": "sa", "UTA": "utah", "WAS": "wsh"}
ESPN_SCOREBOARD = "https://site.api.espn.com/apis/site/v2/sports/basketball/nba/scoreboard"
ESPN_ABBR_TO_NBA = {"GS": "GSW", "NY": "NYK", "NO": "NOP", "SA": "SAS", "UTAH": "UTA", "WSH": "WAS"}
ESPN_TTL = 45
ESPN_NEWS = "https://site.api.espn.com/apis/site/v2/sports/basketball/nba/news"
ESPN_INJURIES = "https://site.api.espn.com/apis/site/v2/sports/basketball/nba/injuries"
GOOGLE_NEWS = "https://news.google.com/rss/search"
ODDS_REFRESH_MS = 60_000

ODDS_API_KEY = os.environ.get("ODDS_API_KEY", "").strip()
ODDS_BASE = "https://api.the-odds-api.com/v4/sports/basketball_nba"
ODDS_TTL = 300
# Stoiximan (Greece) is not on The Odds API. Betano is the same company (Kaizen Gaming), so Betano comes first, then Pinnacle (the sharp market
# Greek books follow), then other European books, then US books as a fallback when a market (e.g. NBA player props) is not offered elsewhere.
BOOK_PREFERENCE = ("betano_uk", "pinnacle", "betsson", "unibet_eu", "marathonbet", "betclic_fr", "williamhill", "nordicbet", "coolbet", "betfair_ex_eu",
                   "draftkings", "fanduel", "betmgm", "caesars", "betrivers")
ODDS_REGIONS = "uk,eu,us"
PROP_MARKETS = {
    "PTS": "player_points", "REB": "player_rebounds", "AST": "player_assists",
    "FG3M": "player_threes", "PRA": "player_points_rebounds_assists",
    "PR": "player_points_rebounds", "PA": "player_points_assists",
    "RA": "player_rebounds_assists", "STL": "player_steals", "BLK": "player_blocks",
    "STL_BLK": "player_blocks_steals",
}

HOME_COURT_POINTS = 2.5
MARGIN_STD = 12.0
RECENT_SAMPLE = 5
MIN_GAMES_FOR_MODEL = 2
CHART_MAX_BARS = 15
FALLBACK_TO_PREVIOUS_SEASON = True
UI_POLL_MS = 30

PLACEHOLDER_TEXT = "Search player & prop (e.g. Darius Acuff Jr Threes Over 1.5)..."
FORMAT_HELP = ("Use: [Player] [Prop] [Over/Under] [Line]    or    [Player] [O/U] [Line] [Prop]\n"
               "Optional: add  vs BOS  to pick the opponent.\n"
               "Examples:  Darius Acuff Jr Threes Over 1.5   |   Donovan Mitchell O 24.5 PTS")

PROP_MAPPING = {
    "PTS": "PTS", "POINTS": "PTS",
    "REB": "REB", "REBOUNDS": "REB",
    "AST": "AST", "ASSISTS": "AST",
    "PRA": "PRA", "PTS+REB+AST": "PRA", "POINTS+REBOUNDS+ASSISTS": "PRA",
    "PR": "PR", "PTS+REB": "PR", "POINTS+REBOUNDS": "PR",
    "PA": "PA", "PTS+AST": "PA", "POINTS+AST": "PA",
    "RA": "RA", "REB+AST": "RA", "REBOUNDS+ASSISTS": "RA",
    "3PM": "FG3M", "3PT": "FG3M", "THREES": "FG3M", "THREE": "FG3M",
    "THREE POINTERS": "FG3M", "3-POINTERS": "FG3M",
    "STL": "STL", "STEALS": "STL",
    "BLK": "BLK", "BLOCKS": "BLK",
    "STL+BLK": "STL_BLK", "STOCKS": "STL_BLK",
    "FTM": "FTM", "FREE THROWS MADE": "FTM", "FREE THROW MADE": "FTM", "FREE THROWS": "FTM", "FT MADE": "FTM", "FREE THROW": "FTM",
    "2PM": "FG2M", "2PT": "FG2M", "2P MADE": "FG2M", "TWOS": "FG2M", "TWO POINTERS": "FG2M", "2-POINTERS": "FG2M", "2 POINTERS MADE": "FG2M",
    "FGA": "FGA", "FG ATTEMPTS": "FGA", "FIELD GOAL ATTEMPTS": "FGA", "SHOT ATTEMPTS": "FGA", "SHOTS": "FGA",
}
PROP_SHORT = {"PTS": "PTS", "REB": "REB", "AST": "AST", "STL": "STL", "BLK": "BLK", "FG3M": "3PM",
              "PR": "PTS+REB", "PA": "PTS+AST", "RA": "REB+AST", "PRA": "PTS+REB+AST",
              "STL_BLK": "STL+BLK", "FTM": "FTM", "FG2M": "2PM", "FGA": "FGA"}
PROP_TITLE = {"PTS": "Points", "REB": "Rebounds", "AST": "Assists", "STL": "Steals", "BLK": "Blocks",
              "FG3M": "Threes", "PR": "Pts + Reb", "PA": "Pts + Ast", "RA": "Reb + Ast",
              "PRA": "Pts + Reb + Ast", "STL_BLK": "Stocks", "FTM": "Free throws made", "FG2M": "2-pointers made",
              "FGA": "FG attempts"}
PILL_KEYS = ["PTS", "REB", "AST", "STL", "BLK", "3PM", "FTM", "2PM", "FGA", "PTS+REB", "PTS+AST", "REB+AST", "PTS+REB+AST"]
PILL_TO_PROP = {k: PROP_MAPPING[k] for k in PILL_KEYS}
BEST_PICK_PROPS = [("PTS", "POINTS"), ("REB", "REBOUNDS"), ("AST", "ASSISTS"),
                   ("PRA", "PRA"), ("FG3M", "3PM")]
POS_STATS = (("PTS", "PTS"), ("REB", "REB"), ("OREB", "Off. reb"), ("AST", "AST"), ("STL", "STL"), ("BLK", "BLK"),
             ("FGA", "FG attempts"), ("FG_PCT", "FG %"), ("FG2M", "2PM"), ("FG3M", "3PM"), ("FG3A", "3PT attempts"), ("FG3_PCT", "3PT %"),
             ("FTM", "Free throws made"), ("FTA", "FT attempts"), ("FT_PCT", "FT %"))
POS_CORE = ("PTS", "REB", "AST", "FG3M")          # the four stats that define a position's overall defence rating
POS_PATTERNS = {"FG_PCT": "{:.1f}%", "FG3_PCT": "{:.1f}%", "FT_PCT": "{:.1f}%"}
GROUP_NAMES = {"G": "Guards", "F": "Forwards", "C": "Centers"}
TEAM_STAT_ROWS = (("PTS", "Points allowed", "{:.1f}"), ("REB", "Rebounds allowed", "{:.1f}"),
                  ("AST", "Assists allowed", "{:.1f}"), ("FG3M", "3PM allowed", "{:.1f}"),
                  ("FG3A", "3PA allowed", "{:.1f}"), ("FG3_PCT", "3P% allowed", "{:.1f}%"),
                  ("FGA", "FG attempts allowed", "{:.1f}"), ("FG2M", "2PM allowed", "{:.1f}"),
                  ("FTM", "Free throws made allowed", "{:.1f}"), ("FTA", "FT attempts allowed", "{:.1f}"), ("FT_PCT", "FT% allowed", "{:.1f}%"),
                  ("OREB", "Off. rebounds allowed", "{:.1f}"), ("STL", "Steals allowed", "{:.1f}"), ("BLK", "Blocks allowed", "{:.1f}"),
                  ("FG_PCT", "FG% allowed", "{:.1f}%"), ("OFF", "Offensive rating", "{:.1f}"), ("DEF", "Defense rating", "{:.1f}"),
                  ("PACE", "Pace", "{:.1f}"))
TEAM_STAT_NAMES = {"PTS": "points", "REB": "rebounds", "AST": "assists", "FG3M": "3PM",
                   "FG3A": "3PA", "FG3_PCT": "3P%", "FG_PCT": "FG%", "FGA": "FG attempts", "FG2M": "2PM", "FTM": "free throws made",
                   "FTA": "FT attempts", "FT_PCT": "FT%", "OREB": "offensive rebounds", "STL": "steals", "BLK": "blocks"}

# (label, NBA measure type, column, higher is better (None = neutral), pattern, is percentage)
TEAM_SECTIONS = (
    ("SCORING & EFFICIENCY", (
        ("Points per game", "Base", "PTS", True, "{:.1f}", False),
        ("FG %", "Base", "FG_PCT", True, "{:.1f}%", True),
        ("3PM", "Base", "FG3M", True, "{:.1f}", False),
        ("3P %", "Base", "FG3_PCT", True, "{:.1f}%", True),
        ("FG attempts", "Base", "FGA", True, "{:.1f}", False),
        ("Free throws made", "Base", "FTM", True, "{:.1f}", False),
        ("FT attempts", "Base", "FTA", True, "{:.1f}", False),
        ("FT %", "Base", "FT_PCT", True, "{:.1f}%", True),
        ("eFG %", "Advanced", "EFG_PCT", True, "{:.1f}%", True),
        ("True shooting %", "Advanced", "TS_PCT", True, "{:.1f}%", True),
        ("Offensive rating", "Advanced", "OFF_RATING", True, "{:.1f}", False))),
    ("PLAYMAKING & REBOUNDING", (
        ("Assists", "Base", "AST", True, "{:.1f}", False),
        ("Assist / turnover", "Advanced", "AST_TO", True, "{:.2f}", False),
        ("Rebounds", "Base", "REB", True, "{:.1f}", False),
        ("Off. rebounds", "Base", "OREB", True, "{:.1f}", False),
        ("Rebound %", "Advanced", "REB_PCT", True, "{:.1f}%", True),
        ("Turnovers", "Base", "TOV", False, "{:.1f}", False),
        ("Turnover %", "Advanced", "TM_TOV_PCT", False, "{:.1f}%", True))),
    ("DEFENSE", (
        ("Defensive rating", "Advanced", "DEF_RATING", False, "{:.1f}", False),
        ("Opp. points", "Opponent", "OPP_PTS", False, "{:.1f}", False),
        ("Opp. FG %", "Opponent", "OPP_FG_PCT", False, "{:.1f}%", True),
        ("Opp. 3P %", "Opponent", "OPP_FG3_PCT", False, "{:.1f}%", True),
        ("Opp. 3PM", "Opponent", "OPP_FG3M", False, "{:.1f}", False),
        ("Opp. FG attempts", "Opponent", "OPP_FGA", False, "{:.1f}", False),
        ("Opp. free throws made", "Opponent", "OPP_FTM", False, "{:.1f}", False),
        ("Opp. FT attempts", "Opponent", "OPP_FTA", False, "{:.1f}", False),
        ("Opp. FT %", "Opponent", "OPP_FT_PCT", False, "{:.1f}%", True),
        ("Opp. rebounds", "Opponent", "OPP_REB", False, "{:.1f}", False),
        ("Opp. assists", "Opponent", "OPP_AST", False, "{:.1f}", False),
        ("Steals", "Base", "STL", True, "{:.1f}", False),
        ("Blocks", "Base", "BLK", True, "{:.1f}", False),
        ("Opp. turnovers", "Opponent", "OPP_TOV", True, "{:.1f}", False))),
    ("PACE & OVERALL", (
        ("Net rating", "Advanced", "NET_RATING", True, "{:+.1f}", False),
        ("Pace", "Advanced", "PACE", None, "{:.1f}", False),
        ("Win %", "Base", "W_PCT", True, "{:.1f}%", True),
        ("Point differential", "Base", "PLUS_MINUS", True, "{:+.1f}", False))),
)
NAV_PAGES = ["Overview", "Matchup", "Player profile", "Analysis", "Player's team", "Player's opponent", "Today's picks", "News", "Games & injuries"]
NAV_LABELS = {"Overview": "📊  Overview", "Matchup": "🛡  Matchup", "Player profile": "👤  Player profile", "Analysis": "🔬  Analysis",
              "Player's team": "🏀  Player's team", "Player's opponent": "⚔  Player's opponent", "Today's picks": "⭐  Today's picks",
              "News": "📰  News", "Games & injuries": "📅  Games & injuries"}
BRAND_FONTS = ("Segoe UI Black", "Arial Black", "Impact", "Bahnschrift SemiBold", "Trebuchet MS")
BRAND_FONT_URL = "https://raw.githubusercontent.com/google/fonts/main/ofl/poppins/Poppins-ExtraBold.ttf"
BRAND_FONT_FILE = os.path.join(os.path.expanduser("~"), ".outplai", "Poppins-ExtraBold.ttf")
SYSTEM_BRAND_FONTS = ("seguibl.ttf", "ariblk.ttf", "impact.ttf", "segoeuib.ttf", "Poppins-ExtraBold.ttf", "Poppins-Bold.ttf", "DejaVuSans-Bold.ttf")

SAMPLE_SIZES = {"L5": 5, "L10": 10, "L15": 15, "SEA": None, "PREV": None, "ALL": None}
HIT_TITLES = {"L5": "LAST 5", "L10": "LAST 10", "L15": "LAST 15", "SEA": "THIS SEASON",
              "PREV": "LAST SEASON", "ALL": "ALL GAMES"}
SPLIT_OPTIONS = ["All games", "Home", "Away"]
MINUTES_OPTIONS = {"Any minutes": 0, "25+ min": 25, "30+ min": 30, "35+ min": 35}
REST_OPTIONS = ["Any rest", "Back-to-back", "2+ days rest"]

PROFILE_LAYOUT = [
    ("PTS", "Points"), ("FGM", "FG made"), ("FGA", "FG attempts"), ("FG_PCT", "FG %"), ("FG2M", "2PT made"), ("FG2A", "2PT attempts"),
    ("FG3M", "3PT made"), ("FG3A", "3PT attempts"), ("FG3_PCT", "3PT %"), ("FTM", "FT made"), ("FTA", "FT attempts"), ("FT_PCT", "FT %"),
    ("REB", "Rebounds"), ("REB_CH", "Reb. chances"), ("REB_MISS", "Missed boards"), ("AST", "Assists"), ("POT_AST", "Potential ast."), ("AST_MISS", "Missed assists"),
    ("MIN", "Minutes"), ("TOV", "Turnovers"), ("STL", "Steals"), ("BLK", "Blocks"), ("DRIVES", "Drives"), ("TOUCHES", "Touches"),
    ("CS_FGA", "Catch & shoot FGA"), ("PU_FGA", "Pull-up FGA"), ("OREB", "Off. rebounds"), ("PF", "Fouls"), ("PM", "Plus / minus"), ("AST_PTS", "Pts off assists"),
]
PT_MEASURES = ("Passing", "Rebounding", "Drives", "CatchShoot", "PullUpShot", "Possessions")

_PROP_ALT = "|".join(re.escape(k) for k in sorted(PROP_MAPPING, key=len, reverse=True))
_DIR = r"(?P<dir>OVER|UNDER|HIGHER|LOWER|O|U)"
_LINE = r"(?P<line>\d+(?:\.\d+)?)"
_TAIL = r"(?:\s+(?:VS\.?|@)\s*(?P<opp>[A-Za-z]{3}))?$"
QUERY_PROP_FIRST = re.compile(rf"^(?P<player>.+?)\s+(?P<prop>{_PROP_ALT})\s+{_DIR}\s+{_LINE}{_TAIL}", re.I)
QUERY_LINE_FIRST = re.compile(rf"^(?P<player>.+?)\s+{_DIR}\s+{_LINE}\s+(?P<prop>[A-Za-z0-9+\- ]+?){_TAIL}", re.I)
OVER_WORDS = {"O", "OVER", "HIGHER"}

UI_FONTS = ("Segoe UI", "SF Pro Text", "Helvetica Neue", "Inter", "Roboto", "Arial")

TEAM_COLORS = {
    "ATL": "#e03a3e", "BOS": "#007a33", "BKN": "#ffffff", "CHA": "#1d1160",
    "CHI": "#ce1141", "CLE": "#860038", "DAL": "#00538c", "DEN": "#0e2240",
    "DET": "#c8102e", "GSW": "#1d428a", "HOU": "#ce1141", "IND": "#002d62",
    "LAC": "#c8102e", "LAL": "#552583", "MEM": "#5d76a9", "MIA": "#98002e",
    "MIL": "#00471b", "MIN": "#0c2340", "NOP": "#0c2340", "NYK": "#f58426",
    "OKC": "#007ac1", "ORL": "#0077c0", "PHI": "#006bb6", "PHX": "#1d1160",
    "POR": "#e03a3e", "SAC": "#572b85", "SAS": "#c4ced4", "TOR": "#ce1141",
    "UTA": "#002b5c", "WAS": "#002b65"
}
DEFAULT_ACCENT = "#a855f7"


class Theme:
    BG = "#08080b"
    SURFACE = "#101014"
    SURFACE_RAISED = "#18181f"
    INSET = "#1a1a21"
    GHOST = "#17171d"
    CTRL = "#201b29"
    CHIP = "#34343e"
    BORDER = "#25252e"
    BORDER_STRONG = "#3a3a47"
    ROYAL = "#4c1d95"
    ACCENT = DEFAULT_ACCENT
    ACCENT_HOVER = "#9333ea"
    GOLD = "#f59e0b"
    GOLD_SOFT = "#fbbf24"
    GREEN = "#22c993"
    RED = "#f2453d"
    HIT_BAR = "#19c3a1"
    MISS_BAR = "#e5322e"
    PUSH_BAR = "#94a3b8"
    LINE = "#d4d4d8"
    TEXT = "#f8fafc"
    TEXT_SOFT = "#cbd5e1"
    MUTED = "#9a9aae"
    DIM = "#6b6b80"


STATUS_STYLES = {
    "idle": ("#1c1c25", Theme.MUTED),
    "busy": ("#3b2d05", Theme.GOLD_SOFT),
    "info": ("#241a3d", "#c4b5fd"),
    "ok": ("#06341f", Theme.GREEN),
    "error": ("#4a1020", "#fda4af"),
}
RANK_STYLES = {"good": ("#064e3b", "#34d399"), "mid": ("#451a03", "#fbbf24"), "bad": ("#4c0519", "#f43f5e")}


class QueryError(ValueError): pass
class DataError(RuntimeError): pass


class TTLCache:
    """Thread-safe TTL cache. get_or_compute() runs a loader once even if many threads ask at the same time,
    and remembers a recent failure for neg_ttl seconds so a dead service is not hammered."""
    def __init__(self, ttl: float):
        self._ttl, self._data, self._lock = ttl, {}, threading.Lock()
        self._gates, self._failed = {}, {}
    def get(self, key):
        with self._lock:
            item = self._data.get(key)
            if item and time.monotonic() - item[0] < self._ttl:
                return item[1]
        return None
    def set(self, key, value):
        with self._lock:
            self._data[key] = (time.monotonic(), value)
    def clear(self):
        with self._lock:
            self._data.clear()
            self._failed.clear()
    def get_or_compute(self, key, factory: Callable, neg_ttl: float = 0.0):
        hit = self.get(key)
        if hit is not None: return hit
        with self._lock:
            failed = self._failed.get(key)
            if failed and neg_ttl > 0 and time.monotonic() - failed[0] < neg_ttl: raise failed[1]
            gate = self._gates.setdefault(key, threading.Lock())
        with gate:
            hit = self.get(key)
            if hit is not None: return hit
            try:
                value = factory()
            except Exception as exc:
                if neg_ttl > 0:
                    with self._lock: self._failed[key] = (time.monotonic(), exc)
                raise
            if value is not None: self.set(key, value)
            return value


def safe_call(fn: Callable, default, *args):
    """Run fn(*args); on any error log it and return default (used for optional background loads)."""
    try: return fn(*args)
    except Exception as exc:
        log.warning("%s failed: %s", getattr(fn, "__name__", "call"), exc)
        return default


def with_retries(func: Callable, what: str, attempts: int = NBA_RETRIES, base_delay: float = 0.5):
    last = None
    for attempt in range(1, attempts + 1):
        try:
            return func()
        except Exception as exc:
            last = exc
            log.warning("%s failed (%d/%d): %s", what, attempt, attempts, exc)
            if attempt < attempts:
                time.sleep(base_delay * attempt)
    raise DataError(f"The NBA data service is not responding ({what}). Try again in a moment.") from last


def normalize_text(text: str) -> str:
    if not text: return ""
    text = unicodedata.normalize("NFD", text)
    return "".join(c for c in text if unicodedata.category(c) != "Mn").lower()


def fmt(value) -> str:
    if value is None or pd.isna(value): return "–"
    value = float(value)
    return str(int(value)) if value.is_integer() else f"{value:.1f}"


def fmt_signed(value) -> str:
    if value is None or pd.isna(value): return "–"
    return f"{float(value):+.0f}" if float(value).is_integer() else f"{float(value):+.1f}"


def fmt_pct(value) -> str:
    return "–" if value is None or pd.isna(value) else f"{float(value):.1f}%"


def fmt_odds(price: Optional[int]) -> str:
    return "–" if price is None else (f"+{price}" if price > 0 else str(price))


def fmt_point(point: Optional[float]) -> str:
    return "–" if point is None else (f"+{point:g}" if point > 0 else f"{point:g}")


def ordinal(n: int) -> str:
    if 10 <= n % 100 <= 20: return f"{n}th"
    return f"{n}{ {1: 'st', 2: 'nd', 3: 'rd'}.get(n % 10, 'th') }"


def blend(c1: str, c2: str, t: float) -> str:
    try:
        a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
        b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
        return "#%02x%02x%02x" % tuple(round(x + (y - x) * t) for x, y in zip(a, b))
    except Exception:
        return c2


def luminance(color: str) -> float:
    try:
        r, g, b = [int(color[i:i + 2], 16) / 255 for i in (1, 3, 5)]
        return 0.2126 * r + 0.7152 * g + 0.0722 * b
    except Exception:
        return 0.5


def ensure_visible(color: str, min_lum: float = 0.33) -> str:
    """Lighten very dark team colours (navy, near-black) so they stay readable on the dark UI."""
    for i in range(11):
        cand = blend(color, "#ffffff", i / 10)
        if luminance(cand) >= min_lum:
            return cand
    return "#ffffff"


def selected_fill(color: str) -> str:
    """Fill for 'selected' buttons: light team colours (white, silver, orange ...) are darkened so white text stays readable."""
    return blend(color, "#000000", 0.55) if luminance(color) > 0.5 else color


def season_string(start_year: int) -> str:
    return f"{start_year}-{str(start_year + 1)[-2:]}"


def current_season(today: Optional[date] = None) -> str:
    today = today or date.today()
    return season_string(today.year if today.month >= 10 else today.year - 1)


def previous_season(season: str) -> str:
    return season_string(int(season[:4]) - 1)


def year_label(season: str) -> str:
    """'2025-26' -> '2026' (the year the season ends)."""
    return "20" + season[-2:] if season else "–"


def today_eastern() -> date:
    try:
        from zoneinfo import ZoneInfo
        return datetime.now(ZoneInfo("America/New_York")).date()
    except Exception:
        return (datetime.now(timezone.utc) - timedelta(hours=5)).date()


@dataclass(frozen=True)
class PropQuery:
    player: str
    is_over: bool
    line: float
    prop_key: str
    opponent: Optional[str] = None
    @property
    def side(self) -> str: return "Over" if self.is_over else "Under"
    @property
    def label(self) -> str: return PROP_SHORT.get(self.prop_key, self.prop_key)
    @property
    def title(self) -> str: return PROP_TITLE.get(self.prop_key, self.prop_key)


@lru_cache(maxsize=1)
def _team_tables():
    all_teams = teams.get_teams()
    return ({t["abbreviation"]: t["id"] for t in all_teams},
            {t["id"]: t["abbreviation"] for t in all_teams},
            {t["abbreviation"]: t["full_name"] for t in all_teams})


def parse_search_query(text: str) -> PropQuery:
    text = text.strip()
    match = QUERY_PROP_FIRST.match(text) or QUERY_LINE_FIRST.match(text)
    if not match:
        raise QueryError(f"Invalid search format.\n\n{FORMAT_HELP}")
    raw_prop = re.sub(r"\s+", " ", re.sub(r"\s*\+\s*", "+", match["prop"].strip().upper()))
    prop_key = PROP_MAPPING.get(raw_prop)
    if prop_key is None:
        raise QueryError(f"Unknown prop '{raw_prop}'.\n\nSupported: " + ", ".join(PROP_SHORT.values()))
    opponent = match["opp"].upper() if match["opp"] else None
    if opponent and opponent not in _team_tables()[0]:
        raise QueryError(f"'{opponent}' is not an NBA team abbreviation (e.g. BOS, LAL, MIA).")
    return PropQuery(player=match["player"].strip(), is_over=match["dir"].upper() in OVER_WORDS,
                     line=float(match["line"]), prop_key=prop_key, opponent=opponent)


@dataclass(frozen=True)
class PlayerInfo:
    id: int
    name: str
    team_abbr: str
    position: str


@dataclass
class PlayerData:
    df: pd.DataFrame                      # games of the season being analysed
    name: str
    player_id: int
    team_abbr: str
    season: str
    position: str
    prev_df: Optional[pd.DataFrame] = None   # the season before `season` (empty for rookies)
    recent_df: Optional[pd.DataFrame] = None  # `df` + `prev_df` merged, newest first (pads short samples)
    prev_season: str = ""
    def __post_init__(self):
        if self.prev_df is None: self.prev_df = self.df.iloc[0:0].copy()
        if self.recent_df is None: self.recent_df = self.df
        if not self.prev_season: self.prev_season = previous_season(self.season)
    @property
    def is_rookie(self) -> bool: return self.prev_df.empty


_index_cache = TTLCache(INDEX_TTL)


def _s(value) -> str: return value if isinstance(value, str) else ""


def _fetch_player_index() -> list:
    infos = []
    try:
        df = pd.DataFrame()
        for season in (current_season(), previous_season(current_season())):
            try:
                df = playerindex.PlayerIndex(season=season, timeout=NBA_TIMEOUT).get_data_frames()[0]
                if not df.empty: break
            except Exception: continue
        for r in df.to_dict("records"):
            name = f"{_s(r.get('PLAYER_FIRST_NAME'))} {_s(r.get('PLAYER_LAST_NAME'))}".strip()
            if name:
                infos.append(PlayerInfo(int(r["PERSON_ID"]), name, _s(r.get("TEAM_ABBREVIATION")), _s(r.get("POSITION"))))
    except Exception as exc:
        log.warning("Live player index warning (%s); using fallback list", exc)
    if not infos:
        infos = [PlayerInfo(p["id"], p["full_name"], "", "") for p in players.get_players() if p["is_active"]]
    return infos


def load_player_index() -> list:
    return _index_cache.get_or_compute("index", _fetch_player_index)


def _named_index() -> list:
    return _index_cache.get_or_compute("named", lambda: [(normalize_text(p.name), p) for p in load_player_index()])


def find_player(name: str) -> PlayerInfo:
    needle = normalize_text(name).strip()
    named = _named_index()
    exact = [p for n, p in named if n == needle]
    if exact: return exact[0]
    tokens = needle.split()
    pool = [p for n, p in named if n.startswith(needle)] or [p for n, p in named if tokens and all(t in n for t in tokens)]
    if not pool:
        close = difflib.get_close_matches(needle, [n for n, _ in named], n=1, cutoff=0.72)
        pool = [p for n, p in named if close and n == close[0]]
    if not pool: raise DataError(f"No active NBA player found for '{name}'.")
    if len(pool) > 1:
        raise DataError(f"'{name}' matches several players ({', '.join(p.name for p in pool[:5])}). Be more specific.")
    return pool[0]


_gamelog_cache = TTLCache(CACHE_TTL)


def fetch_gamelog(player_id: int, season: str) -> pd.DataFrame:
    df = _gamelog_cache.get_or_compute(
        (player_id, season),
        lambda: with_retries(lambda: playergamelog.PlayerGameLog(player_id=player_id, season=season, timeout=NBA_TIMEOUT).get_data_frames()[0], what="game log"),
        neg_ttl=20)
    return df.copy()


def enrich_gamelog(df: pd.DataFrame) -> pd.DataFrame:
    if df.empty: return df
    df = df.copy()
    df.columns = [c.upper() for c in df.columns]
    dates = pd.to_datetime(df["GAME_DATE"], format="%b %d, %Y", errors="coerce")
    if dates.isna().any():   # league-wide logs use ISO dates (2026-10-28)
        dates = dates.fillna(pd.to_datetime(df["GAME_DATE"], errors="coerce"))
    df["GAME_DATE_DT"] = dates
    df = df.dropna(subset=["GAME_DATE_DT"]).sort_values("GAME_DATE_DT", ascending=False).reset_index(drop=True)
    df["MIN"] = pd.to_numeric(df["MIN"], errors="coerce")
    for col in ["PTS", "REB", "AST", "FG3M", "STL", "BLK"]:
        if col not in df.columns: df[col] = 0.0
        else: df[col] = pd.to_numeric(df[col], errors="coerce").fillna(0.0)
    for col in ["FGM", "FGA", "FG3A", "FTM", "FTA", "OREB", "DREB", "TOV", "PF", "PLUS_MINUS"]:
        df[col] = pd.to_numeric(df[col], errors="coerce") if col in df.columns else float("nan")
    df["FG2M"] = df["FGM"] - df["FG3M"]      # 2-pointers made
    df["FG2A"] = df["FGA"] - df["FG3A"]      # 2-pointers attempted
    df["PRA"] = df["PTS"] + df["REB"] + df["AST"]
    df["PR"] = df["PTS"] + df["REB"]
    df["PA"] = df["PTS"] + df["AST"]
    df["RA"] = df["REB"] + df["AST"]
    df["STL_BLK"] = df["STL"] + df["BLK"]
    parts = df["MATCHUP"].str.split()
    df["TEAM_ABBR"] = parts.str[0]
    df["OPPONENT"] = parts.str[-1]
    df["IS_HOME"] = ~df["MATCHUP"].str.contains("@")
    df["REST_DAYS"] = df["GAME_DATE_DT"].diff(-1).dt.days
    return df


def _safe_logs(player_id: int, season: str) -> pd.DataFrame:
    try:
        return enrich_gamelog(fetch_gamelog(player_id, season))
    except Exception:
        return pd.DataFrame()


def build_player_data(info: PlayerInfo, df: pd.DataFrame, season: str, prev_df: pd.DataFrame, prev_season: str) -> PlayerData:
    df = df.copy()
    df["SEASON_LABEL"] = season
    if prev_df is None or prev_df.empty:
        prev_df = df.iloc[0:0].copy()
        recent = df.copy()
    else:
        prev_df = prev_df.copy()
        prev_df["SEASON_LABEL"] = prev_season
        recent = pd.concat([df, prev_df], ignore_index=True)
        recent = recent.sort_values("GAME_DATE_DT", ascending=False).reset_index(drop=True)
        recent["REST_DAYS"] = recent["GAME_DATE_DT"].diff(-1).dt.days
    return PlayerData(df, info.name, info.id, df.iloc[0]["TEAM_ABBR"], season, info.position, prev_df, recent, prev_season)


def get_player_data(player_name: str) -> PlayerData:
    """Both seasons are fetched in parallel (and cached), so a search costs one round trip instead of two."""
    info = find_player(player_name)
    cur = current_season()
    prev = previous_season(cur)
    with ThreadPoolExecutor(max_workers=2) as pool:
        f_cur, f_prev = pool.submit(_safe_logs, info.id, cur), pool.submit(_safe_logs, info.id, prev)
        df_cur, df_prev = f_cur.result(), f_prev.result()
    if not df_cur.empty:
        return build_player_data(info, df_cur, cur, df_prev, prev)
    if FALLBACK_TO_PREVIOUS_SEASON and not df_prev.empty:
        older = previous_season(prev)
        return build_player_data(info, df_prev, prev, _safe_logs(info.id, older), older)
    raise DataError(f"{info.name} has no recorded games yet.")


@dataclass
class UpcomingGame:
    opponent: str
    is_home: bool
    when_label: str
    status: int
    source: str
    short_date: str = ""
    game_date: Optional[date] = None
    @property
    def is_live(self) -> bool: return self.status == 2


@dataclass
class ScheduleLookup:
    game: Optional[UpcomingGame]
    error: Optional[str] = None


def _next_from_scoreboard(team_abbr: str) -> Optional[UpcomingGame]:
    abbr_to_id, id_to_abbr, _ = _team_tables()
    team_id = abbr_to_id.get(team_abbr)
    if team_id is None: return None
    start = today_eastern()
    for offset in range(SCOREBOARD_LOOKAHEAD_DAYS):
        day = start + timedelta(days=offset)
        try:
            header = scoreboardv2.ScoreboardV2(game_date=day.strftime("%Y-%m-%d"), timeout=8).get_data_frames()[0]
            if header.empty: continue
            mask = (((header["HOME_TEAM_ID"] == team_id) | (header["VISITOR_TEAM_ID"] == team_id))
                    & (header["GAME_STATUS_ID"] != 3)
                    & ~header["GAME_ID"].astype(str).str.startswith(NON_OFFICIAL_PREFIXES))
            mine = header[mask]
            if mine.empty: continue
            row = mine.iloc[0]
            is_home = row["HOME_TEAM_ID"] == team_id
            opp_id = row["VISITOR_TEAM_ID"] if is_home else row["HOME_TEAM_ID"]
            status = int(row["GAME_STATUS_ID"])
            label = "LIVE NOW" if status == 2 else f"{day.strftime('%a, %b %d')} · {str(row['GAME_STATUS_TEXT']).strip()}"
            return UpcomingGame(id_to_abbr.get(opp_id, "TBD"), bool(is_home), label, status, "scoreboard", day.strftime("%b %d"), day)
        except Exception: continue
    return None


def _next_from_espn(team_abbr: str) -> Optional[UpcomingGame]:
    """ESPN's scoreboard is much faster than stats.nba.com, so it is tried first (days fetched in parallel)."""
    start = today_eastern()
    days = [start + timedelta(days=i) for i in range(SCOREBOARD_LOOKAHEAD_DAYS)]
    with ThreadPoolExecutor(max_workers=4) as pool:
        batches = list(pool.map(_espn_events, days))
    for day, events in zip(days, batches):
        for ev in events:
            try:
                if (ev.get("season") or {}).get("type") == 1: continue   # preseason
                comp = (ev.get("competitions") or [{}])[0]
                status = (comp.get("status") or ev.get("status") or {}).get("type", {})
                state = status.get("state") or "pre"
                if state == "post": continue
                comps = comp.get("competitors") or []
                home_c = next(c for c in comps if c.get("homeAway") == "home")
                away_c = next(c for c in comps if c.get("homeAway") == "away")
                h_raw, a_raw = home_c["team"]["abbreviation"], away_c["team"]["abbreviation"]
                home, away = ESPN_ABBR_TO_NBA.get(h_raw, h_raw), ESPN_ABBR_TO_NBA.get(a_raw, a_raw)
            except Exception:
                continue
            if team_abbr not in (home, away): continue
            is_home = home == team_abbr
            detail = str(status.get("shortDetail") or "")
            clock = detail.split(" - ", 1)[-1].strip() if " - " in detail else detail
            label = "LIVE NOW" if state == "in" else f"{day.strftime('%a, %b %d')} · {clock}"
            return UpcomingGame(away if is_home else home, is_home, label, 2 if state == "in" else 1, "espn", day.strftime("%b %d"), day)
    return None


def lookup_next_game(team_abbr: str) -> ScheduleLookup:
    try:
        game = _next_from_espn(team_abbr)
        if game: return ScheduleLookup(game)
    except Exception as exc: log.warning("ESPN schedule lookup failed: %s", exc)
    try:
        game = _next_from_scoreboard(team_abbr)
        if game: return ScheduleLookup(game)
    except Exception as exc: log.warning("Scoreboard lookup failed: %s", exc)
    return ScheduleLookup(None, error="Could not reach the NBA schedule.")


def classify(value, line: float, is_over: bool) -> str:
    if pd.isna(value) or value == line: return "push"
    return "hit" if (value > line) == is_over else "miss"


def hit_rate(values, line: float, is_over: bool):
    results = [classify(v, line, is_over) for v in values]
    hits = results.count("hit")
    decided = hits + results.count("miss")
    return (hits / decided * 100 if decided else 0.0), hits, decided


def implied_probability(mean, std, line: float, is_over: bool = True) -> Optional[float]:
    if pd.isna(mean) or pd.isna(std): return None
    if std == 0:
        if mean > line: return 100.0 if is_over else 0.0
        elif mean < line: return 0.0 if is_over else 100.0
        else: return 50.0
    prob_over = (1 - norm.cdf((line - mean) / std)) * 100
    return prob_over if is_over else 100.0 - prob_over


@dataclass(frozen=True)
class Filters:
    sample: str = "L5"
    split: str = "All games"
    minutes: int = 0
    rest: str = "Any rest"
    h2h_only: bool = False


@dataclass
class View:
    sample: pd.DataFrame
    hit_rate: float
    hits: int
    decided: int
    mean: float
    median: float
    model_prob: Optional[float]
    season_mean: float
    games_total: int


def build_view(player: PlayerData, query: PropQuery, filters: Filters, opponent: Optional[str], adjust: float = 1.0) -> View:
    df, key = player.df, query.prop_key
    # L5/L10/L15 (and ALL) use the padded list so a short season is filled with last season's games.
    if filters.sample == "PREV": out = player.prev_df
    elif filters.sample == "SEA": out = player.df
    else: out = player.recent_df
    if filters.split == "Home": out = out[out["IS_HOME"]]
    elif filters.split == "Away": out = out[~out["IS_HOME"]]
    if filters.minutes: out = out[out["MIN"] >= filters.minutes]
    if filters.rest == "Back-to-back": out = out[out["REST_DAYS"] == 1]
    elif filters.rest == "2+ days rest": out = out[out["REST_DAYS"] >= 3]
    if filters.h2h_only and opponent: out = out[out["OPPONENT"] == opponent]
    n = SAMPLE_SIZES[filters.sample]
    sample = out if n is None else out.head(n)
    values = sample[key]
    hr, hits, decided = hit_rate(values, query.line, query.is_over)
    prob = None
    if len(values.dropna()) >= MIN_GAMES_FOR_MODEL:
        prob = implied_probability(values.mean() * adjust, values.std() * adjust, query.line, query.is_over)
    return View(sample, hr, hits, decided, values.mean() if len(values) else float("nan"),
                values.median() if len(values) else float("nan"), prob, df[key].mean(), len(df))


def suggest_line(df: pd.DataFrame, key: str) -> float:
    if key not in df.columns: return 0.5
    vals = df[key].head(RECENT_SAMPLE).dropna()
    return 0.5 if vals.empty else max(0.5, math.floor(vals.mean()) + 0.5)


@dataclass
class BestPick:
    label: str
    line: float
    probability: float


def find_best_value_line(df: pd.DataFrame, mults: Optional[dict] = None) -> Optional[BestPick]:
    recent = df.head(RECENT_SAMPLE)
    best, best_gap = None, float("inf")
    for code, label in BEST_PICK_PROPS:
        if code not in recent.columns: continue
        series = recent[code].dropna()
        if len(series) < MIN_GAMES_FOR_MODEL: continue
        adj = (mults or {}).get(code, 1.0)
        mean, std = series.mean() * adj, series.std() * adj
        for mult in (0.0, 0.2, -0.2, 0.4):
            line = max(0.5, math.floor(mean + mult * std) + 0.5)
            prob = implied_probability(mean, std, line, True)
            if prob is not None and abs(prob - 45.0) < best_gap:
                best, best_gap = BestPick(label, line, prob), abs(prob - 45.0)
    return best


# ---------------------------------------------------------------- box score + profile helpers
def _n(row, col) -> float:
    try:
        v = row.get(col)
        return float(v) if v is not None and pd.notna(v) else float("nan")
    except Exception:
        return float("nan")


def _ratio(a: float, b: float) -> float:
    if a is None or b is None or math.isnan(a) or math.isnan(b) or b == 0: return float("nan")
    return a / b * 100


def box_score_rows(r, q: PropQuery, val, state: str, date_full: str) -> list:
    """Rows for the detailed hover box score (title / sub / prop / rule / cells)."""
    symbol = {"hit": "✓", "miss": "✗", "push": "–"}[state]
    pts, reb, ast = _n(r, "PTS"), _n(r, "REB"), _n(r, "AST")
    fgm, fga, tpm, tpa = _n(r, "FGM"), _n(r, "FGA"), _n(r, "FG3M"), _n(r, "FG3A")
    ftm, fta = _n(r, "FTM"), _n(r, "FTA")
    fg2m, fg2a = _n(r, "FG2M"), _n(r, "FG2A")
    wl = r.get("WL") if hasattr(r, "get") else None
    result = {"W": "Win", "L": "Loss"}.get(wl, "")
    season = r.get("SEASON_LABEL", "") if hasattr(r, "get") else ""
    diff = (float(val) - q.line) if pd.notna(val) else float("nan")
    efg = _ratio(fgm + 0.5 * tpm, fga)
    ts = _ratio(pts, 2 * (fga + 0.44 * fta)) if not (math.isnan(fga) or math.isnan(fta)) else float("nan")
    shoot = lambda m, a: f"{fmt(m)}/{fmt(a)}  {fmt_pct(_ratio(m, a)).replace('.0%', '%')}"
    sub = "  ·  ".join(x for x in (str(season), result, f"{fmt(_n(r, 'MIN'))} min") if x)
    return [
        ("title", f"{r['MATCHUP']}   ·   {date_full}"),
        ("sub", sub),
        ("prop", f"{q.title}  {fmt(val)}  {symbol}    ({fmt_signed(diff)} vs {q.line:g})", state),
        ("rule",),
        ("cells", [("PTS", fmt(pts)), ("REB", fmt(reb)), ("AST", fmt(ast))]),
        ("cells", [("STL", fmt(_n(r, "STL"))), ("BLK", fmt(_n(r, "BLK"))), ("TOV", fmt(_n(r, "TOV")))]),
        ("cells", [("OREB", fmt(_n(r, "OREB"))), ("DREB", fmt(_n(r, "DREB"))), ("PF", fmt(_n(r, "PF")))]),
        ("cells", [("PRA", fmt(_n(r, "PRA"))), ("P+R", fmt(_n(r, "PR"))), ("P+A", fmt(_n(r, "PA")))]),
        ("rule",),
        ("cells", [("FG", shoot(fgm, fga)), ("3PT", shoot(tpm, tpa)), ("FT", shoot(ftm, fta))]),
        ("cells", [("2PT", shoot(fg2m, fg2a)), ("FGA", fmt(fga)), ("FTM", fmt(ftm))]),
        ("cells", [("+/-", fmt_signed(_n(r, "PLUS_MINUS"))), ("eFG", fmt_pct(efg)), ("TS", fmt_pct(ts))]),
    ]


def make_chart_bars(sample: pd.DataFrame, q: PropQuery, current: str, limit: int = CHART_MAX_BARS) -> list:
    bars = []
    for _, r in sample.head(limit).iloc[::-1].iterrows():
        val = r[q.prop_key] if q.prop_key in r.index else 0.0
        state = classify(val, q.line, q.is_over)
        tag = r["SEASON_LABEL"] if "SEASON_LABEL" in r.index else current
        bars.append(ChartBar(
            value=float(val) if pd.notna(val) else 0.0, text=fmt(val), state=state,
            opp=("" if r["IS_HOME"] else "@") + r["OPPONENT"], date=r["GAME_DATE_DT"].strftime("%b %d"),
            tip=box_score_rows(r, q, val, state, r["GAME_DATE_DT"].strftime("%b %d, %Y")),
            prev=tag != current, season=tag))
    return bars


def build_profile(df: pd.DataFrame, tracking: Optional[dict]) -> dict:
    """Per-game profile tiles: key -> (value text, sub text). `tracking` None = still loading, {} = unavailable."""
    out = {}
    l5 = df.head(5)
    def mean(d, col): return float(d[col].mean()) if col in d.columns and len(d) else float("nan")
    def avg(key, col):
        out[key] = (fmt(mean(df, col)), f"L5 {fmt(mean(l5, col))}")
    def pct(key, made, att):
        a = _ratio(float(df[made].sum()), float(df[att].sum())) if made in df.columns and att in df.columns else float("nan")
        b = _ratio(float(l5[made].sum()), float(l5[att].sum())) if made in l5.columns and att in l5.columns else float("nan")
        out[key] = (fmt_pct(a), f"L5 {fmt_pct(b)}")
    for key, col in (("PTS", "PTS"), ("FGM", "FGM"), ("FGA", "FGA"), ("FG2M", "FG2M"), ("FG2A", "FG2A"), ("FG3M", "FG3M"), ("FG3A", "FG3A"),
                     ("FTM", "FTM"), ("FTA", "FTA"), ("REB", "REB"), ("AST", "AST"),
                     ("MIN", "MIN"), ("TOV", "TOV"), ("STL", "STL"), ("BLK", "BLK"), ("OREB", "OREB"), ("PF", "PF")):
        avg(key, col)
    pct("FG_PCT", "FGM", "FGA")
    pct("FG3_PCT", "FG3M", "FG3A")
    pct("FT_PCT", "FTM", "FTA")
    out["PM"] = (fmt_signed(mean(df, "PLUS_MINUS")), f"L5 {fmt_signed(mean(l5, 'PLUS_MINUS'))}")

    def tk(measure: str, *keys) -> float:
        d = (tracking or {}).get(measure) or {}
        for k in keys:
            v = d.get(k)
            if v is not None and pd.notna(v):
                try: return float(v)
                except (TypeError, ValueError): continue
        return float("nan")
    sub = "loading…" if tracking is None else ("per game" if tracking else "n/a")
    reb_ch, pot = tk("Rebounding", "REB_CHANCES"), tk("Passing", "POTENTIAL_AST")
    out["REB_CH"] = (fmt(reb_ch), sub)
    out["REB_MISS"] = (fmt(reb_ch - mean(df, "REB")), "chances − boards" if tracking else sub)
    out["POT_AST"] = (fmt(pot), sub)
    out["AST_MISS"] = (fmt(pot - mean(df, "AST")), "potential − assists" if tracking else sub)
    out["AST_PTS"] = (fmt(tk("Passing", "AST_PTS_CREATED")), sub)
    out["DRIVES"] = (fmt(tk("Drives", "DRIVES")), sub)
    out["TOUCHES"] = (fmt(tk("Possessions", "TOUCHES")), sub)
    out["CS_FGA"] = (fmt(tk("CatchShoot", "CATCH_SHOOT_FGA")), sub)
    out["PU_FGA"] = (fmt(tk("PullUpShot", "PULL_UP_FGA")), sub)
    return out


# ---------------------------------------------------------------- matchup data
@dataclass
class TeamMetric:
    def_rating: float
    def_rank: int
    pace: float
    pace_rank: int
    net_rating: float
    off_rating: float = float("nan")
    off_rank: int = 15


@dataclass
class MatchupContext:
    opponent: str
    season: str
    pos_group: str
    pos_allowed: dict
    pos_n: int
    team_metrics: dict = field(default_factory=dict)
    pos_all: dict = field(default_factory=dict)       # group -> stat -> (value, rank) allowed by the opponent
    team_allowed: dict = field(default_factory=dict)  # stat -> (value, rank) allowed by the opponent (rank 1 = fewest)


_league_cache = TTLCache(LEAGUE_TTL)


def fetch_team_metrics(season: str) -> dict:
    def load():
        df = leaguedashteamstats.LeagueDashTeamStats(measure_type_detailed_defense="Advanced", per_mode_detailed="PerGame", season=season, timeout=NBA_TIMEOUT).get_data_frames()[0]
        id_to_abbr = _team_tables()[1]
        out = {}
        for r in df.to_dict("records"):
            abbr = id_to_abbr.get(r.get("TEAM_ID"))
            if abbr:
                out[abbr] = TeamMetric(float(r["DEF_RATING"]), int(r["DEF_RATING_RANK"]), float(r["PACE"]), int(r["PACE_RANK"]), float(r["NET_RATING"]),
                                       float(r.get("OFF_RATING", float("nan"))), int(r.get("OFF_RATING_RANK", 15)))
        if not out: raise DataError("no team metrics")
        return out
    try: return _league_cache.get_or_compute(("metrics", season), load, neg_ttl=30)
    except Exception as exc:
        log.warning("Team metrics unavailable: %s", exc)
        return {}


def fetch_team_allowed(season: str) -> dict:
    """What every team allows opponents per game: abbr -> stat -> (value, rank). Rank 1 = allows the fewest."""
    def load():
        df = leaguedashteamstats.LeagueDashTeamStats(measure_type_detailed_defense="Opponent", per_mode_detailed="PerGame", season=season, timeout=NBA_TIMEOUT).get_data_frames()[0]
        id_to_abbr = _team_tables()[1]
        if {"OPP_FGM", "OPP_FG3M"} <= set(df.columns): df["OPP_FG2M"] = pd.to_numeric(df["OPP_FGM"], errors="coerce") - pd.to_numeric(df["OPP_FG3M"], errors="coerce")
        cols = {"PTS": "OPP_PTS", "REB": "OPP_REB", "AST": "OPP_AST", "FG3M": "OPP_FG3M",
                "FG3A": "OPP_FG3A", "FG3_PCT": "OPP_FG3_PCT", "FG_PCT": "OPP_FG_PCT",
                "FGA": "OPP_FGA", "FG2M": "OPP_FG2M", "FTM": "OPP_FTM", "FTA": "OPP_FTA", "FT_PCT": "OPP_FT_PCT",
                "OREB": "OPP_OREB", "STL": "OPP_STL", "BLK": "OPP_BLK"}
        cols = {k: v for k, v in cols.items() if v in df.columns}
        ranks = {k: df[v].rank(method="min", ascending=True).astype(int) for k, v in cols.items()}
        out = {}
        for i, r in df.iterrows():
            abbr = id_to_abbr.get(r.get("TEAM_ID"))
            if not abbr: continue
            row = {}
            for stat, col in cols.items():
                value = float(r[col]) * (100 if stat.endswith("_PCT") else 1)
                row[stat] = (value, int(ranks[stat].loc[i]))
            out[abbr] = row
        if not out: raise DataError("no opponent stats")
        return out
    try: return _league_cache.get_or_compute(("allowed", season), load, neg_ttl=30)
    except Exception as exc:
        log.warning("Team allowed stats unavailable: %s", exc)
        return {}


def fetch_league_player_logs(season: str) -> pd.DataFrame:
    """Every player's game log for the season (one cached, single-flight call shared by everything)."""
    return _league_cache.get_or_compute(
        ("plogs", season),
        lambda: with_retries(lambda: leaguegamelog.LeagueGameLog(season=season, player_or_team_abbreviation="P", timeout=NBA_TIMEOUT).get_data_frames()[0], what="league player logs"),
        neg_ttl=45)


def fetch_team_profile(season: str) -> dict:
    """Full team statistics: abbr -> {'record': (W, L), 'stats': {label: (value, rank, higher_is_better)}}. Rank 1 = best."""
    def load():
        def one(measure):
            try:
                return measure, leaguedashteamstats.LeagueDashTeamStats(measure_type_detailed_defense=measure, per_mode_detailed="PerGame", season=season, timeout=NBA_TIMEOUT).get_data_frames()[0]
            except Exception as exc:
                log.warning("Team stats %s unavailable: %s", measure, exc)
                return measure, None
        with ThreadPoolExecutor(max_workers=3) as pool:
            frames = dict(pool.map(one, ("Base", "Advanced", "Opponent")))
        base = frames.get("Base")
        if base is None or base.empty: raise DataError("no team profile")
        id_to_abbr = _team_tables()[1]
        out = {}
        for r in base.to_dict("records"):
            abbr = id_to_abbr.get(r.get("TEAM_ID"))
            if abbr: out[abbr] = {"record": (int(r.get("W", 0) or 0), int(r.get("L", 0) or 0)), "stats": {}}
        for _, specs in TEAM_SECTIONS:
            for label, measure, col, higher, pattern, is_pct in specs:
                df = frames.get(measure)
                if df is None or col not in df.columns: continue
                series = pd.to_numeric(df[col], errors="coerce")
                scale = 100 if is_pct and series.abs().max() <= 1.5 else 1
                values = series * scale
                ranks = values.rank(method="min", ascending=(higher is False)).fillna(0).astype(int)
                for i in df.index:
                    abbr = id_to_abbr.get(df.at[i, "TEAM_ID"])
                    if abbr in out and pd.notna(values.at[i]):
                        out[abbr]["stats"][label] = (float(values.at[i]), int(ranks.at[i]), higher)
        return out
    try: return _league_cache.get_or_compute(("teamprofile", season), load, neg_ttl=30)
    except Exception as exc:
        log.warning("Team profile unavailable: %s", exc)
        return {}


def compute_position_defense(logs: pd.DataFrame, pos_by_id: dict) -> dict:
    """Per opponent and position group (G / F / C): what that group scores / attempts / draws against the defence, per game, with ranks (1 = allows the fewest)."""
    wanted = ["PTS", "REB", "OREB", "AST", "STL", "BLK", "FGM", "FGA", "FG3M", "FG3A", "FTM", "FTA"]
    df = logs.copy()
    df.columns = [c.upper() for c in df.columns]
    stats = [c for c in wanted if c in df.columns]
    for c in stats: df[c] = pd.to_numeric(df[c], errors="coerce").fillna(0)
    df["POS"] = df["PLAYER_ID"].map(pos_by_id).fillna("").astype(str).str[:1].str.upper()
    df["MIN"] = pd.to_numeric(df["MIN"], errors="coerce").fillna(0)
    df = df[df["POS"].isin(["G", "F", "C"]) & (df["MIN"] >= 5)]
    if df.empty: return {}
    df["OPP"] = df["MATCHUP"].str.split().str[-1]
    per_game = df.groupby(["OPP", "POS", "GAME_ID"])[stats].sum().reset_index()
    avg = per_game.groupby(["OPP", "POS"])[stats].mean()
    def ratio(a, b): return (avg[a] / avg[b].where(avg[b] > 0)) * 100
    if {"FGM", "FG3M"} <= set(stats): avg["FG2M"] = avg["FGM"] - avg["FG3M"]
    if {"FGM", "FGA"} <= set(stats): avg["FG_PCT"] = ratio("FGM", "FGA")
    if {"FG3M", "FG3A"} <= set(stats): avg["FG3_PCT"] = ratio("FG3M", "FG3A")
    if {"FTM", "FTA"} <= set(stats): avg["FT_PCT"] = ratio("FTM", "FTA")
    cols = list(avg.columns)
    out = {}
    for pos in ("G", "F", "C"):
        if pos not in avg.index.get_level_values("POS"): continue
        sub = avg.xs(pos, level="POS").replace([np.inf, -np.inf], np.nan)
        ranks = sub.rank(method="min", ascending=True)
        out[pos] = {opp: {s: (float(sub.loc[opp, s]), int(ranks.loc[opp, s])) for s in cols if pd.notna(sub.loc[opp, s])} for opp in sub.index}
    return out


def fetch_position_defense(season: str) -> dict:
    def load():
        logs = fetch_league_player_logs(season)
        pos_by_id = {p.id: p.position for p in load_player_index() if p.position}
        result = compute_position_defense(logs, pos_by_id) if not logs.empty else {}
        if not result: raise DataError("no position data")
        return result
    try: return _league_cache.get_or_compute(("posdef", season), load, neg_ttl=60)
    except Exception as exc:
        log.warning("Position defense unavailable: %s", exc)
        return {}


def build_matchup_context(player: PlayerData, opponent: str) -> MatchupContext:
    season = player.season
    metrics = fetch_team_metrics(season)
    posdef = fetch_position_defense(season)
    allowed = fetch_team_allowed(season)
    if not metrics and not posdef and not allowed:
        season = previous_season(season)
        metrics = fetch_team_metrics(season)
        posdef = fetch_position_defense(season)
        allowed = fetch_team_allowed(season)
    group = player.position[:1].upper() if player.position[:1].upper() in ("G", "F", "C") else ""
    by_pos = posdef.get(group, {})
    pos_all = {g: posdef.get(g, {}).get(opponent, {}) for g in ("G", "F", "C")}
    pos_n = max(max((len(v) for v in posdef.values()), default=0), 1)
    return MatchupContext(opponent, season, group, by_pos.get(opponent, {}), pos_n,
                          {a: metrics[a] for a in (opponent, player.team_abbr) if a in metrics},
                          pos_all, allowed.get(opponent, {}))


def rank_tone(kind: str, rank: int, n: int, is_over: bool) -> str:
    n = max(n, 2)
    score = rank / n if kind == "allow" else 1 - (rank - 1) / n
    if not is_over: score = 1 - score
    return "good" if score >= 0.67 else "mid" if score >= 0.34 else "bad"


def summarize_matchup(ctx: MatchupContext) -> tuple:
    """Plain-language list of where the opponent is weak / tough (from the opponent's point of view), most extreme spots first."""
    weak, tough, n = [], [], 30
    for stat in ("PTS", "REB", "AST", "FG3M", "FG3A", "FG3_PCT", "FG_PCT", "FGA", "FG2M", "FTM", "FTA", "FT_PCT", "OREB"):
        data = ctx.team_allowed.get(stat)
        if not data: continue
        rank = data[1]
        if rank >= n - 6: weak.append((n - rank, f"{TEAM_STAT_NAMES[stat]} ({ordinal(n + 1 - rank)} most allowed)"))
        elif rank <= 7: tough.append((rank - 1, f"{TEAM_STAT_NAMES[stat]} ({ordinal(rank)} fewest allowed)"))
    for g in ("G", "F", "C"):
        for stat, label in POS_STATS:
            data = ctx.pos_all.get(g, {}).get(stat)
            if not data: continue
            rank = data[1]
            if rank >= ctx.pos_n - 6: weak.append((ctx.pos_n - rank, f"{label} to {GROUP_NAMES[g].lower()} ({ordinal(ctx.pos_n + 1 - rank)} most)"))
            elif rank <= 7: tough.append((rank - 1, f"{label} to {GROUP_NAMES[g].lower()} ({ordinal(rank)} fewest)"))
    weak.sort(key=lambda x: x[0])
    tough.sort(key=lambda x: x[0])
    return [t for _, t in weak][:8], [t for _, t in tough][:6]


def offense_summary(ctx: MatchupContext) -> str:
    m = ctx.team_metrics.get(ctx.opponent)
    if not m or math.isnan(m.off_rating): return ""
    level = "weak" if m.off_rank >= 21 else "strong" if m.off_rank <= 10 else "average"
    return f"{ctx.opponent} offense is {level}: {ordinal(m.off_rank)} in offensive rating, {ordinal(m.pace_rank)} in pace"


ADJ_COMPONENTS = {
    "PTS": {"PTS": 1.0}, "REB": {"REB": 1.0}, "AST": {"AST": 1.0}, "FG3M": {"FG3M": 1.0},
    "PR": {"PTS": 0.7, "REB": 0.3}, "PA": {"PTS": 0.7, "AST": 0.3}, "RA": {"REB": 0.55, "AST": 0.45},
    "PRA": {"PTS": 0.55, "REB": 0.25, "AST": 0.20}, "STL": {}, "BLK": {}, "STL_BLK": {},
    "FGA": {"FGA": 1.0}, "FTM": {"FTM": 1.0}, "FG2M": {"FG2M": 1.0},
}
ADJ_DEF_WEIGHT = {"PTS": 1.0, "FG3M": 1.0, "AST": 0.6, "PRA": 0.8, "PR": 0.8, "PA": 0.9, "RA": 0.3, "REB": 0.3,
                  "FGA": 0.6, "FG2M": 0.8, "FTM": 0.5}
LEAGUE_AVG_TOTAL = 225.0   # rough league-average game total used as the neutral point for the "game total" effect


def _rank_z(rank: int, n: int) -> float:
    """Rank -> -1..+1. Rank 1 (allows the fewest) = -1, last (allows the most) = +1."""
    n = max(n, 2)
    return max(-1.0, min(1.0, (rank - (n + 1) / 2) / ((n - 1) / 2)))


def matchup_adjustment(player: PlayerData, query: PropQuery, ctx: Optional[MatchupContext], odds: Optional[GameOdds],
                       home_known: bool, is_home: bool, extra: Optional[list] = None) -> tuple:
    """Multiplier for the player's expected stat from the matchup and game context, plus a list of (reason, % effect)."""
    key, effects = query.prop_key, []
    if ctx is not None:
        group, eff = ctx.pos_group, 0.0
        for stat, weight in ADJ_COMPONENTS.get(key, {}).items():
            parts = []
            pos = ctx.pos_all.get(group, {}).get(stat) if group else None
            if pos: parts.append((0.55, _rank_z(pos[1], ctx.pos_n)))
            team = ctx.team_allowed.get(stat)
            if team: parts.append((0.45, _rank_z(team[1], 30)))
            if parts: eff += weight * 0.07 * sum(a * z for a, z in parts) / sum(a for a, _ in parts)
        who = GROUP_NAMES.get(group, "position").lower()
        effects.append((f"{ctx.opponent} defense vs {who}", eff))
        opp, mine = ctx.team_metrics.get(ctx.opponent), ctx.team_metrics.get(player.team_abbr)
        if opp: effects.append((f"{ctx.opponent} defensive rating", _rank_z(opp.def_rank, 30) * 0.03 * ADJ_DEF_WEIGHT.get(key, 0.0)))
        paces = [-_rank_z(m.pace_rank, 30) for m in (opp, mine) if m]
        if paces: effects.append(("pace", 0.03 * sum(paces) / len(paces)))
    if odds is not None:
        if odds.total is not None:
            effects.append(("game total", max(-0.04, min(0.04, 0.25 * (odds.total - LEAGUE_AVG_TOTAL) / LEAGUE_AVG_TOTAL))))
        line = odds.lines.get(player.team_abbr)
        if line and line.spread is not None and abs(line.spread) > 8:
            effects.append(("blowout risk", -min(0.06, 0.008 * (abs(line.spread) - 8))))
    df = player.recent_df
    if home_known and key in df.columns:
        overall = df[key].mean()
        side = df[df["IS_HOME"] == is_home][key]
        if len(side) >= 4 and pd.notna(overall) and overall > 0:
            effects.append(("home form" if is_home else "road form", max(-0.06, min(0.06, 0.5 * (side.mean() / overall - 1)))))
    if extra: effects += list(extra)   # injury effects
    total = max(-0.15, min(0.15, sum(e for _, e in effects)))
    notes = [(label, e * 100) for label, e in effects if abs(e) >= 0.003]
    return 1.0 + total, notes


# ---------------------------------------------------------------- player tracking (potential assists, rebound chances ...)
def _league_pt(measure: str, season: str) -> pd.DataFrame:
    return _league_cache.get_or_compute(
        ("pt", measure, season),
        lambda: with_retries(lambda: leaguedashptstats.LeagueDashPtStats(per_mode_simple="PerGame", player_or_team="Player", pt_measure_type=measure, season=season, timeout=NBA_TIMEOUT).get_data_frames()[0],
                             what=f"tracking {measure}", attempts=1),
        neg_ttl=60)


def fetch_player_tracking(player_id: int, season: str) -> dict:
    def load():
        def one(measure):
            try:
                df = _league_pt(measure, season)
                row = df[df["PLAYER_ID"] == player_id]
                return measure, (row.iloc[0].to_dict() if not row.empty else {})
            except Exception:
                return measure, {}
        with ThreadPoolExecutor(max_workers=len(PT_MEASURES)) as pool:
            data = dict(pool.map(one, PT_MEASURES))
        if not any(data.values()): raise DataError("no tracking data")
        return data
    try: return _league_cache.get_or_compute(("track", player_id, season), load, neg_ttl=60)
    except Exception: return {}


# ---------------------------------------------------------------- odds
@dataclass
class TeamLine:
    ml: Optional[int] = None
    spread: Optional[float] = None
    spread_price: Optional[int] = None


@dataclass
class GameOdds:
    event_id: str
    home: str
    away: str
    lines: dict
    total: Optional[float] = None
    over_price: Optional[int] = None
    under_price: Optional[int] = None
    book: str = ""
    source: str = "odds-api"


@dataclass
class PropOdds:
    point: float
    over: Optional[int]
    under: Optional[int]
    book: str


_odds_cache = TTLCache(ODDS_TTL)
_espn_cache = TTLCache(ESPN_TTL)


def _odds_get(path: str, **params):
    params.update(apiKey=ODDS_API_KEY, oddsFormat="american", dateFormat="iso")
    resp = requests.get(f"{ODDS_BASE}{path}", params=params, timeout=10)
    if resp.status_code in (401, 403): raise DataError("The Odds API rejected the key.")
    if resp.status_code == 429: raise DataError("The Odds API quota is used up.")
    if resp.status_code == 422: raise DataError("That market is not offered for this game.")
    resp.raise_for_status()
    return resp.json()


def _abbr_from_name(name: str) -> Optional[str]:
    for t in teams.get_teams():
        if name == t["full_name"] or name.endswith(t["nickname"]): return t["abbreviation"]
    return None


def _ordered_books(bookmakers: list) -> list:
    return sorted(bookmakers, key=lambda b: BOOK_PREFERENCE.index(b["key"]) if b["key"] in BOOK_PREFERENCE else 99)


def _market(book: dict, key: str) -> Optional[dict]:
    return next((m for m in book.get("markets", []) if m.get("key") == key), None)


def parse_game_odds(event: dict) -> Optional[GameOdds]:
    home, away = _abbr_from_name(event.get("home_team", "")), _abbr_from_name(event.get("away_team", ""))
    books = _ordered_books(event.get("bookmakers", []))
    if not home or not away or not books: return None
    book = books[0]
    odds = GameOdds(event["id"], home, away, {home: TeamLine(), away: TeamLine()}, book=book.get("title", ""))
    for o in (_market(book, "h2h") or {}).get("outcomes", []):
        abbr = _abbr_from_name(o["name"])
        if abbr in odds.lines: odds.lines[abbr].ml = int(o["price"])
    for o in (_market(book, "spreads") or {}).get("outcomes", []):
        abbr = _abbr_from_name(o["name"])
        if abbr in odds.lines: odds.lines[abbr].spread, odds.lines[abbr].spread_price = o.get("point"), int(o["price"])
    for o in (_market(book, "totals") or {}).get("outcomes", []):
        odds.total = o.get("point", odds.total)
        if o["name"] == "Over": odds.over_price = int(o["price"])
        elif o["name"] == "Under": odds.under_price = int(o["price"])
    return odds


def fetch_game_odds() -> list:
    cached = _odds_cache.get("games")
    if cached is not None: return cached
    if not ODDS_API_KEY: return []
    try:
        games = [g for g in (parse_game_odds(ev) for ev in _odds_get("/odds", regions=ODDS_REGIONS, markets="h2h,spreads,totals")) if g]
        _odds_cache.set("games", games)
        return games
    except Exception: return []


def _to_int_price(value) -> Optional[int]:
    if value is None: return None
    text = str(value).strip().upper()
    if text in ("EVEN", "EV", "PK"): return 100
    try: return int(float(text.replace("+", "")))
    except ValueError: return None


def _to_float(value) -> Optional[float]:
    if value is None: return None
    m = re.search(r"-?\d+(?:\.\d+)?", str(value))
    return float(m.group()) if m else None


def _espn_node(side) -> dict:
    side = side or {}
    return side.get("current") or side.get("close") or side.get("open") or {}


def parse_espn_event(event: dict) -> Optional[GameOdds]:
    """Turn one ESPN scoreboard event (with its sportsbook odds block) into GameOdds."""
    comp = (event.get("competitions") or [{}])[0]
    odds_list = comp.get("odds") or []
    competitors = comp.get("competitors") or []
    if not odds_list or len(competitors) < 2: return None
    try:
        home_c = next(c for c in competitors if c.get("homeAway") == "home")
        away_c = next(c for c in competitors if c.get("homeAway") == "away")
        h_raw, a_raw = home_c["team"]["abbreviation"], away_c["team"]["abbreviation"]
        home, away = ESPN_ABBR_TO_NBA.get(h_raw, h_raw), ESPN_ABBR_TO_NBA.get(a_raw, a_raw)
    except Exception:
        return None
    o = odds_list[0]
    provider = (o.get("provider") or {}).get("name") or "ESPN"
    odds = GameOdds(str(event.get("id", "")), home, away, {home: TeamLine(), away: TeamLine()}, book=provider, source="espn")
    money = o.get("moneyline") or {}
    spread = o.get("pointSpread") or {}
    for side, abbr in (("home", home), ("away", away)):
        odds.lines[abbr].ml = _to_int_price(_espn_node(money.get(side)).get("odds"))
        node = _espn_node(spread.get(side))
        odds.lines[abbr].spread = _to_float(node.get("line"))
        odds.lines[abbr].spread_price = _to_int_price(node.get("odds"))
    if odds.lines[home].spread is None and odds.lines[away].spread is None:
        m = re.match(r"\s*([A-Z]{2,4})\s+(-?\d+(?:\.\d+)?)", str(o.get("details") or ""))
        if m:
            fav = ESPN_ABBR_TO_NBA.get(m.group(1), m.group(1))
            if fav in odds.lines:
                other = away if fav == home else home
                odds.lines[fav].spread, odds.lines[other].spread = float(m.group(2)), -float(m.group(2))
    total = o.get("total") or {}
    over_node, under_node = _espn_node(total.get("over")), _espn_node(total.get("under"))
    odds.total = _to_float(o.get("overUnder"))
    if odds.total is None: odds.total = _to_float(over_node.get("line"))
    odds.over_price, odds.under_price = _to_int_price(over_node.get("odds")), _to_int_price(under_node.get("odds"))
    has_data = odds.total is not None or any(l.ml is not None or l.spread is not None for l in odds.lines.values())
    return odds if has_data else None


def _espn_events(day: date) -> list:
    def load():
        resp = requests.get(ESPN_SCOREBOARD, params={"dates": day.strftime("%Y%m%d")}, headers={"User-Agent": "Mozilla/5.0"}, timeout=8)
        resp.raise_for_status()
        return resp.json().get("events", [])
    try: return _espn_cache.get_or_compute(("espn_events", day.isoformat()), load, neg_ttl=15)
    except Exception as exc:
        log.warning("ESPN scoreboard unavailable: %s", exc)
        return []


def fetch_game_odds_espn(day: date) -> list:
    """Free, key-less sportsbook game lines (spread, moneyline, total) from ESPN's public scoreboard."""
    return [g for g in (parse_espn_event(ev) for ev in _espn_events(day)) if g]


def find_game_odds(team: str, opponent: Optional[str], lookup: Optional[ScheduleLookup]) -> Optional[GameOdds]:
    if not opponent: return None
    pair = {team, opponent}
    match = next((g for g in fetch_game_odds() if {g.home, g.away} == pair), None)
    if match: return match
    game = lookup.game if lookup else None
    if game and game.game_date: days = [game.game_date]
    else: days = [today_eastern() + timedelta(days=i) for i in range(3)]
    for day in days:
        match = next((g for g in fetch_game_odds_espn(day) if {g.home, g.away} == pair), None)
        if match: return match
    return None


def fetch_prop_odds(event_id: str, prop_key: str, player_name: str, line: float) -> Optional[PropOdds]:
    if not ODDS_API_KEY: return None
    market = PROP_MARKETS.get(prop_key)
    if not market: return None
    try:
        data = _odds_cache.get((event_id, market))
        if data is None:
            data = _odds_get(f"/events/{event_id}/odds", regions=ODDS_REGIONS, markets=market)
            _odds_cache.set((event_id, market), data)
        target = normalize_text(player_name).replace(".", "").strip()
        for book in _ordered_books(data.get("bookmakers", [])):
            by_point = {}
            for o in (_market(book, market) or {}).get("outcomes", []):
                who = normalize_text(o.get("description", "")).replace(".", "").strip()
                if who == target and o.get("point") is not None:
                    by_point.setdefault(float(o["point"]), {})[o["name"]] = int(o["price"])
            if by_point:
                point = min(by_point, key=lambda p: abs(p - line))
                return PropOdds(point, by_point[point].get("Over"), by_point[point].get("Under"), book.get("title", ""))
    except Exception: pass
    return None


def american_to_prob(price: int) -> float:
    return 100 / (price + 100) if price > 0 else -price / (-price + 100)


@dataclass
class WinProb:
    home: str
    away: str
    p_home: float
    source: str
    home_known: bool


def compute_win_prob(home: str, away: str, home_known: bool, odds: Optional[GameOdds], metrics: dict) -> Optional[WinProb]:
    if odds and odds.lines.get(home) and odds.lines.get(away):
        ml_h, ml_a = odds.lines[home].ml, odds.lines[away].ml
        if ml_h is not None and ml_a is not None:
            raw_h, raw_a = american_to_prob(ml_h), american_to_prob(ml_a)
            total_vig = raw_h + raw_a
            p_h = raw_h / total_vig
            return WinProb(home, away, p_h, f"Market ({odds.book}) · de-vigged", home_known)
    mh, ma = metrics.get(home), metrics.get(away)
    if mh and ma:
        margin = mh.net_rating - ma.net_rating + (HOME_COURT_POINTS if home_known else 0.0)
        return WinProb(home, away, float(norm.cdf(margin / MARGIN_STD)), "Model · net rating + home court", home_known)
    return None


# ---------------------------------------------------------------- news, injuries, rosters, schedule
@dataclass
class NewsItem:
    title: str
    source: str
    when: Optional[datetime]
    url: str
    summary: str = ""
    tag: str = "League"


@dataclass
class InjuryItem:
    name: str
    pos: str
    status: str
    comment: str = ""
    date: str = ""


_news_cache = TTLCache(300)
_injury_cache = TTLCache(600)
_roster_cache = TTLCache(6 * 3600)
UTC = timezone.utc


def time_ago(dt: Optional[datetime]) -> str:
    if dt is None: return ""
    if dt.tzinfo is None: dt = dt.replace(tzinfo=UTC)
    secs = (datetime.now(UTC) - dt).total_seconds()
    if secs < 3600: return f"{max(1, int(secs // 60))}m ago"
    if secs < 86400: return f"{int(secs // 3600)}h ago"
    return f"{int(secs // 86400)}d ago"


def fetch_espn_news(limit: int = 50) -> list:
    resp = requests.get(ESPN_NEWS, params={"limit": limit}, headers={"User-Agent": "Mozilla/5.0"}, timeout=8)
    resp.raise_for_status()
    items = []
    for a in resp.json().get("articles", []):
        when = None
        try: when = datetime.fromisoformat(str(a.get("published", "")).replace("Z", "+00:00"))
        except ValueError: pass
        url = ((a.get("links") or {}).get("web") or {}).get("href", "")
        if a.get("headline"):
            items.append(NewsItem(a["headline"], "ESPN", when, url, a.get("description", "") or ""))
    return items


def fetch_google_news(query: str, limit: int = 12) -> list:
    resp = requests.get(GOOGLE_NEWS, params={"q": query, "hl": "en-US", "gl": "US", "ceid": "US:en"}, headers={"User-Agent": "Mozilla/5.0"}, timeout=8)
    resp.raise_for_status()
    items = []
    for node in ET.fromstring(resp.content).iter("item"):
        title = (node.findtext("title") or "").strip()
        src_node = node.find("source")
        source = (src_node.text or "").strip() if src_node is not None else ""
        if source and title.endswith(" - " + source): title = title[: -len(source) - 3]
        elif not source and " - " in title: title, source = title.rsplit(" - ", 1)
        when = None
        try: when = parsedate_to_datetime(node.findtext("pubDate") or "")
        except Exception: pass
        if title: items.append(NewsItem(title, source or "Google News", when, node.findtext("link") or "", "", "News"))
        if len(items) >= limit: break
    return items


def build_news(player: str, team: str, opp: str) -> list:
    """Headlines for the searched player / his team / the match, plus league news. Empty names = league news only."""
    key = (player, team, opp)
    cached = _news_cache.get(key)
    if cached is not None: return cached
    names = _team_tables()[2]
    team_full, opp_full = names.get(team, ""), names.get(opp, "")
    jobs = []
    if player: jobs.append(("Player", lambda: fetch_google_news(f'"{player}" NBA')))
    if team_full: jobs.append(("Team", lambda: fetch_google_news(f"{team_full} NBA")))
    if team_full and opp_full: jobs.append(("Matchup", lambda: fetch_google_news(f"{team_full} {opp_full} NBA")))
    jobs.append(("League", fetch_espn_news))
    def run(job):
        tag, fn = job
        try: return tag, fn()
        except Exception as exc:
            log.warning("News (%s) unavailable: %s", tag, exc)
            return tag, []
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run, jobs))
    nick = team_full.split()[-1].lower() if team_full else ""
    last = player.split()[-1].lower() if player else ""
    items, seen = [], set()
    for tag, found in results:
        for it in found:
            fingerprint = normalize_text(it.title)[:80]
            if fingerprint in seen: continue
            seen.add(fingerprint)
            if tag == "League" and (player or team):
                text = f"{it.title} {it.summary}".lower()
                it.tag = "Player" if last and last in text else "Team" if nick and nick in text else "League"
            else:
                it.tag = tag
            items.append(it)
    items.sort(key=lambda x: x.when.astimezone(UTC) if x.when else datetime.min.replace(tzinfo=UTC), reverse=True)
    items = items[:40]
    if items: _news_cache.set(key, items)
    return items


def fetch_injuries() -> dict:
    """League injury report from ESPN: NBA team abbr -> [InjuryItem]. Cached for 10 minutes, one request at a time."""
    def load():
        resp = requests.get(ESPN_INJURIES, headers={"User-Agent": "Mozilla/5.0"}, timeout=8)
        resp.raise_for_status()
        out = {}
        for team in resp.json().get("injuries", []):
            abbr = _abbr_from_name(team.get("displayName", "") or "")
            if not abbr: continue
            for it in team.get("injuries", []):
                ath = it.get("athlete") or {}
                name = ath.get("displayName") or ""
                if not name: continue
                status = it.get("status") or (it.get("type") or {}).get("description") or "Unknown"
                comment = it.get("shortComment") or it.get("longComment") or ""
                out.setdefault(abbr, []).append(InjuryItem(name, (ath.get("position") or {}).get("abbreviation", ""), str(status), str(comment), str(it.get("date", ""))))
        if not out: raise DataError("empty injury report")
        return out
    return _injury_cache.get_or_compute("injuries", load, neg_ttl=30)


def injury_index(injuries: dict) -> dict:
    return {normalize_text(i.name): i for items in (injuries or {}).values() for i in items}


def injury_style(status: str) -> tuple:
    """(background, text colour, short label, severity) for an injury status."""
    s = (status or "").lower()
    if s.startswith("out"): return ("#4c0519", "#f43f5e", "OUT", 0)
    if "doubtful" in s: return ("#4c0519", "#fb7185", "DBT", 1)
    if "question" in s: return ("#451a03", "#fb923c", "Q", 2)
    if "day" in s: return ("#422006", "#fbbf24", "DTD", 3)
    if "probable" in s: return ("#064e3b", "#34d399", "P", 4)
    return ("#1e293b", "#94a3b8", (status or "?")[:3].upper(), 5)


def absence_weight(status: str) -> float:
    """How likely a player on the injury report is to miss the game."""
    s = (status or "").lower()
    if s.startswith("out"): return 1.0
    if "doubtful" in s: return 0.75
    if "question" in s: return 0.35
    if "day" in s: return 0.30
    return 0.0


def status_warning(status: str) -> str:
    p_play = 1.0 - absence_weight(status)
    return f"⚠ {status.upper()} – about {p_play * 100:.0f}% to play"


def match_injury(name: str, items: list) -> Optional["InjuryItem"]:
    """Find a player in a team's injury list: exact name first, then a close spelling with the same last name."""
    if not items or not name: return None
    target = normalize_text(name)
    for it in items:
        if normalize_text(it.name) == target: return it
    last = target.split()[-1] if target.split() else ""
    pool = [i for i in items if normalize_text(i.name).split()[-1:] == [last]]
    close = difflib.get_close_matches(target, [normalize_text(i.name) for i in pool], n=1, cutoff=0.8)
    return next((i for i in pool if close and normalize_text(i.name) == close[0]), None)


def injury_effects(team: str, opp: str, prop_key: str, rotations: dict, injuries: dict, exclude_name: str = "") -> list:
    """(label, effect) pairs: missing opponent defenders/bigs help the player, missing teammates give him more usage."""
    comp = ADJ_COMPONENTS.get(prop_key, {})
    if not comp or not injuries: return []
    effects, skip = [], normalize_text(exclude_name)
    for rot_team, is_opp in ((opp, True), (team, False)):
        rot = (rotations or {}).get(rot_team)
        items = injuries.get(rot_team, [])
        if rot is None or rot.empty or not items: continue
        for r in rot.head(9).to_dict("records"):
            name = str(r.get("NAME", ""))
            if normalize_text(name) == skip: continue
            it = match_injury(name, items)
            if it is None: continue
            weight = absence_weight(it.status)
            mpg = float(r.get("MIN") or 0)
            if weight <= 0 or mpg < 16: continue
            share = min(1.3, mpg / 32)
            pts, reb = float(r.get("PTS") or 0), float(r.get("REB") or 0)
            blk = float(r.get("BLK") or 0)
            eff = 0.0
            for stat, w in comp.items():
                if is_opp:     # weaker defence / rim protection / rebounding
                    if stat in ("PTS", "FG3M", "FGA", "FG2M", "FTM"): eff += w * (0.035 * share + (0.015 if blk >= 1.2 else 0.0))
                    elif stat == "AST": eff += w * 0.02 * share
                    elif stat == "REB": eff += w * 0.04 * min(1.5, reb / 8)
                else:          # teammate out -> more shots, touches and boards
                    if stat in ("PTS", "FG3M", "FGA", "FG2M", "FTM"): eff += w * 0.03 * share * min(1.5, pts / 16)
                    elif stat == "AST": eff += w * 0.025 * share * min(1.5, pts / 16)
                    elif stat == "REB": eff += w * 0.02 * min(1.5, reb / 8)
            eff *= weight
            if abs(eff) >= 0.002:
                short = injury_style(it.status)[2]
                effects.append((f"{rot_team} without {name} ({short})" if is_opp else f"{team} without {name} ({short}) – more usage", eff))
    return effects


def injury_report_line(team: str, rotations: Optional[dict], injuries: Optional[dict], skip_name: str = "") -> str:
    """'BOS rotation on the report: A (OUT, 31 mpg), B (Q, 22 mpg).' or '' when nobody matters."""
    rot, items = (rotations or {}).get(team), (injuries or {}).get(team, [])
    if rot is None or rot.empty or not items: return ""
    names = []
    for r in rot.head(10).to_dict("records"):
        if normalize_text(str(r.get("NAME", ""))) == normalize_text(skip_name): continue
        it = match_injury(str(r.get("NAME", "")), items)
        if it is not None and absence_weight(it.status) > 0.1:
            names.append(f"{r.get('NAME')} ({injury_style(it.status)[2]}, {float(r.get('MIN') or 0):.0f} mpg)")
    return f"{team} rotation players on the report: " + ", ".join(names) + "." if names else ""


def fetch_roster(abbr: str) -> list:
    team_id = _team_tables()[0].get(abbr)
    if team_id is None: return []
    for season in (current_season(), previous_season(current_season())):
        key = ("roster", abbr, season)
        cached = _roster_cache.get(key)
        if cached: return cached
        try:
            df = with_retries(lambda: commonteamroster.CommonTeamRoster(team_id=team_id, season=season, timeout=NBA_TIMEOUT).get_data_frames()[0], what="roster", attempts=1)
        except DataError:
            continue
        rows = [{"name": str(r.get("PLAYER", "")), "num": str(r.get("NUM", "") or ""), "pos": str(r.get("POSITION", "") or ""),
                 "height": str(r.get("HEIGHT", "") or ""), "exp": str(r.get("EXP", "") or "")} for r in df.to_dict("records")]
        if rows:
            _roster_cache.set(key, rows)
            return rows
    return []


def fetch_schedule() -> tuple:
    """(day, games) for the first day from today with NBA games – every game, including live and finished."""
    start = today_eastern()
    for offset in range(PICK_LOOKAHEAD_DAYS):
        day = start + timedelta(days=offset)
        games = fetch_day_games(day, only_pre=False)
        if games: return day, games
    return start, []


# ---------------------------------------------------------------- unified probability model (one engine for search + Today's picks)
@dataclass
class Baseline:
    """Everything the model knows about one player/prop for one game."""
    prop: str
    mean: float            # final projection (all adjustments applied)
    std: float
    raw_mean: float        # recent form only
    raw_std: float
    mult: float            # matchup + context + injury multiplier
    notes: list            # (reason, % effect)
    vals: pd.Series        # the games used (newest first)
    conf: float            # probability he plays (confidence multiplier)
    mfac: float            # minutes factor from his own injury status
    status: str = ""       # injury status text, "" = healthy
    comment: str = ""


def build_baseline(pdata: PlayerData, team: str, opp: str, prop: str, odds: Optional[GameOdds], ctx: Optional[MatchupContext],
                   home_known: bool, is_home: bool, rotations: Optional[dict], injuries: Optional[dict], sample_n: int = 10) -> Optional[Baseline]:
    sample = pdata.recent_df.head(sample_n)
    if prop not in sample.columns: return None
    vals = sample[prop].dropna()
    if len(vals) < 3: return None
    mean, std = float(vals.mean()), float(vals.std())
    if math.isnan(std): return None
    extra = injury_effects(team, opp, prop, rotations or {}, injuries or {}, pdata.name)
    mult, notes = matchup_adjustment(pdata, PropQuery(pdata.name, True, 0.5, prop, opp), ctx, odds, home_known, is_home, extra)
    inj = match_injury(pdata.name, (injuries or {}).get(team, []))
    w = absence_weight(inj.status) if inj else 0.0
    conf, mfac = 1.0 - w, 1.0 - 0.08 * w
    return Baseline(prop, mean * mult * mfac, std * mult * mfac, mean, std, mult, notes, vals, conf, mfac,
                    inj.status if inj else "", inj.comment if inj else "")


def model_probability(base: Baseline, line: float, is_over: bool) -> Optional[float]:
    """Chance of the pick winning: normal model on the projection, pulled toward 50% by the chance he actually plays."""
    p = implied_probability(base.mean, base.std, line, is_over)
    return None if p is None else 50.0 + (p - 50.0) * base.conf


def rest_days_for(pdata: PlayerData, game_day: Optional[date]) -> Optional[int]:
    """Days between the player's last game and the upcoming one (1 = back-to-back)."""
    if game_day is None or pdata.recent_df is None or pdata.recent_df.empty: return None
    try: days = (game_day - pdata.recent_df["GAME_DATE_DT"].iloc[0].date()).days
    except Exception: return None
    return days if days > 0 else None


def analysis_sections(pdata: PlayerData, base: Baseline, team: str, opp: str, line: float, is_over: bool, prob: Optional[float],
                      ctx: Optional[MatchupContext], odds: Optional[GameOdds], home_known: bool, is_home: bool,
                      rotations: Optional[dict], injuries: Optional[dict], rest_days: Optional[int] = None) -> list:
    """Written analysis: [(title, [lines])] – form, matchup, pace/script, home/away & rest, injuries, model."""
    prop, title = base.prop, PROP_TITLE[base.prop]
    side, name = ("over" if is_over else "under"), pdata.name
    df_all = pdata.recent_df
    col = df_all[prop].dropna()
    l5, l10, season_vals = col.head(5), base.vals, pdata.df[prop].dropna()
    sections = []

    form = [f"Averages: L5 {fmt(l5.mean())}  ·  L10 {fmt(l10.mean())}  ·  season {fmt(season_vals.mean())} over {len(season_vals)} games."]
    if len(l10) >= 4:
        y = list(reversed(list(l10)))
        slope = float(np.polyfit(range(len(y)), y, 1)[0])
        rel = slope / max(float(l10.mean()), 0.1) * 100
        direction = "trending UP" if rel > 2.5 else "trending DOWN" if rel < -2.5 else "flat"
        form.append(f"Trend over the last {len(y)} games: {direction} ({slope:+.2f} per game, {rel:+.1f}% of his average); L5 is {fmt_signed(l5.mean() - l10.mean())} versus L10.")
    if len(l10) > 1:
        sd, cv = float(l10.std()), float(l10.std()) / max(float(l10.mean()), 0.1)
        verdict = "very consistent" if cv < 0.25 else "normal variance" if cv < 0.45 else "high variance (volatile)"
        form.append(f"Variance: std dev {sd:.1f}, range {fmt(l10.min())}–{fmt(l10.max())}, coefficient of variation {cv:.2f} → {verdict}.")
    h5, h10, hs = hit_rate(l5, line, is_over), hit_rate(l10, line, is_over), hit_rate(season_vals, line, is_over)
    form.append(f"Hit rate for {side} {line:g}: L5 {h5[1]}/{h5[2]}  ·  L10 {h10[1]}/{h10[2]} ({h10[0]:.0f}%)  ·  season {hs[1]}/{hs[2]} ({hs[0]:.0f}%).")
    if "SEASON_LABEL" in df_all.columns and (df_all["SEASON_LABEL"].head(10) != pdata.season).any():
        form.append(f"Early in the season, so part of the sample comes from {pdata.prev_season}.")
    elif pdata.is_rookie:
        form.append("Rookie year – there is no previous season to blend in.")
    sections.append(("RECENT FORM", form))

    group = pdata.position[:1].upper() if pdata.position[:1].upper() in ("G", "F", "C") else ""
    mu = []
    if ctx is not None:
        m = ctx.team_metrics.get(opp)
        if m:
            off = f"; offensive rating {m.off_rating:.1f} ({ordinal(m.off_rank)})" if not math.isnan(m.off_rating) else ""
            mu.append(f"{opp} defensive rating {m.def_rating:.1f} – ranked {ordinal(m.def_rank)} of 30 (1st = best defence){off}.")
        for stat in ADJ_COMPONENTS.get(prop, {}):
            pos, tm = (ctx.pos_all.get(group, {}).get(stat) if group else None), ctx.team_allowed.get(stat)
            bits = []
            if pos: bits.append(f"to {GROUP_NAMES[group].lower()}: {pos[0]:.1f} per game ({ordinal(ctx.pos_n + 1 - pos[1])} most)")
            if tm: bits.append(f"to everyone: {tm[0]:.1f} ({ordinal(31 - tm[1])} most)")
            if bits: mu.append(f"{opp} allows {TEAM_STAT_NAMES.get(stat, stat)} – " + "; ".join(bits) + ".")
        weak, tough = summarize_matchup(ctx)
        if weak: mu.append(f"Where {opp} is weak: " + ", ".join(weak[:4]) + ".")
        if tough: mu.append(f"Where {opp} is tough: " + ", ".join(tough[:3]) + ".")
        verdict = next((f"{lbl} {pct:+.1f}%" for lbl, pct in base.notes if "defense vs" in lbl), None)
        if verdict: mu.append(f"Net matchup effect on his {title.lower()}: {verdict}.")
    else:
        mu.append("Opponent defensive data is not available yet.")
    sections.append(("MATCHUP", mu))

    pace = []
    metrics = ctx.team_metrics if ctx else {}
    mt, mo = metrics.get(team), metrics.get(opp)
    if mt and mo:
        avg_rank = (mt.pace_rank + mo.pace_rank) / 2
        speed = "fast" if avg_rank <= 10 else "slow" if avg_rank >= 21 else "average"
        effect = "adds possessions (good for counting stats)" if speed == "fast" else "removes possessions" if speed == "slow" else "barely changes his volume"
        pace.append(f"Pace: {team} {mt.pace:.1f} ({ordinal(mt.pace_rank)} fastest), {opp} {mo.pace:.1f} ({ordinal(mo.pace_rank)}) → a {speed}-tempo game that {effect}.")
    if odds is not None and odds.total is not None:
        env = "high-scoring" if odds.total >= LEAGUE_AVG_TOTAL + 6 else "low-scoring" if odds.total <= LEAGUE_AVG_TOTAL - 6 else "normal-scoring"
        pace.append(f"Market total {odds.total:g} (league norm ≈ {LEAGUE_AVG_TOTAL:g}) → {env} environment.")
    ln = odds.lines.get(team) if odds else None
    if ln is not None and ln.spread is not None:
        gap = abs(ln.spread)
        role = "favoured" if ln.spread < 0 else "underdog" if ln.spread > 0 else "pick'em"
        script = ("blowout risk – starters may sit the fourth quarter, so minutes could be trimmed" if gap >= 10
                  else "competitive game – starters should play their usual minutes" if gap <= 5
                  else "moderate spread – small minutes risk if it gets out of hand")
        pace.append(f"Expected game script: {team} {fmt_point(ln.spread)} ({role}); {script}.")
    mins = df_all["MIN"].head(10).dropna() if "MIN" in df_all.columns else pd.Series(dtype=float)
    if len(mins): pace.append(f"Minutes: {fmt(mins.mean())} per game over his last {len(mins)} (range {fmt(mins.min())}–{fmt(mins.max())}).")
    if not pace: pace.append("No pace or market data available yet.")
    sections.append(("PACE & GAME SCRIPT", pace))

    sp = []
    recent30 = df_all.head(30)
    home_vals, away_vals = recent30[recent30["IS_HOME"]][prop].dropna(), recent30[~recent30["IS_HOME"]][prop].dropna()
    if len(home_vals) >= 2 and len(away_vals) >= 2:
        sp.append(f"Home/road split (last {len(recent30)} games): home {fmt(home_vals.mean())} over {len(home_vals)} games, road {fmt(away_vals.mean())} over {len(away_vals)}.")
    if home_known: sp.append(f"This game {team} plays {'at home' if is_home else 'on the road'}.")
    if rest_days is None: sp.append("Rest days could not be determined (game date unknown).")
    elif rest_days <= 1: sp.append(f"⚠ Back-to-back: only {rest_days} day since his last game – fatigue risk and possible minutes management.")
    elif rest_days >= 3: sp.append(f"Well rested: {rest_days} days since his last game.")
    else: sp.append(f"Normal rest: {rest_days} days since his last game.")
    sections.append(("HOME / AWAY & REST", sp))

    inj_lines = []
    if base.status:
        inj_lines.append(status_warning(base.status) + (f" ({base.comment})" if base.comment else "") + f". Model confidence is pulled toward 50% by ×{base.conf:.2f}.")
    for label, pct in base.notes:
        if " without " in label: inj_lines.append(f"{label}: {pct:+.1f}% on his expected {title.lower()}.")
    for t in (team, opp):
        line_txt = injury_report_line(t, rotations, injuries, name)
        if line_txt: inj_lines.append(line_txt)
    if not inj_lines: inj_lines.append("No relevant injuries reported for either rotation – no lineup adjustment applied.")
    sections.append(("INJURIES & LINEUPS", inj_lines))

    raw = implied_probability(base.raw_mean, base.raw_std, line, is_over)
    model = [f"Recent form alone: {fmt(base.raw_mean)} ± {base.raw_std:.1f} → {raw:.0f}% to go {side} {line:g}." if raw is not None else "Recent form alone: not enough data."]
    for label, pct in base.notes:
        if " without " not in label: model.append(f"{label}: {pct:+.1f}% on his expected {title.lower()}.")
    model.append(f"Combined multiplier ×{base.mult:.3f}" + (f" and minutes ×{base.mfac:.2f}" if base.mfac != 1.0 else "") + f" → projection {fmt(base.mean)} {title.lower()}.")
    if prob is not None: model.append(f"Final model probability: {prob:.1f}%.")
    sections.append(("MODEL", model))
    return sections


# ---------------------------------------------------------------- picks engine (best pick of a game / of the day)
PICK_PROPS = ("PTS", "REB", "AST", "FG3M", "PRA")
PICK_PROB_MIN, PICK_PROB_MAX = 45.0, 58.0       # model win chance window
PICK_ODDS_MIN, PICK_ODDS_MAX = 1.70, 2.10       # decimal-odds window
PICK_TOP_PLAYERS = 5
PICK_LOOKAHEAD_DAYS = 5
_today_cache = TTLCache(600)


def american_to_decimal(price: int) -> float:
    return 1 + price / 100 if price > 0 else 1 + 100 / -price


@dataclass
class DayGame:
    home: str
    away: str
    when: str = ""
    odds: Optional[GameOdds] = None
    home_known: bool = True
    state: str = "pre"
    day: Optional[date] = None


@dataclass
class Pick:
    kind: str                 # "player" or "team"
    headline: str
    short: str
    game: str
    when: str = ""
    player: str = ""
    team: str = ""
    opp: str = ""
    prop_key: str = ""
    line: float = 0.0
    is_over: bool = True
    prob: float = 0.0
    score: float = 0.0
    decimal_odds: Optional[float] = None
    chips: list = field(default_factory=list)
    reasons: list = field(default_factory=list)
    sample: Optional[pd.DataFrame] = None
    season: str = ""
    recent: Optional[dict] = None     # team picks: team -> last games
    sections: list = field(default_factory=list)
    status: str = ""                  # injury warning for the player, "" = healthy


@dataclass
class TodayPicks:
    day: date
    games: int
    picks: list
    season: str
    note: str = ""


def fetch_day_games(day: date, only_pre: bool = True) -> list:
    games = []
    for ev in _espn_events(day):
        try:
            if (ev.get("season") or {}).get("type") == 1: continue   # preseason
            comp = (ev.get("competitions") or [{}])[0]
            status = (comp.get("status") or ev.get("status") or {}).get("type", {})
            if only_pre and status.get("state") not in (None, "pre"): continue
            comps = comp.get("competitors") or []
            home_c = next(c for c in comps if c.get("homeAway") == "home")
            away_c = next(c for c in comps if c.get("homeAway") == "away")
            h_raw, a_raw = home_c["team"]["abbreviation"], away_c["team"]["abbreviation"]
            games.append(DayGame(ESPN_ABBR_TO_NBA.get(h_raw, h_raw), ESPN_ABBR_TO_NBA.get(a_raw, a_raw),
                                 status.get("shortDetail") or "", parse_espn_event(ev), True, status.get("state") or "pre", day))
        except Exception:
            continue
    return games


def find_pick_games() -> tuple:
    start = today_eastern()
    days = [start + timedelta(days=i) for i in range(PICK_LOOKAHEAD_DAYS)]
    with ThreadPoolExecutor(max_workers=5) as pool:
        batches = list(pool.map(fetch_day_games, days))
    for day, games in zip(days, batches):
        if games: return day, games
    return start, []


def get_pick_logs() -> tuple:
    cur = current_season()
    for season in (cur, previous_season(cur)):
        try:
            df = fetch_league_player_logs(season)
        except Exception:
            continue
        if df is not None and not df.empty:
            return df, season
    return pd.DataFrame(), cur


_player_groups: dict = {}
_groups_lock = threading.Lock()


def rows_for_player(logs: pd.DataFrame, pid: int, team: Optional[str] = None) -> pd.DataFrame:
    """One player's rows from the league-wide log; the per-player grouping is built once per log, not once per player."""
    if logs is None or logs.empty: return pd.DataFrame()
    with _groups_lock:
        entry = _player_groups.get(id(logs))
        if entry is None or entry[0] is not logs:
            if len(_player_groups) >= 3: _player_groups.pop(next(iter(_player_groups)))
            entry = (logs, {k: v for k, v in logs.groupby("PLAYER_ID")})
            _player_groups[id(logs)] = entry
    df = entry[1].get(pid)
    if df is None: return logs.iloc[0:0]
    return df[df["TEAM_ABBREVIATION"] == team] if team else df


def team_recent_games(logs: pd.DataFrame, team: str, n: int = 5) -> list:
    """A team's last n games (date, opponent, W/L, score) rebuilt from the league-wide player logs."""
    if logs is None or logs.empty or not team: return []
    t = logs[logs["TEAM_ABBREVIATION"] == team]
    if t.empty: return []
    games = t.groupby("GAME_ID").agg(DATE=("GAME_DATE", "first"), MATCHUP=("MATCHUP", "first"), WL=("WL", "first"), PTS=("PTS", "sum")).reset_index()
    games["DT"] = pd.to_datetime(games["DATE"], errors="coerce")
    games = games.sort_values("DT", ascending=False).head(n)
    opp_rows = logs[logs["GAME_ID"].isin(games["GAME_ID"]) & (logs["TEAM_ABBREVIATION"] != team)]
    opp_pts = pd.to_numeric(opp_rows["PTS"], errors="coerce").groupby(opp_rows["GAME_ID"]).sum()
    out = []
    for r in games.to_dict("records"):
        matchup = str(r["MATCHUP"])
        out.append({"date": r["DT"].strftime("%b %d") if pd.notna(r["DT"]) else "", "opp": matchup.split()[-1], "home": "@" not in matchup,
                    "wl": str(r["WL"] or ""), "pts": float(r["PTS"]), "opp_pts": float(opp_pts.get(r["GAME_ID"], float("nan")))})
    return out


def team_rotation(logs: pd.DataFrame, team: str, n: int = 8) -> pd.DataFrame:
    if logs is None or logs.empty or not team: return pd.DataFrame()
    df = logs[logs["TEAM_ABBREVIATION"] == team].copy()
    if df.empty: return pd.DataFrame()
    for c in ("MIN", "PTS", "REB", "AST", "FG3M", "STL", "BLK"):
        df[c] = pd.to_numeric(df[c], errors="coerce")
    g = df.groupby("PLAYER_ID").agg(NAME=("PLAYER_NAME", "first"), GP=("GAME_ID", "nunique"), MIN=("MIN", "mean"),
                                    PTS=("PTS", "mean"), REB=("REB", "mean"), AST=("AST", "mean"), FG3M=("FG3M", "mean"),
                                    STL=("STL", "mean"), BLK=("BLK", "mean")).reset_index()
    g = g[g["GP"] >= 2].sort_values("MIN", ascending=False).head(n)
    return g.reset_index(drop=True)


def player_pick_candidates(pdata: PlayerData, info: PlayerInfo, team: str, opp: str, is_home: bool, home_known: bool, odds: Optional[GameOdds],
                           ctx: Optional[MatchupContext], rotations: dict, injuries: dict, game_label: str, when: str) -> list:
    """Best (line, side) per prop for one player – the SAME function feeds the game pick, the day's picks and the player search."""
    inj = match_injury(info.name, (injuries or {}).get(team, []))
    if inj is not None and absence_weight(inj.status) >= 0.75: return []   # out / doubtful – no pick
    weak, tough = summarize_matchup(ctx) if ctx else ([], [])
    spread = total = None
    if odds is not None:
        ln = odds.lines.get(team)
        spread, total = (ln.spread if ln else None), odds.total
    picks = []
    for prop in PICK_PROPS:
        base = build_baseline(pdata, team, opp, prop, odds, ctx, home_known, is_home, rotations, injuries)
        if base is None: continue
        best, base_line = None, math.floor(base.mean) + 0.5
        for line in sorted({max(0.5, base_line + d) for d in (-1, 0, 1)}):
            for is_over in (True, False):
                prob = model_probability(base, line, is_over)
                if prob is None or not (PICK_PROB_MIN <= prob <= PICK_PROB_MAX): continue
                hr, hits, decided = hit_rate(base.vals, line, is_over)
                if decided < 4 or hr < 50: continue
                score = prob + 0.35 * (hr - 50) + 0.3 * min(decided, 10) - 6.0 * (1.0 - base.conf)
                if best is None or score > best[0]: best = (score, line, is_over, prob, hr, hits, decided)
        if best is None: continue
        score, line, is_over, prob, hr, hits, decided = best
        side, title = ("over" if is_over else "under"), PROP_TITLE[prop]
        short = f"{'OVER' if is_over else 'UNDER'} {line:g} {PROP_SHORT[prop]}"
        raw = implied_probability(base.raw_mean, base.raw_std, line, is_over)
        reasons = [
            f"Hit rate: {hits} of his last {decided} games finished {side} {line:g} {title.lower()} ({hr:.0f}%).",
            f"Recent form: {fmt(base.raw_mean)} {title.lower()} per game over the last {len(base.vals)} games (median {fmt(base.vals.median())}); season average {fmt(pdata.df[prop].mean())}.",
            f"Model: {prob:.0f}% chance after the matchup and injury adjustment ({(base.mult - 1) * 100:+.1f}%), {raw:.0f}% from recent form alone.",
        ]
        for label, pct in base.notes:
            reasons.append(f"{label}: {pct:+.1f}% effect on his expected {title.lower()}.")
        support, against = (weak, tough) if is_over else (tough, weak)
        if support: reasons.append(f"{opp} spots that support this pick: {', '.join(support[:3])}.")
        if against: reasons.append(f"{opp} spots that work against it: {', '.join(against[:2])}.")
        ctx_bits = [f"{team} {'at home' if is_home else 'on the road'}" if home_known else f"{team} vs {opp}"]
        if spread is not None: ctx_bits.append(f"spread {fmt_point(spread)}")
        if total is not None: ctx_bits.append(f"game total {total:g}")
        reasons.append("Game context: " + ", ".join(ctx_bits) + ".")
        reasons.append("Check injuries and lineups before betting. The line is OutplAI's suggested line from recent form, not a sportsbook line.")
        chips = [f"Model {prob:.0f}%", f"Hit rate {hits}/{decided}", f"Avg {fmt(base.raw_mean)}"]
        warning = ""
        if inj is not None:
            warning = status_warning(inj.status)
            reasons.insert(0, f"⚠ Injury report: {inj.status}" + (f" – {inj.comment}" if inj.comment else "") + ". Confirm he is playing before betting.")
            chips[2] = f"⚠ {inj.status}"
        sections = analysis_sections(pdata, base, team, opp, line, is_over, prob, ctx, odds, home_known, is_home, rotations, injuries)
        picks.append(Pick("player", f"{info.name} {short}", short, game_label, when, info.name, team, opp, prop, line, is_over,
                          prob, score, None, chips, reasons, pdata.recent_df.head(10).copy(), pdata.season, None, sections, warning))
    return picks


def player_picks_for_team(logs, season, team, opp, is_home, home_known, odds, info_by_id, game_label, when, injuries=None, prev_logs=None, day=None) -> list:
    picks, ctx_memo, done = [], {}, 0
    injuries = injuries or {}
    rotations = {team: team_rotation(logs, team, n=9), opp: team_rotation(logs, opp, n=9)}
    prev_season = previous_season(season)
    for _, r in rotations[team].iterrows():
        if done >= PICK_TOP_PLAYERS: break
        pid = int(r["PLAYER_ID"])
        df = enrich_gamelog(rows_for_player(logs, pid, team).copy())
        if df.empty: continue
        info = info_by_id.get(pid) or PlayerInfo(pid, str(r["NAME"]), team, "")
        inj = match_injury(info.name, injuries.get(team, []))
        if inj is not None and absence_weight(inj.status) >= 0.75: continue   # out / doubtful – the next man up gets the slot
        done += 1
        prev_df = enrich_gamelog(rows_for_player(prev_logs, pid).copy()) if prev_logs is not None and not prev_logs.empty else df.iloc[0:0]
        pdata = build_player_data(info, df, season, prev_df, prev_season)
        group = info.position[:1].upper()
        if group not in ctx_memo:   # one matchup lookup per position group, not per player
            try: ctx_memo[group] = build_matchup_context(pdata, opp)
            except Exception: ctx_memo[group] = None
        ctx = ctx_memo[group]
        picks += PICK_BOOK.get_or_compute(
            pick_key(pid, team, opp, day, injuries),
            lambda: player_pick_candidates(pdata, info, team, opp, is_home, home_known, odds, ctx, rotations, injuries, game_label, when))
    return picks


def team_market_picks(game: DayGame, metrics: dict, label: str, logs: Optional[pd.DataFrame] = None) -> list:
    odds = game.odds
    if odds is None: return []
    h, a = odds.lines.get(game.home), odds.lines.get(game.away)
    if not h or not a or h.ml is None or a.ml is None: return []
    raw_h, raw_a = american_to_prob(h.ml), american_to_prob(a.ml)
    fair = {game.home: raw_h / (raw_h + raw_a), game.away: raw_a / (raw_h + raw_a)}
    wp = compute_win_prob(game.home, game.away, game.home_known, None, metrics)
    if wp is None: return []
    model = {game.home: wp.p_home, game.away: 1 - wp.p_home}
    picks = []
    for team, opp, line in ((game.home, game.away, h), (game.away, game.home, a)):
        dec = american_to_decimal(line.ml)
        edge = model[team] - fair[team]
        if not (PICK_ODDS_MIN <= dec <= PICK_ODDS_MAX) or edge < 0.01: continue
        mt, mo = metrics.get(team), metrics.get(opp)
        reasons = [
            f"Market: {fmt_odds(line.ml)} ({dec:.2f} decimal) – the no-vig market gives {team} a {fair[team] * 100:.0f}% chance.",
            f"OutplAI's team model gives {team} {model[team] * 100:.0f}% – {edge * 100:+.1f} points above the market.",
        ]
        if mt and mo: reasons.append(f"Net rating: {team} {mt.net_rating:+.1f} vs {opp} {mo.net_rating:+.1f}" + (", plus home court." if game.home_known and team == game.home else "."))
        recent = {t: team_recent_games(logs, t) for t in (team, opp)} if logs is not None else {}
        form = [f"{t} {sum(1 for g in recent[t] if g['wl'] == 'W')}-{sum(1 for g in recent[t] if g['wl'] == 'L')}" for t in (team, opp) if recent.get(t)]
        if form: reasons.append("Last 5 games: " + ", ".join(form) + ".")
        reasons.append("Check injuries and lineups before betting.")
        picks.append(Pick("team", f"{team} to win", "Moneyline", label, game.when, "", team, opp, "", 0.0, True,
                          model[team] * 100, model[team] * 100 + 120 * edge, dec,
                          [f"Model {model[team] * 100:.0f}%", f"Market {fair[team] * 100:.0f}%", f"Odds {dec:.2f}"], reasons, None, "", recent))
    return picks


def build_game_picks(game: DayGame, logs: pd.DataFrame, season: str, info_by_id: dict, metrics: dict, injuries: Optional[dict] = None, prev_logs: Optional[pd.DataFrame] = None) -> list:
    label = f"{game.away} @ {game.home}" if game.home_known else f"{game.home} vs {game.away}"
    picks = []
    for team, opp, is_home in ((game.home, game.away, True), (game.away, game.home, False)):
        try: picks += player_picks_for_team(logs, season, team, opp, is_home, game.home_known, game.odds, info_by_id, label, game.when, injuries, prev_logs, game.day)
        except Exception: log.exception("Player picks failed for %s", team)
    try: picks += team_market_picks(game, metrics, label, logs)
    except Exception: log.exception("Team picks failed for %s", label)
    return picks


def select_top_picks(picks: list, limit: int = 8, per_game: int = 3) -> list:
    chosen, players_used, per = [], set(), {}
    for pick in sorted(picks, key=lambda x: x.score, reverse=True):
        if pick.player and pick.player in players_used: continue
        if per.get(pick.game, 0) >= per_game: continue
        chosen.append(pick)
        if pick.player: players_used.add(pick.player)
        per[pick.game] = per.get(pick.game, 0) + 1
        if len(chosen) >= limit: break
    return chosen


def compute_today_picks(limit: int = 8, progress: Optional[Callable] = None) -> TodayPicks:
    """Runs on a worker thread. Loads run in parallel, games are analysed in parallel; `progress(text)` reports each step."""
    say = progress or (lambda _msg: None)
    cached = _today_cache.get("today")
    if cached is not None: return cached
    say("Finding the next games…")
    day, games = find_pick_games()
    if not games:
        return TodayPicks(day, 0, [], current_season(), "No upcoming NBA games found in the next few days.")
    say("Loading player logs, injuries and team ratings…")
    with ThreadPoolExecutor(max_workers=4) as pool:
        f_logs = pool.submit(get_pick_logs)
        f_inj = pool.submit(safe_call, fetch_injuries, {})
        f_index = pool.submit(safe_call, load_player_index, [])
        logs, season = f_logs.result()
        f_metrics = pool.submit(safe_call, fetch_team_metrics, {}, season)
        f_prev = pool.submit(safe_call, fetch_league_player_logs, pd.DataFrame(), previous_season(season))
        inj, index, metrics, prev_logs = f_inj.result(), f_index.result(), f_metrics.result(), f_prev.result()
    if logs.empty:
        return TodayPicks(day, len(games), [], season, "Could not load player data.")
    info_by_id = {p.id: p for p in index}
    def one_game(game):
        try: return build_game_picks(game, logs, season, info_by_id, metrics, inj, prev_logs)
        except Exception:
            log.exception("Game analysis failed for %s @ %s", game.away, game.home)
            return []
    everything = []
    with ThreadPoolExecutor(max_workers=4) as pool:
        for i, found in enumerate(pool.map(one_game, games), 1):
            say(f"Analysed game {i}/{len(games)}…")
            everything += found
    say("Ranking picks…")
    result = TodayPicks(day, len(games), select_top_picks(everything, limit), season,
                        "" if everything else "No pick met the 45–58% / 1.70–2.10 window today.")
    _today_cache.set("today", result)
    return result



xlog = logging.getLogger("outplai.ext")


# ====================================================================== 1. pools + cache
IO_POOL = ThreadPoolExecutor(max_workers=10, thread_name_prefix="outplai-io")     # network + long workers
CPU_POOL = ThreadPoolExecutor(max_workers=3, thread_name_prefix="outplai-cpu")    # analysis jobs (may call IO_POOL)


def shutdown_pools():
    for pool in (IO_POOL, CPU_POOL):
        pool.shutdown(wait=False, cancel_futures=True)


class Memo:
    """Thread-safe TTL cache with single-flight loading (many threads asking = one computation) and a size cap."""
    def __init__(self, ttl: float, maxsize: int = 512):
        self.ttl, self.maxsize = ttl, maxsize
        self._data, self._gates, self._lock = {}, {}, threading.Lock()

    def _fresh(self, key):
        hit = self._data.get(key)
        return hit if hit and time.monotonic() - hit[0] < self.ttl else None

    def get_or_compute(self, key, factory: Callable):
        with self._lock:
            hit = self._fresh(key)
            if hit: return hit[1]
            gate = self._gates.setdefault(key, threading.Lock())
        with gate:
            with self._lock:
                hit = self._fresh(key)
                if hit: return hit[1]
            value = factory()
            with self._lock:
                self._data[key] = (time.monotonic(), value)
                if len(self._data) > self.maxsize:
                    for k in sorted(self._data, key=lambda k_: self._data[k_][0])[: len(self._data) - self.maxsize]:
                        self._data.pop(k, None)
                self._gates.pop(key, None)
            return value

    def clear(self):
        with self._lock: self._data.clear()


# ====================================================================== 2. unified pick book (single source of truth)
PICK_BOOK = Memo(600, 1024)


def injury_signature(injuries: Optional[dict], *teams) -> int:
    return hash(tuple(sorted((t, i.name, i.status) for t in teams for i in (injuries or {}).get(t, []))))


def pick_key(pid: int, team: str, opp: str, day, injuries: Optional[dict]) -> tuple:
    """Same key from the search page and from Today's picks -> the same cached candidate list -> the same pick."""
    return (int(pid), team, opp, str(day), injury_signature(injuries, team, opp))


def best_player_pick(candidates: list):
    """THE rule for a player's recommendation: highest engine score across all props, lines and sides."""
    return max(candidates, key=lambda p: p.score) if candidates else None


# ====================================================================== 3. advanced stats
def _col(df: pd.DataFrame, name: str) -> pd.Series:
    return pd.to_numeric(df[name], errors="coerce") if name in df.columns else pd.Series(np.nan, index=df.index)


def _adv_block(rows: pd.DataFrame, team_tot: Optional[pd.DataFrame]) -> dict:
    out = {"USG": float("nan"), "TS": float("nan"), "EFG": float("nan")}
    if rows.empty: return out
    fga, fta, fgm, tpm, pts = (_col(rows, c).sum() for c in ("FGA", "FTA", "FGM", "FG3M", "PTS"))
    if fga + 0.44 * fta > 0: out["TS"] = pts / (2 * (fga + 0.44 * fta)) * 100
    if fga > 0: out["EFG"] = (fgm + 0.5 * tpm) / fga * 100
    if team_tot is not None and "GAME_ID" in rows.columns:
        m = rows.assign(GAME_ID=rows["GAME_ID"].astype(str)).merge(team_tot, left_on="GAME_ID", right_index=True, how="inner")
        mins = _col(m, "MIN")
        m = m[mins > 0]
        if not m.empty:
            poss = _col(m, "FGA") + 0.44 * _col(m, "FTA") + _col(m, "TOV")
            num = (poss * (m["T_MIN"] / 5)).sum()
            den = (_col(m, "MIN") * (m["T_FGA"] + 0.44 * m["T_FTA"] + m["T_TOV"])).sum()
            if den > 0: out["USG"] = 100 * num / den
    return out


def advanced_stats(player_df: pd.DataFrame, league_logs: Optional[pd.DataFrame], team: str) -> dict:
    """{'season': {USG, TS, EFG}, 'l5': {...}}. USG% uses the standard box-score formula with team totals from the league log."""
    team_tot = None
    try:
        if league_logs is not None and not league_logs.empty:
            t = league_logs[league_logs["TEAM_ABBREVIATION"] == team].copy()
            for c in ("FGA", "FTA", "TOV", "MIN"): t[c] = pd.to_numeric(t[c], errors="coerce")
            team_tot = t.groupby(t["GAME_ID"].astype(str))[["FGA", "FTA", "TOV", "MIN"]].sum()
            team_tot.columns = ["T_FGA", "T_FTA", "T_TOV", "T_MIN"]
    except Exception as exc:
        xlog.warning("Team totals for USG%% unavailable: %s", exc)
    return {"season": _adv_block(player_df, team_tot), "l5": _adv_block(player_df.head(5), team_tot)}


def position_def_ratings(ctx) -> dict:
    """Per position group: 0 = toughest defence vs that group, 100 = softest (average rank of PTS/REB/AST/3PM allowed)."""
    out = {}
    if ctx is None: return out
    n = max(ctx.pos_n, 2)
    for g, stats in (ctx.pos_all or {}).items():
        core = {k: v for k, v in (stats or {}).items() if k in POS_CORE}
        ranks = [r for _, r in core.values()]
        if not ranks: continue
        score = float(np.mean([(r - 1) / (n - 1) for r in ranks]) * 100)
        label = "soft" if score >= 67 else "tough" if score <= 33 else "average"
        detail = ", ".join(f"{s} {v:.1f}" for s, (v, _) in core.items())
        out[g] = {"score": score, "label": label, "detail": detail, "mine": g == ctx.pos_group}
    return out


# ====================================================================== 4. head-to-head layer
def h2h_games(loader: Callable, seasons: list, opp: Optional[str]) -> pd.DataFrame:
    """All games of one player vs one opponent over several seasons (loader(season) -> enriched game log)."""
    if not opp: return pd.DataFrame()
    def safe(season):
        try: return loader(season)
        except Exception: return pd.DataFrame()
    frames = [f for f in IO_POOL.map(safe, seasons) if f is not None and not f.empty]
    if not frames: return pd.DataFrame()
    df = pd.concat(frames, ignore_index=True)
    df = df[df["OPPONENT"] == opp]
    return df.sort_values("GAME_DATE_DT", ascending=False).reset_index(drop=True)


def h2h_summary(df: pd.DataFrame, prop: str, line: float, is_over: bool, overall_mean: float) -> dict:
    vals = df[prop].dropna() if (not df.empty and prop in df.columns) else pd.Series(dtype=float)
    n = len(vals)
    if n == 0: return {"n": 0}
    over, under = int((vals > line).sum()), int((vals < line).sum())
    hits = over if is_over else under
    decided = over + under
    mean = float(vals.mean())
    ratio = mean / overall_mean if overall_mean and overall_mean > 0 else 1.0
    weight = n / (n + 6.0)                                   # few games -> small weight
    effect = max(-0.04, min(0.04, 0.5 * (ratio - 1) * weight))
    rows = []
    for _, r in df.head(8).iterrows():
        v = r[prop]
        state = "push" if v == line else ("hit" if (v > line) == is_over else "miss")
        rows.append((r["GAME_DATE_DT"].strftime("%b %d, %Y"), str(r["MATCHUP"]), f"{v:g}", f"{r['MIN']:.0f}" if pd.notna(r["MIN"]) else "–", state))
    return {"n": n, "mean": mean, "vs_overall": (ratio - 1) * 100, "hits": hits, "decided": decided,
            "hit_rate": hits / decided * 100 if decided else 0.0, "effect": effect, "weight": weight, "rows": rows}


# ====================================================================== 5. quarter / half splits
SPLIT_MEMO = Memo(1800, 256)
PROP_PARTS = {"PTS": ("PTS",), "REB": ("REB",), "AST": ("AST",), "FG3M": ("FG3M",), "STL": ("STL",), "BLK": ("BLK",),
              "PR": ("PTS", "REB"), "PA": ("PTS", "AST"), "RA": ("REB", "AST"), "PRA": ("PTS", "REB", "AST"), "STL_BLK": ("STL", "BLK"),
              "FTM": ("FTM",), "FGA": ("FGA",), "FG2M": ("FGM",)}
PERIOD_ORDER = ["1st Quarter", "2nd Quarter", "3rd Quarter", "4th Quarter", "1st Half", "2nd Half"]


def fetch_period_splits(player_id: int, season: str) -> dict:
    """{'half': df, 'period': df} per-game averages by half / quarter (nba_api PlayerDashboardByGameSplits)."""
    def load():
        try:
            from nba_api.stats.endpoints import playerdashboardbygamesplits as ep_mod
            ep = ep_mod.PlayerDashboardByGameSplits(player_id=player_id, season=season, per_mode_detailed="PerGame", timeout=15)
            frames = ep.get_data_frames()
            def pick(attr, idx):
                node = getattr(ep, attr, None)
                if node is not None: return node.get_data_frame()
                return frames[idx] if len(frames) > idx else pd.DataFrame()
            return {"half": pick("by_half_player_dashboard", 2), "period": pick("by_period_player_dashboard", 3)}
        except Exception as exc:
            xlog.warning("Period splits unavailable: %s", exc)
            return {}
    return SPLIT_MEMO.get_or_compute((player_id, season), load)


def split_table(splits: dict, prop: str) -> list:
    """Rows: (segment, MIN, PTS, REB, AST, 3PM, prop value, share of full game %, is_late)."""
    frames = [f for f in (splits.get("period"), splits.get("half")) if f is not None and not f.empty]
    if not frames: return []
    df = pd.concat(frames, ignore_index=True)
    df = df[df["GROUP_VALUE"].isin(PERIOD_ORDER)].copy()
    parts = PROP_PARTS.get(prop, ("PTS",))
    df["PROPV"] = sum(_col(df, c) for c in parts)
    if prop == "FG2M": df["PROPV"] = _col(df, "FGM") - _col(df, "FG3M")
    quarters = df[df["GROUP_VALUE"].str.contains("Quarter")]["PROPV"].sum()
    rows = []
    for name in PERIOD_ORDER:
        r = df[df["GROUP_VALUE"] == name]
        if r.empty: continue
        r = r.iloc[0]
        share = r["PROPV"] / quarters * 100 if quarters > 0 else float("nan")
        rows.append((name, r.get("MIN"), r.get("PTS"), r.get("REB"), r.get("AST"), r.get("FG3M"), r["PROPV"], share, name in ("4th Quarter", "2nd Half")))
    return rows


# ====================================================================== 6. analysis text helpers
def norm_prob(mean: float, std: float, line: float, is_over: bool) -> Optional[float]:
    if mean is None or std is None or math.isnan(mean) or math.isnan(std): return None
    if std <= 0: return 100.0 if (mean > line) == is_over and mean != line else 50.0 if mean == line else 0.0
    p_over = (1 - norm.cdf((line - mean) / std)) * 100
    return p_over if is_over else 100 - p_over


def injury_impact_lines(base, clean, p_full, p_clean, line, is_over, status_text, report_lines, title) -> list:
    out, side = [], "over" if is_over else "under"
    if status_text:
        out.append(f"{status_text} Confidence ×{base.conf:.2f}, minutes ×{base.mfac:.2f} if he plays.")
    absences = [(l, p) for l, p in base.notes if " without " in l]
    if absences:
        out.append("Key absences and what they do to his projection:")
        out += [f"   – {l}: {p:+.1f}% on expected {title.lower()}." for l, p in absences]
    else:
        out.append("No rotation absence moves this projection – no lineup adjustment applied.")
    out += report_lines
    if p_full is not None and p_clean is not None and clean is not None:
        d = (base.mean / clean.mean - 1) * 100 if clean.mean else 0.0
        out.append(f"Projection: {clean.mean:.1f} with a fully healthy slate → {base.mean:.1f} with the current report ({d:+.1f}%).")
        out.append(f"Probability of {side} {line:g}: {p_clean:.1f}% → {p_full:.1f}% ({p_full - p_clean:+.1f} pts) because of the injury report.")
    return out


def final_probability_lines(base, line, is_over, prob, h2h: dict, prop_odds, title) -> list:
    side = "over" if is_over else "under"
    out = [f"Projection {base.mean:.1f} ± {base.std:.1f} {title.lower()} (recent form {base.raw_mean:.1f}, matchup/context multiplier ×{base.mult:.3f}, minutes ×{base.mfac:.2f})."]
    if base.std > 0:
        z = (line - base.mean) / base.std
        raw = norm_prob(base.mean, base.std, line, is_over)
        out.append(f"P({side} {line:g}) = {'1 − ' if is_over else ''}Φ(({line:g} − {base.mean:.1f}) / {base.std:.1f}) = Φ({z:+.2f}) → {raw:.1f}%  (normal model).")
    out.append(f"Availability: {base.conf * 100:.0f}% to play pulls the result toward 50% → final model probability {prob:.1f}%." if prob is not None else "Not enough games for a probability.")
    if prob is not None and h2h.get("n", 0) >= 2:
        eff = h2h["effect"]
        p2 = norm_prob(base.mean * (1 + eff), base.std * (1 + eff), line, is_over)
        if p2 is not None:
            p2 = 50 + (p2 - 50) * base.conf
            out.append(f"H2H check ({h2h['n']} games vs this team, weight {h2h['weight']:.2f}): projection {eff * 100:+.1f}% → {p2:.1f}% (not part of the headline number).")
    if prob is not None and prob > 0:
        out.append(f"Fair price for this side: {100 / prob:.2f} decimal ({_american(100 / prob)}).")
    if prop_odds is not None:
        price = prop_odds.over if is_over else prop_odds.under
        if price is not None:
            dec = 1 + price / 100 if price > 0 else 1 + 100 / -price
            out.append(f"{prop_odds.book}: {price:+d} ({dec:.2f}) at {prop_odds.point:g} → model edge {(prob / 100 * dec - 1) * 100:+.1f}% EV per unit." if prob is not None else "")
    return [x for x in out if x]


def _american(dec: float) -> str:
    if dec <= 1: return "–"
    return f"+{round((dec - 1) * 100)}" if dec >= 2 else f"{round(-100 / (dec - 1))}"





# ====================================================================================================
#  WEB LAYER  -  serves the OutplAI dashboard in a browser (standard library WSGI server, no Flask needed)
#  Everything above this line is the same data + model code as the desktop app.
# ====================================================================================================
import argparse
from urllib.parse import parse_qs
import hashlib
import mimetypes
import socket
import sys
from dataclasses import fields as dc_fields, is_dataclass
from socketserver import ThreadingMixIn
from wsgiref.simple_server import WSGIRequestHandler, WSGIServer, make_server

HERE = os.path.dirname(os.path.abspath(__file__)) if "__file__" in globals() else os.getcwd()
BRAND_IMAGE = "image_3c998c.png"
ALLOW_KEY_EDIT = True          # set in main(): only for local servers unless OUTPLAI_ALLOW_KEY_EDIT=1


@dataclass
class ChartBar:
    value: float
    text: str
    state: str
    opp: str
    date: str
    tip: list
    prev: bool = False
    season: str = ""


def jsonable(o):
    """Recursively convert pandas / numpy / dataclass values into plain JSON (NaN -> null)."""
    if o is None or isinstance(o, (str, bool)): return o
    if isinstance(o, (np.bool_,)): return bool(o)
    if isinstance(o, (int, np.integer)): return int(o)
    if isinstance(o, (float, np.floating)):
        f = float(o)
        return None if math.isnan(f) or math.isinf(f) else f
    if isinstance(o, (pd.Timestamp, datetime, date)): return o.isoformat()
    if isinstance(o, dict): return {str(k): jsonable(v) for k, v in o.items()}
    if isinstance(o, (list, tuple, set)): return [jsonable(x) for x in o]
    if isinstance(o, pd.Series): return [jsonable(x) for x in o.tolist()]
    if isinstance(o, pd.DataFrame): return [jsonable(r) for r in o.to_dict("records")]
    if is_dataclass(o) and not isinstance(o, type): return {f.name: jsonable(getattr(o, f.name)) for f in dc_fields(o)}
    if isinstance(o, SimpleNamespace): return jsonable(vars(o))
    return str(o)


class ApiError(Exception):
    def __init__(self, message: str, kind: str = "data", status: int = 400):
        super().__init__(message)
        self.kind, self.status = kind, status


# ---------------------------------------------------------------- request context (the browser keeps the state, the server re-builds it)
_player_cache = TTLCache(300)
_enrich_cache = TTLCache(180)
_gamepick_memo = Memo(600, 128)
_jobs: dict = {}
_jobs_lock = threading.Lock()


def load_player(name: str) -> PlayerData:
    key = normalize_text(name).strip()
    hit = _player_cache.get(key)
    if hit is not None: return hit
    data = get_player_data(name)
    _player_cache.set(key, data)
    return data


def _query_from(d: dict) -> PropQuery:
    return PropQuery(player=str(d["player"]), is_over=bool(d["is_over"]), line=float(d["line"]), prop_key=str(d["prop_key"]),
                     opponent=(d.get("opponent") or None))


def _filters_from(d: dict) -> Filters:
    sample = d.get("sample", "L5")
    if sample not in SAMPLE_SIZES: sample = "L5"
    minutes = int(d.get("minutes") or 0)
    return Filters(sample, d.get("split", "All games"), minutes, d.get("rest", "Any rest"), bool(d.get("h2h")))


def _game_from(d: Optional[dict]) -> Optional[UpcomingGame]:
    if not d: return None
    gd = None
    if d.get("game_date"):
        try: gd = date.fromisoformat(str(d["game_date"])[:10])
        except ValueError: gd = None
    return UpcomingGame(str(d["opponent"]), bool(d["is_home"]), str(d.get("when_label", "")), int(d.get("status", 1)),
                        str(d.get("source", "espn")), str(d.get("short_date", "")), gd)


def request_ctx(b: dict) -> SimpleNamespace:
    player = load_player(b["name"])
    game = _game_from(b.get("game"))
    return SimpleNamespace(player=player, query=_query_from(b["query"]) if b.get("query") else None, filters=_filters_from(b.get("filters") or {}),
                           game=game, lookup=ScheduleLookup(game, "Could not reach the NBA schedule." if b.get("sched_err") else None),
                           opp=(b.get("opp") or None), home=b.get("home"), away=b.get("away"), hk=bool(b.get("hk")))


def game_day(R) -> date:
    return R.game.game_date if R.game and R.game.game_date else today_eastern()


def resolve_matchup(player: PlayerData, lookup: ScheduleLookup, query: PropQuery) -> tuple:
    game = lookup.game
    opponent = query.opponent or (game.opponent if game else None)
    if game and (not query.opponent or query.opponent == game.opponent): home_known, is_home = True, game.is_home
    else: home_known, is_home = False, True
    team = player.team_abbr
    home, away = (team, opponent) if is_home else (opponent, team)
    return opponent, home, away, home_known


def game_subtitle(R) -> str:
    p, g, q = R.player, R.game, R.query
    if q.opponent and (g is None or q.opponent != g.opponent): return f"{p.team_abbr} vs {q.opponent} · manual matchup"
    if g: return f"{p.team_abbr} {'vs' if g.is_home else '@'} {g.opponent} · {g.when_label}"
    return "Schedule unavailable" if R.lookup and R.lookup.error else "No upcoming game scheduled"


# ---------------------------------------------------------------- enrichment (matchup, odds, injuries, team data) - computed once, cached
def compute_team_data(player: PlayerData, opp: Optional[str]) -> tuple:
    logs, lseason = pd.DataFrame(), player.season
    try:
        season = player.season
        profile = fetch_team_profile(season)
        if not profile:
            season = previous_season(season)
            profile = fetch_team_profile(season)
        logs, lseason = get_pick_logs()
        rotations = {a: team_rotation(logs, a, 9) for a in (player.team_abbr, opp) if a}
        return (season, lseason, profile, rotations)
    except Exception:
        log.exception("Team data failed")
        return (player.season, lseason, {}, {})


def odds_for(R) -> tuple:
    try: game = find_game_odds(R.player.team_abbr, R.opp, R.lookup)
    except Exception as exc:
        log.warning("Odds lookup failed: %s", exc)
        game = None
    note = "" if game is not None else ("No sportsbook lines posted for this game yet." if R.opp else "No opponent yet.")
    return game, note


def get_enrich(R, compute: bool = True) -> Optional[SimpleNamespace]:
    key = (R.player.player_id, R.opp or "", str(game_day(R)))
    hit = _enrich_cache.get(key)
    if hit is not None or not compute: return hit
    p, opp = R.player, R.opp
    ctx, err = None, None
    if opp:
        try: ctx = build_matchup_context(p, opp)
        except Exception:
            log.exception("Matchup failed")
            err = "Matchup data unavailable."
    else:
        err = "No opponent yet. Add  vs BOS  to your search."
    odds, note = odds_for(R)
    injuries = safe_call(fetch_injuries, {})
    E = SimpleNamespace(ctx=ctx, err=err, odds=odds, note=note, injuries=injuries or {}, team_data=compute_team_data(p, opp))
    _enrich_cache.set(key, E)
    return E


def model_adjust(R, E, prop_key: str) -> tuple:
    p = R.player
    is_home = R.home == p.team_abbr
    extra = []
    if E is not None and E.team_data and E.injuries:
        extra = injury_effects(p.team_abbr, R.opp or "", prop_key, E.team_data[3], E.injuries, p.name)
    return matchup_adjustment(p, replace(R.query, prop_key=prop_key), E.ctx if E else None, E.odds if E else None, R.hk, is_home, extra)


def player_injury(R, E) -> Optional[InjuryItem]:
    return match_injury(R.player.name, (E.injuries if E else {}).get(R.player.team_abbr, []))


def injury_dict(it: InjuryItem) -> dict:
    bg, fg, short, sev = injury_style(it.status)
    return {"name": it.name, "pos": it.pos, "status": it.status, "comment": it.comment, "bg": bg, "fg": fg, "short": short, "sev": sev}


def odds_dict(o: Optional[GameOdds]) -> Optional[dict]:
    if o is None: return None
    return {"event_id": o.event_id, "home": o.home, "away": o.away, "total": o.total, "over_price": o.over_price, "under_price": o.under_price,
            "book": o.book, "source": o.source, "lines": {t: {"ml": l.ml, "spread": l.spread, "spread_price": l.spread_price} for t, l in o.lines.items()}}


def prop_odds_for(R, E) -> Optional[dict]:
    if not (ODDS_API_KEY and E and E.odds and E.odds.source == "odds-api" and R.query): return None
    try: po = fetch_prop_odds(E.odds.event_id, R.query.prop_key, R.player.name, R.query.line)
    except Exception: po = None
    return None if po is None else {"point": po.point, "over": po.over, "under": po.under, "book": po.book}


# ---------------------------------------------------------------- /api/search
def api_parse(b: dict) -> dict:
    try: q = parse_search_query(str(b.get("q", "")))
    except QueryError as exc: raise ApiError(str(exc), "format")
    return {"query": jsonable(q)}


def api_search(b: dict) -> dict:
    try: query = parse_search_query(str(b.get("q", "")))
    except QueryError as exc: raise ApiError(str(exc), "format")
    player = load_player(query.player)
    lookup = lookup_next_game(player.team_abbr)
    opponent, home, away, home_known = resolve_matchup(player, lookup, query)
    g = lookup.game
    game = None if g is None else {"opponent": g.opponent, "is_home": g.is_home, "when_label": g.when_label, "status": g.status, "source": g.source,
                                   "short_date": g.short_date, "game_date": g.game_date.isoformat() if g.game_date else None}
    pill_lines = {k: suggest_line(player.recent_df, PILL_TO_PROP[k]) for k in PILL_KEYS}
    return {"player": {"id": player.player_id, "name": player.name, "team": player.team_abbr, "position": player.position, "season": player.season,
                       "prev_season": player.prev_season, "is_rookie": player.is_rookie, "year": year_label(player.season), "prev_year": year_label(player.prev_season)},
            "query": jsonable(query), "game": game, "sched_err": bool(lookup.error), "opp": opponent, "home": home, "away": away, "hk": home_known,
            "pill_lines": pill_lines}


# ---------------------------------------------------------------- /api/view  (hit rate, tabs, chart, alt lines)
def view_payload(R, E) -> dict:
    p, q, f = R.player, R.query, R.filters
    mult, notes = model_adjust(R, E, q.prop_key)
    v = build_view(p, q, f, R.opp, adjust=mult)

    title = HIT_TITLES[f.sample]
    if f.sample.startswith("L") and len(v.sample) and "SEASON_LABEL" in v.sample.columns:
        padded = int((v.sample["SEASON_LABEL"] != p.season).sum())
        if padded: title += f"  ·  {padded} from {p.prev_season}"
    if f.h2h_only: title += "  ·  H2H"
    hit = {"title": title, "big": f"{v.hit_rate:.0f}%" if v.decided else "–", "sub": f"{v.hits} of {v.decided}" if v.decided else "no games",
           "tone": ("good" if v.hit_rate >= 50 else "bad") if v.decided else "text"}

    if v.model_prob is None: model = {"text": "n/a", "tone": "muted"}
    else: model = {"text": f"{v.model_prob:.0f}%", "tone": "good" if v.model_prob >= 50 else "bad"}
    if notes:
        note = f"Model adjusted {(mult - 1) * 100:+.1f}% for the matchup: " + ", ".join(f"{label} {pct:+.1f}%" for label, pct in notes)
    elif R.opp and (E is None or E.ctx is None) and not (E and E.err):
        note = "Model: recent form only for now – loading matchup data…"
    else:
        note = "Model: recent form only (no strong matchup edge found)"
    hurt = player_injury(R, E)
    if hurt is not None and absence_weight(hurt.status) >= 0.75:
        note = f"⚠ Listed {hurt.status.upper()} on the injury report – this only applies if he plays.  " + note
    injury = None
    if hurt is not None:
        injury = {"text": f"🩺 {hurt.status}" + (f" – {hurt.comment[:70]}" if hurt.comment else ""), "color": injury_style(hurt.status)[1]}

    tabs = {}
    for key in ("L5", "L10", "L15", "SEA", "PREV", "H2H"):
        rookie_tab = False
        if key == "H2H":
            active = f.h2h_only
            tv = build_view(p, q, replace(f, sample="ALL", h2h_only=True), R.opp) if R.opp else None
            name = "H2H"
        elif key == "PREV":
            active, rookie_tab = f.sample == "PREV", p.is_rookie
            tv = None if rookie_tab else build_view(p, q, replace(f, sample="PREV"), R.opp)
            name = year_label(p.prev_season)
        else:
            active = key == f.sample
            tv = build_view(p, q, replace(f, sample=key), R.opp)
            name = year_label(p.season) if key == "SEA" else key
        if tv is not None and tv.decided:
            tabs[key] = {"name": name, "active": active, "pct": f"{tv.hit_rate:.0f}%", "tone": "good" if tv.hit_rate >= 50 else "bad", "avg": f"Avg {fmt(tv.mean)}"}
        else:
            tabs[key] = {"name": name, "active": active, "pct": "–", "tone": "dim", "avg": "Rookie" if rookie_tab else ""}

    n = min(len(v.sample), CHART_MAX_BARS)
    chart = {"title": f"LAST {n} GAMES   ·   {q.title.upper()}" if n else "NO GAMES", "line": q.line, "unit": q.label, "bars": [], "next_opp": None, "next_date": "", "empty": ""}
    if v.sample.empty:
        chart["empty"] = (f"Rookie year – no {p.prev_season} games on record" if (f.sample == "PREV" and p.is_rookie) else "No games match these filters")
    else:
        chart["bars"] = make_chart_bars(v.sample, q, p.season)
        if R.opp:
            chart["next_opp"] = ("@" if R.away == p.team_abbr else "") + R.opp
            g = R.game
            chart["next_date"] = g.short_date if g and g.opponent == R.opp else ""

    alt = []
    for ln in sorted({max(0.5, q.line + d) for d in (-2, -1, 0, 1, 2)}):
        av = build_view(p, replace(q, line=ln), f, R.opp)
        alt.append({"line": ln, "text": f"{ln:g}    ·    " + (f"{av.hit_rate:.0f}% hit" if av.decided else "no data")})

    return {"subtitle": game_subtitle(R), "position": p.position or "", "target": f"{q.title}  ·", "side": f"{q.side} {q.line:g}",
            "hit": hit, "avg": fmt(v.mean), "med": fmt(v.median), "model": model, "season": f"{fmt(v.season_mean)}  ({v.games_total} gm · {p.season})",
            "rookie": f"⚠ Rookie year – no {p.prev_season} games on record" if p.is_rookie else "", "model_note": note, "injury": injury,
            "tabs": tabs, "chart": chart, "alt": alt, "prop_odds": prop_odds_for(R, E),
            "quick": {"Home": f.split == "Home", "Back-to-back": f.rest == "Back-to-back", "30+ min": f.minutes == 30},
            "model_adj": mult}


def api_view(b: dict) -> dict:
    R = request_ctx(b)
    return view_payload(R, get_enrich(R, compute=False))


# ---------------------------------------------------------------- /api/enrich  (matchup, odds, win predictor, injuries)
def matchup_payload(R, E) -> dict:
    ctx = E.ctx
    out = {"error": E.err, "ctx": None}
    if ctx is not None:
        weak, tough = summarize_matchup(ctx)
        out["ctx"] = {"opponent": ctx.opponent, "season": ctx.season, "pos_group": ctx.pos_group, "pos_n": ctx.pos_n, "pos_all": ctx.pos_all,
                      "team_allowed": ctx.team_allowed, "metrics": {a: jsonable(m) for a, m in ctx.team_metrics.items()},
                      "weak": weak, "tough": tough, "offense": offense_summary(ctx)}
    return out


def win_payload(R, E) -> Optional[dict]:
    if not (R.home and R.away): return None
    metrics = E.ctx.team_metrics if E and E.ctx else {}
    wp = compute_win_prob(R.home, R.away, R.hk, E.odds if E else None, metrics)
    return None if wp is None else jsonable(wp)


def api_enrich(b: dict) -> dict:
    R = request_ctx(b)
    E = get_enrich(R)
    home, away, hk = R.home, R.away, R.hk
    o = E.odds
    if o and not hk and {o.home, o.away} == {R.player.team_abbr, R.opp}:
        home, away, hk = o.home, o.away, True
    R.home, R.away, R.hk = home, away, hk
    return {"matchup": matchup_payload(R, E), "odds": odds_dict(o), "odds_note": E.note, "win": win_payload(R, E), "home": home, "away": away, "hk": hk,
            "injuries": {t: [injury_dict(i) for i in items] for t, items in E.injuries.items() if t in (R.player.team_abbr, R.opp)},
            "odds_key": bool(ODDS_API_KEY)}


def api_odds(b: dict) -> dict:
    """Light refresh used every minute: new game lines (and prop odds) only."""
    R = request_ctx(b)
    E = get_enrich(R, compute=False)
    if E is None: return {"skip": True}
    odds, note = odds_for(R)
    if odds is not None:
        E.odds, E.note = odds, ""
    else:
        note = E.note
    home, away, hk = R.home, R.away, R.hk
    if E.odds and not hk and {E.odds.home, E.odds.away} == {R.player.team_abbr, R.opp}:
        home, away, hk = E.odds.home, E.odds.away, True
    R.home, R.away, R.hk = home, away, hk
    return {"odds": odds_dict(E.odds), "odds_note": note, "win": win_payload(R, E), "home": home, "away": away, "hk": hk,
            "prop_odds": prop_odds_for(R, E), "odds_key": bool(ODDS_API_KEY)}


# ---------------------------------------------------------------- /api/profile
def api_profile(b: dict) -> dict:
    R = request_ctx(b)
    p = R.player
    labels = [year_label(p.season), year_label(p.prev_season)]
    prev = b.get("which") == "prev"
    df, season = (p.prev_df, p.prev_season) if prev else (p.df, p.season)
    out = {"labels": labels, "which": "prev" if prev else "cur", "season": season}
    if df.empty:
        return {**out, "empty": True, "tiles": {}, "games": "", "note": f"⚠ Rookie year – no {season} games on record", "note_tone": "gold"}
    tracking = fetch_player_tracking(p.player_id, season) if b.get("tracking") else _league_cache.get(("track", p.player_id, season))
    tiles = {k: list(v) for k, v in build_profile(df, tracking).items()}
    if tracking is None: note, tone = "Loading tracking data (potential assists, rebound chances, drives)…", "muted"
    elif not tracking: note, tone = "NBA tracking data is unavailable right now – game-log stats shown only.", "muted"
    else: note, tone = "", "muted"
    return {**out, "empty": False, "tiles": tiles, "games": f"{len(df)} games · {season} · per-game averages", "note": note, "note_tone": tone, "loading": tracking is None}


# ---------------------------------------------------------------- /api/teams
def team_page_payload(abbr: Optional[str], td: Optional[tuple], idx: dict, has_player: bool) -> dict:
    if not abbr:
        return {"abbr": None, "note": "Search a player to fill this page." if not has_player else "No opponent yet. Add  vs BOS  to your search."}
    if td is None: return {"abbr": abbr, "name": _team_tables()[2].get(abbr, abbr), "note": "Loading team statistics…", "stats": {}, "rotation": []}
    season, lseason, profile, rotations = td
    entry, rot = profile.get(abbr), rotations.get(abbr)
    records = rot.to_dict("records") if rot is not None and not rot.empty else []
    rotation = []
    for r in records:
        hurt = idx.get(normalize_text(str(r["NAME"])))
        rotation.append({"name": str(r["NAME"]), "tag": injury_style(hurt.status)[2] if hurt else "", "min": fmt(r["MIN"]), "pts": fmt(r["PTS"]), "reb": fmt(r["REB"]),
                         "ast": fmt(r["AST"]), "fg3m": fmt(r["FG3M"])})
    return {"abbr": abbr, "name": _team_tables()[2].get(abbr, abbr), "record": list(entry["record"]) if entry else None, "season": season, "rot_season": lseason,
            "stats": {k: list(v) for k, v in (entry or {}).get("stats", {}).items()}, "rotation": rotation,
            "note": "" if profile else "Team statistics are unavailable right now."}


def api_teams(b: dict) -> dict:
    R = request_ctx(b)
    E = get_enrich(R)
    idx = injury_index(E.injuries)
    return {"team": team_page_payload(R.player.team_abbr, E.team_data, idx, True), "opp": team_page_payload(R.opp, E.team_data, idx, True)}


# ---------------------------------------------------------------- /api/best  (best player's pick + best game pick, same engine as Today's picks)
def unified_pick(R, E):
    p = R.player
    if not (R.opp and E and E.team_data and (E.ctx is not None or E.err)): return None
    game = R.game
    is_home = R.home == p.team_abbr
    key = pick_key(p.player_id, p.team_abbr, R.opp, game_day(R), E.injuries)
    home, away = (p.team_abbr, R.opp) if is_home else (R.opp, p.team_abbr)
    label = f"{away} @ {home}" if R.hk else f"{home} vs {away}"
    info = PlayerInfo(p.player_id, p.name, p.team_abbr, p.position)
    cands = PICK_BOOK.get_or_compute(key, lambda: player_pick_candidates(
        p, info, p.team_abbr, R.opp, is_home, R.hk, E.odds, E.ctx, E.team_data[3], E.injuries, label, game.when_label if game else ""))
    return best_player_pick(cands), cands


def api_best_player(b: dict) -> dict:
    R = request_ctx(b)
    E = get_enrich(R)
    p, head = R.player, "⭐ OUTPLAI BEST PLAYER'S PICK"
    hurt = player_injury(R, E)
    if hurt is not None and absence_weight(hurt.status) >= 0.75:
        return {"text": f"{head}\n{p.name.upper()} is listed {hurt.status.upper()} – no pick"}
    if not R.opp: return {"text": f"{head}\nAdd  vs BOS  to your search to get a pick"}
    res = unified_pick(R, E)
    if res is None: return {"text": f"{head}\nCalculating with matchup + injury data…"}
    best = res[0]
    if best is None: return {"text": f"{head}\nNo line clears the 45–58% / hit-rate filter"}
    return {"text": f"{head}\n{p.name.upper()} {best.short.upper()}   •   ~{best.prob:.0f}%\n(same engine as Today's picks)"}


def day_game_for(R, odds: Optional[GameOdds]) -> DayGame:
    g, p, opp = R.game, R.player, R.opp
    day = game_day(R)
    if odds is not None: return DayGame(odds.home, odds.away, "", odds, True, "pre", day)
    if g and g.opponent == opp:
        home, away = (p.team_abbr, opp) if g.is_home else (opp, p.team_abbr)
        return DayGame(home, away, g.when_label, None, True, "pre", day)
    return DayGame(p.team_abbr, opp, "", None, False, "pre", day)


def api_best_game(b: dict) -> dict:
    R = request_ctx(b)
    E = get_enrich(R)
    head = "🏆 OUTPLAI BEST GAME PICK"
    if not R.opp: return {"text": f"{head}\nNo opponent yet."}
    try:
        logs, lseason = get_pick_logs()
        if logs.empty: raise DataError("no player logs")
        game = day_game_for(R, E.odds)
        key = (R.player.team_abbr, R.opp, str(game.day), injury_signature(E.injuries, R.player.team_abbr, R.opp), bool(E.odds))
        def build():
            info_by_id = {p.id: p for p in load_player_index()}
            prev_logs = safe_call(fetch_league_player_logs, pd.DataFrame(), previous_season(lseason))
            picks = build_game_picks(game, logs, lseason, info_by_id, fetch_team_metrics(lseason), E.injuries, prev_logs)
            return max(picks, key=lambda x: x.score) if picks else False
        best = _gamepick_memo.get_or_compute(key, build)
    except Exception:
        log.exception("Game picks failed")
        return {"text": f"{head}\nCould not scan this game."}
    if not best: return {"text": f"{head}\nNo pick in the 45–58% / 1.70–2.10 range for this game"}
    if best.kind == "team": return {"text": f"{head}\n{best.headline} • odds {best.decimal_odds:.2f} • ~{best.prob:.0f}%\n{best.game}"}
    return {"text": f"{head}\n{best.player.upper()} {best.short} • ~{best.prob:.0f}%\n{best.game}"}


# ---------------------------------------------------------------- /api/analysis
def api_analysis(b: dict) -> dict:
    R = request_ctx(b)
    E = get_enrich(R)
    p, q, opp, ctx, odds = R.player, R.query, R.opp or "", E.ctx, E.odds
    team, prop, title = p.team_abbr, q.prop_key, q.title
    rest = rest_days_for(p, R.game.game_date if R.game else None)
    rotations = E.team_data[3] if E.team_data else {}
    inj = E.injuries
    is_home = R.home == team
    args = (p, team, opp, prop, odds, ctx, R.hk, is_home, rotations)
    base, clean = build_baseline(*args, inj), build_baseline(*args, {})
    if base is None: return {"loading": "Not enough games for a full analysis yet."}
    prob = model_probability(base, q.line, q.is_over)
    p_clean = model_probability(clean, q.line, q.is_over) if clean else None
    sec = dict(analysis_sections(p, base, team, opp or "—", q.line, q.is_over, prob, ctx, odds, R.hk, is_home, rotations, inj, rest))
    report = [ln for ln in (injury_report_line(t, rotations, inj, p.name) for t in (team, opp) if t) if ln]
    status = (status_warning(base.status) + (f" ({base.comment})" if base.comment else "")) if base.status else ""
    logs, lseason = get_pick_logs()
    adv = advanced_stats(p.df, logs if lseason == p.season else None, team)
    seasons = [p.season, previous_season(p.season), previous_season(previous_season(p.season))]
    h2h_df = h2h_games(lambda se: _safe_logs(p.player_id, se), seasons, opp)
    h2h = h2h_summary(h2h_df, prop, q.line, q.is_over, float(p.recent_df[prop].mean()))
    prop_odds = None
    if ODDS_API_KEY and odds is not None and odds.source == "odds-api":
        try: prop_odds = fetch_prop_odds(odds.event_id, prop, p.name, q.line)
        except Exception: prop_odds = None
    splits = fetch_period_splits(p.player_id, p.season)
    return {"subtitle": f"{p.name} · {title} {q.side} {q.line:g} · vs {opp or '–'} · {p.season}", "adv": adv, "posdef": position_def_ratings(ctx),
            "sections": {"form": sec["RECENT FORM"], "matchup": sec["MATCHUP"] + sec["PACE & GAME SCRIPT"] + sec["HOME / AWAY & REST"],
                         "injury": injury_impact_lines(base, clean, prob, p_clean, q.line, q.is_over, status, report, title),
                         "final": final_probability_lines(base, q.line, q.is_over, prob, h2h, prop_odds, title)},
            "h2h": h2h, "h2h_note": f"No games vs {opp} found in the last 3 seasons." if opp else "No opponent yet – add  vs BOS  to your search.",
            "splits": split_table(splits, prop), "split_note": "Quarter/half data is unavailable right now (NBA endpoint did not respond).",
            "prop_label": PROP_SHORT.get(prop, prop)}


# ---------------------------------------------------------------- /api/today  (background job + polling)
def serialize_pick(pick: Pick) -> dict:
    d = {"kind": pick.kind, "headline": pick.headline, "short": pick.short, "game": pick.game, "when": pick.when, "player": pick.player, "team": pick.team,
         "opp": pick.opp, "prop_key": pick.prop_key, "prop_short": PROP_SHORT.get(pick.prop_key, ""), "line": pick.line, "is_over": pick.is_over, "prob": pick.prob,
         "decimal_odds": pick.decimal_odds, "chips": pick.chips, "reasons": pick.reasons, "status": pick.status, "recent": pick.recent, "chart": None}
    if pick.kind == "player" and pick.sample is not None and not pick.sample.empty:
        q = PropQuery(pick.player, pick.is_over, pick.line, pick.prop_key, pick.opp)
        d["chart"] = {"title": "", "line": pick.line, "unit": PROP_SHORT.get(pick.prop_key, ""), "bars": make_chart_bars(pick.sample, q, pick.season),
                      "next_opp": None, "next_date": "", "empty": ""}
    return d


def serialize_today(res: TodayPicks) -> dict:
    return {"day": res.day.isoformat(), "day_text": res.day.strftime("%a, %b %d"), "games": res.games, "season": res.season, "note": res.note,
            "picks": [serialize_pick(p) for p in res.picks]}


def api_today(b: dict) -> dict:
    force = bool(b.get("force"))
    with _jobs_lock:
        job = _jobs.get("today")
        if job and job["status"] == "running": return {"status": "running", "msg": job["msg"]}
        if job and job["status"] == "done" and not force: return {"status": "done", "result": job["result"]}
        if force:
            _today_cache.clear()
            PICK_BOOK.clear()
        job = {"status": "running", "msg": "Scanning today's games… the first scan can take 20–40 seconds.", "result": None}
        _jobs["today"] = job
    def run():
        try:
            res = compute_today_picks(progress=lambda msg: job.__setitem__("msg", msg))
            job["result"], job["status"] = serialize_today(res), "done"
        except Exception:
            log.exception("Today's picks failed")
            job["status"] = "error"
    IO_POOL.submit(run)
    return {"status": "running", "msg": job["msg"]}


# ---------------------------------------------------------------- /api/news, /api/games, /api/roster
def api_news(b: dict) -> dict:
    player, team, opp = str(b.get("player") or ""), str(b.get("team") or ""), str(b.get("opp") or "")
    if b.get("force"): _news_cache.clear()
    items = build_news(player, team, opp)
    names = _team_tables()[2]
    if player: sub = f"News for {player}  ·  {names.get(team, team)}" + (f" vs {names.get(opp, opp)}" if opp else "")
    else: sub = "League headlines – search a player to focus this page on his team and his match."
    return {"sub": sub, "items": [{"title": i.title, "source": i.source, "ago": time_ago(i.when), "url": i.url, "summary": (i.summary or "").strip()[:220] +
                                   ("…" if len((i.summary or "").strip()) > 220 else ""), "tag": i.tag} for i in items]}


def api_games(b: dict) -> dict:
    if b.get("force"):
        _espn_cache.clear()
        _injury_cache.clear()
    day, games = fetch_schedule()
    inj = safe_call(fetch_injuries, {}) or {}
    out_games = []
    for g in games:
        spread = None
        if g.odds:
            ln = g.odds.lines.get(g.home)
            spread = ln.spread if ln else None
        count = sum(1 for t in (g.away, g.home) for it in inj.get(t, []) if injury_style(it.status)[3] <= 3)
        out_games.append({"away": g.away, "home": g.home, "when": g.when or "", "spread": spread, "total": g.odds.total if g.odds else None, "hurt": count})
    hurt = sum(1 for items in inj.values() for i in items if injury_style(i.status)[3] <= 3)
    return {"day": day.isoformat(), "day_text": day.strftime("%A, %b %d"), "games": out_games, "hurt": hurt,
            "injuries": {t: [injury_dict(i) for i in sorted(items, key=lambda i: injury_style(i.status)[3])] for t, items in inj.items()}}


def api_roster(b: dict) -> dict:
    abbr = str(b.get("abbr") or "")
    rows = fetch_roster(abbr)
    return {"abbr": abbr, "roster": rows}


def api_odds_key(b: dict) -> dict:
    global ODDS_API_KEY
    if not ALLOW_KEY_EDIT: raise ApiError("Changing the odds key is disabled on this server (set OUTPLAI_ALLOW_KEY_EDIT=1 to enable).", "data", 403)
    ODDS_API_KEY = str(b.get("key") or "").strip()
    _odds_cache.clear()
    _espn_cache.clear()
    return {"ok": True, "odds_key": bool(ODDS_API_KEY)}


def api_config(_b: dict) -> dict:
    t = {k: v for k, v in vars(Theme).items() if k.isupper()}
    legend = {s: dict(zip(("bg", "fg", "short", "sev"), injury_style(s))) for s in ("Out", "Doubtful", "Questionable", "Day-To-Day", "Probable")}
    return {"theme": t, "team_colors": TEAM_COLORS, "default_accent": DEFAULT_ACCENT, "pill_keys": PILL_KEYS, "profile_layout": PROFILE_LAYOUT,
            "pos_stats": POS_STATS, "pos_patterns": POS_PATTERNS, "group_names": GROUP_NAMES,
            "team_stat_rows": TEAM_STAT_ROWS, "team_sections": [[name, [[s[0], s[4]] for s in specs]] for name, specs in TEAM_SECTIONS],
            "nav_pages": NAV_PAGES, "nav_labels": NAV_LABELS, "rank_styles": RANK_STYLES, "status_styles": STATUS_STYLES,
            "split_options": SPLIT_OPTIONS, "minutes_options": MINUTES_OPTIONS, "rest_options": REST_OPTIONS, "placeholder": PLACEHOLDER_TEXT,
            "logo_url": LOGO_URL, "logo_map": NBA_TO_ESPN_LOGO, "headshot_urls": list(HEADSHOT_URLS), "odds_refresh_ms": ODDS_REFRESH_MS,
            "team_names": _team_tables()[2], "injury_legend": legend, "odds_key": bool(ODDS_API_KEY), "allow_key_edit": ALLOW_KEY_EDIT,
            "has_brand_image": _brand_source() is not None, "today": today_eastern().isoformat(),
            "pill_props": PILL_TO_PROP, "current_season": current_season()}


# ---------------------------------------------------------------- brand logo (same recolouring as the desktop app, needs Pillow + image_3c998c.png)
_brand_cache: dict = {}


def _brand_source() -> Optional[str]:
    for d in (HERE, os.getcwd()):
        path = os.path.join(d, BRAND_IMAGE)
        if os.path.exists(path): return path
    return None


def brand_png(size: int, color: str) -> Optional[bytes]:
    key = (size, color)
    if key in _brand_cache: return _brand_cache[key]
    path = _brand_source()
    if path is None: return None
    try:
        from PIL import Image, ImageChops, ImageOps
        raw = Image.open(path).convert("RGBA")
        r, g, b, a = raw.split()
        colored = Image.new("RGBA", raw.size, color)
        colored.putalpha(ImageChops.multiply(ImageOps.invert(raw.convert("L")), a))
        buf = io.BytesIO()
        colored.resize((size, size), Image.Resampling.LANCZOS).save(buf, "PNG")
        _brand_cache[key] = buf.getvalue()
        return _brand_cache[key]
    except Exception as exc:
        log.warning("Brand image unavailable: %s", exc)
        return None


INDEX_HTML = r'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>OutplAI Engine - Live NBA Betting Engine</title>
<meta name="description" content="Live NBA prop research: hit rates, odds, matchups, injuries and news in one place.">
<link rel="icon" href="/brand.png?size=64&color=%23a855f7">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@700;800&display=swap" rel="stylesheet">
<style>
:root{
  --bg:#08080b;--surface:#101014;--raised:#18181f;--inset:#1a1a21;--ghost:#17171d;--ctrl:#201b29;--chip:#34343e;
  --border:#25252e;--border2:#3a3a47;--royal:#4c1d95;--accent:#a855f7;--accent-h:#9333ea;--accent-soft:rgba(168,85,247,.22);
  --gold:#f59e0b;--gold-soft:#fbbf24;--green:#22c993;--red:#f2453d;--hit:#19c3a1;--miss:#e5322e;--push:#94a3b8;--line:#d4d4d8;
  --text:#f8fafc;--soft:#cbd5e1;--muted:#9a9aae;--dim:#6b6b80;--hdr:#a855f7;
  --font:"Segoe UI","SF Pro Text","Helvetica Neue",Inter,Roboto,Arial,sans-serif;
  --brand:"Poppins","Segoe UI Black","Arial Black",Impact,sans-serif;
}
*{box-sizing:border-box}
html,body{margin:0;background:var(--bg);color:var(--text);font-family:var(--font);font-size:12px;-webkit-font-smoothing:antialiased}
body{min-height:100vh}
button,select,input{font-family:inherit;color:inherit}
button{cursor:pointer}
[hidden]{display:none!important}
::-webkit-scrollbar{width:10px;height:10px}::-webkit-scrollbar-thumb{background:var(--border2);border-radius:6px}::-webkit-scrollbar-thumb:hover{background:var(--muted)}::-webkit-scrollbar-track{background:transparent}

/* ---------- brand */
.brand-logo{display:inline-block;flex:none}
.brand-logo img,.brand-logo svg{display:block;width:100%;height:100%}
.wordmark{font-family:var(--brand);font-weight:800;letter-spacing:.07em;display:inline-flex;gap:.34em;line-height:1;transform:skewX(-11deg);white-space:nowrap;align-items:baseline}
.wordmark .w1{background:linear-gradient(180deg,#fff,#aab4cc);-webkit-background-clip:text;background-clip:text;color:transparent}
.wordmark .w2{background:linear-gradient(180deg,var(--accent-light,#d8b4fe),var(--accent));-webkit-background-clip:text;background-clip:text;color:transparent}
.wordmark.glow{filter:drop-shadow(0 0 .22em var(--accent-glow,rgba(168,85,247,.55)))}

/* ---------- home */
#home{padding:64px 20px 30px;max-width:1280px;margin:0 auto}
.home-top{text-align:center;margin-bottom:22px}
.home-title{display:flex;align-items:center;justify-content:center;gap:14px}
.home-tag{font-family:var(--brand);font-weight:700;font-size:13px;color:var(--soft);margin-top:10px;letter-spacing:.04em}
.home-sub{font-size:12px;color:var(--dim);margin-top:4px}
.home-slot{max-width:1080px;margin:0 auto}
.home-bottom{max-width:1080px;margin:10px auto 0;text-align:center}
.btn-today{height:40px;border-radius:20px;padding:0 22px;font-size:13px;font-weight:700;background:var(--ctrl);border:1px solid var(--accent);color:var(--text);margin:2px 0 14px}
.btn-today:hover{background:var(--border)}
.try-row{display:flex;gap:8px;justify-content:center;align-items:center;flex-wrap:wrap;margin:4px 0 26px}
.try-row span{font-size:10px;font-weight:700;color:var(--dim);margin-right:4px}
.chip-btn{height:32px;border-radius:16px;padding:0 14px;font-size:11px;font-weight:700;background:var(--inset);border:1px solid var(--border);color:var(--soft)}
.chip-btn:hover{background:var(--border)}
.features{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;text-align:left}
.feature{background:var(--surface);border:1px solid var(--border);border-radius:14px;padding:12px 14px 14px}
.feature .ic{font-size:22px}.feature b{display:block;font-size:13px;margin-top:2px}.feature p{margin:2px 0 0;font-size:10px;color:var(--muted);line-height:1.45}

/* ---------- search bar with glow */
.searchbar{position:relative;padding:20px}
.searchbar .pill{position:relative;display:flex;align-items:center;height:50px;border-radius:25px;background:var(--surface);border:2px solid var(--accent);padding:0 8px 0 24px;
  box-shadow:0 0 calc(34px*var(--glow,.4)) calc(6px*var(--glow,.4)) var(--royal-glow,rgba(76,29,149,.9));transition:box-shadow .3s}
.searchbar.focus .pill{--glow:.9}
.searchbar input{flex:1;background:transparent;border:0;outline:0;color:var(--text);font-size:13px;height:36px;min-width:0}
.searchbar input::placeholder{color:var(--dim)}
.searchbar .go{width:44px;height:34px;border-radius:17px;border:0;background:var(--accent);color:var(--bg);font-size:14px;font-weight:700}
.searchbar .go:hover{background:var(--accent-h)}
.searchbar .go.busy{opacity:.6}

/* ---------- dashboard shell */
#app{display:flex;flex-direction:column;height:100vh;padding:8px 12px 0;max-width:1600px;margin:0 auto}
.topbar{display:flex;align-items:center;margin-bottom:6px;padding:0 4px;gap:8px}
.topbar .brand{display:flex;align-items:center;gap:10px;margin-right:auto}
.status{font-size:10px;font-weight:700;border-radius:10px;padding:4px 4px;white-space:pre}
.btn-small{height:28px;border-radius:14px;padding:0 14px;font-size:10px;font-weight:700;background:var(--inset);border:1px solid transparent;color:var(--soft)}
.btn-small:hover{background:var(--border)}
.nav{display:grid;grid-template-columns:repeat(6,1fr);gap:4px 6px;margin-bottom:8px;padding:0 3px}
.nav button{height:42px;border-radius:12px;font-size:12px;font-weight:700;background:var(--raised);border:1px solid var(--border);color:var(--soft);white-space:nowrap}
.nav button:hover{background:var(--border)}
.nav button.on{background:var(--nav-fill,var(--accent));border-color:var(--accent);color:var(--text)}
.content{flex:1;display:flex;gap:6px;min-height:0}
#main{flex:1;min-width:0;overflow-y:auto;padding-right:4px}
#side{width:318px;flex:none;overflow-y:auto}
.dock{flex:none;padding:0 0 4px}
.dock .searchbar{padding:6px 0}

/* ---------- panels */
.panel{position:relative;background:var(--surface);border:1px solid var(--border);border-radius:16px;margin-bottom:8px}
.panel.sm{border-radius:14px}
.panel .strip{height:3px;margin:1px 22px 0;background:linear-gradient(90deg,var(--accent),color-mix(in srgb,var(--accent) 25%,var(--surface)))}
.page-head{display:flex;align-items:center;padding:14px 16px 0}
.page-head h2{margin:0;font-size:18px;font-weight:700;flex:1}
.page-sub{padding:2px 16px 0;font-size:11px;color:var(--muted)}
.page-desc{padding:0 16px 8px;font-size:10px;color:var(--dim)}
.sec-head{display:flex;align-items:center;gap:8px;padding:10px 14px 4px;font-size:11px;font-weight:700}
.sec-head i{display:block;width:3px;height:12px;border-radius:2px;background:var(--accent)}
.divider{height:1px;background:var(--border);margin:10px 16px 0}
.muted{color:var(--muted)}.dim{color:var(--dim)}.soft{color:var(--soft)}.good{color:var(--green)}.bad{color:var(--red)}.gold{color:var(--gold-soft)}.text{color:var(--text)}
.italic{font-style:italic}
.card{background:var(--inset);border:1px solid var(--border);border-radius:12px}
.cap{font-size:10px;font-weight:700;color:var(--muted)}

/* ---------- hero */
.hero{position:relative;height:124px;overflow:hidden;background:var(--bg)}
.hero .bg{position:absolute;inset:0;
  -webkit-mask-image:linear-gradient(180deg,transparent,#000 22%,#000 78%,transparent);mask-image:linear-gradient(180deg,transparent,#000 22%,#000 78%,transparent)}
.hero .orb{position:absolute;left:5px;top:50%;width:116px;height:116px;margin-top:-58px;border-radius:50%;background:radial-gradient(circle,var(--hdr) 0%,var(--hdr) 38%,transparent 72%);opacity:.95}
.hero .halo{position:absolute;left:19px;top:50%;width:88px;height:88px;margin-top:-44px;border-radius:50%;background:radial-gradient(circle,var(--hdr-light) 0%,transparent 72%);opacity:.55}
.hero .wash{position:absolute;left:60px;top:50%;width:580px;height:80px;margin-top:-40px;border-radius:50%;background:radial-gradient(ellipse,var(--hdr) 0%,transparent 70%);opacity:.38}
.hero .photo{position:absolute;left:18px;top:50%;width:104px;height:104px;margin-top:-52px}
.hero .photo .face{position:absolute;left:0;top:0;width:76px;height:76px;border-radius:19px;background:var(--inset);overflow:hidden}
.hero .photo .face img{width:100%;height:100%;object-fit:cover;object-position:top center;display:block}
.hero .photo .tlogo{position:absolute;right:0;bottom:0;width:48px;height:48px}
.hero .photo .tlogo img{width:100%;height:100%;object-fit:contain}
.hero .txt{position:absolute;left:126px;top:0;bottom:0;display:flex;flex-direction:column;justify-content:center;gap:5px}
.hero .game{font-size:11px;color:var(--soft)}
.hero .nm{display:flex;align-items:baseline;gap:12px}
.hero .nm b{font-size:26px;font-weight:700;line-height:1.1}
.hero .nm span{font-size:13px;font-weight:700;color:var(--muted)}
.hero .tgt{font-size:13px;color:var(--soft)}.hero .tgt b{color:var(--text)}
.ctl{display:flex;align-items:center;padding:2px 18px 10px;gap:8px;flex-wrap:wrap}
.book{display:flex;align-items:center;background:var(--ctrl);border:1px solid var(--border);border-radius:12px;padding:3px 5px 3px 10px}
.book .lbl{font-size:9px;font-weight:700;color:var(--muted);margin-right:6px}
.book .ln{font-size:13px;font-weight:700;margin-right:6px}
.book button{width:92px;height:32px;border-radius:10px;font-size:12px;font-weight:700;background:var(--ctrl);border:1px solid var(--ctrl);margin:0 2px}
.book button.over{color:var(--green)}.book button.under{color:var(--red)}
.book button.on{background:color-mix(in srgb,var(--ctrl) 72%,var(--accent));border-color:var(--accent)}
.ctl select,.ctl .ctlbtn{height:38px;border-radius:12px;background:var(--ctrl);border:1px solid var(--ctrl);color:var(--text);font-size:12px;font-weight:700;padding:0 12px}
.ctl .ctlbtn:hover,.ctl select:hover{background:var(--border)}
.ctl .plus{width:40px;font-size:16px;padding:0}

/* ---------- prop pills / filters / summary */
.pills{display:grid;grid-template-columns:repeat(7,1fr);gap:6px;padding:12px 12px 2px}
.pill-btn{height:48px;border-radius:11px;font-size:10px;font-weight:700;background:var(--raised);border:1px solid var(--border);color:var(--soft);line-height:1.35;white-space:pre-line}
.pill-btn:hover{background:var(--border)}
.pill-btn.on{background:color-mix(in srgb,var(--raised) 78%,var(--accent));border-color:var(--accent);color:var(--text)}
.filters{display:flex;align-items:center;flex-wrap:wrap;padding:8px 16px 0;gap:6px 0}
.filters .cap{margin:0 8px 0 18px}.filters .cap:first-child{margin-left:0}
.sel{height:32px;border-radius:10px;background:var(--inset);border:1px solid var(--inset);color:var(--soft);font-size:11px;font-weight:700;padding:0 10px;margin-right:8px}
.sel:hover{background:var(--border)}.sel option{background:var(--raised)}
.quick{height:30px;width:88px;border-radius:15px;font-size:11px;font-weight:700;background:var(--inset);border:1px solid var(--border);color:var(--soft);margin-right:6px}
.quick:hover{background:var(--border)}
.quick.on{background:color-mix(in srgb,var(--inset) 78%,var(--accent));border-color:var(--accent);color:var(--text)}
.summary{display:flex;justify-content:space-between;align-items:flex-start;padding:8px 16px 0;gap:12px;flex-wrap:wrap}
.hit-title{font-size:11px;font-weight:700;color:var(--muted)}
.hit-big{display:flex;align-items:baseline;gap:8px}.hit-big b{font-size:34px;font-weight:700}.hit-big span{font-size:12px;color:var(--muted)}
.tabs{display:flex;gap:4px}
.tab{width:80px;height:64px;border-radius:10px;background:transparent;border:1px solid var(--surface);text-align:center;padding:6px 0 0}
.tab:hover{background:var(--ghost)}
.tab.on{background:var(--raised);border-color:var(--accent)}
.tab .n{display:block;font-size:11px;font-weight:700;color:var(--muted)}.tab.on .n{color:var(--text)}
.tab .p{display:block;font-size:13px;font-weight:700;margin-top:2px;color:var(--dim)}.tab .p.good{color:var(--green)}.tab .p.bad{color:var(--red)}
.tab .a{display:block;font-size:9px;color:var(--dim);min-height:11px}
.meta{display:flex;align-items:center;padding:2px 16px 0;flex-wrap:wrap;gap:2px 0}
.meta .k{color:var(--muted);font-size:11px;margin-right:4px}.meta .v{font-weight:700;font-size:11px;margin-right:16px}
.meta .sp{flex:1}.meta .nt{font-weight:700;font-size:11px;color:var(--gold-soft);margin-left:12px}
.model-note{padding:2px 16px 0;font-size:10px;font-style:italic;color:var(--muted)}
.lacks{padding:2px 16px 0;font-size:11px;font-weight:700;color:var(--green)}
.chart-head{display:flex;justify-content:space-between;padding:8px 16px 0}
.chart-head .hint{font-size:10px;color:var(--dim);margin-right:14px}

/* ---------- bar chart (HTML) */
.chart{position:relative;height:270px;margin:2px 10px 10px;user-select:none}
.chart.tall{height:330px}
.chart .plot{position:absolute;left:22px;right:64px;top:0;bottom:0;display:flex}
.chart .slot{position:relative;flex:1;min-width:0}
.chart .col{position:absolute;left:50%;transform:translateX(-50%);top:30px;bottom:74px;border-radius:9px;background:var(--ghost);border:1px solid var(--border)}
.chart .slot.hov .col{border-color:var(--accent)}
.chart .slot.next .col{border:1px dashed var(--border2);display:flex;align-items:center;justify-content:center;font-size:20px;font-weight:700;color:var(--muted);cursor:pointer}
.chart .fill{position:absolute;left:0;right:0;bottom:0;border-radius:8px}
.chart .fill::after{content:"";position:absolute;left:8px;right:8px;top:1px;height:2px;background:rgba(255,255,255,.35);border-radius:2px}
.chart .val{position:absolute;left:50%;transform:translate(-50%,50%);min-width:32px;height:20px;border-radius:6px;background:var(--chip);font-size:11px;font-weight:700;text-align:center;line-height:20px;padding:0 4px}
.chart .unit{position:absolute;left:0;right:0;bottom:4px;text-align:center;font-size:7px;font-weight:700;opacity:.8}
.chart .badge{position:absolute;left:50%;transform:translate(-50%,-50%);display:flex;align-items:center;gap:3px}
.chart .badge .at{font-size:10px;font-weight:700;color:var(--dim)}
.team-badge{border-radius:50%;display:inline-flex;align-items:center;justify-content:center;font-size:8px;font-weight:700;overflow:hidden;flex:none}
.team-badge img{width:100%;height:100%;object-fit:contain}
.chart .date{position:absolute;left:0;right:0;text-align:center;font-size:10px;color:var(--soft)}
.chart .date.nx{color:var(--accent);font-weight:700}
.chart .season{position:absolute;left:0;right:0;text-align:center;font-size:8px;color:var(--dim)}
.chart .ln{position:absolute;left:12px;right:56px;border-top:2px dashed var(--line);pointer-events:none}
.chart .lnlbl{position:absolute;right:4px;width:48px;height:22px;margin-top:-11px;border-radius:6px;background:#fff;color:var(--bg);font-size:11px;font-weight:700;text-align:center;line-height:22px;pointer-events:none}
.chart .empty{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;color:var(--dim);font-size:13px;text-align:center;padding:0 20px}
#tip{position:fixed;z-index:50;pointer-events:none;background:#121218;border:2px solid var(--accent);border-radius:10px;padding:12px 14px;min-width:240px;box-shadow:0 10px 30px rgba(0,0,0,.55)}
#tip .t{font-size:12px;font-weight:700;margin-bottom:3px}#tip .s{font-size:10px;color:var(--muted);margin-bottom:6px}
#tip .pr{font-size:12px;font-weight:700;margin:2px 0 4px}
#tip hr{border:0;border-top:1px solid var(--border2);margin:6px 0}
#tip .row{display:grid;grid-template-columns:repeat(3,1fr);gap:0 14px;margin:2px 0}
#tip .row div{display:flex;justify-content:space-between;gap:8px}
#tip .row span{font-size:9px;font-weight:700;color:var(--dim);align-self:center}#tip .row b{font-size:11px}

/* ---------- matchup */
.mu-head{display:flex;align-items:center;padding:14px 16px 8px;gap:10px}
.vsbadge{width:46px;height:46px;border-radius:50%;background:var(--inset);display:flex;align-items:center;justify-content:center;font-size:9px;font-weight:700;overflow:hidden}
.vsbadge img{width:32px;height:32px;object-fit:contain}
.mu-head h3{margin:0;font-size:18px}.mu-head .d{font-size:11px;color:var(--muted)}
.mini{display:flex;margin-left:auto;background:var(--inset);border:1px solid var(--border);border-radius:12px}
.mini div{padding:4px 10px;text-align:center}.mini small{display:block;font-size:9px;font-weight:700;color:var(--muted);margin-top:2px}.mini b{font-size:16px}
.mu-body{display:grid;grid-template-columns:3fr 2fr;gap:12px;padding:0 12px 4px}
.postable{padding-bottom:10px}
.postable table{width:100%;border-collapse:collapse}
.postable th{font-size:11px;font-weight:700;color:var(--soft);padding:0 3px 4px;text-align:center}.postable th.hl{color:var(--accent)}
.postable th:first-child,.postable td:first-child{text-align:left;padding-left:12px}
.postable td{padding:2px 3px}.postable td:first-child{font-size:11px;font-weight:700;color:var(--soft)}
.pcell{display:block;width:100%;min-width:92px;height:26px;border-radius:8px;background:var(--surface);color:var(--dim);font-size:11px;font-weight:700;text-align:center;line-height:26px}
.rankrow{display:flex;align-items:center;padding:1px 12px;gap:8px;min-height:24px}
.rankrow .nm{flex:1;font-size:11px;color:var(--soft)}.rankrow .vl{font-size:12px}
.rchip{font-size:9px;font-weight:700;border-radius:8px;padding:2px 8px;background:var(--surface);color:var(--dim)}
.mu-foot{padding:4px 16px 14px}.mu-foot div{font-size:11px;font-weight:700;margin-top:2px;line-height:1.45}.mu-foot .nt{font-size:9px;color:var(--dim);font-style:italic;font-weight:400;margin-top:4px}

/* ---------- profile / analysis tiles */
.prof-head{display:flex;align-items:center;padding:14px 16px 2px;gap:12px}
.prof-head h3{margin:0;font-size:16px}.prof-head .g{font-size:11px;color:var(--muted);margin-right:auto}
.seg{display:flex;background:var(--inset);border-radius:8px;padding:2px}
.seg button{height:24px;padding:0 14px;border-radius:7px;border:0;background:transparent;font-size:11px;font-weight:700;color:var(--text)}
.seg button.on{background:var(--seg-fill,var(--accent))}.seg button:hover:not(.on){background:var(--border)}
.prof-note{padding:0 16px;font-size:11px;font-weight:700}
.tiles{display:grid;grid-template-columns:repeat(6,1fr);gap:6px;padding:4px 12px 12px}
.tile{background:var(--inset);border:1px solid var(--border);border-radius:10px;text-align:center;padding:8px 4px 7px}
.tile b{display:block;font-size:20px}.tile .t{display:block;font-size:10px;font-weight:700;color:var(--muted)}.tile .s{display:block;font-size:9px;color:var(--dim);min-height:11px}

/* ---------- team pages */
.team-head{display:flex;align-items:center;padding:14px 16px 2px;gap:12px}
.team-head .lg{width:52px;height:52px;display:flex;align-items:center;justify-content:center}.team-head .lg img{width:52px;height:52px;object-fit:contain}
.team-head h3{margin:0;font-size:20px}.team-head .s{font-size:11px;color:var(--muted)}.team-head .ttl{margin-left:auto;font-size:11px;font-weight:700;color:var(--muted);text-transform:uppercase}
.team-note{padding:0 16px 6px;font-size:10px;font-style:italic;color:var(--dim)}
.team-cols{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;padding:0 12px 12px}
.team-cols .card{margin-bottom:8px;padding-bottom:8px}
.team-cols .card h4{margin:0;padding:10px 12px 4px;font-size:10px;font-weight:700;color:var(--muted)}
.rot{width:100%;border-collapse:collapse;margin-bottom:6px}
.rot th{font-size:9px;font-weight:700;color:var(--dim);text-align:right;padding:0 3px}.rot td{font-size:11px;color:var(--soft);text-align:right;padding:2px 3px}
.rot th:first-child,.rot td:first-child{text-align:left;font-weight:700;color:var(--text);padding-left:10px}

/* ---------- analysis */
.adv{display:grid;grid-template-columns:repeat(6,1fr);gap:6px;padding:0 10px}
.atile{background:var(--inset);border:1px solid var(--border);border-radius:10px;text-align:center;padding:8px 4px 7px}
.atile b{display:block;font-size:20px}.atile .t{font-size:10px;font-weight:700;color:var(--muted)}.atile .s{display:block;font-size:9px;color:var(--dim);min-height:11px}
.acard{margin:5px 12px}.acard .ttl{padding:10px 12px 2px;font-size:10px;font-weight:700;color:var(--muted)}.acard .body{padding:0 12px 10px}
.acard .body p{margin:2px 0;font-size:11px;color:var(--soft);line-height:1.5}
.acard .body p.fin{color:var(--text)}
.atable{border-collapse:collapse}.atable td,.atable th{padding:1px 22px 1px 0;font-size:11px;text-align:left;color:var(--soft)}
.atable th{font-size:9px;font-weight:700;color:var(--dim)}.atable td.b{font-weight:700}.atable tr.late td{color:var(--gold-soft)}

/* ---------- picks / games / news */
.two{display:grid;grid-template-columns:380px 1fr;gap:8px;padding:0 12px 12px}
.two.games{grid-template-columns:330px 1fr}
.pick{display:flex;align-items:center;background:var(--inset);border:1px solid var(--border);border-radius:12px;margin:0 0 6px;padding:6px 10px 6px 10px;cursor:pointer;gap:6px}
.pick.on{border-color:var(--accent)}.pick:hover{background:var(--ghost)}
.pick .rk{width:30px;font-size:14px;font-weight:700;color:var(--muted)}.pick .mid{flex:1;min-width:0}.pick .mid b{display:block;font-size:12px}.pick .mid small{display:block;font-size:10px;color:var(--muted)}
.pchip{background:var(--surface);color:var(--green);font-size:12px;font-weight:700;border-radius:8px;padding:2px 8px;white-space:nowrap}
.detail{background:var(--inset);border:1px solid var(--border);border-radius:12px;min-width:0}
.detail h3{margin:0;padding:14px 16px 0;font-size:17px}.detail .sub{padding:0 16px;font-size:11px;color:var(--muted)}
.chips{display:flex;align-items:center;gap:6px;padding:8px 16px 0;flex-wrap:wrap}
.chips .pchip:first-child{color:var(--green)}.chips .pchip{color:var(--soft)}.chips .pchip:first-child{color:var(--green)}
.chips .open{margin-left:auto;height:30px;border-radius:15px;padding:0 14px;font-size:11px;font-weight:700;background:var(--ctrl);border:1px solid var(--accent)}
.detail .why{padding:10px 16px 2px;font-size:10px;font-weight:700;color:var(--muted)}
.detail .reasons{padding:0 16px 14px;font-size:11px;color:var(--soft);line-height:1.5}.detail .reasons p{margin:0 0 9px}
.formcols{display:flex;gap:8px;padding:8px}.formcols>div{flex:1;background:var(--surface);border:1px solid var(--border);border-radius:10px;padding-bottom:8px}
.fhead{display:flex;align-items:center;padding:10px 12px 4px;gap:8px}.fhead b{font-size:13px}.fhead small{margin-left:auto;font-size:10px;font-weight:700}
.frow{display:flex;align-items:center;padding:2px 12px;gap:8px}.frow .wl{width:26px;text-align:center;border-radius:6px;font-size:10px;font-weight:700}.frow .sc{margin-left:auto;font-weight:700;color:var(--soft)}
.frow b{font-size:12px}.frow small{font-size:10px;color:var(--dim)}
.ncard{background:var(--inset);border:1px solid var(--border);border-radius:12px;margin:0 0 6px;padding:10px 14px;cursor:pointer;display:block;color:inherit;text-decoration:none}
.ncard:hover{background:var(--ghost)}.ncard .top{display:flex;align-items:center;gap:8px}.ncard .tg{background:var(--surface);font-size:9px;font-weight:700;border-radius:8px;padding:2px 8px}
.ncard .mt{font-size:10px;color:var(--muted)}.ncard h5{margin:4px 0 0;font-size:13px}.ncard p{margin:2px 0 0;font-size:11px;color:var(--muted)}
.chips2{display:flex;gap:6px;padding:0 16px 8px}.fchip{width:84px;height:28px;border-radius:14px;font-size:10px;font-weight:700;background:var(--inset);border:1px solid var(--border);color:var(--soft)}
.fchip.on{background:color-mix(in srgb,var(--inset) 75%,var(--accent));border-color:var(--accent);color:var(--text)}
.legend{display:flex;align-items:center;gap:6px;padding:4px 16px 8px}.ibadge{font-size:9px;font-weight:700;border-radius:6px;padding:2px 7px;white-space:nowrap}
.gcard{background:var(--inset);border:1px solid var(--border);border-radius:12px;margin:0 0 6px;padding:8px 10px;cursor:pointer}
.gcard.mine{border-color:var(--border2)}.gcard.on{border-color:var(--accent)}.gcard:hover{background:var(--ghost)}
.gcard .r{display:flex;align-items:center;gap:6px}.gcard .r b{font-size:14px}.gcard .r .at{font-size:12px;color:var(--dim)}.gcard .r img{width:30px;height:30px;object-fit:contain}
.gcard .bd{margin-left:auto;background:#451a03;color:#fb923c;font-size:10px;font-weight:700;border-radius:8px;padding:2px 8px}.gcard small{display:block;font-size:10px;color:var(--muted);margin-top:4px}
.gcols{display:grid;grid-template-columns:1fr 1fr;gap:8px;padding:0 8px 10px}.gcol{background:var(--surface);border:1px solid var(--border);border-radius:12px;padding-bottom:8px}
.gcol .gh{display:flex;align-items:center;gap:8px;padding:12px 12px 4px}.gcol .gh img{width:34px;height:34px;object-fit:contain}.gcol .gh b{font-size:14px}.gcol .gh small{margin-left:auto;font-size:9px;font-weight:700;color:var(--dim)}
.gcol h6{margin:8px 12px 2px;font-size:10px;font-weight:700;color:var(--muted)}
.gcol .ir{display:flex;align-items:center;gap:6px;padding:2px 12px 0}.gcol .ir b{font-size:11px}
.gcol .ic{padding:0 12px 2px 26px;font-size:10px;color:var(--muted)}
.gcol .ok{padding:0 12px;font-size:11px;color:var(--green)}
.gcol .rr{display:flex;align-items:center;padding:1px 12px;gap:6px;font-size:11px}.gcol .rr .nn{width:34px;font-size:10px;color:var(--dim)}.gcol .rr .nm{color:var(--soft)}.gcol .rr .ps{margin-left:auto;font-size:10px;color:var(--dim)}

/* ---------- sidebar */
.wp-grid{display:grid;grid-template-columns:1fr 116px 1fr;gap:2px;padding:0 8px;align-items:start}
.wp-side{text-align:center;padding-top:8px}.wp-side .lg{width:44px;height:44px;margin:0 auto 2px}.wp-side .lg img{width:44px;height:44px;object-fit:contain}
.wp-side b{display:block;font-size:13px}.wp-side .pc{display:block;font-size:19px;font-weight:700}.wp-side small{display:block;font-size:8px;font-weight:700;color:var(--muted);min-height:10px}
.ring{position:relative;width:112px;height:112px;margin-top:6px}.ring svg{position:absolute;inset:0}.ring .mid{position:absolute;inset:0;display:flex;flex-direction:column;align-items:center;justify-content:center}
.ring .mid b{font-size:15px}.ring .mid small{font-size:8px;font-weight:700;color:var(--muted)}
.wpbar{display:flex;height:8px;margin:8px 16px 2px;background:var(--inset);border-radius:0}
.wpleg{text-align:center;font-size:10px;font-weight:700;color:var(--soft);padding-top:2px;min-height:16px}.wpsrc{text-align:center;font-size:9px;color:var(--dim);padding-bottom:10px}
.oteam{margin:3px 8px;padding-bottom:6px}.oteam .nm{font-size:11px;font-weight:700;padding:6px 10px 2px}
.ocells{display:grid;grid-template-columns:repeat(3,1fr);gap:4px;padding:0 6px}
.ocell{background:var(--surface);border:1px solid var(--border);border-radius:8px;text-align:center;padding:4px 0 3px}.ocell small{display:block;font-size:8px;font-weight:700;color:var(--muted)}.ocell b{display:block;font-size:11px}.ocell i{display:block;font-style:normal;font-size:8px;color:var(--dim);min-height:10px}
.onote{padding:2px 12px 8px;font-size:9px;font-style:italic;color:var(--dim);white-space:pre-line}
.bestcard{border:1px solid var(--accent);border-radius:14px;background:color-mix(in srgb,var(--accent) 45%,var(--bg));padding:10px;text-align:center;font-size:11px;font-weight:700;white-space:pre-line;margin-bottom:8px;line-height:1.5}
.bestcard.gold{background:#2a1f05;border-color:var(--gold)}

.toast{position:fixed;left:50%;bottom:90px;transform:translateX(-50%);background:var(--raised);border:1px solid var(--accent);border-radius:12px;padding:10px 16px;font-size:12px;z-index:60}
.spin{display:inline-block;width:12px;height:12px;border:2px solid var(--border2);border-top-color:var(--accent);border-radius:50%;animation:sp .8s linear infinite;vertical-align:-2px;margin-right:6px}
@keyframes sp{to{transform:rotate(360deg)}}

@media (max-width:1100px){#side{display:none}.features{grid-template-columns:repeat(2,1fr)}.nav{grid-template-columns:repeat(3,1fr)}.pills{grid-template-columns:repeat(4,1fr)}.tiles,.adv{grid-template-columns:repeat(3,1fr)}.two,.two.games,.mu-body,.team-cols{grid-template-columns:1fr}}
@media (max-width:640px){#home{padding-top:30px}.wordmark{font-size:30px!important}.nav{grid-template-columns:repeat(2,1fr)}.pills{grid-template-columns:repeat(3,1fr)}.tabs{flex-wrap:wrap}.gcols{grid-template-columns:1fr}.features{grid-template-columns:1fr}}

.team-badge{position:relative}.team-badge img{position:absolute;inset:0}.team-badge em{font-style:normal}.team-badge.ok em{display:none}
.hero .nm{position:static}
.side-pad{padding:0 0 8px}
.page-head .btn-small{margin-left:8px}

</style>
</head>
<body>

<!-- ============================ HOME / SEARCH ============================ -->
<div id="home">
  <div class="home-top">
    <div class="home-title">
      <span class="brand-logo" id="homeLogo" style="width:54px;height:54px"></span>
      <span class="wordmark glow" style="font-size:54px"><span class="w1">OUTPLAI</span><span class="w2">ENGINE</span></span>
    </div>
    <div class="home-tag">LIVE NBA PROP RESEARCH  ·  ODDS  ·  MATCHUPS  ·  INJURIES  ·  NEWS</div>
    <div class="home-sub">Search a player, a stat and a line to see hit rates, matchup, odds and win chances in one place.</div>
  </div>
  <div class="home-slot" id="homeSlot">
    <div class="searchbar" id="searchbar">
      <div class="pill">
        <input id="q" type="text" autocomplete="off" spellcheck="false" aria-label="Search player and prop">
        <button class="go" id="go" aria-label="Search">➔</button>
      </div>
    </div>
  </div>
  <div class="home-bottom">
    <button class="btn-today" id="btnToday">⭐  See today's best picks</button>
    <div class="try-row"><span>TRY</span>
      <button class="chip-btn" data-example="Donovan Mitchell Points Over 24.5">Donovan Mitchell Points Over 24.5</button>
      <button class="chip-btn" data-example="Darius Acuff Jr Threes Over 1.5">Darius Acuff Jr Threes Over 1.5</button>
      <button class="chip-btn" data-example="AJ Dybantsa Rebounds Over 4.5 vs CHA">AJ Dybantsa Rebounds Over 4.5 vs CHA</button>
    </div>
    <div class="features" id="feat">
      <div class="feature"><div class="ic">📊</div><b>Hit rates</b><p>L5, L10, L15 and season splits, padded with last season for early-year players.</p></div>
      <div class="feature"><div class="ic">📈</div><b>Live odds</b><p>Spread, moneyline and total refreshed every minute, plus win odds for both teams.</p></div>
      <div class="feature"><div class="ic">🛡</div><b>Matchup</b><p>What the opponent allows to guards, forwards and centers, and where they are weak.</p></div>
      <div class="feature"><div class="ic">🎯</div><b>Box scores</b><p>Hover any game for a full box score and see the deep player profile below.</p></div>
    </div>
  </div>
</div>

<!-- ============================ DASHBOARD ============================ -->
<div id="app" hidden>
  <div class="topbar">
    <div class="brand">
      <span class="brand-logo" id="topLogo" style="width:30px;height:30px"></span>
      <span class="wordmark" style="font-size:22px"><span class="w1">OUTPLAI</span><span class="w2">ENGINE</span></span>
    </div>
    <button class="btn-small" id="btnKey">⚙  Odds key</button>
    <span class="status" id="status"></span>
  </div>
  <div class="nav" id="nav"></div>
  <div class="content">
    <div id="main">
      <div id="pages">

        <!-- Overview -->
        <section data-page="Overview">
          <div class="panel">
            <div class="hero">
              <div class="bg"><div class="orb"></div><div class="halo"></div><div class="wash"></div></div>
              <div class="photo"><div class="face" id="hFace"></div><div class="tlogo" id="hLogo"></div></div>
              <div class="txt">
                <div class="game" id="hGame"></div>
                <div class="nm"><b id="hName">Search a player</b><span id="hPos"></span></div>
                <div class="tgt"><b id="hTarget"></b> <span id="hSide"></span></div>
              </div>
            </div>
            <div class="ctl">
              <div class="book"><span class="lbl" id="bookLbl">LINE</span><span class="ln" id="lineChip">L –</span>
                <button class="over" id="btnOver">OVER</button><button class="under" id="btnUnder">UNDER</button></div>
              <select id="altSel" aria-label="Alt lines"><option value="">Alt Lines</option></select>
              <button class="ctlbtn plus" id="btnPlus" title="Custom line">+</button>
              <button class="ctlbtn" id="btnWrite">📋  Write-up</button>
            </div>
            <div class="pills" id="pills"></div>
            <div class="filters">
              <span class="cap">SPLIT</span><select class="sel" id="selSplit"></select>
              <span class="cap">MINUTES</span><select class="sel" id="selMin"></select>
              <span class="cap">REST</span><select class="sel" id="selRest"></select>
              <span class="cap">QUICK</span>
              <button class="quick" data-quick="Home">Home</button><button class="quick" data-quick="Back-to-back">Back-to-back</button><button class="quick" data-quick="30+ min">30+ min</button>
            </div>
            <div class="summary">
              <div><div class="hit-title" id="hitTitle"></div><div class="hit-big"><b id="hitBig">–</b><span id="hitSub"></span></div></div>
              <div class="tabs" id="tabs"></div>
            </div>
            <div class="meta">
              <span class="k">Avg</span><span class="v" id="vAvg">–</span>
              <span class="k">Median</span><span class="v" id="vMed">–</span>
              <span class="k">Model</span><span class="v" id="vModel">–</span>
              <span class="k">Season</span><span class="v" id="vSeason">–</span>
              <span class="sp"></span><span class="nt" id="note"></span>
            </div>
            <div class="model-note" id="modelNote"></div>
            <div class="meta"><span class="v" id="injury"></span></div>
            <div class="lacks" id="lacks"></div>
            <div class="chart-head"><span class="cap" id="chartTitle"></span><span class="hint">Hover a bar for the box score  ·  click “?” for the matchup</span></div>
            <div class="chart" id="chart"></div>
          </div>
        </section>

        <!-- Matchup -->
        <section data-page="Matchup" hidden>
          <div class="panel">
            <div class="strip"></div>
            <div class="mu-head">
              <div class="vsbadge" id="vsBadge"></div>
              <div><h3 id="vsText">vs –</h3><div class="d" id="vsDate"></div></div>
              <div class="mini"><div><b id="cellSpread">–</b><small>SPREAD</small></div><div><b id="cellTotal">–</b><small>TOTAL</small></div></div>
            </div>
            <div class="mu-body">
              <div class="card postable"><div class="sec-head"><i></i>WHAT THE OPPONENT ALLOWS BY POSITION</div><div id="posTable"></div><div class="mu-foot"><div class="nt" id="posNote"></div></div></div>
              <div class="card"><div class="sec-head"><i></i>OPPONENT TEAM PROFILE <span class="muted" id="muSrc" style="margin-left:auto;font-weight:400"></span></div><div id="teamRows"></div></div>
            </div>
            <div class="mu-foot">
              <div class="good" id="muWeak"></div><div class="bad" id="muTough"></div><div class="soft" id="muOff"></div><div class="nt" id="muNote"></div>
            </div>
          </div>
        </section>

        <!-- Player profile -->
        <section data-page="Player profile" hidden>
          <div class="panel">
            <div class="strip"></div>
            <div class="prof-head"><h3>Player profile</h3><span class="g" id="profGames"></span><div class="seg" id="profSeg"></div></div>
            <div class="prof-note" id="profNote"></div>
            <div class="tiles" id="profTiles"></div>
          </div>
        </section>

        <!-- Analysis -->
        <section data-page="Analysis" hidden>
          <div class="panel">
            <div class="strip"></div>
            <div class="page-head"><h2>🔬  Analysis</h2></div>
            <div class="page-sub" id="anSub">Search a player to see the full breakdown.</div>
            <div class="page-desc"> </div>
            <div class="adv" id="advTiles"></div>
            <div id="anCards" style="padding-bottom:10px"></div>
          </div>
        </section>

        <!-- Team pages -->
        <section data-page="Player's team" hidden><div class="panel" id="tp_team"></div></section>
        <section data-page="Player's opponent" hidden><div class="panel" id="tp_opp"></div></section>

        <!-- Today's picks -->
        <section data-page="Today's picks" hidden>
          <div class="panel">
            <div class="strip"></div>
            <div class="page-head"><h2>⭐  Today's best picks</h2><button class="btn-small" id="btnPicksRefresh">⟳  Refresh</button></div>
            <div class="page-sub" id="picksSub"></div>
            <div class="page-desc">Ranked by model probability using matchup, injuries, pace and home court.</div>
            <div class="two">
              <div id="pickList"></div>
              <div class="detail">
                <h3 id="pdTitle">Select a pick</h3><div class="sub" id="pdSub"></div>
                <div class="chips" id="pdChips"></div>
                <div class="chart tall" id="pdChart" hidden></div>
                <div id="pdForm"></div>
                <div class="why">WHY THIS PICK</div><div class="reasons" id="pdReasons"></div>
              </div>
            </div>
          </div>
        </section>

        <!-- News -->
        <section data-page="News" hidden>
          <div class="panel">
            <div class="strip"></div>
            <div class="page-head"><h2>📰  News</h2><button class="btn-small" id="btnNewsRefresh">⟳  Refresh</button></div>
            <div class="page-sub" id="newsSub"></div>
            <div class="page-desc">Headlines about your player, his team, the matchup and the league.</div>
            <div class="chips2" id="newsChips"></div>
            <div id="newsList" style="padding:0 12px 12px"></div>
          </div>
        </section>

        <!-- Games & injuries -->
        <section data-page="Games & injuries" hidden>
          <div class="panel">
            <div class="strip"></div>
            <div class="page-head"><h2>📅  Games &amp; injuries</h2><button class="btn-small" id="btnGamesRefresh">⟳  Refresh</button></div>
            <div class="page-sub" id="gamesSub"></div>
            <div class="legend" id="legend"></div>
            <div class="two games">
              <div id="gameList"></div>
              <div class="detail"><h3 id="gdTitle"></h3><div class="sub" id="gdSub"></div><div class="gcols" id="gdCols" style="padding-top:8px"></div></div>
            </div>
          </div>
        </section>

      </div>
    </div>

    <aside id="side">
      <div class="panel sm">
        <div class="sec-head"><i></i>WIN PROBABILITY</div>
        <div class="wp-grid">
          <div class="wp-side" id="wpAway"><div class="lg"></div><b>–</b><span class="pc">–</span><small> </small></div>
          <div class="ring">
            <svg viewBox="0 0 112 112"><g transform="rotate(-90 56 56)"><circle id="ringTrack" cx="56" cy="56" r="49.4" fill="none" stroke="#26262f" stroke-width="9"/><circle id="ringArc" cx="56" cy="56" r="49.4" fill="none" stroke="#a855f7" stroke-width="9" stroke-linecap="butt" stroke-dasharray="0 311"/></g></svg>
            <div class="mid"><b id="ringTeam">–</b><small id="ringSub"></small></div>
          </div>
          <div class="wp-side" id="wpHome"><div class="lg"></div><b>–</b><span class="pc">–</span><small> </small></div>
        </div>
        <div class="wpbar" id="wpBar"></div>
        <div class="wpleg" id="wpLeg"></div>
        <div class="wpsrc" id="wpSrc">Waiting for data</div>
      </div>
      <div class="panel sm">
        <div class="sec-head"><i></i>GAME LINES</div>
        <div class="oteam card" id="oc0"><div class="nm">–</div><div class="ocells"><div class="ocell"><small>MONEYLINE</small><b>–</b><i> </i></div><div class="ocell"><small>SPREAD</small><b>–</b><i> </i></div><div class="ocell"><small>TOTAL</small><b>–</b><i> </i></div></div></div>
        <div class="oteam card" id="oc1"><div class="nm">–</div><div class="ocells"><div class="ocell"><small>MONEYLINE</small><b>–</b><i> </i></div><div class="ocell"><small>SPREAD</small><b>–</b><i> </i></div><div class="ocell"><small>TOTAL</small><b>–</b><i> </i></div></div></div>
        <div class="onote" id="oddsNote"></div>
      </div>
      <div class="bestcard" id="bestPlayer">⭐ OUTPLAI BEST PLAYER'S PICK: –</div>
      <div class="bestcard gold" id="bestGame">🏆 OUTPLAI BEST GAME PICK: –</div>
    </aside>
  </div>
  <div class="dock" id="dockSlot"></div>
</div>

<div id="tip" hidden></div>
<script>
'use strict';
/* OutplAI Engine - web front end (same pages, colours and behaviour as the desktop app) */
const $ = (s, e = document) => e.querySelector(s);
const $$ = (s, e = document) => [...e.querySelectorAll(s)];
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const sleep = ms => new Promise(r => setTimeout(r, ms));

/* ------------------------------------------------------------------ colour helpers (ported 1:1 from the desktop app) */
const hex2rgb = h => [1, 3, 5].map(i => parseInt(h.substr(i, 2), 16));
const rgb2hex = a => '#' + a.map(v => Math.round(v).toString(16).padStart(2, '0')).join('');
const blend = (c1, c2, t) => { try { const a = hex2rgb(c1), b = hex2rgb(c2); return rgb2hex(a.map((x, i) => x + (b[i] - x) * t)); } catch (e) { return c2; } };
const lum = c => { try { const [r, g, b] = hex2rgb(c).map(v => v / 255); return .2126 * r + .7152 * g + .0722 * b; } catch (e) { return .5; } };
const ensureVisible = (c, min = .33) => { for (let i = 0; i <= 10; i++) { const k = blend(c, '#ffffff', i / 10); if (lum(k) >= min) return k; } return '#ffffff'; };
const selectedFill = c => lum(c) > .5 ? blend(c, '#000000', .55) : c;
const rgba = (h, a) => { const [r, g, b] = hex2rgb(h); return `rgba(${r},${g},${b},${a})`; };

/* ------------------------------------------------------------------ formatting */
const fmtOdds = p => p == null ? '–' : (p > 0 ? '+' + p : String(p));
const fmtPoint = p => p == null ? '–' : (p > 0 ? '+' + (+p) : String(+p));
const g = v => String(+v);
function fmtPat(p, v) {
  const m = String(p).match(/^(.*)\{:(\+?)\.(\d)f\}(.*)$/);
  if (!m) return String(v);
  let s = Number(v).toFixed(+m[3]);
  if (m[2] && v >= 0) s = '+' + s;
  return m[1] + s + m[4];
}
function rankTone(kind, rank, n, isOver) {
  n = Math.max(n, 2);
  let score = kind === 'allow' ? rank / n : 1 - (rank - 1) / n;
  if (!isOver) score = 1 - score;
  return score >= .67 ? 'good' : score >= .34 ? 'mid' : 'bad';
}

/* ------------------------------------------------------------------ api */
async function api(path, body) {
  const r = await fetch(path, { method: body === undefined ? 'GET' : 'POST', headers: { 'Content-Type': 'application/json' }, body: body === undefined ? undefined : JSON.stringify(body) });
  let j = {};
  try { j = await r.json(); } catch (e) { /* ignore */ }
  if (!r.ok || j.error) { const err = new Error(j.error || r.statusText); err.kind = j.kind || 'server'; throw err; }
  return j;
}

/* ------------------------------------------------------------------ state */
let cfg = null;
const S = {
  run: 0, running: null, revealed: false, page: 'Overview',
  player: null, query: null, game: null, schedErr: false, opp: null, home: null, away: null, hk: false, pillLines: {},
  filters: { sample: 'L5', split: 'All games', minutes: 0, rest: 'Any rest', h2h: false },
  view: null, mu: null, odds: null, oddsNote: '', win: null, propOdds: null, injuries: {}, enriched: false,
  accent: null, profileWhich: 'cur', profile: null,
  today: null, todayLoading: false, selPick: null,
  newsKey: null, news: null, newsLoading: false, newsFilter: 'All',
  games: null, gamesLoading: false, selGame: null, rosters: {},
  teams: null, analysis: null, analysisSeq: 0, analysisStale: true,
  charts: new Map(),
};

function base() {
  return { name: S.player.name, query: S.query, filters: S.filters, game: S.game, sched_err: S.schedErr, opp: S.opp, home: S.home, away: S.away, hk: S.hk };
}

/* ------------------------------------------------------------------ small widgets */
function setStatus(text, kind) {
  const [bg, fg] = cfg.status_styles[kind];
  const el = $('#status');
  el.textContent = `  ${text}  `; el.style.background = bg; el.style.color = fg;
}
function toast(msg) {
  const t = document.createElement('div'); t.className = 'toast'; t.textContent = msg; document.body.appendChild(t);
  setTimeout(() => t.remove(), 2200);
}
function logoUrl(abbr) { return cfg.logo_url.replace('{code}', cfg.logo_map[abbr] || abbr.toLowerCase()); }
function badge(abbr, size, ring) {
  abbr = (abbr || '').replace(/^@/, '');
  const baseC = cfg.team_colors[abbr] || cfg.theme.CHIP;
  const fill = lum(baseC) > .12 ? baseC : blend(baseC, '#ffffff', .18);
  const txt = lum(fill) > .6 ? cfg.theme.BG : cfg.theme.TEXT;
  const url = abbr ? logoUrl(abbr) : '';
  return `<span class="team-badge" style="width:${size}px;height:${size}px;background:${fill};color:${txt};${ring ? 'outline:2px solid var(--accent);' : ''}font-size:${Math.max(7, size * .3)}px">` +
    (url ? `<img src="${url}" alt="" onload="this.parentNode.classList.add('ok')" onerror="this.remove()">` : '') + `<em>${esc(abbr)}</em></span>`;
}
function logoImg(abbr, size) { return abbr ? `<img src="${logoUrl(abbr)}" width="${size}" height="${size}" alt="" onerror="this.style.visibility='hidden'">` : ''; }
function brandLogo(el, size, color) {
  const px = Math.round(size * 3);
  if (cfg.has_brand_image) el.innerHTML = `<img src="/brand.png?size=${px}&color=${encodeURIComponent(color)}" alt="" onerror="this.replaceWith(brandSvg('${color}'))">`;
  else el.replaceChildren(brandSvg(color));
}
function brandSvg(color) {
  const s = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
  s.setAttribute('viewBox', '0 0 100 100');
  s.innerHTML = `<circle cx="50" cy="50" r="40" fill="none" stroke="${color}" stroke-width="9"/><path d="M30 60 L48 24 L56 46 L72 40 L52 78 L46 56 Z" fill="${color}"/>`;
  return s;
}
function tone(t) { return { good: 'var(--green)', bad: 'var(--red)', dim: 'var(--dim)', muted: 'var(--muted)', text: 'var(--text)', gold: 'var(--gold-soft)' }[t] || 'var(--text)'; }
function injBadge(it, short) { return `<span class="ibadge" style="background:${it.bg};color:${it.fg}">${esc(short ? it.short : it.status.toUpperCase())}</span>`; }

/* ------------------------------------------------------------------ theme / accent */
function applyTheme() {
  const T = cfg.theme, r = document.documentElement.style;
  const map = { bg: 'BG', surface: 'SURFACE', raised: 'SURFACE_RAISED', inset: 'INSET', ghost: 'GHOST', ctrl: 'CTRL', chip: 'CHIP', border: 'BORDER', border2: 'BORDER_STRONG', royal: 'ROYAL',
    gold: 'GOLD', 'gold-soft': 'GOLD_SOFT', green: 'GREEN', red: 'RED', hit: 'HIT_BAR', miss: 'MISS_BAR', push: 'PUSH_BAR', line: 'LINE', text: 'TEXT', soft: 'TEXT_SOFT', muted: 'MUTED', dim: 'DIM' };
  for (const [k, v] of Object.entries(map)) r.setProperty('--' + k, T[v]);
  r.setProperty('--royal-glow', rgba(T.ROYAL, .9));
}
function applyAccent(team) {
  const baseC = team ? (cfg.team_colors[team] || cfg.default_accent) : cfg.default_accent;
  const c = ensureVisible(baseC);
  S.accent = c;
  const r = document.documentElement.style;
  r.setProperty('--accent', c); r.setProperty('--accent-h', blend(c, '#000000', .2));
  r.setProperty('--accent-light', blend(c, '#ffffff', .4)); r.setProperty('--accent-glow', rgba(c, .55));
  const hdr = lum(c) < .75 ? c : blend(c, cfg.theme.BG, .4);
  r.setProperty('--hdr', hdr); r.setProperty('--hdr-light', blend(hdr, '#ffffff', .4));
  const fill = selectedFill(c);
  r.setProperty('--nav-fill', fill); r.setProperty('--seg-fill', fill);
  brandLogo($('#topLogo'), 30, c);
}

/* ------------------------------------------------------------------ chart (HTML version of the desktop bar chart) */
const STATE_COLOR = () => ({ hit: cfg.theme.HIT_BAR, miss: cfg.theme.MISS_BAR, push: cfg.theme.PUSH_BAR });
function tipHtml(rows) {
  const sc = STATE_COLOR();
  return rows.map(r => {
    if (r[0] === 'title') return `<div class="t">${esc(r[1])}</div>`;
    if (r[0] === 'sub') return `<div class="s">${esc(r[1])}</div>`;
    if (r[0] === 'prop') return `<div class="pr" style="color:${sc[r[2]]}">${esc(r[1])}</div>`;
    if (r[0] === 'rule') return '<hr>';
    return `<div class="row">${r[1].map(([l, v]) => `<div><span>${esc(l)}</span><b>${esc(v)}</b></div>`).join('')}</div>`;
  }).join('');
}
function renderChart(el, ch, onNext) {
  S.charts.set(el, { ch, onNext });
  const bars = ch.bars || [];
  if (!bars.length) { el.innerHTML = `<div class="empty">${esc(ch.empty || '')}</div>`; return; }
  const H = el.classList.contains('tall') ? 330 : 270, padT = 30, padB = 74, plotH = H - padT - padB, base = padT + plotH;
  const slots = bars.length + (ch.next_opp ? 1 : 0), plotW = Math.max(60, el.clientWidth - 22 - 64), slot = plotW / slots;
  const barW = Math.max(24, Math.min(slot * .66, 130)), badgeR = Math.min(14, slot * .32);
  const topVal = Math.max(...bars.map(b => b.value), ch.line, 1) * 1.2, sc = STATE_COLOR();
  let h = '<div class="plot">';
  bars.forEach((b, i) => {
    const ht = Math.max(5, b.value / topVal * plotH), color = sc[b.state];
    h += `<div class="slot" data-i="${i}"><div class="col" style="width:${barW}px"><div class="fill" style="height:${ht}px;background:${color}">` +
      (ht > 40 ? `<span class="unit" style="color:${blend(color, '#ffffff', .55)}">${esc(ch.unit)}</span>` : '') + `</div>` +
      `<div class="val" style="bottom:${ht + 16}px">${esc(b.text)}</div></div>` +
      `<div class="badge" style="top:${base + 24}px">${b.opp.startsWith('@') && slot > 50 ? '<span class="at">@</span>' : ''}${badge(b.opp, Math.max(14, Math.round(badgeR * 2.2)))}</div>` +
      `<div class="date" style="top:${base + 44}px">${esc(b.date)}</div>` + (b.prev ? `<div class="season" style="top:${base + 60}px">${esc(b.season)}</div>` : '') + `</div>`;
  });
  if (ch.next_opp) {
    h += `<div class="slot next"><div class="col" style="width:${barW}px">?</div><div class="badge" style="top:${base + 24}px">${ch.next_opp.startsWith('@') && slot > 50 ? '<span class="at">@</span>' : ''}${badge(ch.next_opp, Math.max(14, Math.round(badgeR * 2.2)), true)}</div>` +
      `<div class="date nx" style="top:${base + 44}px">${esc(ch.next_date || '')}</div></div>`;
  }
  const y = padT + plotH - ch.line / topVal * plotH;
  h += `</div><div class="ln" style="top:${y}px"></div><div class="lnlbl" style="top:${y}px">${g(ch.line)}</div>`;
  el.innerHTML = h;
  const tip = $('#tip');
  $$('.slot', el).forEach(s => {
    if (s.classList.contains('next')) { s.addEventListener('click', () => onNext && onNext()); return; }
    const bar = bars[+s.dataset.i];
    s.addEventListener('mouseenter', () => { s.classList.add('hov'); tip.innerHTML = tipHtml(bar.tip); tip.hidden = false; });
    s.addEventListener('mousemove', e => {
      const w = tip.offsetWidth, hh = tip.offsetHeight;
      let x = e.clientX + 18; if (x + w > innerWidth - 5) x = e.clientX - w - 18;
      tip.style.left = Math.max(5, x) + 'px'; tip.style.top = Math.max(5, Math.min(e.clientY - hh / 2, innerHeight - hh - 5)) + 'px';
    });
    s.addEventListener('mouseleave', () => { s.classList.remove('hov'); tip.hidden = true; });
  });
}
addEventListener('resize', () => { for (const [el, d] of S.charts) if (el.isConnected && el.offsetParent) renderChart(el, d.ch, d.onNext); });

/* ------------------------------------------------------------------ static markup */
function rankRowHtml(id, name) { return `<div class="rankrow"><span class="nm">${esc(name)}</span><span class="vl" id="${id}v">–</span><span class="rchip" id="${id}c"> – </span></div>`; }
function buildApp() {
  $('#nav').innerHTML = cfg.nav_pages.map(p => `<button data-nav="${esc(p)}">${esc(cfg.nav_labels[p] || p)}</button>`).join('');
  $('#pills').innerHTML = cfg.pill_keys.map(k => `<button class="pill-btn" data-pill="${k}">${k}</button>`).join('');
  $('#selSplit').innerHTML = cfg.split_options.map(o => `<option>${o}</option>`).join('');
  $('#selMin').innerHTML = Object.keys(cfg.minutes_options).map(o => `<option>${o}</option>`).join('');
  $('#selRest').innerHTML = cfg.rest_options.map(o => `<option>${o}</option>`).join('');
  $('#tabs').innerHTML = ['L5', 'L10', 'L15', 'SEA', 'PREV', 'H2H'].map(k => `<button class="tab" data-tab="${k}"><span class="n">${k}</span><span class="p">–</span><span class="a"> </span></button>`).join('');
  // matchup tables
  const groups = ['G', 'F', 'C'];
  $('#posTable').innerHTML = `<table><thead><tr><th></th>${groups.map(gg => `<th data-g="${gg}">${esc(cfg.group_names[gg])}</th>`).join('')}</tr></thead><tbody>` +
    cfg.pos_stats.map(([st, label]) => `<tr><td>${esc(label)}</td>${groups.map(gg => `<td><span class="pcell" id="pc_${gg}_${st}">–</span></td>`).join('')}</tr>`).join('') + '</tbody></table>';
  $('#teamRows').innerHTML = cfg.team_stat_rows.map(([k, n]) => rankRowHtml('tr_' + k, n)).join('');
  // profile tiles
  $('#profTiles').innerHTML = cfg.profile_layout.map(([k, t]) => `<div class="tile"><b id="pt_${k}">–</b><span class="t">${esc(t)}</span><span class="s" id="ps_${k}"> </span></div>`).join('');
  // analysis tiles
  $('#advTiles').innerHTML = [['USG', 'USG %'], ['TS', 'TS %'], ['EFG', 'eFG %'], ['G', 'vs GUARDS'], ['F', 'vs FORWARDS'], ['C', 'vs CENTERS']]
    .map(([k, t]) => `<div class="atile"><b id="at_${k}">–</b><span class="t">${t}</span><span class="s" id="as_${k}"> </span></div>`).join('');
  $('#anCards').innerHTML = ['1 · FORM SUMMARY', '2 · MATCHUP ANALYSIS', '3 · INJURY IMPACT', '4 · FINAL MATHEMATICAL PROBABILITY'].map((t, i) =>
    `<div class="card acard"><div class="ttl">${t}</div><div class="body" id="an_${i}"></div></div>`).join('') +
    `<div class="card acard"><div class="ttl">HEAD-TO-HEAD HISTORY (LAST 3 SEASONS)</div><div class="body" id="an_h2h"></div></div>` +
    `<div class="card acard"><div class="ttl">QUARTER &amp; HALF SPLITS (PER GAME)</div><div class="body" id="an_split"></div></div>`;
  // team pages
  for (const id of ['team', 'opp']) {
    $('#tp_' + id).innerHTML = teamPageShell(id);
  }
  // news filter chips
  $('#newsChips').innerHTML = ['All', 'Player', 'Team', 'Matchup', 'League'].map(n => `<button class="fchip" data-nf="${n}">${n}</button>`).join('');
  $('#legend').innerHTML = Object.entries(cfg.injury_legend).map(([s, st]) => `<span class="ibadge" style="background:${st.bg};color:${st.fg}"> ${s.toUpperCase()} </span>`).join('') +
    '<span class="dim" style="font-size:10px;margin-left:6px">Source: ESPN injury report – always confirm close to tip-off.</span>';
  $$('#feat .feature').forEach(() => 0);
}
function teamPageShell(id) {
  const title = id === 'team' ? "Player's team statistics" : "Player's opponent statistics";
  const col = idx => cfg.team_sections.filter((_, i) => [0, 0, 1, 1][i] === idx).map(([name, specs]) =>
    `<div class="card"><h4>${esc(name)}</h4>${specs.map(([label]) => rankRowHtml(`${id}_${label.replace(/\W+/g, '_')}`, label)).join('')}</div>`).join('');
  return `<div class="strip"></div><div class="team-head"><div class="lg" id="${id}_logo"></div><div><h3 id="${id}_name">–</h3><div class="s" id="${id}_sub"></div></div><div class="ttl">${title}</div></div>` +
    `<div class="team-note" id="${id}_note"></div><div class="team-cols"><div>${col(0)}</div><div>${col(1)}</div><div><div class="card"><h4 id="${id}_rt">ROTATION · PER GAME</h4>` +
    `<table class="rot"><thead><tr><th>PLAYER</th><th>MIN</th><th>PTS</th><th>REB</th><th>AST</th><th>3PM</th></tr></thead><tbody id="${id}_rot"></tbody></table></div></div></div>`;
}

/* ------------------------------------------------------------------ navigation + home / dashboard switch */
function revealDashboard() {
  if (S.revealed) return;
  S.revealed = true;
  $('#home').hidden = true; $('#app').hidden = false;
  $('#dockSlot').appendChild($('#searchbar'));
}
function showPage(label) {
  S.page = label;
  $$('#nav button').forEach(b => b.classList.toggle('on', b.dataset.nav === label));
  $$('#pages > section').forEach(s => { s.hidden = s.dataset.page !== label; });
  $('#main').scrollTop = 0;
  // charts hidden while on another page need a fresh layout when shown
  for (const [el, d] of S.charts) if (el.isConnected && el.offsetParent) renderChart(el, d.ch, d.onNext);
  if (label === "Today's picks") loadToday();
  else if (label === 'News') loadNews();
  else if (label === 'Games & injuries') loadGames();
  else if (label === 'Analysis') refreshAnalysis();
}

/* ------------------------------------------------------------------ search flow */
async function submit(text) {
  text = (text ?? $('#q').value).trim();
  if (!text) return;
  if (text === S.running) return;
  try { await api('/api/parse', { q: text }); }
  catch (e) { alert(e.message); return; }
  const run = ++S.run;
  S.running = text;
  revealDashboard(); resetDashboard(); setStatus('Syncing data…', 'busy');
  $('#go').classList.add('busy');
  let res;
  try { res = await api('/api/search', { q: text }); }
  catch (e) {
    if (run !== S.run) return;
    S.running = null; $('#go').classList.remove('busy');
    setStatus('Failed to load', 'error');
    $('#hName').textContent = 'No data'; $('#hGame').textContent = e.message;
    renderChart($('#chart'), { bars: [], empty: e.message });
    return;
  }
  if (run !== S.run) return;
  Object.assign(S, { player: res.player, query: res.query, game: res.game, schedErr: res.sched_err, opp: res.opp, home: res.home, away: res.away, hk: res.hk, pillLines: res.pill_lines });
  S.filters = { sample: 'L5', split: 'All games', minutes: 0, rest: 'Any rest', h2h: false };
  S.profileWhich = 'cur'; S.profile = null; S.analysisStale = true; S.enriched = false;
  syncFilterWidgets();
  applyAccent(res.player.team);
  renderIdentity();
  $('#q').value = '';
  setStatus('Loading matchup data…', 'info');
  $('#bestPlayer').textContent = "⭐ OUTPLAI BEST PLAYER'S PICK\nCalculating with matchup + injury data…";
  $('#bestGame').textContent = '🏆 OUTPLAI BEST GAME PICK\nScanning both teams…';
  $('#go').classList.remove('busy');
  const first = loadView(run);
  loadProfile(run);
  S.newsKey = null; if (S.page === 'News') loadNews();
  await first;
  enrich(run);
}

async function enrich(run) {
  const guard = () => run !== S.run;
  try {
    const e = await api('/api/enrich', base());
    if (guard()) return;
    S.mu = e.matchup; S.odds = e.odds; S.oddsNote = e.odds_note; S.win = e.win; S.home = e.home; S.away = e.away; S.hk = e.hk; S.injuries = e.injuries || {}; S.enriched = true;
    renderMatchup(); renderOddsPanel(); renderWin();
  } catch (err) {
    if (guard()) return;
    S.mu = { error: 'Matchup data unavailable.', ctx: null }; renderMatchup();
  }
  S.running = null;
  setStatus('Live terminal synced' + (S.player.season === cfg.current_season ? '' : ` · ${S.player.season} data`), 'ok');
  loadView(run);
  api('/api/teams', base()).then(t => { if (!guard()) { S.teams = t; renderTeams(); } }).catch(() => { if (!guard()) { S.teams = null; renderTeams('Team statistics are unavailable right now.'); } });
  api('/api/best_player', base()).then(b => { if (!guard()) $('#bestPlayer').textContent = b.text; }).catch(() => {});
  api('/api/best_game', base()).then(b => { if (!guard()) $('#bestGame').textContent = b.text; }).catch(() => {});
  if (S.page === 'Analysis') refreshAnalysis(true);
}

function resetDashboard() {
  Object.assign(S, { player: null, query: null, view: null, mu: null, odds: null, oddsNote: '', win: null, propOdds: null, teams: null, game: null, opp: null, home: null, away: null, hk: false, enriched: false, analysis: null });
  $('#hName').textContent = 'Loading…'; $('#hPos').textContent = ''; $('#hGame').textContent = 'Locating the next game'; $('#hTarget').textContent = ''; $('#hSide').textContent = '';
  $('#hFace').innerHTML = ''; $('#hLogo').innerHTML = '';
  $('#note').textContent = ''; $('#injury').textContent = '';
  renderChart($('#chart'), { bars: [], empty: 'Loading games…' });
  $('#hitBig').textContent = '–'; $('#hitBig').style.color = ''; $('#hitSub').textContent = '';
  $$('#tabs .tab').forEach(t => { t.querySelector('.p').textContent = '–'; t.querySelector('.p').className = 'p'; t.querySelector('.a').textContent = ' '; });
  ['vAvg', 'vMed', 'vModel', 'vSeason'].forEach(id => { $('#' + id).textContent = '–'; $('#' + id).style.color = ''; });
  cfg.profile_layout.forEach(([k]) => { $('#pt_' + k).textContent = '–'; $('#ps_' + k).textContent = ' '; });
  $('#profNote').textContent = ''; $('#profGames').textContent = '';
  $('#modelNote').textContent = ''; $('#lacks').textContent = '';
  $('#bestPlayer').textContent = "⭐ OUTPLAI BEST PLAYER'S PICK: –"; $('#bestGame').textContent = '🏆 OUTPLAI BEST GAME PICK: –';
  $$('.pill-btn').forEach(b => { b.textContent = b.dataset.pill; b.classList.remove('on'); });
  renderTeams(); renderMatchup(); renderOddsPanel(); renderWin();
}

function renderIdentity() {
  const p = S.player;
  $('#hName').textContent = p.name; $('#hPos').textContent = p.position || '';
  const face = $('#hFace'); face.innerHTML = '';
  const img = new Image(); let n = 0;
  img.onerror = () => { n++; if (n < cfg.headshot_urls.length) img.src = cfg.headshot_urls[n].replace('{pid}', p.id); else img.remove(); };
  img.src = cfg.headshot_urls[0].replace('{pid}', p.id); face.appendChild(img);
  $('#hLogo').innerHTML = logoImg(p.team, 48);
}

/* ------------------------------------------------------------------ overview (view payload) */
async function loadView(run) {
  if (!S.player || !S.query) return;
  try {
    const v = await api('/api/view', base());
    if (run !== undefined && run !== S.run) return;
    S.view = v; S.propOdds = v.prop_odds; renderView();
  } catch (e) { setStatus('Failed to load', 'error'); }
}
function syncFilterWidgets() { $('#selSplit').value = cfg.split_options[0]; $('#selMin').value = 'Any minutes'; $('#selRest').value = cfg.rest_options[0]; }

function renderView() {
  const v = S.view, q = S.query, p = S.player;
  if (!v) return;
  $('#hGame').textContent = v.subtitle; $('#hPos').textContent = v.position;
  $('#hTarget').textContent = v.target; $('#hSide').textContent = v.side;
  $$('.pill-btn').forEach(b => {
    const key = b.dataset.pill, propKey = cfg.pill_props[key], active = propKey === q.prop_key;
    const line = active ? q.line : (S.pillLines[key] ?? 0.5);
    b.textContent = `${key}\n${g(line)}`; b.classList.toggle('on', active);
  });
  $('#hitTitle').textContent = v.hit.title;
  $('#hitBig').textContent = v.hit.big; $('#hitBig').style.color = tone(v.hit.tone); $('#hitSub').textContent = v.hit.sub;
  $('#vAvg').textContent = v.avg; $('#vMed').textContent = v.med;
  $('#vModel').textContent = v.model.text; $('#vModel').style.color = tone(v.model.tone);
  $('#vSeason').textContent = v.season; $('#note').textContent = v.rookie;
  $('#modelNote').textContent = v.model_note;
  const inj = $('#injury'); inj.textContent = v.injury ? v.injury.text : ''; inj.style.color = v.injury ? v.injury.color : '';
  $$('#tabs .tab').forEach(t => {
    const d = v.tabs[t.dataset.tab];
    t.classList.toggle('on', d.active);
    t.querySelector('.n').textContent = d.name;
    const pe = t.querySelector('.p'); pe.textContent = d.pct; pe.className = 'p ' + (d.tone === 'good' ? 'good' : d.tone === 'bad' ? 'bad' : '');
    t.querySelector('.a').textContent = d.avg || ' ';
  });
  $$('.quick').forEach(b => b.classList.toggle('on', !!v.quick[b.dataset.quick]));
  $('#chartTitle').textContent = v.chart.title;
  renderChart($('#chart'), v.chart, () => showPage('Matchup'));
  // alt lines
  $('#altSel').innerHTML = '<option value="">Alt Lines</option>' + v.alt.map(a => `<option value="${a.line}">${esc(a.text)}</option>`).join('');
  // line chip + odds buttons
  const po = S.propOdds;
  $('#bookLbl').textContent = po && po.book ? po.book.slice(0, 10).toUpperCase() : 'LINE';
  $('#lineChip').textContent = `L ${g(q.line)}`;
  const label = (prefix, price) => {
    if (!po || price == null) return prefix === 'O' ? 'OVER' : 'UNDER';
    return Math.abs(po.point - q.line) < .01 ? `${prefix}  ${fmtOdds(price)}` : `${prefix} ${g(po.point)}  ${fmtOdds(price)}`;
  };
  $('#btnOver').textContent = label('O', po && po.over); $('#btnUnder').textContent = label('U', po && po.under);
  $('#btnOver').classList.toggle('on', q.is_over); $('#btnUnder').classList.toggle('on', !q.is_over);
  renderMatchupLacks();
  if (S.mu) renderMatchup(true);
}

async function onQueryChange(changes) {
  if (!S.player || !S.query) return;
  S.query = { ...S.query, ...changes }; S.analysisStale = true;
  renderMatchup(true);
  await loadView(S.run);
  if (S.page === 'Analysis') refreshAnalysis();
}

/* ------------------------------------------------------------------ matchup page + odds panel + win predictor */
function setRankRow(idv, idc, data, kind, n, isOver, pattern) {
  const v = $('#' + idv), c = $('#' + idc);
  if (!data) { v.textContent = '–'; c.textContent = ' – '; c.style.background = 'var(--surface)'; c.style.color = 'var(--dim)'; return; }
  const [value, rank] = data, [bg, fg] = cfg.rank_styles[rankTone(kind, rank, n, isOver)];
  v.textContent = fmtPat(pattern, value); c.textContent = ` #${rank} `; c.style.background = bg; c.style.color = fg;
}
function renderMatchupLacks() {
  const ctx = S.mu && S.mu.ctx;
  if (ctx) $('#lacks').textContent = `Where ${S.opp} lacks: ` + (ctx.weak.length ? ctx.weak.slice(0, 3).join(', ') : 'no clear weak spot') + '   (full breakdown in the Matchup tab)';
  else $('#lacks').textContent = S.opp && !(S.mu && S.mu.error) ? 'Loading how the opponent defends…' : '';
}
function renderMatchup() {
  const mu = S.mu, ctx = mu && mu.ctx, opp = S.opp, isOver = S.query ? S.query.is_over : true, p = S.player;
  $('#vsText').textContent = opp ? `vs ${opp}` : 'vs –';
  $('#vsDate').textContent = S.game && S.game.opponent === opp ? S.game.short_date : '';
  $('#vsBadge').innerHTML = opp ? `${logoImg(opp, 32)}` : '';
  let sp = '–', tot = '–';
  if (S.odds && p && opp) { const ln = S.odds.lines[p.team]; sp = ln ? fmtPoint(ln.spread) : '–'; tot = S.odds.total != null ? g(S.odds.total) : '–'; }
  $('#cellSpread').textContent = sp; $('#cellTotal').textContent = tot;
  const group = ctx ? ctx.pos_group : '';
  $$('#posTable th[data-g]').forEach(th => th.classList.toggle('hl', th.dataset.g === group));
  for (const gg of ['G', 'F', 'C']) for (const [st] of cfg.pos_stats) {
    const cell = $(`#pc_${gg}_${st}`), data = ctx && ctx.pos_all[gg] ? ctx.pos_all[gg][st] : null;
    if (!data) { cell.textContent = '–'; cell.style.background = 'var(--surface)'; cell.style.color = 'var(--dim)'; continue; }
    const [value, rank] = data, [bg, fg] = cfg.rank_styles[rankTone('allow', rank, ctx.pos_n, isOver)];
    cell.textContent = `${fmtPat(cfg.pos_patterns[st] || '{:.1f}', value)}  ·  #${rank}`; cell.style.background = bg; cell.style.color = fg;
  }
  $('#posNote').textContent = ctx && group ? `Highlighted = this player's position group (${cfg.group_names[group]}). Rank #1 = allows the fewest. The NBA only splits players into guards / forwards / centers.` : "The NBA only splits players into guards / forwards / centers.";
  const m = ctx && ctx.metrics[opp || ''], allowed = ctx ? ctx.team_allowed : {};
  for (const [key, , pattern] of cfg.team_stat_rows) {
    let data, kind = 'allow';
    if (key === 'DEF') data = m ? [m.def_rating, m.def_rank] : null;
    else if (key === 'PACE') { data = m ? [m.pace, m.pace_rank] : null; kind = 'pace'; }
    else if (key === 'OFF') { data = m && m.off_rating != null ? [m.off_rating, m.off_rank] : null; kind = 'pace'; }
    else data = allowed[key];
    setRankRow('tr_' + key + 'v', 'tr_' + key + 'c', data, kind, 30, isOver, pattern);
  }
  $('#muSrc').textContent = ctx ? ctx.season : '';
  if (ctx) {
    $('#muWeak').textContent = `Where ${opp} lacks (defense): ` + (ctx.weak.length ? ctx.weak.join(', ') : 'no clear weak spot – they defend close to league average');
    $('#muTough').textContent = `Where ${opp} is tough: ` + (ctx.tough.length ? ctx.tough.join(', ') : 'nothing stands out');
    $('#muOff').textContent = ctx.offense;
  } else { $('#muWeak').textContent = ''; $('#muTough').textContent = ''; $('#muOff').textContent = ''; }
  let note = '';
  if (mu && mu.error) note = mu.error;
  else if (ctx && !(ctx.pos_all[group || 'G'] && Object.keys(ctx.pos_all[group || 'G']).length)) note = 'Position data needs a few more games this season.';
  else if (ctx) note = 'Per-game numbers the opponent allows. Green = favourable for your pick, red = tough.';
  $('#muNote').textContent = note;
  renderMatchupLacks();
}
function renderOddsPanel() {
  const odds = S.odds, order = [S.away, S.home];
  [0, 1].forEach(i => {
    const abbr = order[i], home = i === 1, root = $('#oc' + i);
    const name = abbr ? (cfg.team_names[abbr] || abbr) : '–';
    root.querySelector('.nm').textContent = home && abbr && S.hk ? `${name}    ⌂` : name;
    const ln = odds && abbr ? odds.lines[abbr] : null, cells = root.querySelectorAll('.ocell');
    const set = (c, a, b) => { c.querySelector('b').textContent = a; c.querySelector('i').textContent = b || ' '; };
    set(cells[0], ln && ln.ml != null ? fmtOdds(ln.ml) : '–', '');
    set(cells[1], ln && ln.spread != null ? fmtPoint(ln.spread) : '–', ln && ln.spread_price ? fmtOdds(ln.spread_price) : '');
    if (odds && odds.total != null) { const price = home ? odds.under_price : odds.over_price; set(cells[2], `${home ? 'U' : 'O'} ${g(odds.total)}`, price ? fmtOdds(price) : ''); }
    else set(cells[2], '–', '');
  });
  if (odds) $('#oddsNote').textContent = (odds.book ? `Live lines via ${odds.book} · refreshes every minute` : 'Live lines') + (cfg.odds_key ? '' : '\nPlayer-prop odds need an Odds API key (⚙ button, top right).');
  else $('#oddsNote').textContent = S.oddsNote || "Search a player to load the game's lines.";
}
function renderWin() {
  const wp = S.win, side = { home: $('#wpHome'), away: $('#wpAway') };
  const ring = $('#ringArc'), track = $('#ringTrack'), bar = $('#wpBar'), R = 49.4, C = 2 * Math.PI * R;
  ring.setAttribute('stroke-dasharray', `0 ${C}`);
  if (!wp) {
    track.setAttribute('stroke', '#26262f'); ring.setAttribute('stroke', S.accent || cfg.default_accent);
    $('#ringTeam').textContent = '–'; $('#ringSub').textContent = '';
    for (const s of Object.values(side)) { s.querySelector('b').textContent = '–'; const pc = s.querySelector('.pc'); pc.textContent = '–'; pc.style.color = ''; s.querySelector('small').textContent = ' '; s.querySelector('.lg').innerHTML = ''; }
    $('#wpLeg').textContent = ''; $('#wpSrc').textContent = 'Waiting for data'; bar.innerHTML = '';
    return;
  }
  const homeC = ensureVisible(cfg.team_colors[wp.home] || S.accent || cfg.default_accent);
  let awayC = ensureVisible(cfg.team_colors[wp.away] || '#94a3b8');
  if (homeC === awayC) awayC = '#94a3b8';
  track.setAttribute('stroke', awayC); ring.setAttribute('stroke', homeC);
  const frac = Math.min(wp.p_home, .9999); ring.setAttribute('stroke-dasharray', `${C * frac} ${C}`);
  const pAway = 1 - wp.p_home, favHome = wp.p_home >= .5;
  $('#ringTeam').textContent = favHome ? wp.home : wp.away; $('#ringSub').textContent = 'FAVORED';
  const setSide = (s, abbr, p, fav, tag) => { s.querySelector('b').textContent = abbr; const pc = s.querySelector('.pc'); pc.textContent = `${(p * 100).toFixed(1)}%`; pc.style.color = fav ? 'var(--text)' : 'var(--muted)'; s.querySelector('small').textContent = tag; s.querySelector('.lg').innerHTML = logoImg(abbr, 44); };
  setSide(side.home, wp.home, wp.p_home, favHome, wp.home_known ? 'HOME' : ' ');
  setSide(side.away, wp.away, pAway, !favHome, wp.home_known ? 'AWAY' : ' ');
  $('#wpLeg').textContent = `${wp.away} ${(pAway * 100).toFixed(1)}%     •     ${wp.home} ${(wp.p_home * 100).toFixed(1)}%`;
  $('#wpSrc').textContent = wp.source;
  bar.innerHTML = `<div style="width:${pAway * 100}%;background:${awayC}"></div><div style="width:${wp.p_home * 100}%;background:${homeC};border-left:2px solid var(--surface)"></div>`;
}

/* ------------------------------------------------------------------ player profile */
async function loadProfile(run) {
  if (!S.player) return;
  const call = tracking => api('/api/profile', { ...base(), which: S.profileWhich, tracking });
  try {
    const first = await call(false);
    if (run !== S.run) return;
    S.profile = first; renderProfile();
    if (first.loading) {
      const full = await call(true);
      if (run !== S.run || full.which !== S.profileWhich) return;
      S.profile = full; renderProfile();
    }
  } catch (e) { /* profile stays empty */ }
}
function renderProfile() {
  const pr = S.profile;
  if (!pr) return;
  $('#profSeg').innerHTML = pr.labels.map((l, i) => `<button data-which="${i ? 'prev' : 'cur'}" class="${(pr.which === 'prev') === !!i ? 'on' : ''}">${l}</button>`).join('');
  cfg.profile_layout.forEach(([k]) => { const t = pr.tiles[k]; $('#pt_' + k).textContent = t ? t[0] : '–'; $('#ps_' + k).textContent = t ? t[1] : ' '; });
  $('#profGames').textContent = pr.games;
  const n = $('#profNote'); n.textContent = pr.note; n.style.color = pr.note_tone === 'gold' ? 'var(--gold-soft)' : 'var(--muted)';
}

/* ------------------------------------------------------------------ team pages */
function renderTeamPage(id, d, abbrFallbackNote) {
  const set = (k, v) => { $(`#${id}_${k}`).textContent = v; };
  if (!d || !d.abbr) {
    set('name', '–'); set('sub', ''); $(`#${id}_logo`).innerHTML = ''; set('note', (d && d.note) || abbrFallbackNote || '');
    $$(`#tp_${id} .rankrow`).forEach(r => { r.children[1].textContent = '–'; r.children[2].textContent = ' – '; r.children[2].style.cssText = ''; });
    $(`#${id}_rot`).innerHTML = ''; return;
  }
  $(`#${id}_logo`).innerHTML = logoImg(d.abbr, 52);
  set('name', d.name); set('sub', d.record ? `${d.record[0]}-${d.record[1]}  ·  ${d.season}` : (d.season || ''));
  set('note', d.note || 'Rank #1 = best in the league for that stat (fewest allowed, fewest turnovers). Pace is neutral.');
  for (const [, specs] of cfg.team_sections) for (const [label, pattern] of specs) {
    const key = `${id}_${label.replace(/\W+/g, '_')}`, data = (d.stats || {})[label], v = $(`#${key}v`), c = $(`#${key}c`);
    if (!data) { v.textContent = '–'; c.textContent = ' – '; c.style.background = 'var(--surface)'; c.style.color = 'var(--dim)'; continue; }
    const [value, rank, higher] = data, [bg, fg] = higher == null ? ['#1e293b', cfg.theme.MUTED] : cfg.rank_styles[rankTone('pace', rank, 30, true)];
    v.textContent = fmtPat(pattern, value); c.textContent = ` #${rank} `; c.style.background = bg; c.style.color = fg;
  }
  $(`#${id}_rt`).textContent = 'ROTATION · PER GAME' + (d.rot_season ? ` · ${d.rot_season}` : '');
  $(`#${id}_rot`).innerHTML = (d.rotation || []).map(r => `<tr><td>${esc(r.name)}${r.tag ? `  [${esc(r.tag)}]` : ''}</td><td>${r.min}</td><td>${r.pts}</td><td>${r.reb}</td><td>${r.ast}</td><td>${r.fg3m}</td></tr>`).join('');
}
function renderTeams(note) {
  const t = S.teams, p = S.player;
  if (!p) { renderTeamPage('team', { note: 'Search a player to fill this page.' }); renderTeamPage('opp', { note: 'Search a player to fill this page.' }); return; }
  if (!t) {
    renderTeamPage('team', { abbr: p.team, name: cfg.team_names[p.team] || p.team, note: note || 'Loading team statistics…', stats: {}, rotation: [] });
    renderTeamPage('opp', S.opp ? { abbr: S.opp, name: cfg.team_names[S.opp] || S.opp, note: note || 'Loading team statistics…', stats: {}, rotation: [] } : { note: 'No opponent yet. Add  vs BOS  to your search.' });
    return;
  }
  renderTeamPage('team', t.team); renderTeamPage('opp', t.opp);
}

/* ------------------------------------------------------------------ analysis */
let analysisTimer = null;
function refreshAnalysis(now) {
  if (!S.player || !S.query) return;
  if (!S.analysisStale && S.analysis) return;
  clearTimeout(analysisTimer);
  analysisTimer = setTimeout(runAnalysis, now ? 0 : 250);
}
async function runAnalysis() {
  if (!S.player || !S.query || !S.enriched) { $('#anSub').textContent = 'Waiting for matchup, injury and team data…'; return; }
  const seq = ++S.analysisSeq, run = S.run;
  $('#anSub').textContent = 'Crunching the numbers…';
  try {
    const b = await api('/api/analysis', base());
    if (seq !== S.analysisSeq || run !== S.run) return;
    if (b.loading) { $('#anSub').textContent = b.loading; return; }
    S.analysis = b; S.analysisStale = false; renderAnalysis(b);
  } catch (e) { if (seq === S.analysisSeq) $('#anSub').textContent = 'Analysis failed – see the server log.'; }
}
function renderAnalysis(b) {
  $('#anSub').textContent = b.subtitle;
  for (const k of ['USG', 'TS', 'EFG']) {
    const s = b.adv.season[k], l5 = b.adv.l5[k];
    $('#at_' + k).textContent = s == null ? '–' : `${s.toFixed(1)}%`; $('#as_' + k).textContent = `L5 ${l5 == null ? '–' : l5.toFixed(1) + '%'}`;
  }
  for (const gg of ['G', 'F', 'C']) {
    const d = b.posdef[gg], v = $('#at_' + gg), s = $('#as_' + gg);
    if (!d) { v.textContent = '–'; v.style.color = ''; s.textContent = ' '; continue; }
    v.textContent = Math.round(d.score); v.style.color = { soft: 'var(--green)', tough: 'var(--red)', average: 'var(--gold-soft)' }[d.label];
    s.textContent = d.label + (d.mine ? ' · his group' : '');
  }
  ['form', 'matchup', 'injury', 'final'].forEach((k, i) => { $('#an_' + i).innerHTML = b.sections[k].map(l => `<p class="${k === 'final' ? 'fin' : ''}">${esc(l)}</p>`).join(''); });
  const h = b.h2h, hb = $('#an_h2h'), col = { hit: 'var(--green)', miss: 'var(--red)', push: 'var(--muted)' };
  if (!h.n) hb.innerHTML = `<p class="muted">${esc(b.h2h_note)}</p>`;
  else hb.innerHTML = `<p class="text" style="font-weight:700;font-size:12px">${h.n} games · avg ${h.mean.toFixed(1)} (${h.vs_overall >= 0 ? '+' : ''}${h.vs_overall.toFixed(0)}% vs his normal) · hit rate ${h.hits}/${h.decided} (${h.hit_rate.toFixed(0)}%) · projection effect ${h.effect * 100 >= 0 ? '+' : ''}${(h.effect * 100).toFixed(1)}%</p>` +
    `<table class="atable">${h.rows.map(([d, m, v, mn, st]) => `<tr><td>${esc(d)}</td><td>${esc(m)}</td><td class="b" style="color:${col[st]}">${esc(v)}</td><td>${esc(mn)} min</td></tr>`).join('')}</table>`;
  const sb = $('#an_split'), f1 = v => v == null ? '–' : (+v).toFixed(1);
  if (!b.splits.length) sb.innerHTML = `<p class="muted">${esc(b.split_note)}</p>`;
  else sb.innerHTML = `<table class="atable"><tr>${['SEGMENT', 'MIN', 'PTS', 'REB', 'AST', '3PM', b.prop_label, 'SHARE'].map(t => `<th>${esc(t)}</th>`).join('')}</tr>` +
    b.splits.map(([name, mn, pts, reb, ast, tpm, pv, share, late]) => `<tr class="${late ? 'late' : ''}"><td class="b">${esc(name)}</td><td>${f1(mn)}</td><td>${f1(pts)}</td><td>${f1(reb)}</td><td>${f1(ast)}</td><td>${f1(tpm)}</td><td class="b">${f1(pv)}</td><td>${share == null || name.includes('Half') ? '–' : Math.round(share) + '%'}</td></tr>`).join('') +
    `</table><p class="dim italic" style="font-size:9px;margin-top:6px">Gold = late-game segments (4th quarter / 2nd half). 4th-quarter numbers are the clutch-time proxy; blowouts inflate or deflate them.</p>`;
}

/* ------------------------------------------------------------------ today's picks */
async function loadToday(force) {
  if (S.todayLoading) return;
  if (S.today && !force) return;
  S.todayLoading = true;
  $('#picksSub').innerHTML = '<span class="spin"></span>Scanning today\'s games… the first scan can take 20–40 seconds.';
  try {
    let r = await api('/api/today', { force: !!force });
    while (r.status === 'running') {
      $('#picksSub').innerHTML = `<span class="spin"></span>${esc(r.msg)}`;
      await sleep(1200);
      r = await api('/api/today', {});
    }
    if (r.status === 'error') throw new Error('failed');
    S.today = r.result; renderToday();
  } catch (e) { $('#picksSub').textContent = "Could not build today's picks – check your connection and press Refresh."; }
  S.todayLoading = false;
}
function renderToday() {
  const t = S.today, list = $('#pickList');
  list.innerHTML = '';
  if (!t.picks.length) {
    $('#picksSub').textContent = t.note || `No pick in the range for ${t.games} game(s) on ${t.day_text}.`;
    $('#pdTitle').textContent = 'No picks found'; $('#pdSub').textContent = ''; $('#pdChips').innerHTML = ''; $('#pdChart').hidden = true; $('#pdForm').innerHTML = ''; $('#pdReasons').innerHTML = '';
    return;
  }
  $('#picksSub').textContent = `${t.picks.length} best picks from ${t.games} game(s) on ${t.day_text}  ·  ${t.season} data`;
  t.picks.forEach((p, i) => {
    const d = document.createElement('div'); d.className = 'pick'; d.dataset.i = i;
    d.innerHTML = `<span class="rk">#${i + 1}</span><div class="mid"><b>${esc(p.player || p.headline)}</b><small>${esc(p.short)}  ·  ${esc(p.game)}</small></div><span class="pchip"> ${p.prob.toFixed(0)}% </span>`;
    d.onclick = () => selectPick(i); list.appendChild(d);
  });
  selectPick(0);
}
function selectPick(i) {
  const t = S.today; if (!t || !t.picks[i]) return;
  S.selPick = i;
  $$('#pickList .pick').forEach((d, k) => d.classList.toggle('on', k === i));
  const p = t.picks[i];
  $('#pdTitle').textContent = p.headline; $('#pdSub').textContent = p.game + (p.when ? `  ·  ${p.when}` : '');
  $('#pdChips').innerHTML = p.chips.map(c => `<span class="pchip"> ${esc(c)} </span>`).join('') + (p.chart ? '<button class="open" id="pdOpen">📊  Open overview</button>' : '');
  if (p.chart) {
    $('#pdForm').innerHTML = ''; $('#pdChart').hidden = false; renderChart($('#pdChart'), p.chart);
    $('#pdOpen').onclick = () => openPickOverview(p);
  } else { $('#pdChart').hidden = true; showTeamForm(p); }
  $('#pdReasons').innerHTML = p.reasons.map(r => `<p>•  ${esc(r)}</p>`).join('');
}
function showTeamForm(p) {
  $('#pdForm').innerHTML = `<div class="formcols">` + [p.team, p.opp].map(team => {
    const games = (p.recent || {})[team] || [], wins = games.filter(x => x.wl === 'W').length;
    return `<div><div class="fhead">${logoImg(team, 28)}<b>${esc(cfg.team_names[team] || team)}</b><small style="color:${games.length && wins >= 3 ? 'var(--green)' : 'var(--muted)'}">${games.length ? `LAST 5: ${wins}-${games.length - wins}` : 'NO DATA'}</small></div>` +
      games.map(x => { const won = x.wl === 'W'; return `<div class="frow"><span class="wl" style="background:${won ? '#064e3b' : '#4c0519'};color:${won ? '#34d399' : '#f43f5e'}"> ${esc(x.wl || '–')} </span><b>${x.home ? 'vs' : '@'} ${esc(x.opp)}</b><small>${esc(x.date)}</small><span class="sc">${x.opp_pts != null ? `${Math.round(x.pts)}-${Math.round(x.opp_pts)}` : Math.round(x.pts)}</span></div>`; }).join('') + '</div>';
  }).join('') + '</div>';
}
function openPickOverview(p) {
  if (p.kind !== 'player') return;
  const text = `${p.player} ${p.prop_short} ${p.is_over ? 'Over' : 'Under'} ${g(p.line)}` + (p.opp ? ` vs ${p.opp}` : '');
  $('#q').value = text; S.running = null; showPage('Overview'); submit(text);
}

/* ------------------------------------------------------------------ news */
function newsTarget() { const p = S.player; return [p ? p.name : '', p ? p.team : '', S.opp || '']; }
async function loadNews(force) {
  const key = newsTarget().join('|');
  if (S.newsLoading) return;
  if (key === S.newsKey && !force) return;
  S.newsLoading = true; $('#newsSub').innerHTML = '<span class="spin"></span>Loading headlines…';
  try {
    const [player, team, opp] = newsTarget();
    const r = await api('/api/news', { player, team, opp, force: !!force });
    S.news = r; S.newsKey = key; renderNews();
  } catch (e) { $('#newsSub').textContent = 'Could not load news – check your connection and press Refresh.'; }
  S.newsLoading = false;
  if (S.page === 'News' && key !== newsTarget().join('|')) loadNews();
}
function renderNews() {
  const n = S.news; if (!n) return;
  const shown = n.items.filter(i => S.newsFilter === 'All' || i.tag === S.newsFilter);
  $('#newsSub').textContent = `${n.sub}  ·  ${shown.length} stories (click one to open it)`;
  $$('#newsChips .fchip').forEach(b => b.classList.toggle('on', b.dataset.nf === S.newsFilter));
  const tagC = { Player: 'var(--accent)', Team: 'var(--green)', Matchup: 'var(--gold-soft)', League: 'var(--muted)', News: 'var(--muted)' };
  $('#newsList').innerHTML = shown.slice(0, 20).map(i => `<a class="ncard" ${i.url ? `href="${esc(i.url)}" target="_blank" rel="noopener"` : ''}><div class="top"><span class="tg" style="color:${tagC[i.tag] || 'var(--muted)'}"> ${esc(i.tag.toUpperCase())} </span><span class="mt">${esc([i.source, i.ago].filter(Boolean).join('  ·  '))}</span></div><h5>${esc(i.title)}</h5>${i.summary ? `<p>${esc(i.summary)}</p>` : ''}</a>`).join('');
}

/* ------------------------------------------------------------------ games, rosters & injuries */
async function loadGames(force) {
  if (S.gamesLoading) return;
  if (S.games && !force) return;
  S.gamesLoading = true; $('#gamesSub').innerHTML = '<span class="spin"></span>Loading today\'s games and the injury report…';
  try {
    const r = await api('/api/games', { force: !!force });
    S.games = r; S.injuriesAll = r.injuries; renderGames();
  } catch (e) { $('#gamesSub').textContent = 'Could not load the schedule – check your connection and press Refresh.'; }
  S.gamesLoading = false;
}
function renderGames() {
  const r = S.games, list = $('#gameList'); list.innerHTML = '';
  if (!r.games.length) { $('#gamesSub').textContent = 'No NBA games found in the next few days.'; return; }
  $('#gamesSub').textContent = `${r.games.length} game(s) on ${r.day_text}  ·  ${r.hurt} players with an injury tag  ·  click a game for rosters`;
  const mine = S.player ? S.player.team : null; let pick = 0;
  r.games.forEach((gm, i) => {
    const bits = [gm.when]; if (gm.spread != null) bits.push(`${gm.home} ${fmtPoint(gm.spread)}`); if (gm.total != null) bits.push(`total ${g(gm.total)}`);
    const d = document.createElement('div'); d.className = 'gcard' + (mine && [gm.away, gm.home].includes(mine) ? ' mine' : ''); d.dataset.i = i;
    d.innerHTML = `<div class="r">${logoImg(gm.away, 30)}<b>${esc(gm.away)}</b><span class="at">@</span>${logoImg(gm.home, 30)}<b>${esc(gm.home)}</b>${gm.hurt ? `<span class="bd"> ⚠ ${gm.hurt} </span>` : ''}</div><small>${esc(bits.filter(Boolean).join('  ·  '))}</small>`;
    d.onclick = () => selectGame(i); list.appendChild(d);
    if (mine && [gm.away, gm.home].includes(mine)) pick = i;
  });
  selectGame(pick);
}
function selectGame(i) {
  const r = S.games; if (!r || !r.games[i]) return;
  S.selGame = i;
  $$('#gameList .gcard').forEach((d, k) => d.classList.toggle('on', k === i));
  const gm = r.games[i], bits = [gm.when]; if (gm.spread != null) bits.push(`spread ${gm.home} ${fmtPoint(gm.spread)}`); if (gm.total != null) bits.push(`total ${g(gm.total)}`);
  $('#gdTitle').textContent = `${gm.away}  @  ${gm.home}`; $('#gdSub').textContent = bits.filter(Boolean).join('  ·  ');
  $('#gdCols').innerHTML = teamCol(gm.away, 'AWAY') + teamCol(gm.home, 'HOME');
  [gm.away, gm.home].forEach(requestRoster);
}
function teamCol(abbr, tag) {
  const inj = (S.games.injuries[abbr] || []), roster = S.rosters[abbr], idx = {};
  Object.values(S.games.injuries).flat().forEach(it => { idx[it.name.toLowerCase()] = it; });
  let h = `<div class="gcol" data-team="${abbr}"><div class="gh">${logoImg(abbr, 34)}<b>${esc(cfg.team_names[abbr] || abbr)}</b><small>${tag}</small></div><h6>INJURY REPORT</h6>`;
  if (!inj.length) h += '<div class="ok">✓  No injuries reported</div>';
  inj.forEach(it => { h += `<div class="ir">${injBadge(it)}<b>${esc(it.name)}${it.pos ? '  ·  ' + esc(it.pos) : ''}</b></div>` + (it.comment ? `<div class="ic">${esc(it.comment)}</div>` : ''); });
  h += '<h6>ROSTER</h6>';
  if (roster === undefined) h += '<div class="dim" style="padding:0 12px;font-size:11px">Loading roster…</div>';
  else if (!roster.length) h += '<div class="dim" style="padding:0 12px;font-size:11px">Roster unavailable right now.</div>';
  (roster || []).forEach(r => {
    const hurt = idx[r.name.toLowerCase()];
    h += `<div class="rr"><span class="nn">${r.num ? '#' + esc(r.num) : ''}</span><span class="nm">${esc(r.name)}</span><span class="ps">${esc([r.pos, r.height].filter(Boolean).join('  '))}</span>${hurt ? injBadge(hurt, true) : ''}</div>`;
  });
  return h + '</div>';
}
async function requestRoster(abbr) {
  if (S.rosters[abbr] !== undefined || S.rosters['_p' + abbr]) return;
  S.rosters['_p' + abbr] = true;
  try { const r = await api('/api/roster', { abbr }); S.rosters[abbr] = r.roster; } catch (e) { S.rosters[abbr] = []; }
  if (S.games && S.selGame != null) { const gm = S.games.games[S.selGame]; if (gm) $('#gdCols').innerHTML = teamCol(gm.away, 'AWAY') + teamCol(gm.home, 'HOME'); }
}

/* ------------------------------------------------------------------ event wiring */
function wire() {
  $('#go').onclick = () => submit();
  const q = $('#q');
  q.addEventListener('keydown', e => { if (e.key === 'Enter') submit(); });
  q.addEventListener('focus', () => $('#searchbar').classList.add('focus'));
  q.addEventListener('blur', () => $('#searchbar').classList.remove('focus'));
  $$('[data-example]').forEach(b => b.onclick = () => { $('#q').value = b.dataset.example; submit(b.dataset.example); });
  $('#btnToday').onclick = () => {
    revealDashboard();
    if (!S.player) { $('#hName').textContent = 'Search a player'; $('#hGame').textContent = 'Type a player, a stat and a line below to fill the other pages'; }
    showPage("Today's picks");
  };
  $('#nav').onclick = e => { const b = e.target.closest('[data-nav]'); if (b) showPage(b.dataset.nav); };
  $('#pills').onclick = e => { const b = e.target.closest('[data-pill]'); if (!b || !S.player) return; const prop = cfg.pill_props[b.dataset.pill]; if (prop !== S.query.prop_key) onQueryChange({ prop_key: prop, line: S.pillLines[b.dataset.pill] ?? .5 }); };
  $('#btnOver').onclick = () => { if (S.query && !S.query.is_over) onQueryChange({ is_over: true }); };
  $('#btnUnder').onclick = () => { if (S.query && S.query.is_over) onQueryChange({ is_over: false }); };
  $('#altSel').onchange = e => { const l = parseFloat(e.target.value); e.target.value = ''; if (S.query && !isNaN(l) && l !== S.query.line) onQueryChange({ line: l }); };
  $('#btnPlus').onclick = () => {
    if (!S.query) return;
    const raw = prompt('Enter a custom line (e.g. 5.5):'); const l = parseFloat(raw);
    if (!isNaN(l) && l >= 0 && l !== S.query.line) onQueryChange({ line: l });
  };
  $('#btnWrite').onclick = async () => {
    const v = S.view; if (!(S.player && S.query && v)) return;
    const p = S.player, q = S.query, title = v.target.replace(/\s*·$/, '');
    const lines = [`${p.name} (${p.team}) – ${title} ${v.side}`, v.subtitle, `${v.hit.title.split('  ·')[0].toLowerCase().replace(/\b\w/g, c => c.toUpperCase())} hit rate: ${v.hit.big} (${v.hit.sub}) · Avg ${v.avg} · Median ${v.med}`];
    if (v.model.text !== 'n/a') lines.push(`Model probability: ${v.model.text}`);
    lines.push(`Season avg: ${v.season.replace('  (', ' over ').replace(' gm · ', ' games (').replace(/\)$/, '') })`.replace(/\)\)$/, ')'));
    if (S.propOdds) lines.push(`${S.propOdds.book}: Over ${fmtOdds(S.propOdds.over)} / Under ${fmtOdds(S.propOdds.under)} at ${g(S.propOdds.point)}`);
    try { await navigator.clipboard.writeText(lines.join('\n')); } catch (e) { /* clipboard blocked */ }
    setStatus('Write-up copied to clipboard', 'ok');
  };
  $('#selSplit').onchange = e => { if (S.player) { S.filters = { ...S.filters, split: e.target.value }; filtersChanged(); } };
  $('#selMin').onchange = e => { if (S.player) { S.filters = { ...S.filters, minutes: cfg.minutes_options[e.target.value] }; filtersChanged(); } };
  $('#selRest').onchange = e => { if (S.player) { S.filters = { ...S.filters, rest: e.target.value }; filtersChanged(); } };
  $$('.quick').forEach(b => b.onclick = () => {
    if (!S.player) return; const f = S.filters, n = b.dataset.quick;
    if (n === 'Home') { const v = f.split === 'Home' ? cfg.split_options[0] : 'Home'; $('#selSplit').value = v; S.filters = { ...f, split: v }; }
    else if (n === 'Back-to-back') { const v = f.rest === 'Back-to-back' ? cfg.rest_options[0] : 'Back-to-back'; $('#selRest').value = v; S.filters = { ...f, rest: v }; }
    else { const v = f.minutes === 30 ? 'Any minutes' : '30+ min'; $('#selMin').value = v; S.filters = { ...f, minutes: cfg.minutes_options[v] }; }
    filtersChanged();
  });
  $('#tabs').onclick = e => {
    const b = e.target.closest('[data-tab]'); if (!b || !S.player) return;
    if (b.dataset.tab === 'H2H') S.filters = { ...S.filters, h2h: !S.filters.h2h }; else S.filters = { ...S.filters, sample: b.dataset.tab };
    filtersChanged();
  };
  $('#profSeg').onclick = e => { const b = e.target.closest('[data-which]'); if (b && S.player && b.dataset.which !== S.profileWhich) { S.profileWhich = b.dataset.which; loadProfile(S.run); } };
  $('#newsChips').onclick = e => { const b = e.target.closest('[data-nf]'); if (b) { S.newsFilter = b.dataset.nf; renderNews(); } };
  $('#btnPicksRefresh').onclick = () => loadToday(true);
  $('#btnNewsRefresh').onclick = () => loadNews(true);
  $('#btnGamesRefresh').onclick = () => { S.rosters = {}; loadGames(true); };
  $('#btnKey').onclick = async () => {
    const raw = prompt('Paste your The Odds API key (the-odds-api.com).\nGame lines already load from ESPN without a key;\nthe key adds sportsbook player-prop odds.');
    if (raw === null) return;
    try {
      const r = await api('/api/oddskey', { key: raw }); cfg.odds_key = r.odds_key;
      setStatus(r.odds_key ? 'Odds key saved' : 'Odds key cleared', 'ok');
      if (S.player && S.query) pollOdds();
    } catch (e) { alert(e.message); }
  };
  setInterval(pollOdds, cfg.odds_refresh_ms);
}
async function filtersChanged() { await loadView(S.run); }
async function pollOdds() {
  if (!S.player || !S.query || S.running || document.hidden || !S.enriched) return;
  const run = S.run;
  try {
    const r = await api('/api/odds', base());
    if (run !== S.run || r.skip) return;
    S.odds = r.odds; S.oddsNote = r.odds_note; S.win = r.win; S.home = r.home; S.away = r.away; S.hk = r.hk; S.propOdds = r.prop_odds; cfg.odds_key = r.odds_key;
    renderOddsPanel(); renderWin(); renderMatchup();
    if (S.view) { S.view.prop_odds = r.prop_odds; renderView(); }
  } catch (e) { /* keep the last good lines */ }
}

/* ------------------------------------------------------------------ boot */
(async function init() {
  cfg = await api('/api/config');
  cfg.pill_props = cfg.pill_props || {};
  cfg.current_season = cfg.current_season || '';
  applyTheme();
  $('#q').placeholder = cfg.placeholder;
  buildApp();
  applyAccent(null);
  brandLogo($('#homeLogo'), 54, cfg.default_accent);
  if (!cfg.allow_key_edit) $('#btnKey').hidden = true;
  setStatus('Ready', 'idle');
  showPage('Overview');
  renderTeams(); renderMatchup(); renderOddsPanel(); renderWin();
  syncFilterWidgets();
  wire();
  $('#q').focus();
})();

</script>
</body>
</html>
'''


ROUTES = {"/api/config": api_config, "/api/parse": api_parse, "/api/search": api_search, "/api/view": api_view, "/api/enrich": api_enrich,
          "/api/odds": api_odds, "/api/profile": api_profile, "/api/teams": api_teams, "/api/best_player": api_best_player,
          "/api/best_game": api_best_game, "/api/analysis": api_analysis, "/api/today": api_today, "/api/news": api_news,
          "/api/games": api_games, "/api/roster": api_roster, "/api/oddskey": api_odds_key}


def _json_response(start_response, payload, status="200 OK"):
    body = json.dumps(jsonable(payload), ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    start_response(status, [("Content-Type", "application/json; charset=utf-8"), ("Content-Length", str(len(body))), ("Cache-Control", "no-store")])
    return [body]


def application(environ, start_response):
    """WSGI entry point: `python outplai_web.py`, or `gunicorn outplai_web:application` / `waitress-serve outplai_web:application`."""
    path, method = environ.get("PATH_INFO", "/"), environ.get("REQUEST_METHOD", "GET")
    try:
        if method == "GET" and path in ("/", "/index.html"):
            body = INDEX_HTML.encode("utf-8")
            start_response("200 OK", [("Content-Type", "text/html; charset=utf-8"), ("Content-Length", str(len(body))), ("Cache-Control", "no-cache")])
            return [body]
        if method == "GET" and path == "/brand.png":
            qs = parse_qs(environ.get("QUERY_STRING", ""))
            size = max(16, min(512, int((qs.get("size") or ["90"])[0])))
            color = (qs.get("color") or ["#a855f7"])[0]
            if not re.fullmatch(r"#[0-9a-fA-F]{6}", color): color = "#a855f7"
            png = brand_png(size, color)
            if png is None:
                start_response("404 Not Found", [("Content-Type", "text/plain")])
                return [b"no brand image"]
            start_response("200 OK", [("Content-Type", "image/png"), ("Content-Length", str(len(png))), ("Cache-Control", "public, max-age=86400")])
            return [png]
        if method == "GET" and path == "/api/health": return _json_response(start_response, {"ok": True})
        handler = ROUTES.get(path)
        if handler is None:
            return _json_response(start_response, {"error": "Not found"}, "404 Not Found")
        body = {}
        if method == "POST":
            length = int(environ.get("CONTENT_LENGTH") or 0)
            raw = environ["wsgi.input"].read(length) if length else b""
            body = json.loads(raw.decode("utf-8")) if raw else {}
        elif path != "/api/config":
            return _json_response(start_response, {"error": "Use POST"}, "405 Method Not Allowed")
        return _json_response(start_response, handler(body))
    except ApiError as exc:
        return _json_response(start_response, {"error": str(exc), "kind": exc.kind}, f"{exc.status} Bad Request")
    except (DataError, QueryError) as exc:
        return _json_response(start_response, {"error": str(exc), "kind": "data"}, "400 Bad Request")
    except Exception:
        log.exception("Request %s failed", path)
        return _json_response(start_response, {"error": "Unexpected error while loading data. See the server log.", "kind": "server"}, "500 Internal Server Error")


class _ThreadingServer(ThreadingMixIn, WSGIServer):
    daemon_threads = True
    allow_reuse_address = True


class _QuietHandler(WSGIRequestHandler):
    def log_message(self, *args, **kwargs):
        pass


def main(argv=None):
    global ALLOW_KEY_EDIT
    ap = argparse.ArgumentParser(description="OutplAI Engine - live NBA betting engine (website)")
    ap.add_argument("--host", default=os.environ.get("HOST", "127.0.0.1"), help="interface to listen on (use 0.0.0.0 to share on your network)")
    ap.add_argument("--port", type=int, default=int(os.environ.get("PORT", "8000")))
    ap.add_argument("--no-browser", action="store_true", help="do not open the browser automatically")
    args = ap.parse_args(argv)
    local = args.host in ("127.0.0.1", "localhost", "::1")
    ALLOW_KEY_EDIT = local or os.environ.get("OUTPLAI_ALLOW_KEY_EDIT") == "1"
    try: server = make_server(args.host, args.port, application, server_class=_ThreadingServer, handler_class=_QuietHandler)
    except OSError as exc:
        print(f"Could not start on {args.host}:{args.port} ({exc}). Try --port 8080.")
        return 1
    url = f"http://{'localhost' if local else args.host}:{args.port}"
    print(f"OutplAI Engine web is running at {url}   (Ctrl+C to stop)")
    if not args.no_browser and local:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try: server.serve_forever()
    except KeyboardInterrupt: print("\nStopping…")
    finally:
        shutdown_pools()
        server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
