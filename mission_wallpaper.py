#!/usr/bin/env python3
"""
mission_wallpaper.py  (Windows + Ubuntu/GNOME + macOS)

Keeps a "Mission 2030 - 100 Days" countdown wallpaper running live on the
desktop: every UPDATE_INTERVAL_SECONDS, it recomputes the remaining time,
redraws the timer cards, saves a new wallpaper image, and tells the OS to
refresh the desktop with it.

The countdown always counts down from a fixed calendar date and time --
MISSION_START_DATE below (10th Aug 2026, 11:59 AM) -- not from whenever
this is started. "Now" is read from the local machine's own clock and
timezone, so the countdown reflects whatever that machine considers the
current date/time to be.

On Ubuntu (GNOME) this is normally run as the bundled standalone
"mission-wallpaper" executable -- no Python install needed.

On Windows and macOS this runs as a plain script and needs:
    pip install Pillow
"""

import ctypes
import hashlib
import io
import json
import os
import platform
import subprocess
import sys
import tempfile
import time
import urllib.request
from datetime import datetime, timedelta

from PIL import Image, ImageDraw, ImageFont, ImageFilter

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

# How often to refresh the wallpaper. The OS redraws the whole desktop on
# every refresh call, so 1 second gives a true live tick but can cause a
# brief visible flicker each second on some systems. If that's distracting,
# raise this to e.g. 15 or 60 -- everything else works the same.
UPDATE_INTERVAL_SECONDS = 1

CANVAS_W, CANVAS_H = 1920, 1080

# ---------------------------------------------------------------------------
# Auto-update
# ---------------------------------------------------------------------------
# This app's own version. Bump this in build_src/mission_wallpaper.py every
# time you publish a new version to the URL below -- that's what tells an
# already-installed copy a newer version exists.
APP_VERSION = "1.0.0"

# Where to check for updates. Leave this blank ("") to disable auto-update
# entirely -- everything below is a no-op until this is set.
#
# Point it at an HTTPS URL you control that serves a small JSON file shaped
# like:
#   {
#     "version": "1.0.1",
#     "windows": {"url": "https://.../mission_wallpaper.py", "sha256": "<hex>"},
#     "mac":     {"url": "https://.../mission_wallpaper.py", "sha256": "<hex>"},
#     "linux":   {"url": "https://.../mission-wallpaper",    "sha256": "<hex>"}
#   }
# See Mission_2030_Install_Guide.docx for the full walkthrough (hosting
# options, how to compute the sha256 values, etc).
UPDATE_MANIFEST_URL = ""

# How often a running copy re-checks for updates (once at startup, then on
# this interval for as long as it keeps running).
UPDATE_CHECK_INTERVAL_SECONDS = 6 * 60 * 60  # 6 hours

UPDATE_HTTP_TIMEOUT_SECONDS = 8

# The mission's 100 days count down from this fixed date and time, read
# using the local machine's own clock and timezone -- not from whenever
# the app happens to be launched.
MISSION_START_DATE = datetime(2026, 8, 10, 11, 59, 0)
MISSION_DURATION_DAYS = 100
# The end date/time shown and counted down to. Set to a clean 12:00 PM
# rather than exactly 100*24h after MISSION_START_DATE (which would land
# on 11:59 AM) -- the countdown reaches zero at exactly this timestamp.
MISSION_END_DATE = datetime(2026, 11, 18, 12, 0, 0)

# Palette matches the live web app's :root CSS variables.
TEXT_PRIMARY = (15, 30, 61)
TEXT_SECONDARY = (74, 91, 122)
ACCENT = (18, 62, 158)
CARD_BORDER = (18, 62, 158, 60)
CARD_BG = (255, 255, 255, 168)


# ---------------------------------------------------------------------------
# Locating bundled assets (works both as a plain script and as a
# PyInstaller --onefile frozen executable, where assets are unpacked to a
# temp dir at sys._MEIPASS).
# ---------------------------------------------------------------------------

def resource_path(*parts):
    if getattr(sys, "frozen", False):
        base = sys._MEIPASS  # type: ignore[attr-defined]
    else:
        base = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, *parts)


def app_data_dir():
    """A writable per-user directory for the output wallpaper images, so
    this works even if the app itself is run from a read-only or oddly
    permissioned location (Downloads, a mounted drive, etc.)."""
    system = platform.system()
    if system == "Windows":
        base = os.environ.get("LOCALAPPDATA") or os.path.expanduser("~")
        path = os.path.join(base, "MissionWallpaper")
    elif system == "Darwin":
        path = os.path.join(os.path.expanduser("~"), "Library", "Application Support", "mission-wallpaper")
    else:
        base = os.environ.get("XDG_DATA_HOME") or os.path.join(os.path.expanduser("~"), ".local", "share")
        path = os.path.join(base, "mission-wallpaper")
    os.makedirs(path, exist_ok=True)
    return path


OUTPUT_DIR = app_data_dir()
# The OS caches the desktop wallpaper bitmap by file path (URI on GNOME),
# not by file content or modification time. Alternating between only two
# fixed filenames (the earlier approach) doesn't defeat this on GNOME: once
# a given path has been set once, GNOME appears to cache the *decoded
# texture* for that exact path and silently keeps reusing it on later
# "changes" back to the same path, even though the file's bytes on disk are
# different by then -- which shows up as the countdown freezing into a
# 2-value oscillation (e.g. "54, 53, 54, 53, ...") forever, since there are
# only ever two possible paths for it to have cached.
#
# The robust fix is to never reuse a filename at all: every tick gets a
# brand-new, never-before-seen path, so no OS's path-based cache can
# possibly have anything stale to serve. Old files are cleaned up right
# after so disk usage stays bounded to a handful of small PNGs.
WALLPAPER_FILE_PREFIX = "wallpaper_%d_" % int(time.time())
KEEP_RECENT_FRAMES = 3


def next_output_path(tick_counter):
    return os.path.join(OUTPUT_DIR, "%s%06d.png" % (WALLPAPER_FILE_PREFIX, tick_counter))


LEGACY_FRAME_NAMES = ("current_wallpaper_a.png", "current_wallpaper_b.png")


def cleanup_old_frames(keep_paths):
    """Remove wallpaper_*.png files that aren't one of the ones we're
    currently keeping -- covers this session's rotation, leftovers from a
    previous run that didn't shut down cleanly, and the two fixed
    filenames an older version of this app used to write (which are no
    longer touched by the current naming scheme and would otherwise sit
    there forever for anyone upgrading)."""
    keep = set(os.path.abspath(p) for p in keep_paths)
    try:
        for name in os.listdir(OUTPUT_DIR):
            is_rotated_frame = name.startswith("wallpaper_") and name.endswith(".png")
            is_legacy_frame = name in LEGACY_FRAME_NAMES
            if not (is_rotated_frame or is_legacy_frame):
                continue
            full = os.path.join(OUTPUT_DIR, name)
            if os.path.abspath(full) in keep:
                continue
            try:
                os.remove(full)
            except OSError:
                pass  # still open/locked by the OS reading it -- fine, try again next tick.
    except OSError:
        pass

WINDOWS_FONT_DIR = r"C:\Windows\Fonts"
LINUX_FONT_CANDIDATES_BOLD = [
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation2/LiberationSans-Bold.ttf",
]
BOLD_FONT_CANDIDATES = [
    os.path.join(WINDOWS_FONT_DIR, "segoeuib.ttf"),
    os.path.join(WINDOWS_FONT_DIR, "arialbd.ttf"),
] + LINUX_FONT_CANDIDATES_BOLD


def find_font(candidates, size):
    for path in candidates:
        if os.path.isfile(path):
            return ImageFont.truetype(path, size)
    return ImageFont.load_default()


# ---------------------------------------------------------------------------
# Drawing helpers
# ---------------------------------------------------------------------------

def draw_tracked_text(draw, xy, text, font, fill, tracking=0, anchor_center_x=None):
    x, y = xy
    widths = [draw.textlength(ch, font=font) for ch in text]
    total_w = sum(widths) + tracking * max(0, len(text) - 1)
    if anchor_center_x is not None:
        x = anchor_center_x - total_w / 2
    cur_x = x
    for ch, w in zip(text, widths):
        draw.text((cur_x, y), ch, font=font, fill=fill)
        cur_x += w + tracking
    return total_w


def ordinal_suffix(day):
    if 11 <= day % 100 <= 13:
        return "th"
    return {1: "st", 2: "nd", 3: "rd"}.get(day % 10, "th")


def format_time_12h(dt):
    text = dt.strftime("%I:%M %p")
    return text[1:] if text[0] == "0" else text


def draw_date_line(draw, y, cx, prefix, dt, font_main, font_sup, tracking, fill, include_time=False):
    """Draws "<PREFIX> <DAY><ordinal-superscript> <MONTH> <YEAR>", optionally
    followed by a 12-hour time, centered at cx -- the same tracked-text,
    superscript-ordinal style used for both the start and end date lines."""
    suffix = ordinal_suffix(dt.day)
    main_part = "%s %d" % (prefix, dt.day)
    tail_part = " %s %d" % (dt.strftime("%b"), dt.year)
    if include_time:
        tail_part += ", %s" % format_time_12h(dt)

    main_w = draw.textlength(main_part, font=font_main)
    sup_w = draw.textlength(suffix, font=font_sup)
    tail_w = draw.textlength(tail_part, font=font_main)
    total_w = (
        main_w + tracking * (len(main_part) - 1)
        + sup_w + tracking
        + tail_w + tracking * (len(tail_part) - 1)
    )
    x = cx - total_w / 2
    x += draw_tracked_text(draw, (x, y), main_part, font_main, fill, tracking=tracking) + tracking
    x += draw_tracked_text(draw, (x, y - 8), suffix, font_sup, fill, tracking=1) + tracking
    draw_tracked_text(draw, (x, y), tail_part, font_main, fill, tracking=tracking)


def rounded_rect_shadow(size, radius, blur=18, alpha=70):
    margin = blur * 3
    w, h = size
    layer = Image.new("RGBA", (w + margin * 2, h + margin * 2), (0, 0, 0, 0))
    d = ImageDraw.Draw(layer)
    d.rounded_rectangle([margin, margin, margin + w, margin + h], radius=radius, fill=(15, 30, 61, alpha))
    return layer.filter(ImageFilter.GaussianBlur(blur)), margin


def silhouette_shadow(source_rgba, blur=14, alpha=90):
    margin = blur * 3
    w, h = source_rgba.size
    alpha_channel = source_rgba.split()[3]
    tinted = Image.new("RGBA", (w, h), (15, 30, 61, alpha))
    tinted.putalpha(alpha_channel.point(lambda a: min(a, alpha)))
    layer = Image.new("RGBA", (w + margin * 2, h + margin * 2), (0, 0, 0, 0))
    layer.alpha_composite(tinted, (margin, margin))
    return layer.filter(ImageFilter.GaussianBlur(blur)), margin


# ---------------------------------------------------------------------------
# One-time base render: background + logos + title + date (never changes
# second to second, so we build it once and reuse it every tick).
# ---------------------------------------------------------------------------

class BaseScene:
    def __init__(self):
        backdrop = Image.open(resource_path("assets", "Backdrop.png")).convert("RGB")
        bw, bh = backdrop.size
        scale = max(CANVAS_W / bw, CANVAS_H / bh)
        backdrop = backdrop.resize((round(bw * scale), round(bh * scale)), Image.LANCZOS)
        bw, bh = backdrop.size
        left = (bw - CANVAS_W) // 2
        top = (bh - CANVAS_H) // 2
        canvas = backdrop.crop((left, top, left + CANVAS_W, top + CANVAS_H)).convert("RGBA")

        shadow_layer = Image.new("RGBA", canvas.size, (0, 0, 0, 0))
        content_layer = Image.new("RGBA", canvas.size, (0, 0, 0, 0))
        draw = ImageDraw.Draw(content_layer)

        mlx_logo = Image.open(resource_path("assets", "mlx_logo.png")).convert("RGBA")
        mlx_w = 300
        mlx_h = round(mlx_logo.height * (mlx_w / mlx_logo.width))
        mlx_logo = mlx_logo.resize((mlx_w, mlx_h), Image.LANCZOS)

        mission_logo = Image.open(resource_path("assets", "Mission_2030_logo.png")).convert("RGBA")
        mission_w = 340
        mission_h = round(mission_logo.height * (mission_w / mission_logo.width))
        mission_logo = mission_logo.resize((mission_w, mission_h), Image.LANCZOS)

        font_title = find_font(BOLD_FONT_CANDIDATES, 42)
        font_date = find_font(BOLD_FONT_CANDIDATES, 22)
        font_date_sup = find_font(BOLD_FONT_CANDIDATES, 14)
        self.font_time_value = find_font(BOLD_FONT_CANDIDATES, 68)
        self.font_time_label = find_font(BOLD_FONT_CANDIDATES, 15)

        title_text = "MISSION MODE 100 DAYS"

        # Circular cards: a square box with radius = half its side turns
        # rounded_rectangle() into a perfect circle.
        self.card_w = self.card_h = 180
        self.card_gap = 22
        self.card_radius = self.card_w // 2
        grid_w = self.card_w * 4 + self.card_gap * 3

        gap_logo_mission = 34
        gap_mission_title = 26
        gap_title_date = 16
        gap_date_date = 22
        gap_date_grid = 40

        title_h = draw.textbbox((0, 0), title_text, font=font_title)[3]
        date_h = draw.textbbox((0, 0), "ON 10", font=font_date)[3]

        total_h = (
            mlx_h + gap_logo_mission
            + mission_h + gap_mission_title
            + title_h + gap_title_date
            + date_h + gap_date_date
            + date_h + gap_date_grid
            + self.card_h
        )
        y = (CANVAS_H - total_h) // 2
        cx = CANVAS_W // 2

        content_layer.alpha_composite(mlx_logo, (cx - mlx_w // 2, y))
        y += mlx_h + gap_logo_mission

        ml_shadow, ml_margin = silhouette_shadow(mission_logo, blur=10, alpha=110)
        shadow_layer.alpha_composite(ml_shadow, (cx - mission_w // 2 - ml_margin, y - ml_margin + 6))
        content_layer.alpha_composite(mission_logo, (cx - mission_w // 2, y))
        y += mission_h + gap_mission_title

        draw_tracked_text(draw, (0, y), title_text, font_title, TEXT_PRIMARY + (255,), tracking=1, anchor_center_x=cx)
        y += title_h + gap_title_date

        # Start date, then the mission's end date/time -- so the wallpaper
        # shows both "from" and "till" at a glance.
        draw_date_line(draw, y, cx, "From", MISSION_START_DATE, font_date, font_date_sup, tracking=3, fill=ACCENT + (255,))
        y += date_h + gap_date_date
        draw_date_line(draw, y, cx, "To", MISSION_END_DATE, font_date, font_date_sup, tracking=3, fill=ACCENT + (255,), include_time=True)
        y += date_h + gap_date_grid

        self.grid_x = cx - grid_w // 2
        self.grid_y = y

        # The 4 card shells (shadow + rounded background + border) never
        # change tick to tick -- only the number/label text on top of them
        # does. Baking them into the cached base here (instead of redrawing
        # + re-blurring 4 shadows every second) is what keeps each render()
        # call fast enough to not eat into the 1-second tick budget -- when
        # a tick runs long, the *next* tick's timestamp jumps by 2 seconds
        # instead of 1, which is what "seconds skip by 2" was.
        for i in range(4):
            card_x = self.grid_x + i * (self.card_w + self.card_gap)
            card_box = [card_x, self.grid_y, card_x + self.card_w, self.grid_y + self.card_h]

            card_shadow, cs_margin = rounded_rect_shadow((self.card_w, self.card_h), radius=self.card_radius, blur=16, alpha=60)
            shadow_layer.alpha_composite(card_shadow, (card_x - cs_margin, self.grid_y - cs_margin + 10))

            card_layer = Image.new("RGBA", content_layer.size, (0, 0, 0, 0))
            card_draw = ImageDraw.Draw(card_layer)
            card_draw.rounded_rectangle(card_box, radius=self.card_radius, fill=CARD_BG)
            card_draw.rounded_rectangle(card_box, radius=self.card_radius, outline=CARD_BORDER, width=2)
            content_layer.alpha_composite(card_layer)

        canvas.alpha_composite(shadow_layer)
        canvas.alpha_composite(content_layer)
        self.base = canvas

    def render(self, days, hours, minutes, seconds):
        frame = self.base.copy()
        draw = ImageDraw.Draw(frame)

        cards = [
            (str(days), "DAYS"),
            ("%02d" % hours, "HOURS"),
            ("%02d" % minutes, "MINUTES"),
            ("%02d" % seconds, "SECONDS"),
        ]

        for i, (value, label) in enumerate(cards):
            card_x = self.grid_x + i * (self.card_w + self.card_gap)

            value_bbox = draw.textbbox((0, 0), value, font=self.font_time_value)
            value_w = value_bbox[2] - value_bbox[0]
            value_h = value_bbox[3] - value_bbox[1]
            value_x = card_x + self.card_w / 2 - value_w / 2
            value_y = self.grid_y + self.card_h / 2 - value_h / 2 - 26
            draw.text((value_x, value_y), value, font=self.font_time_value, fill=ACCENT + (255,))

            label_y = self.grid_y + self.card_h / 2 + 26
            draw_tracked_text(
                draw, (0, label_y), label, self.font_time_label, TEXT_SECONDARY + (255,),
                tracking=3, anchor_center_x=card_x + self.card_w / 2,
            )

        return frame.convert("RGB")


# ---------------------------------------------------------------------------
# OS wallpaper APIs
# ---------------------------------------------------------------------------

SPI_SETDESKWALLPAPER = 20
SPIF_UPDATEINIFILE = 0x01
SPIF_SENDCHANGE = 0x02


def set_windows_wallpaper(path):
    ctypes.windll.user32.SystemParametersInfoW(
        SPI_SETDESKWALLPAPER, 0, path, SPIF_UPDATEINIFILE | SPIF_SENDCHANGE
    )


def is_screen_locked_linux():
    """Best-effort check for the GNOME lock screen being active, via the
    standard ScreenSaver D-Bus interface. Returns False (assume unlocked)
    if it can't be determined -- e.g. a non-GNOME desktop -- so this never
    blocks wallpaper updates on setups we can't detect."""
    try:
        result = subprocess.run(
            ["gdbus", "call", "--session", "--dest", "org.gnome.ScreenSaver",
             "--object-path", "/org/gnome/ScreenSaver",
             "--method", "org.gnome.ScreenSaver.GetActive"],
            check=True, capture_output=True, text=True, timeout=2,
        )
        return "true" in result.stdout.lower()
    except Exception:
        return False


def set_linux_wallpaper(path):
    uri = "file://" + os.path.abspath(path)
    # Best-effort: some of these gsettings keys don't exist on older GNOME
    # versions or non-GNOME desktops, so failures here are not fatal.
    for args in (
        ["gsettings", "set", "org.gnome.desktop.background", "picture-uri", uri],
        ["gsettings", "set", "org.gnome.desktop.background", "picture-uri-dark", uri],
        ["gsettings", "set", "org.gnome.desktop.background", "picture-options", "zoom"],
    ):
        try:
            subprocess.run(args, check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except FileNotFoundError:
            break  # gsettings itself isn't installed -- nothing more to try.


def set_macos_wallpaper(path):
    # Note: the first time this runs, macOS will prompt for permission for
    # the calling process to control "System Events" -- that's a normal,
    # expected one-time Automation permission dialog, not an error.
    abs_path = os.path.abspath(path)
    script = 'tell application "System Events" to tell every desktop to set picture to "%s"' % abs_path
    subprocess.run(["osascript", "-e", script], check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def set_wallpaper(path):
    system = platform.system()
    if system == "Windows":
        set_windows_wallpaper(path)
    elif system == "Darwin":
        set_macos_wallpaper(path)
    elif system == "Linux":
        set_linux_wallpaper(path)


def save_png(image, path):
    # Pillow's Image.save() opens the target file in "w+b" (read+write)
    # mode internally so it can seek back and patch PNG header bytes. On
    # some setups (antivirus intercepting new-file writes, certain Python
    # builds on Windows) that fails with "OSError: [Errno 22] Invalid
    # argument" even though a plain write would succeed. Sidestep it
    # entirely: render to an in-memory buffer, then write those bytes out
    # with a plain write-only open.
    buf = io.BytesIO()
    image.save(buf, "PNG")
    with open(path, "wb") as f:
        f.write(buf.getvalue())


# ---------------------------------------------------------------------------
# Restoring the user's original wallpaper on uninstall
# ---------------------------------------------------------------------------

SPI_GETDESKWALLPAPER = 0x0073
ORIGINAL_WALLPAPER_FILE = os.path.join(OUTPUT_DIR, "original_wallpaper.json")


def get_windows_wallpaper():
    buf = ctypes.create_unicode_buffer(260)
    ctypes.windll.user32.SystemParametersInfoW(SPI_GETDESKWALLPAPER, 260, buf, 0)
    return buf.value or None


def get_linux_wallpaper():
    settings = {}
    for key in ("picture-uri", "picture-uri-dark", "picture-options"):
        try:
            result = subprocess.run(
                ["gsettings", "get", "org.gnome.desktop.background", key],
                check=True, capture_output=True, text=True, timeout=5,
            )
            value = result.stdout.strip()
            if value.startswith("'") and value.endswith("'"):
                value = value[1:-1]
            settings[key] = value
        except Exception:
            pass  # this key may not exist on this GNOME version -- skip it.
    return settings or None


def get_macos_wallpaper():
    try:
        result = subprocess.run(
            ["osascript", "-e", 'tell application "System Events" to tell current desktop to get picture'],
            check=True, capture_output=True, text=True, timeout=5,
        )
        value = result.stdout.strip()
        return value or None
    except Exception:
        return None


def save_original_wallpaper_if_first_run():
    """Captures whatever wallpaper was in place before this app ever
    touched it, so it can be put back on uninstall. Only ever runs once --
    on every later run (including every day of the 100-day countdown) this
    file already exists and is left untouched, so we never accidentally
    "capture" our own countdown frame as the original."""
    if os.path.isfile(ORIGINAL_WALLPAPER_FILE):
        return

    system = platform.system()
    data = None
    if system == "Windows":
        path = get_windows_wallpaper()
        if path:
            data = {"type": "windows", "path": path}
    elif system == "Linux":
        settings = get_linux_wallpaper()
        if settings:
            data = {"type": "linux", "settings": settings}
    elif system == "Darwin":
        path = get_macos_wallpaper()
        if path:
            data = {"type": "darwin", "path": path}

    try:
        with open(ORIGINAL_WALLPAPER_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f)
    except OSError:
        pass


def restore_original_wallpaper():
    if not os.path.isfile(ORIGINAL_WALLPAPER_FILE):
        print("No saved original wallpaper found -- nothing to restore.")
        return

    try:
        with open(ORIGINAL_WALLPAPER_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError):
        print("Could not read the saved original wallpaper -- nothing to restore.")
        return

    if not data:
        print("The original wallpaper couldn't be determined when this was installed -- nothing to restore.")
        return

    system = platform.system()
    kind = data.get("type")

    if kind == "windows" and system == "Windows" and data.get("path"):
        set_windows_wallpaper(data["path"])
        print("Restored your original wallpaper.")
    elif kind == "linux" and system == "Linux" and data.get("settings"):
        for key, value in data["settings"].items():
            subprocess.run(
                ["gsettings", "set", "org.gnome.desktop.background", key, value],
                check=False,
            )
        print("Restored your original wallpaper.")
    elif kind == "darwin" and system == "Darwin" and data.get("path"):
        set_macos_wallpaper(data["path"])
        print("Restored your original wallpaper.")
    else:
        print("Saved wallpaper info doesn't match this OS -- nothing restored.")


# ---------------------------------------------------------------------------
# Process priority
# ---------------------------------------------------------------------------

def raise_process_priority():
    """Best-effort: ask the OS scheduler to favor this process over normal
    background work, so a busy machine is less likely to delay a tick past
    its 1-second budget and make the countdown skip a second. This only
    reduces the *chance* of a delay -- the self-correcting monotonic loop
    below is what actually guarantees the displayed time stays accurate
    even if a delay happens anyway. Never fatal: if the OS refuses (e.g.
    no permission), the app just keeps running at normal priority."""
    system = platform.system()
    try:
        if system == "Windows":
            HIGH_PRIORITY_CLASS = 0x00000080
            handle = ctypes.windll.kernel32.GetCurrentProcess()
            ctypes.windll.kernel32.SetPriorityClass(handle, HIGH_PRIORITY_CLASS)
        else:
            # Linux and macOS: lower niceness = higher scheduling priority.
            # Unprivileged processes usually can't go negative, in which
            # case this raises and we just fall back to normal priority.
            os.setpriority(os.PRIO_PROCESS, 0, -10)
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Auto-update
# ---------------------------------------------------------------------------

def platform_manifest_key():
    system = platform.system()
    if system == "Windows":
        return "windows"
    if system == "Darwin":
        return "mac"
    return "linux"


def restart_self():
    """Re-executes this same process in place (same PID), so the OS-level
    autostart registration -- which points at this file/binary's path, not
    at a specific process -- doesn't need to be touched."""
    print("Restarting to run the updated version...")
    sys.stdout.flush()
    if getattr(sys, "frozen", False):
        os.execv(sys.argv[0], sys.argv)
    else:
        os.execv(sys.executable, [sys.executable, os.path.abspath(__file__)] + sys.argv[1:])


def check_for_update():
    """Best-effort, safe-by-default auto-update: checks UPDATE_MANIFEST_URL
    (a no-op if left blank) for a newer version, and if the platform's entry
    verifies against its published sha256, atomically replaces this app's
    own file/binary on disk and restarts into it. Never fatal -- any
    failure (no internet, bad manifest, checksum mismatch) just leaves the
    app running as-is and it tries again on the next check interval."""
    if not UPDATE_MANIFEST_URL:
        return
    if not UPDATE_MANIFEST_URL.lower().startswith("https://"):
        print("UPDATE_MANIFEST_URL must be an https:// URL -- skipping update check.")
        return

    try:
        with urllib.request.urlopen(UPDATE_MANIFEST_URL, timeout=UPDATE_HTTP_TIMEOUT_SECONDS) as resp:
            manifest = json.loads(resp.read().decode("utf-8"))

        remote_version = str(manifest.get("version", "")).strip()
        if not remote_version or remote_version == APP_VERSION:
            return  # already up to date (or manifest not usable)

        entry = manifest.get(platform_manifest_key()) or {}
        download_url = entry.get("url")
        expected_sha256 = entry.get("sha256")

        if not download_url or not download_url.lower().startswith("https://"):
            print("Update %s has no valid https download URL for this OS -- skipping." % remote_version)
            return
        if not expected_sha256:
            # Never install anything we can't verify -- refuse rather than
            # silently trusting whatever the URL happens to return.
            print("Update %s has no checksum to verify -- skipping for safety." % remote_version)
            return

        with urllib.request.urlopen(download_url, timeout=UPDATE_HTTP_TIMEOUT_SECONDS) as resp:
            data = resp.read()

        actual_sha256 = hashlib.sha256(data).hexdigest()
        if actual_sha256.lower() != expected_sha256.strip().lower():
            print("Update %s failed checksum verification -- skipping." % remote_version)
            return

        target_path = os.path.abspath(sys.argv[0])
        fd, tmp_path = tempfile.mkstemp(dir=os.path.dirname(target_path), prefix=".mission_wallpaper_update_")
        try:
            with os.fdopen(fd, "wb") as f:
                f.write(data)
            if platform.system() != "Windows":
                os.chmod(tmp_path, 0o755)
            # Atomic replace: on Linux this avoids ETXTBSY even though this
            # same file may currently be running as this very process --
            # rename() repoints the directory entry to the new inode without
            # touching the old (still-open, still-running) one.
            os.replace(tmp_path, target_path)
        except OSError:
            try:
                os.remove(tmp_path)
            except OSError:
                pass
            raise

        print("Updated from %s to %s." % (APP_VERSION, remote_version))
        restart_self()
    except Exception as err:
        print("Update check failed (will retry later):", err)


# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------

def main():
    if "--restore-wallpaper" in sys.argv:
        restore_original_wallpaper()
        return

    system = platform.system()
    if system not in ("Windows", "Linux", "Darwin"):
        print("This build supports Windows, Ubuntu/GNOME (Linux) and macOS only.")
        print("It will still render the image file itself for testing purposes.")

    raise_process_priority()
    check_for_update()  # does nothing unless UPDATE_MANIFEST_URL is configured

    target = MISSION_END_DATE
    print("Mission started:", MISSION_START_DATE.isoformat())
    print("Counting down to:", target.isoformat())
    print("Writing wallpaper frames to:", OUTPUT_DIR)

    # Capture the user's current wallpaper before we ever change it (a
    # no-op on every run after the first), so it can be put back later.
    save_original_wallpaper_if_first_run()

    # Clear out anything left behind by a previous run that didn't exit
    # cleanly, so we don't accumulate files forever across restarts.
    cleanup_old_frames(keep_paths=[])

    scene = BaseScene()
    tick_counter = 0
    recent_paths = []

    # Fixed-rate loop: each tick's *target* start time is spaced exactly
    # UPDATE_INTERVAL_SECONDS apart, and the sleep at the end only makes up
    # the remainder after accounting for however long that tick's own
    # rendering/saving/OS call actually took. A plain "sleep(1) after the
    # work" would instead make the real period (work time + 1s), which is
    # exactly what caused seconds to skip by 2 when a tick ran long.
    next_tick = time.monotonic()
    next_update_check = time.monotonic() + UPDATE_CHECK_INTERVAL_SECONDS

    while True:
        if time.monotonic() >= next_update_check:
            check_for_update()  # no-op unless UPDATE_MANIFEST_URL is set
            next_update_check = time.monotonic() + UPDATE_CHECK_INTERVAL_SECONDS

        try:
            # datetime.now() -- the local machine's own clock and timezone.
            remaining = target - datetime.now()
            total_seconds = max(0, round(remaining.total_seconds()))
            days, rem = divmod(total_seconds, 86400)
            hours, rem = divmod(rem, 3600)
            minutes, seconds = divmod(rem, 60)

            frame = scene.render(days, hours, minutes, seconds)
            tick_counter += 1
            output_path = next_output_path(tick_counter)
            save_png(frame, output_path)

            recent_paths.append(output_path)
            del recent_paths[:-KEEP_RECENT_FRAMES]
            cleanup_old_frames(keep_paths=recent_paths)
        except OSError as err:
            # Don't let one bad tick (e.g. a transient antivirus file lock)
            # kill an app meant to run for months at a time.
            print("Skipped this tick due to a file error:", err)
            next_tick += UPDATE_INTERVAL_SECONDS
            time.sleep(max(0, next_tick - time.monotonic()))
            continue

        # Skip touching the desktop background while the GNOME lock screen
        # is active -- changing it while locked can briefly flash the
        # desktop through the lock overlay, exposing it for a split second.
        if system == "Linux" and is_screen_locked_linux():
            pass
        else:
            set_wallpaper(output_path)

        if total_seconds <= 0:
            print("Mission countdown complete.")
            break

        next_tick += UPDATE_INTERVAL_SECONDS
        sleep_time = next_tick - time.monotonic()
        if sleep_time > 0:
            time.sleep(sleep_time)
        else:
            # A tick ran more than a full interval over budget (e.g. the
            # machine briefly stalled) -- resync instead of trying to
            # "catch up" with zero-length sleeps forever.
            next_tick = time.monotonic()


if __name__ == "__main__":
    main()
