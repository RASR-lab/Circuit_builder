#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Circuit Builder
===============
A friendly circuit / wiring-diagram editor for undergraduate students.

  * Drag parts from the library on the left onto the canvas.
  * Click a pin (small circle), then click a pin on another part to wire them.
  * Make your own parts with any pins in the Component Editor.
  * See which pins are connected (the netlist) and check the circuit for shorts.
  * Simulate the circuit: live voltages and currents, an oscilloscope and
    frequency-response (Bode) plots.

Runs on Windows (also macOS / Linux) with Python 3.8 or newer.
Only the standard library is used (Tkinter ships with the Windows installer).
If Pillow is installed it is used for smoother pictures, but it is optional.
"""

import copy
import csv
import json
import math
import os
import re
import sys
import time
import traceback
import uuid
import base64
import colorsys
import hashlib
import io
import shutil
import struct
import subprocess
import tempfile
import zlib
from bisect import bisect_left
from collections import OrderedDict
from itertools import repeat
from operator import add as _op_add, itemgetter
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, filedialog, messagebox, colorchooser

try:  # optional: JPG/BMP/WebP support and higher-quality scaling of pictures
    from PIL import Image as _PILImage
    from PIL import ImageOps as _PILOps
except Exception:  # Pillow not installed: pictures still work (PNG/GIF, plus JPG on Windows)
    _PILImage = None
    _PILOps = None

APP_NAME = "Circuit Builder"
APP_VERSION = "1.7"
FILE_EXT = ".circuit"
LIB_EXT = ".cblib"
G = 24  # pixels per grid unit at 100 % zoom

# --------------------------------------------------------------------------
# Look & feel (light and dark themes)
# --------------------------------------------------------------------------
# Every color the app draws with lives in these two palettes.  C is the live palette:
# set_palette() copies one of them into it, so code just reads C["..."] when drawing.
LIGHT_C = {
    # windows and panels
    "bg": "#eef1f5", "panel": "#ffffff", "border": "#d6dce4", "text": "#1f2933", "muted": "#6b7785",
    "field": "#ffffff",                       # text boxes, entries
    "accent": "#2563eb",                      # lines and highlights in the accent color
    "accent_dark": "#1d4ed8",                 # accent-colored text (custom parts, step numbers)
    "accent_light": "#e3ecff",                # soft accent background (selection, pressed)
    "accent_btn": "#2563eb", "accent_btn_press": "#1d4ed8", "accent_btn_off": "#dfe7f7",
    "on_btn": "#ffffff",                      # text on the colored buttons
    "button": "#f6f8fa", "button_hover": "#edf2fa", "tool_hover": "#eef2f8", "disabled": "#a0a8b2",
    "trough": "#e6eaf0", "thumb": "#e6eaf0", "heading": "#f3f5f8", "arrow": "#000000",
    "clam_frame": "#dcdad5", "clam_active": "#eeebe7", "clam_disabled": "#999999",
    "chk_hi": "#9e9a91", "chk_lo": "#cfcdc8",
    "tip_bg": "#1f2933", "tip_fg": "#ffffff",
    # circuit canvas
    "canvas": "#fbfcfd", "grid": "#eef1f5", "grid_major": "#e0e5ec",
    "stroke": "#26323f", "sym_fill": "#ffffff", "pin_on": "#26323f", "pin_off": "#8d99a6",
    "pin_free": "#ffffff", "pinlabel": "#3e4a57",
    "select": "#2563eb", "sel_fill": "#eaf1ff", "sel_wire": "#bfd3ff", "handle": "#ffffff",
    "hover": "#f59e0b", "highlight": "#fde68a", "net_pin": "#d97706",
    # status colors
    "danger": "#dc2626", "danger_btn": "#dc2626", "danger_btn_press": "#b91c1c",
    "ok": "#16a34a", "ok_btn": "#16a34a", "ok_btn_press": "#15803d", "warn": "#b45309",
    # simulation
    "sim_bg": "#ecfdf3", "sim_border": "#b7e4c7", "sim_btn": "#ffffff", "sim_btn_hover": "#f3faf6",
    "meter_bg": "#0f172a", "meter_fg": "#a7f3d0",
    "volt_pos": "#b91c1c", "volt_neg": "#1d4ed8", "volt_bg": "#ffffff",
    # oscilloscope and Bode plot
    "plot_bg": "#ffffff", "plot_grid": "#eef1f5", "plot_zero": "#d6dce4",
    "bode_grid": "#e6eaf0", "bode_minor": "#f3f5f8", "marker": "#ea580c",
}

DARK_C = {
    "bg": "#161a21", "panel": "#1e232c", "border": "#323a47", "text": "#e5e9ef", "muted": "#98a3b3",
    "field": "#14181e",
    "accent": "#5b9bff",
    "accent_dark": "#93b8ff",
    "accent_light": "#203558",
    "accent_btn": "#2563eb", "accent_btn_press": "#1d4ed8", "accent_btn_off": "#7f9bd0",
    "on_btn": "#ffffff",
    "button": "#272e39", "button_hover": "#313a47", "tool_hover": "#2a323e", "disabled": "#5f6977",
    "trough": "#20262f", "thumb": "#3a4452", "heading": "#252c36", "arrow": "#c9d1dc",
    "clam_frame": "#272e39", "clam_active": "#313a47", "clam_disabled": "#5f6977",
    "chk_hi": "#5f6977", "chk_lo": "#3a4452",
    "tip_bg": "#323b49", "tip_fg": "#f3f5f8",
    "canvas": "#12161c", "grid": "#1b2028", "grid_major": "#262d37",
    "stroke": "#d4dae2", "sym_fill": "#12161c", "pin_on": "#d4dae2", "pin_off": "#6f7b8b",
    "pin_free": "#12161c", "pinlabel": "#a9b4c2",
    "select": "#5b9bff", "sel_fill": "#172540", "sel_wire": "#28467a", "handle": "#e5e9ef",
    "hover": "#fbbf24", "highlight": "#5c4813", "net_pin": "#f59e0b",
    "danger": "#f87171", "danger_btn": "#dc2626", "danger_btn_press": "#b91c1c",
    "ok": "#4ade80", "ok_btn": "#16a34a", "ok_btn_press": "#15803d", "warn": "#fbbf24",
    "sim_bg": "#10241a", "sim_border": "#24553b", "sim_btn": "#1a3326", "sim_btn_hover": "#22412f",
    "meter_bg": "#05080c", "meter_fg": "#a7f3d0",
    "volt_pos": "#fca5a5", "volt_neg": "#93c5fd", "volt_bg": "#12161c",
    "plot_bg": "#12161c", "plot_grid": "#1f252e", "plot_zero": "#3c4655",
    "bode_grid": "#29313c", "bode_minor": "#1b2028", "marker": "#fb923c",
}

C = dict(LIGHT_C)
THEME = {"dark": False}

# Drawing colors chosen by the user (wires, scope traces …) are stored as they are and only
# shown brighter in dark mode, so files and exported images look the same in both themes.
DARK_INK = {
    "#2563eb": "#60a5fa", "#dc2626": "#f87171", "#1f2933": "#cbd5e1", "#16a34a": "#4ade80",
    "#ea580c": "#fb923c", "#d4a106": "#facc15", "#7c3aed": "#a78bfa", "#92400e": "#d08a52",
    "#0d9488": "#2dd4bf", "#6b7280": "#9ca3af", "#d97706": "#fbbf24", "#0891b2": "#22d3ee",
    "#db2777": "#f472b6", "#4b5563": "#d1d5db", "#111827": "#e5e7eb",
}


def set_palette(dark):
    """Make the light or dark palette the live one (C)."""
    THEME["dark"] = bool(dark)
    C.clear()
    C.update(DARK_C if dark else LIGHT_C)


def _rgb(col):
    col = col.strip()
    if len(col) == 4 and col.startswith("#"):
        col = "#" + "".join(ch * 2 for ch in col[1:])
    if len(col) != 7 or not col.startswith("#"):
        raise ValueError(col)
    return [int(col[i:i + 2], 16) for i in (1, 3, 5)]


def ink(col):
    """Display color for a stored drawing color (wire, trace) in the current theme."""
    if not THEME["dark"] or not col:
        return col
    k = col.lower()
    if k in DARK_INK:
        return DARK_INK[k]
    try:
        r, g, b = _rgb(k)
    except ValueError:
        return col
    if 0.2126 * r + 0.7152 * g + 0.0722 * b < 115:   # too dark to see on the dark canvas
        return _mix("#%02x%02x%02x" % (r, g, b), "#ffffff", 0.5)
    return col


def body_fill(col):
    """Display fill for a part's body color: dark mode keeps the hue but darkens it."""
    if not THEME["dark"] or not col:
        return col
    try:
        r, g, b = _rgb(col)
    except ValueError:
        return col
    h, lum, s = colorsys.rgb_to_hls(r / 255.0, g / 255.0, b / 255.0)
    r, g, b = colorsys.hls_to_rgb(h, min(lum, 0.23), min(s, 0.42))
    return "#%02x%02x%02x" % (int(round(r * 255)), int(round(g * 255)), int(round(b * 255)))

WIRE_COLORS = [
    ("Blue", "#2563eb"), ("Red", "#dc2626"), ("Black", "#1f2933"),
    ("Green", "#16a34a"), ("Orange", "#ea580c"), ("Yellow", "#d4a106"),
    ("Purple", "#7c3aed"), ("Brown", "#92400e"), ("Teal", "#0d9488"),
    ("Gray", "#6b7280"),
]
WIRE_COLOR_NAMES = {v: k for k, v in WIRE_COLORS}

BODY_COLORS = ["#e8eefc", "#dbeafe", "#d1fae5", "#fef3c7", "#fde2e4",
               "#ede9fe", "#e5e7eb", "#cfe8ef", "#ffffff"]

ICON_PNG_B64 = "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAYAAACqaXHeAAANr0lEQVR42uWbe5RV1X3HP799zj33OTPM8BoUTAgQfICkWiutCSPGqMtnrR11JSZRMY8uE1dIa6u17UjTxkezGptqY3yEmERppEuXK3GZJiCQaIsVFbDyGkCRlyIKA3fu65yzf/1j33uZgRkEwjBA91pn3Vl3zzn39/vu7+959oYDHiptbQv8tg71QYWjbxySfHIgire3Y+bOlbjnt6Nnarq51JXq6uqCpqbBUbmri6amJmR3U2X5T6W751R7u3pz52JB9NAB6FDDLLEAo768OZOj4SKx8QWq9kygFTQLdpDZYBSkhMg7ImYZIvNLnj779veH7HBIqMdei3dgAFRvHHXpkkzDqAlfQblZEslxIh4aV1CNQO3Rwn4wCcQkALBxYSsqDyVs1/dWPHrSB/sDoU8AHH0k/tiMd8/xvfQPjJ85zUbdaFyOVVEBAwJylPgCR3JVEYtaMV7gmUQjNsxvjLXy9XWPDH+mPxD2VaBtgc+i6dGEG7deL372YRHjx2F3JIhBxHAsDFVVNDZ+yhcTEIf529c+OvzutrYF/qJF06P+AaiiNOH6LV/0MsN/FJe7FKwF8TgWh6pFRL30MC/ufvdvOme3/mNbh/qLZkm0LwDtT3rMvToef9M7U43JvKA2BBvLMbPq+0EBJDZBo28rO6/qfHTkUz3NQWqhjg5k9IqNyXRjepnxMxNs1B0fsyvfBxPES6Ia74y0cuqbj4zc5jQXNQBtbXjMEptqSH3ZS7VMiMN8dNwoDyBibFyyXrKpxUduR0Tb2zFVBjhPPnUmqfe73lstfnK0RmU99qnfhymIB6oFz7MTVj00YiuoMW0dCz0Q/aBr+4Um2TTGxmV7/CnvaKA2jr3kkKy15hqAtg6MgXNd8iBcLGIURTlOhwiiGqmqXgSwaMVcrZqA6PgZ2142idzva5iPjyv738sMxEuKjcubyQwft/ZfpWxA9CNf1BRwAjYEMBy3Q8BGiMowjT4YUVc2bunKiJI9enL7gc2NEJP0CjZbB8CUUOTw2r4RMObg56Q6N7BFhiKe03dA6G4ECmWlu6gY2XeuWFHyRUX6mIti2F1QrLLP/IDIOgCelu6yMnmsz1kfT1CsaC8Fu8vKhBN8zjk1QSVSVHsDMyQrTJsckExAJRp4EPzD+TDPQFdBubYtxXdmNGAM3Psf3dz3dIHmBkNXt+Xc0wMeuqWRTFL4yfwit/8oT0NGKFegtcXj3/+qibGtHq+ti7ju3p1UIgeODjYDjIDvuas/+40t5FLCn/9JFmOc0LdckWHMcEM5dOYw88oMmaQQx/D5T6c5faxPueJM5obPpBjb6lGqKL83zueKP0yxq6D9/t7BynfIAHjGCbh9l7vyfdl29X8mf9TnhBaDrRbSqYQw9eSAHbst40Z5nHaSj6oDRxWmTQrIlywNaWHapABV93tWYfqUAM8cHvkO2QREoKtb+cQ4n0+dFuB58NKqkMWrQ3IpwTNOEd9zDPjUpAAR97dUmzUXnhnw8C8LnH1yglQgbk7cdcEZAf/8dDcnj/GZONoHAd8TROCsCQlGtRh25JXA73tlVfuXL5uU3w0AI7C7qNx8WYbbr8n2QvXhXxa547G8CynVoBXFynlTgjq1RBwIf3RKQGuzx7RJQa9VA5jysQQnDvU4e6KPZ1wU8D3HgCE54ayJCX6+uIxnhA/yuldao1Qi+Iursn3K9/dP5Mkkpe5oDwqAmkO74IyAO67NYhXmLCzRXVaum57iSxelaWkQ3nrXkko4wXNp4ZQxPtY6BfwqO4bkhEvPTjLpI34dWMWZiGfg/E8ETD0lUWecVs3HeDD99ICfzi8x6aM+l/5B0rU3quwJIxjaKHzh02m0h3yfq8q3fmvM7F8Xac451h00A6yF9k+mUIX7ni7wrTl5rIXOzTF33ZDjqnNSB+xcbr0qQ2uzV1eyBgTAVy/JMKxJejGjRve2yQETR3sMazR8/fJMvz2f7z1T4M7HnXyrN0bcM6OBq6eleGJh8dAYoAoJD4Y2OEleWl0hFQiphPA/qysILk73DFCqQsKD55aUiSxcdGZAMuFSzDHD99RXUQyVSMlUbXTcKK9Xg7e7pORS7r7WZsNvv9PChm0xYcQ+xapVSPrC4tXhHvnWhAjQnBNSgWD1EKKACJQj+N+3I0TcKo0YYggS8LXLs4hA4EPgS/1KJtzKLVhe4Y87djBvaaVOdVXqgqzeFDFnYakeOmtRgaryDz5bqDcsFcgknWkl9vq9wHcKi8CfXZLeI99lGURg1caYXQXdbyTplwFWIZuE2b8qcsXUJNNPD3j+7mbCyK1KsazcNjvP9l0W36MXzTa+FzOixeO5l8tcclYSqQIaW0f7JZ0hTywsMePCNKZqz9aCGFi7JebH84p86aIMTVnnLGrm29Wt3PrILsqhA9paSCaEu27IMW3SvvI98IsCCW//SdR+TSAZCBu2xXz+n7p46BtNnDTMQbllh+WbP9jNr18tk07uoVhtxdKBkEsJL68JyReVXNp54tpCvLQqZOXGiM3vx5w41HM5Q3X+pVUVOrfGvLI25LwpQf3ZnoEX3qjw5G/LNGWlDmapomzYFvP9WxoZ3+pMaftu5RsP7mJJZ8iQbP8O8ICcYC4trNoU8ZtOy8SiU6Fzs+XFFRVGNruER/pgjxHY+J7lv1eGnH9GQGxdeNtVUF5dF1GuKPNeq/CF89P1aKAK85dWSBhh3muVekitjYXLK+RSQlPGKaVAU1Z4/a2Q55bHfDL2qETKe7uUJZ0hufT+7f+AMsFaNpfwoRi6yxjIJoUodvPxXlfNHGIL85c5hxnFSmxhyZqQzdtjMklh/lI3Z9Xds2FbzLI3I1oahf9aWaEUap1Z+aLy4grniMPYPdta51DTgRD4UIygEDrwM0nB2sOUCtcENLIndH0YsladEC+8UcEqpAKXNS58vUIlhmxKeHVtyAe7bT3LW/h6hZ15JZsyrN8as2ZTjGfc3OJVIRu2WZIJ9glrhyLfgJXDvXxIAja8G3Pb7N2s3hTx1IslnnqxREPaee6d3cqtj+5m5caIeUsrPPDzAtmUYKt2defjeZatj1i8KuTbP+smmZADVmxQyuE+WZASHn++xFMvlCmFSjIh9bohmxL+85UKC5eHhJHie87UIutovWRNyJXf2ukAwTllPZYAqDGhISN1h6q6h8Kq7jtrIZGUeoUo1c9Mstank7qvOKobIvtzpD0/+5zTvhnUM0M8Jlpix9r4fw/AAZuA9Kjijso9cj1klMMNgBGIFcLqDpuomobao+QtohEnU2hdhVqT7/C0xIB8ScklYUx1O2Ch2/XgasmNDuKq1yrIpjSc2AhxDFt3uu9+ZwCMwK6i8rXLMlw82cevlu3jhvn87Wdz/N2P8wfUtBwwAKrF0Mwrs1wzNUHCd7CMHy7c+qdZZj2ex/fk0ADo2RL762tcS+xnvylRKCufPde1nJoaDG9sUdKJI28OtZbYic3CjE8ngT3yXduW4qYL06zbMkAtsVUbI+66oYHLpyY5aQt4cuTNQMT5pNNGuqTpX54pMKvaElvxdsQ9Nw5gS+yl1a7lFEVQKOmgOAEBIoVKBQiExat6tuwGoCX2lYszjGgyJHy4udpyKlfL0lrFdkSvqj8qx07Wr/aU79IBaImdNyVgwb2u5TRyiKFUUW55YBdrt8akAjniWwtqJtCSE2bPbOTc0/eV7/4DbYnZCoL2zh96tsQ+d08Xd16XY+rJCYyBpesivv1knkXLQ3IplyMc6eRIcb5n/Rb6le/VtWG9e7S3AWnsdscJwMjrtmYbA3+d+ImRGld6vZk3Boplh+HYVg/PCG+9G1MOlYa0DHoyVNuL0J98eymviIhaDb3Y//jqx5rf2rNJ6sZtS00iO0XD7n22ydXe5JQrriufTEi9K3u0ZIIHJp+qeIFoVHm32DR87KbvStG0deC5h8gyYwLt0YXep+WUDIR0IP2WtoM1DkI+KyYJsHLTd6VIh+5532qVX7mjAP2fAej5cuNoHB8mnyoqJgHCPIAzt77imUWziAGs7/0iLu/cbrzA0AcLjoOhIuLF5a4Qa+cAvDLqzNiAaFvbAn/9Qy1dqvKACRpF1R53AKja2Es2i2o8p3N26/r2dvWYJdYALFp0boyqRNa/Ly7teMf4Kc9tqDt+1BcvEBvmi6J2FqjMPbXXNjlRrsZseKx5J2pvEpMUxMQc9h7soPmGyAuaPBuXvtk5u3U97dRPw+0Jd3Mlbmtb4Hf+cMSzcaXrNi89NAESH9NMUFVVDRPZ4YmouP2BtT9sfbCtQ/2eh6f6PzQ1Y/sdJsj9g0YlbFyORMQ7MlsXD5vqsRjP95JDsOWd9695pOUW2jHsdZiyb4WqZ2rGz9jWbkzyfpPIjogrXaiNIxEEFXFH5o4WPKoVqWBVURHje8kmbFjohvgv1zzc8m/uECi690nSfjWonR2ceON7J1gveaug15tEdojaCI3LPQ5O1l6KD1ZTTHEn+jzESyImgQ3zJTBzwlLp7jd/MmKNW9C+j9Hufwl7nK4af9P20Ua8dlU+g9rJoMMQXLdk0JjgyhZVKoK8j/FWAs9HKnPffKRpzd467K+vuN8IwtWYng8ZPfPtdGp3ZqhPLgO7UDs4vkGMKjRijC35hfT7vQ5Qt6vHqWjN2x86ALXR0WHauNMsAvthDx200aGmDQ5Kxv8D6xPoI1cr/5AAAAAASUVORK5CYII="  # window/taskbar icon (64 px PNG)

DIRS = {"L": (-1, 0), "R": (1, 0), "U": (0, -1), "D": (0, 1)}
SIDE_OF_DIR = {"L": "left", "R": "right", "U": "top", "D": "bottom"}


# --------------------------------------------------------------------------
# Drawing primitives for component symbols (local grid units)
# --------------------------------------------------------------------------
def L(*pts, w=1.0):
    return {"t": "line", "pts": list(pts), "w": w}


def PG(*pts, fill=None):
    return {"t": "poly", "pts": list(pts), "fill": fill}


def CI(cx, cy, r, fill=None):
    return {"t": "circle", "c": (cx, cy), "r": r, "fill": fill}


def TX(x, y, s, size=11, bold=False):
    return {"t": "text", "p": (x, y), "s": s, "size": size, "bold": bold}


def P(name, x, y, d):
    return {"name": name, "x": x, "y": y, "dir": d}


def _arc(cx, cy, r, a0, a1, n=14):
    out = []
    for i in range(n + 1):
        a = math.radians(a0 + (a1 - a0) * i / n)
        out.append((cx + r * math.cos(a), cy + r * math.sin(a)))
    return out


def _bez(p0, p1, p2, n=14):
    out = []
    for i in range(n + 1):
        t = i / n
        u = 1 - t
        out.append((u * u * p0[0] + 2 * u * t * p1[0] + t * t * p2[0],
                    u * u * p0[1] + 2 * u * t * p1[1] + t * t * p2[1]))
    return out


def _head(tip, frm, size=0.28):
    dx, dy = tip[0] - frm[0], tip[1] - frm[1]
    ln = math.hypot(dx, dy) or 1.0
    dx, dy = dx / ln, dy / ln
    bx, by = tip[0] - dx * size, tip[1] - dy * size
    px, py = -dy * size * 0.55, dx * size * 0.55
    return PG(tip, (bx + px, by + py), (bx - px, by - py), fill="stroke")


def _arrow(x0, y0, x1, y1, size=0.22):
    return [L((x0, y0), (x1, y1)), _head((x1, y1), (x0, y0), size)]


def _zigzag(x0=1.0, x1=3.0, y=1.0, amp=0.35, n=6):
    pts = [(x0, y)]
    step = (x1 - x0) / (2 * n)
    for i in range(n):
        pts.append((x0 + step * (2 * i + 1), y - amp if i % 2 == 0 else y + amp))
    pts.append((x1, y))
    return pts


def _leads(a, b, y=1.0, total=4.0):
    return [L((0, y), (a, y)), L((b, y), (total, y))]


def sym_resistor():
    return [L((0, 1), (1, 1)), L(*_zigzag()), L((3, 1), (4, 1))]


def sym_capacitor():
    return _leads(1.8, 2.2) + [L((1.8, 0.35), (1.8, 1.65), w=1.5),
                               L((2.2, 0.35), (2.2, 1.65), w=1.5)]


def sym_capacitor_pol():
    arc = _arc(2.95, 1, 0.75, 135, 225)
    return [L((0, 1), (1.8, 1)), L((1.8, 0.35), (1.8, 1.65), w=1.5),
            L(*arc, w=1.5), L((2.2, 1), (4, 1)), TX(1.42, 0.42, "+", 10, True)]


def sym_inductor():
    pts = []
    for k in range(4):
        cx = 1.25 + 0.5 * k
        seg = _arc(cx, 1, 0.25, 180, 360, 10)
        pts.extend(seg if not pts else seg[1:])
    return [L((0, 1), (1, 1)), L(*pts), L((3, 1), (4, 1))]


def sym_potentiometer():
    return sym_resistor() + [L((2, 0), (2, 0.4)), _head((2, 0.62), (2, 0.0), 0.26)]


def sym_ldr():
    return (sym_resistor()
            + _arrow(1.0, -0.45, 1.5, 0.15)
            + _arrow(1.55, -0.45, 2.05, 0.15))


def sym_fuse():
    return [L((0, 1), (4, 1)), PG((1.2, 0.7), (2.8, 0.7), (2.8, 1.3), (1.2, 1.3))]


def sym_switch():
    return [L((0, 1), (1.2, 1)), CI(1.3, 1, 0.1, "white"),
            L((1.38, 0.94), (2.75, 0.38)), CI(2.7, 1, 0.1, "white"),
            L((2.8, 1), (4, 1))]


def sym_switch_closed():
    return [L((0, 1), (1.2, 1)), CI(1.3, 1, 0.1, "white"),
            L((1.4, 0.97), (2.62, 0.9)), CI(2.7, 1, 0.1, "white"),
            L((2.8, 1), (4, 1))]


def sym_pushbutton():
    return [L((0, 1), (1.2, 1)), CI(1.3, 1, 0.1, "white"), CI(2.7, 1, 0.1, "white"),
            L((2.8, 1), (4, 1)), L((1.15, 0.6), (2.85, 0.6)), L((2, 0.6), (2, 0.15)),
            L((1.7, 0.15), (2.3, 0.15))]


def sym_pushbutton_pressed():
    return [L((0, 1), (1.2, 1)), CI(1.3, 1, 0.1, "white"), CI(2.7, 1, 0.1, "white"),
            L((2.8, 1), (4, 1)), L((1.15, 0.86), (2.85, 0.86)), L((2, 0.86), (2, 0.41)),
            L((1.7, 0.41), (2.3, 0.41))]


def sym_lamp():
    return _leads(1.25, 2.75) + [CI(2, 1, 0.75, "white"),
                                 L((1.47, 0.47), (2.53, 1.53)), L((1.47, 1.53), (2.53, 0.47))]


def _circle_letter(letter, plus=False):
    prims = _leads(1.25, 2.75) + [CI(2, 1, 0.75, "white"), TX(2, 1, letter, 13, True)]
    if plus:
        prims.append(TX(0.75, 0.55, "+", 10, True))
    return prims


def sym_motor():
    return _circle_letter("M")


def sym_voltmeter():
    return _circle_letter("V", True)


def sym_ammeter():
    return _circle_letter("A", True)


def sym_buzzer():
    return _leads(1.3, 2.7) + [PG((1.3, 0.45), (2.7, 0.45), (2.7, 1.55), (1.3, 1.55), fill="white"),
                               TX(2, 1, "BZ", 9, True), TX(0.8, 0.55, "+", 10, True)]


def sym_battery():
    return [L((0, 1), (1.8, 1)), L((1.8, 0.3), (1.8, 1.7), w=1.4),
            L((2.2, 0.65), (2.2, 1.35), w=2.4), L((2.2, 1), (4, 1)),
            TX(1.4, 0.42, "+", 10, True)]


def sym_dc_source():
    return [L((1, 0), (1, 1.1)), CI(1, 2, 0.9, "white"), L((1, 2.9), (1, 4)),
            TX(1, 1.55, "+", 12, True), TX(1, 2.42, "−", 12, True)]


def sym_ac_source():
    wave = [(0.5 + i / 20.0, 2 - 0.32 * math.sin(2 * math.pi * i / 20.0)) for i in range(21)]
    return [L((1, 0), (1, 1.1)), CI(1, 2, 0.9, "white"), L((1, 2.9), (1, 4)), L(*wave)]


def sym_square_source():
    wave = [(0.5, 2.3), (0.75, 2.3), (0.75, 1.7), (1.25, 1.7), (1.25, 2.3), (1.5, 2.3)]
    return [L((1, 0), (1, 1.1)), CI(1, 2, 0.9, "white"), L((1, 2.9), (1, 4)), L(*wave),
            TX(1.5, 0.55, "+", 10, True)]


def sym_current_source():
    return [L((1, 0), (1, 1.1)), CI(1, 2, 0.9, "white"), L((1, 2.9), (1, 4)),
            L((1, 2.55), (1, 1.65)), _head((1, 1.4), (1, 2.0), 0.36)]


def sym_ground():
    return [L((1, 0), (1, 1)), L((0.25, 1), (1.75, 1), w=1.3),
            L((0.55, 1.32), (1.45, 1.32), w=1.3), L((0.85, 1.64), (1.15, 1.64), w=1.3)]


def sym_vcc():
    return [L((1, 2), (1, 1)), L((0.35, 1), (1.65, 1), w=1.6)]


def sym_probe():
    return [L((1, 2), (1, 1.25)), CI(1, 0.8, 0.45, "white"), TX(1, 0.8, "V", 9, True)]


def sym_port():
    """Component Pin: a tag marking where a wire leaves a circuit that becomes a component."""
    return [L((0, 1), (0.7, 1)),
            PG((0.7, 0.55), (3.25, 0.55), (3.7, 1), (3.25, 1.45), (0.7, 1.45), fill="white")]


def sym_diode():
    return [L((0, 1), (1.5, 1)), PG((1.5, 0.5), (1.5, 1.5), (2.4, 1), fill="stroke"),
            L((2.4, 0.5), (2.4, 1.5), w=1.3), L((2.4, 1), (4, 1))]


def sym_zener():
    return [L((0, 1), (1.5, 1)), PG((1.5, 0.5), (1.5, 1.5), (2.4, 1), fill="stroke"),
            L((2.15, 0.36), (2.4, 0.5), (2.4, 1.5), (2.65, 1.64), w=1.3), L((2.4, 1), (4, 1))]


def sym_led():
    return (sym_diode()
            + _arrow(2.05, 0.35, 2.55, -0.15)
            + _arrow(2.5, 0.55, 3.0, 0.05))


def _bjt(pnp=False):
    prims = [CI(2.2, 2, 1.35), L((0, 2), (1.5, 2)), L((1.5, 1.2), (1.5, 2.8), w=1.6),
             L((1.5, 1.65), (3, 0.9)), L((3, 0.9), (3, 0)),
             L((1.5, 2.35), (3, 3.1)), L((3, 3.1), (3, 4))]
    if pnp:
        # emitter on top, arrow points in toward the base
        a, b = (3, 0.9), (1.5, 1.65)
        t = 0.8
        tip = (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t)
        prims.append(_head(tip, a, 0.32))
    else:
        a, b = (1.5, 2.35), (3, 3.1)
        t = 0.85
        tip = (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t)
        prims.append(_head(tip, a, 0.32))
    return prims


def sym_npn():
    return _bjt(False)


def sym_pnp():
    return _bjt(True)


def sym_nmos():
    return [L((0, 2), (1.3, 2)), L((1.3, 1.2), (1.3, 2.8), w=1.4),
            L((1.6, 1.05), (1.6, 1.55), w=1.4), L((1.6, 1.75), (1.6, 2.25), w=1.4),
            L((1.6, 2.45), (1.6, 2.95), w=1.4),
            L((1.6, 1.3), (3, 1.3)), L((3, 1.3), (3, 0)),
            L((1.6, 2.7), (3, 2.7)), L((3, 2.7), (3, 4)),
            L((1.85, 2), (3, 2)), L((3, 2), (3, 2.7)), _head((1.62, 2), (2.4, 2), 0.3)]


def sym_opamp():
    return [PG((1, 0.8), (1, 5.2), (5, 3), fill="white"),
            L((0, 2), (1, 2)), L((0, 4), (1, 4)), L((5, 3), (6, 3)),
            L((3, 0), (3, 1.9)), L((3, 4.1), (3, 6)),
            TX(1.45, 2, "−", 13, True), TX(1.45, 4, "+", 13, True)]


def _gate_inputs(x_end=1.0):
    return [L((0, 1), (x_end, 1)), L((0, 3), (x_end, 3))]


def _and_body(cx):
    pts = [(1, 0.5), (cx, 0.5)] + _arc(cx, 2, 1.5, -90, 90, 18)[1:-1] + [(cx, 3.5), (1, 3.5)]
    return PG(*pts, fill="white")


def _or_body(tip_x):
    back = _bez((1, 0.5), (1.6, 2), (1, 3.5))
    top = _bez((1, 0.5), (2.6, 0.5), (tip_x, 2))
    bot = _bez((tip_x, 2), (2.6, 3.5), (1, 3.5))
    pts = top + bot[1:] + list(reversed(back))[1:-1]
    return PG(*pts, fill="white")


def sym_and():
    return [_and_body(2.5)] + _gate_inputs() + [L((4, 2), (5, 2))]


def sym_nand():
    return [_and_body(2.2), CI(3.85, 2, 0.15, "white")] + _gate_inputs() + [L((4, 2), (5, 2))]


def sym_or():
    return [_or_body(4.0)] + _gate_inputs(1.17) + [L((4, 2), (5, 2))]


def sym_nor():
    return [_or_body(3.7), CI(3.85, 2, 0.15, "white")] + _gate_inputs(1.17) + [L((4, 2), (5, 2))]


def sym_xor():
    return ([_or_body(4.0), L(*_bez((0.7, 0.5), (1.3, 2), (0.7, 3.5)))]
            + _gate_inputs(0.87) + [L((4, 2), (5, 2))])


def sym_not():
    return [PG((1, 0.2), (1, 1.8), (3.6, 1), fill="white"), CI(3.75, 1, 0.15, "white"),
            L((0, 1), (1, 1)), L((3.9, 1), (5, 1))]


QBAR = "Q'"   # name of the inverted output pin ("Q-bar"; the symbol draws it as Q with a bar over it)


def _ff_box(h):
    """Rectangle body of a flip-flop / latch, h grid squares tall, between x = 1 and x = 5."""
    return PG((1, 1), (5, 1), (5, h), (1, h), fill="white")


def _ff_outputs(yq, yqb):
    return [L((5, yq), (6, yq)), L((5, yqb), (6, yqb)),
            TX(4.45, yq, "Q", 10), TX(4.45, yqb, "Q", 10), L((4.27, yqb - 0.36), (4.63, yqb - 0.36), w=0.8)]


def _ff_clock(y):
    """Clock input: lead plus the triangle that marks an edge-triggered input."""
    return [L((0, y), (1, y)), PG((1, y - 0.38), (1.5, y), (1, y + 0.38))]


def _ff_set_clr(bottom):
    return [L((3, 0), (3, 1)), L((3, bottom), (3, bottom + 1)),
            TX(3, 1.42, "SET", 7), TX(3, bottom - 0.42, "CLR", 7)]


def sym_dff(letter="D"):
    return ([_ff_box(6), L((0, 2), (1, 2)), TX(1.5, 2, letter, 10)] + _ff_clock(5)
            + _ff_outputs(2, 5) + _ff_set_clr(6))


def sym_tff():
    return sym_dff("T")


def sym_jkff():
    return ([_ff_box(7), L((0, 2), (1, 2)), TX(1.45, 2, "J", 10), L((0, 6), (1, 6)), TX(1.5, 6, "K", 10)]
            + _ff_clock(4) + _ff_outputs(2, 6) + _ff_set_clr(7))


def sym_srlatch():
    return [_ff_box(6), L((0, 2), (1, 2)), TX(1.5, 2, "S", 10), L((0, 5), (1, 5)), TX(1.5, 5, "R", 10)] + _ff_outputs(2, 5)


SYMBOLS = {
    "dff": sym_dff, "tff": sym_tff, "jkff": sym_jkff, "srlatch": sym_srlatch,
    "resistor": sym_resistor, "capacitor": sym_capacitor, "capacitor_pol": sym_capacitor_pol,
    "inductor": sym_inductor, "potentiometer": sym_potentiometer, "ldr": sym_ldr,
    "fuse": sym_fuse, "switch": sym_switch, "pushbutton": sym_pushbutton, "lamp": sym_lamp,
    "motor": sym_motor, "buzzer": sym_buzzer, "voltmeter": sym_voltmeter, "ammeter": sym_ammeter,
    "battery": sym_battery, "dc_source": sym_dc_source, "ac_source": sym_ac_source,
    "square_source": sym_square_source, "probe": sym_probe,
    "current_source": sym_current_source, "ground": sym_ground, "vcc": sym_vcc, "port": sym_port,
    "diode": sym_diode, "zener": sym_zener, "led": sym_led, "npn": sym_npn, "pnp": sym_pnp,
    "nmos": sym_nmos, "opamp": sym_opamp, "and": sym_and, "nand": sym_nand, "or": sym_or,
    "nor": sym_nor, "xor": sym_xor, "not": sym_not,
}

# Drawing used while a switch is closed / a push button is held down
ALT_SYMBOLS = {"switch": sym_switch_closed, "pushbutton": sym_pushbutton_pressed}

# --------------------------------------------------------------------------
# Built-in component library
# --------------------------------------------------------------------------
CATEGORY_ORDER = ["Passive", "Sources & Meters", "Switches & Outputs", "Semiconductors",
                  "Logic Gates", "Flip-Flops & Latches", "Logic ICs (74HC)", "ICs & Boards", "Modules & Sensors",
                  "Building Blocks"]

# Id of the built-in "Component Pin" part.  When a selection becomes a component, each
# Component Pin in it becomes one pin of the new part, named after the Component Pin's label.
PORT_DEF = "port"
MAX_NESTING = 8   # components built from circuits may contain others, this many levels deep


def two_term(a="1", b="2"):
    return [P(a, 0, 1, "L"), P(b, 4, 1, "R")]


def SY(id_, name, cat, prefix, value, desc, symbol=None, pins=None, pivot=(2, 1), **kw):
    d = {"id": id_, "name": name, "category": cat, "prefix": prefix, "value": value,
         "description": desc, "symbol": symbol or id_, "pins": pins or two_term(),
         "pivot": list(pivot)}
    d.update(kw)
    return d


def BX(id_, name, cat, prefix, value, desc, w, h, pins, color="#e5e7eb", **kw):
    d = {"id": id_, "name": name, "category": cat, "prefix": prefix, "value": value,
         "description": desc, "symbol": "box", "w": w, "h": h, "color": color,
         "pins": [{"name": n, "side": s, "pos": p} for (n, s, p) in pins]}
    d.update(kw)
    return d


GATE2 = [P("A", 0, 1, "L"), P("B", 0, 3, "L"), P("Y", 5, 2, "R")]


def DIP14(id_, name, desc, pins, logic):
    """A 14-pin 74HC logic chip drawn in its real pin order (pin 1 top-left, pin 14 top-right)."""
    side = [(n, "left", i + 1) for i, n in enumerate(pins[:7])] + \
           [(n, "right", 7 - i) for i, n in enumerate(pins[7:])]
    return BX(id_, name, "Logic ICs (74HC)", "U", "",
              desc + " Pins are in the chip’s real order: pin 1 top-left, 7 = GND bottom-left, "
                     "14 = VCC top-right. Wire VCC to +5 V and GND to ground, or it won’t work.",
              6, 8, side, color="#e5e7eb", logic=logic)


def _quad(fmt):
    return "".join(fmt.format(n=n) + "\n" for n in "1234")


_PIN_QUAD = ["1A", "1B", "1Y", "2A", "2B", "2Y", "GND", "3Y", "3A", "3B", "4Y", "4A", "4B", "VCC"]
VERT2 = [P("+", 1, 0, "U"), P("−", 1, 4, "D")]

BUILTIN_DEFS = [
    # Passive
    SY("resistor", "Resistor", "Passive", "R", "1 kΩ",
       "Limits current (V = I·R). Two pins, no polarity."),
    SY("capacitor", "Capacitor", "Passive", "C", "100 nF",
       "Stores charge. Ceramic / film type, no polarity."),
    SY("capacitor_pol", "Electrolytic Capacitor", "Passive", "C", "10 µF",
       "Polarized capacitor: the + pin must be at the higher voltage.",
       pins=two_term("+", "−")),
    SY("inductor", "Inductor", "Passive", "L", "1 mH", "Coil that stores energy in a magnetic field."),
    SY("potentiometer", "Potentiometer", "Passive", "RV", "10 kΩ",
       "Adjustable resistor. Pin W is the wiper (middle). Set the wiper position in its properties.",
       pins=[P("1", 0, 1, "L"), P("W", 2, 0, "U"), P("2", 4, 1, "R")]),
    SY("ldr", "Photoresistor (LDR)", "Passive", "R", "",
       "Light-dependent resistor: resistance drops in bright light (about 1 MΩ in the dark, "
       "1 kΩ in bright light). Set the light level in its properties."),
    SY("fuse", "Fuse", "Passive", "F", "1 A", "Opens the circuit if the current is too high."),
    # Sources & meters
    SY("battery", "Battery", "Sources & Meters", "B", "9 V",
       "DC battery. Long plate is +. Has a small internal resistance.", pins=two_term("+", "−")),
    SY("dc_source", "DC Voltage Source", "Sources & Meters", "V", "5 V",
       "Ideal DC voltage source.", pins=VERT2, pivot=(1, 2)),
    SY("ac_source", "AC Voltage Source", "Sources & Meters", "V", "10 V 60 Hz",
       "Sinusoidal AC voltage source. Value: peak voltage and frequency (write “rms” for an RMS "
       "voltage, e.g. 120 V rms 60 Hz). Pin 1 is positive in the first half-cycle.",
       pins=[P("1", 1, 0, "U"), P("2", 1, 4, "D")], pivot=(1, 2)),
    SY("square_source", "Square Wave Source", "Sources & Meters", "V", "5 V 1 Hz",
       "Switches between 0 V and the set voltage at the set frequency (50 % duty). "
       "Handy as a clock or to blink something.", pins=VERT2, pivot=(1, 2)),
    SY("current_source", "Current Source", "Sources & Meters", "I", "1 mA",
       "Ideal current source. Current flows out of the + pin (arrow).", pins=VERT2, pivot=(1, 2)),
    SY("vcc", "Power Rail (VCC)", "Sources & Meters", "PWR", "+5 V",
       "Supply-voltage label. All power rails with the same value are connected together.",
       pins=[P("V", 1, 2, "D")], pivot=(1, 1), label_mode="value"),
    SY("ground", "Ground", "Sources & Meters", "GND", "",
       "0 V reference. All ground symbols are connected together.",
       pins=[P("GND", 1, 0, "U")], pivot=(1, 1), label_mode="none"),
    SY("voltmeter", "Voltmeter", "Sources & Meters", "VM", "",
       "Measures voltage. Connect in parallel (across) a part.", pins=two_term("+", "−")),
    SY("ammeter", "Ammeter", "Sources & Meters", "AM", "",
       "Measures current. Connect in series with a part.", pins=two_term("+", "−")),
    SY("probe", "Voltage Probe", "Sources & Meters", "TP", "",
       "Shows the voltage at this point while simulating, and adds it to the oscilloscope.",
       pins=[P("V", 1, 2, "D")], pivot=(1, 1), label_mode="label"),
    # Switches & outputs
    SY("switch", "Switch (SPST)", "Switches & Outputs", "SW", "",
       "Simple on/off switch. Click it to flip it while simulating."),
    SY("pushbutton", "Push Button", "Switches & Outputs", "SW", "",
       "Momentary switch: connected only while pressed. Hold the mouse on it while simulating."),
    SY("lamp", "Lamp", "Switches & Outputs", "LP", "6 V 1 W",
       "Incandescent light bulb. Value: rated voltage and power."),
    SY("motor", "DC Motor", "Switches & Outputs", "M", "6 V 0.2 A",
       "DC motor. Value: rated voltage and current."),
    SY("buzzer", "Buzzer", "Switches & Outputs", "BZ", "5 V", "Piezo buzzer (polarized).",
       pins=two_term("+", "−")),
    # Semiconductors
    SY("diode", "Diode", "Semiconductors", "D", "1N4148",
       "Lets current flow from A (anode) to K (cathode) only.", pins=two_term("A", "K")),
    SY("zener", "Zener Diode", "Semiconductors", "D", "5.1 V",
       "Also conducts backwards once the reverse voltage reaches its Zener voltage (the value). "
       "Used to hold a voltage steady.", pins=two_term("A", "K")),
    SY("led", "LED", "Semiconductors", "D", "Red",
       "Light-emitting diode. Long leg = A (anode, +). Needs a series resistor. "
       "Value: color (Red, Green, Blue, Yellow, White …).",
       pins=two_term("A", "K")),
    SY("npn", "NPN Transistor", "Semiconductors", "Q", "2N2222",
       "Bipolar transistor. B = base, C = collector, E = emitter.",
       pins=[P("B", 0, 2, "L"), P("C", 3, 0, "U"), P("E", 3, 4, "D")], pivot=(2, 2)),
    SY("pnp", "PNP Transistor", "Semiconductors", "Q", "2N2907",
       "Bipolar transistor. B = base, E = emitter (top), C = collector.",
       pins=[P("B", 0, 2, "L"), P("E", 3, 0, "U"), P("C", 3, 4, "D")], pivot=(2, 2)),
    SY("nmos", "N-MOSFET", "Semiconductors", "Q", "2N7000",
       "N-channel MOSFET. G = gate, D = drain, S = source.",
       pins=[P("G", 0, 2, "L"), P("D", 3, 0, "U"), P("S", 3, 4, "D")], pivot=(2, 2)),
    SY("opamp", "Op-Amp", "Semiconductors", "U", "LM741",
       "Operational amplifier with supply pins V+ and V−.",
       pins=[P("IN−", 0, 2, "L"), P("IN+", 0, 4, "L"), P("OUT", 6, 3, "R"),
             P("V+", 3, 0, "U"), P("V−", 3, 6, "D")], pivot=(3, 3), label_pt=[4.3, 1.2]),
    # Logic gates
    SY("and", "AND Gate", "Logic Gates", "U", "", "Output is 1 only if A AND B are 1.",
       pins=GATE2, pivot=(2, 2)),
    SY("nand", "NAND Gate", "Logic Gates", "U", "", "NOT-AND: output is 0 only if both inputs are 1.",
       pins=GATE2, pivot=(2, 2)),
    SY("or", "OR Gate", "Logic Gates", "U", "", "Output is 1 if A OR B is 1.",
       pins=GATE2, pivot=(2, 2)),
    SY("nor", "NOR Gate", "Logic Gates", "U", "", "NOT-OR: output is 1 only if both inputs are 0.",
       pins=GATE2, pivot=(2, 2)),
    SY("xor", "XOR Gate", "Logic Gates", "U", "", "Output is 1 if the inputs are different.",
       pins=GATE2, pivot=(2, 2)),
    SY("not", "NOT Gate (Inverter)", "Logic Gates", "U", "", "Output is the opposite of the input.",
       pins=[P("A", 0, 1, "L"), P("Y", 5, 1, "R")], pivot=(2, 1)),
    # Flip-flops & latches (5 V logic; SET and CLR are optional and active-HIGH)
    SY("dff", "D Flip-Flop", "Flip-Flops & Latches", "FF", "",
       "Stores one bit. On each rising edge of CLK (LOW → HIGH), Q copies D and holds it until the next "
       "edge. Q' (Q-bar) is always the opposite of Q. SET forces Q = 1 and CLR forces Q = 0 at any time; "
       "leave them unconnected if you don't need them.",
       pins=[P("D", 0, 2, "L"), P("CLK", 0, 5, "L"), P("Q", 6, 2, "R"), P(QBAR, 6, 5, "R"),
             P("SET", 3, 0, "U"), P("CLR", 3, 7, "D")], pivot=(3, 3), label_pt=[6.3, 3.5],
       optional_pins=["SET", "CLR", QBAR]),
    SY("tff", "T Flip-Flop", "Flip-Flops & Latches", "FF", "",
       "Toggle flip-flop. On each rising edge of CLK, Q flips (0 → 1 or 1 → 0) if T is HIGH, and stays the "
       "same if T is LOW. Tie T HIGH to divide a clock by 2; chain them to build a counter. SET / CLR "
       "force Q to 1 / 0.",
       pins=[P("T", 0, 2, "L"), P("CLK", 0, 5, "L"), P("Q", 6, 2, "R"), P(QBAR, 6, 5, "R"),
             P("SET", 3, 0, "U"), P("CLR", 3, 7, "D")], pivot=(3, 3), label_pt=[6.3, 3.5],
       optional_pins=["SET", "CLR", QBAR]),
    SY("jkff", "JK Flip-Flop", "Flip-Flops & Latches", "FF", "",
       "On each rising edge of CLK: J = K = 0 holds Q, J = 1 sets Q = 1, K = 1 resets Q = 0, and "
       "J = K = 1 toggles Q. SET / CLR force Q to 1 / 0 at any time.",
       pins=[P("J", 0, 2, "L"), P("CLK", 0, 4, "L"), P("K", 0, 6, "L"), P("Q", 6, 2, "R"), P(QBAR, 6, 6, "R"),
             P("SET", 3, 0, "U"), P("CLR", 3, 8, "D")], pivot=(3, 4), label_pt=[6.3, 4],
       optional_pins=["SET", "CLR", QBAR]),
    SY("srlatch", "SR Latch", "Flip-Flops & Latches", "FF", "",
       "The simplest memory: S = 1 sets Q = 1, R = 1 resets Q = 0, and with both at 0 it remembers. "
       "No clock. S = R = 1 is not allowed (both outputs go to 0).",
       pins=[P("S", 0, 2, "L"), P("R", 0, 5, "L"), P("Q", 6, 2, "R"), P(QBAR, 6, 5, "R")], pivot=(3, 3),
       optional_pins=[QBAR]),
    # Logic ICs: real 74HC chips, simulated from their logic equations
    DIP14("74hc00", "74HC00 Quad NAND", "Four 2-input NAND gates.", _PIN_QUAD,
          "# Four NAND gates\n" + _quad("{n}Y = !({n}A & {n}B)")),
    DIP14("74hc02", "74HC02 Quad NOR", "Four 2-input NOR gates (note: outputs come first on this chip).",
          ["1Y", "1A", "1B", "2Y", "2A", "2B", "GND", "3A", "3B", "3Y", "4A", "4B", "4Y", "VCC"],
          "# Four NOR gates\n" + _quad("{n}Y = !({n}A | {n}B)")),
    DIP14("74hc04", "74HC04 Hex Inverter", "Six NOT gates.",
          ["1A", "1Y", "2A", "2Y", "3A", "3Y", "GND", "4Y", "4A", "5Y", "5A", "6Y", "6A", "VCC"],
          "# Six NOT gates\n" + "".join("%dY = !%dA\n" % (n, n) for n in range(1, 7))),
    DIP14("74hc08", "74HC08 Quad AND", "Four 2-input AND gates.", _PIN_QUAD,
          "# Four AND gates\n" + _quad("{n}Y = {n}A & {n}B")),
    DIP14("74hc32", "74HC32 Quad OR", "Four 2-input OR gates.", _PIN_QUAD,
          "# Four OR gates\n" + _quad("{n}Y = {n}A | {n}B")),
    DIP14("74hc86", "74HC86 Quad XOR", "Four 2-input XOR gates.", _PIN_QUAD,
          "# Four XOR gates\n" + _quad("{n}Y = {n}A ^ {n}B")),
    DIP14("74hc74", "74HC74 Dual D Flip-Flop",
          "Two rising-edge D flip-flops. PRE and CLR are active-LOW: connect them to VCC for normal use "
          "(a LOW on PRE sets Q = 1, a LOW on CLR clears Q = 0).",
          ["1CLR", "1D", "1CLK", "1PRE", "1Q", "1Q'", "GND", "2Q'", "2Q", "2PRE", "2CLK", "2D", "2CLR", "VCC"],
          "# Two D flip-flops. PRE and CLR are active-LOW.\n"
          + "".join("{n}Q = 1 when !{n}PRE\n{n}Q = 0 when !{n}CLR\n{n}Q = {n}D on {n}CLK\n{n}Q' = !{n}Q\n".format(n=n)
                    for n in "12")),
    # ICs & boards
    BX("arduino_uno", "Arduino Uno", "ICs & Boards", "U", "",
       "ATmega328P microcontroller board. D0–D13 digital pins, A0–A5 analog inputs.",
       8, 15,
       [("VIN", "left", 1), ("5V", "left", 2), ("3.3V", "left", 3), ("GND", "left", 4),
        ("GND", "left", 5), ("RESET", "left", 6), ("A0", "left", 8), ("A1", "left", 9),
        ("A2", "left", 10), ("A3", "left", 11), ("A4", "left", 12), ("A5", "left", 13)]
       + [("D%d" % i + (" RX" if i == 0 else " TX" if i == 1 else ""), "right", i + 1)
          for i in range(14)],
       color="#cfe8ef", microcontroller=True),
    BX("rpi_pico", "Raspberry Pi Pico", "ICs & Boards", "U", "RP2040",
       "RP2040 microcontroller board (3.3 V logic). GP0–GP28 digital pins; GP26–GP28 are also "
       "analog inputs ADC0–ADC2. Pins are in the board's physical order (pin 1 top-left).",
       9, 21,
       [(n, "left", i + 1) for i, n in enumerate(
           ["GP0", "GP1", "GND", "GP2", "GP3", "GP4", "GP5", "GND", "GP6", "GP7",
            "GP8", "GP9", "GND", "GP10", "GP11", "GP12", "GP13", "GND", "GP14", "GP15"])]
       + [(n, "right", i + 1) for i, n in enumerate(
           ["VBUS", "VSYS", "GND", "3V3_EN", "3V3", "ADC_VREF", "GP28 ADC2", "AGND", "GP27 ADC1",
            "GP26 ADC0", "RUN", "GP22", "GND", "GP21", "GP20", "GP19", "GP18", "GND", "GP17", "GP16"])],
       color="#d1fae5", microcontroller=True),
    BX("timer555", "555 Timer", "ICs & Boards", "U", "NE555",
       "Timer IC for oscillators (astable) and one-shot pulses (monostable).",
       6, 6,
       [("TRIG", "left", 1), ("THRES", "left", 2), ("DISCH", "left", 4), ("CTRL", "left", 5),
        ("OUT", "right", 2), ("VCC", "top", 2), ("RESET", "top", 4), ("GND", "bottom", 3)]),
    BX("reg7805", "Voltage Regulator 7805", "ICs & Boards", "U", "",
       "Linear regulator: 7–35 V in, steady 5 V out.",
       6, 5, [("IN", "left", 2), ("OUT", "right", 2), ("GND", "bottom", 3)]),
    BX("ic8", "Generic IC (8-pin DIP)", "ICs & Boards", "U", "",
       "Blank 8-pin chip. Pin 1 is top-left; numbering goes counter-clockwise.",
       4, 5, [("1", "left", 1), ("2", "left", 2), ("3", "left", 3), ("4", "left", 4),
              ("8", "right", 1), ("7", "right", 2), ("6", "right", 3), ("5", "right", 4)]),
    BX("ic14", "Generic IC (14-pin DIP)", "ICs & Boards", "U", "",
       "Blank 14-pin chip (e.g. 74xx logic). Pin 1 top-left, counter-clockwise.",
       4, 8, [(str(i), "left", i) for i in range(1, 8)]
       + [(str(15 - i), "right", i) for i in range(1, 8)]),
    # Modules & sensors
    BX("servo", "Servo Motor", "Modules & Sensors", "M", "SG90",
       "Hobby servo. SIG takes a PWM signal.", 5, 4,
       [("GND", "left", 1), ("V+", "left", 2), ("SIG", "left", 3)], color="#dbeafe"),
    BX("hcsr04", "Ultrasonic Sensor", "Modules & Sensors", "U", "HC-SR04",
       "Distance sensor: send a pulse on TRIG, time the pulse on ECHO.", 6, 5,
       [("VCC", "left", 1), ("TRIG", "left", 2), ("ECHO", "left", 3), ("GND", "left", 4)],
       color="#d1fae5"),
    BX("tmp36", "Temperature Sensor", "Modules & Sensors", "U", "TMP36",
       "Analog temperature sensor: VOUT rises 10 mV per °C. Set the temperature in its properties.", 5, 4,
       [("+VS", "left", 1), ("VOUT", "left", 2), ("GND", "left", 3)], color="#fef3c7"),
    BX("lcd_i2c", "LCD 16×2 (I2C)", "Modules & Sensors", "U", "",
       "Character display with I2C backpack.", 6, 5,
       [("GND", "left", 1), ("VCC", "left", 2), ("SDA", "left", 3), ("SCL", "left", 4)],
       color="#d1fae5"),
    BX("relay", "Relay Module", "Modules & Sensors", "K", "5 V",
       "Electrically controlled switch. When IN is HIGH, COM connects to NO; otherwise COM connects to NC.", 6, 4,
       [("VCC", "left", 1), ("GND", "left", 2), ("IN", "left", 3),
        ("NO", "right", 1), ("COM", "right", 2), ("NC", "right", 3)], color="#dbeafe"),
    # Building blocks for making your own components from a circuit
    SY(PORT_DEF, "Component Pin", "Building Blocks", "P", "",
       "Marks a pin of a component you make from a circuit. Wire it to the circuit and set its label to the "
       "pin name (A, B, OUT, VCC …). Then select the circuit together with its Component Pins and click "
       "Make component: each Component Pin becomes a pin of the new part.",
       pins=[P("PIN", 0, 1, "L")], pivot=(2, 1), label_mode="label", label_pt=[2, 1]),
]


# Pin names that count as power or ground on a microcontroller board (case-insensitive)
_POWER_PIN_RX = re.compile(r"^\+?(VIN|VCC|VDD|VBUS|VUSB|VSYS|V\+|5V|5V0|3V3|3\.3V|3V|12V)\d*$")
_GROUND_PIN_RX = re.compile(r"^([ADP]?GND|VSS|GROUND|0V)\d*$")


def is_power_pin(name):
    return bool(_POWER_PIN_RX.match(re.sub(r"\s+", "", name or "").upper()))


def is_ground_pin(name):
    return bool(_GROUND_PIN_RX.match(re.sub(r"\s+", "", name or "").upper()))


# --------------------------------------------------------------------------
# Resolved component definition (geometry ready for drawing)
# --------------------------------------------------------------------------
class RDef:
    def __init__(self, d):
        self.raw = d
        self.id = d["id"]
        self.name = d.get("name", "Part")
        self.category = d.get("category", "My Components")
        self.prefix = d.get("prefix", "U") or "U"
        self.value = d.get("value", "")
        self.description = d.get("description", "")
        self.custom = bool(d.get("custom"))
        self.microcontroller = bool(d.get("microcontroller"))
        self.symbol = d.get("symbol", "box")
        self.label_mode = d.get("label_mode", "both")
        self.color = d.get("color", "#e8eefc")
        self.box = None
        self.alt_prims = None
        self.image = d.get("image") if valid_picture(d.get("image")) else None
        self.image_key = picture_key(self.image) if self.image else None
        self.pic_region = None
        if self.symbol == "box":
            self._build_box(d)
        else:
            fn = SYMBOLS.get(self.symbol)
            self.prims = fn() if fn else []
            alt = ALT_SYMBOLS.get(self.symbol)
            self.alt_prims = alt() if alt else None
            self.pins = [dict(p) for p in d.get("pins", [])]
            self.pivot = tuple(d.get("pivot", (2, 1)))
        xs, ys = [], []
        for p in self.prims:
            if p["t"] in ("line", "poly"):
                xs += [q[0] for q in p["pts"]]
                ys += [q[1] for q in p["pts"]]
            elif p["t"] == "circle":
                xs += [p["c"][0] - p["r"], p["c"][0] + p["r"]]
                ys += [p["c"][1] - p["r"], p["c"][1] + p["r"]]
        if not xs:
            xs, ys = [0, 2], [0, 2]
        self.body_bbox = (min(xs), min(ys), max(xs), max(ys))
        for p in self.pins:
            xs.append(p["x"])
            ys.append(p["y"])
        self.bbox = (min(xs), min(ys), max(xs), max(ys))
        self.label_pt = None
        if self.box is None:
            if d.get("label_pt"):
                self.label_pt = tuple(d["label_pt"])
            else:
                dirs = {p["dir"] for p in self.pins}
                x0, y0, x1, y1 = self.body_bbox
                if "U" not in dirs:
                    self.label_pt = (self.pivot[0], y0 - 0.15)
                elif "D" not in dirs:
                    self.label_pt = (self.pivot[0], y1 + 0.15)
                elif "R" not in dirs:
                    self.label_pt = (x1 + 0.2, self.pivot[1])
                else:
                    self.label_pt = (x0 - 0.2, self.pivot[1])

    def _build_box(self, d):
        w = max(2, int(d.get("w", 4)))
        h = max(2, int(d.get("h", 3)))
        self.box = (w, h)
        self.prims = [PG((0, 0), (w, 0), (w, h), (0, h), fill="body")]
        self.pins = []
        for p in d.get("pins", []):
            side = p.get("side", "left")
            pos = float(p.get("pos", 1))
            if side == "left":
                x, y, dr, ix, iy = -1, pos, "L", 0, pos
            elif side == "right":
                x, y, dr, ix, iy = w + 1, pos, "R", w, pos
            elif side == "top":
                x, y, dr, ix, iy = pos, -1, "U", pos, 0
            else:
                x, y, dr, ix, iy = pos, h + 1, "D", pos, h
            self.pins.append(P(p.get("name", "?"), x, y, dr))
            self.prims.append(L((x, y), (ix, iy)))
            ux, uy = -DIRS[dr][0], -DIRS[dr][1]
            self.prims.append({"t": "pintext", "p": (ix + ux * 0.22, iy + uy * 0.22),
                               "s": p.get("name", ""), "inward": (ux, uy)})
        self.pivot = (w // 2, h // 2)
        def side_room(side):
            n = max([len(p.get("name", "")) for p in d.get("pins", []) if p.get("side") == side] or [0])
            return pin_label_room(n)
        x0, x1 = side_room("left"), w - side_room("right")
        if x1 - x0 < 1.5:
            x0, x1 = 0.15, w - 0.15
        self.text_region = (x0, x1)
        if self.image:
            # the picture and the label go in the middle, clear of the pin names on every side
            px0, px1 = side_room("left") + 0.1, w - side_room("right") - 0.1
            py0, py1 = side_room("top") + 0.1, h - side_room("bottom") - 0.1
            if px1 - px0 < 1:
                px0, px1 = 0.15, w - 0.15
            if py1 - py0 < 1:
                py0, py1 = 0.15, h - 0.15
            self.pic_region = (px0, py0, px1, py1)


def local_to_world(comp, rd, lx, ly):
    px, py = rd.pivot
    qx, qy = lx - px, ly - py
    if comp.get("flip"):
        qx = -qx
    for _ in range(comp.get("rot", 0) % 4):
        qx, qy = -qy, qx
    return comp["x"] + qx, comp["y"] + qy


def dir_to_world(comp, dx, dy):
    if comp.get("flip"):
        dx = -dx
    for _ in range(comp.get("rot", 0) % 4):
        dx, dy = -dy, dx
    return dx, dy


def anchor_for(dx, dy):
    if abs(dx) < 1e-9 and abs(dy) < 1e-9:
        return "center"
    if abs(dx) > abs(dy):
        return "w" if dx > 0 else "e"
    return "n" if dy > 0 else "s"


_FONT_CACHE = {}

# Diagram text size, chosen in View -> Diagram text size.  Multiplies every label
# drawn on the circuit canvas (part names, values, pin names, simulation readings).
TEXT_SIZES = (("small", "Small", 0.85), ("normal", "Normal", 1.0), ("large", "Large", 1.3))
DIAGRAM_FONT_SCALE = 1.0


def set_diagram_text_size(key):
    global DIAGRAM_FONT_SCALE
    DIAGRAM_FONT_SCALE = dict((k, f) for k, _n, f in TEXT_SIZES).get(key, 1.0)


def dpx(base, z):
    """Pixel size for diagram text of a given base size at zoom z."""
    return int(round(base * DIAGRAM_FONT_SCALE * z))


def _fit_text(text, fam, px, weight, max_w):
    """Shorten text with … so it fits in max_w pixels."""
    key = (fam, px, weight)
    f = _FONT_CACHE.get(key)
    if f is None:
        try:
            f = _FONT_CACHE[key] = tkfont.Font(family=fam, size=-px, weight=weight)
        except tk.TclError:
            return text
    if max_w <= 0 or f.measure(text) <= max_w:
        return text
    lo, hi = 0, len(text)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if f.measure(text[:mid].rstrip() + "…") <= max_w:
            lo = mid
        else:
            hi = mid - 1
    return text[:lo].rstrip() + "…" if lo else "…"


def _draw_picture_body(cv, rd, comp, tp, z, fam, color, label, value, tags):
    """Picture in the middle of a box part, with the part's label underneath (kept upright)."""
    x0, y0, x1, y1 = rd.pic_region
    (ax, ay), (bx, by) = tp((x0, y0)), tp((x1, y1))
    sx0, sx1 = sorted((ax, bx))
    sy0, sy1 = sorted((ay, by))
    big, small = dpx(11, z), dpx(9, z)
    sub = (rd.name + ("  ·  " + value if value else "")) if label else value
    lines = []
    if big >= 5:
        lines.append((label or rd.name, big, "bold", color))
    if sub and small >= 5:
        lines.append((sub, small, "normal", C["muted"]))
    lab_h = sum(px * 1.28 for _t, px, _w, _c in lines)
    pad = max(1.0, 2.0 * z)
    avail_w, avail_h = sx1 - sx0 - 2 * pad, sy1 - sy0 - 2 * pad - lab_h
    img, dh = None, 0
    if avail_w >= 6 and avail_h >= 6:
        iw, ih = rd.image["w"], rd.image["h"]
        s = min(avail_w / float(iw), avail_h / float(ih))
        s = 1.04 ** math.floor(math.log(s) / math.log(1.04) + 1e-9)  # re-use sizes while zooming
        dw, dh = max(1, int(iw * s)), max(1, int(ih * s))
        img = PICTURES.photo(rd.image, dw, dh, rd.image_key)
        if img is None:
            dh = 0
    gap = 2 * z if (img is not None and lines) else 0
    cx = (sx0 + sx1) / 2.0
    y = (sy0 + sy1) / 2.0 - (dh + gap + lab_h) / 2.0
    if img is not None:
        cv.create_image(cx, y + dh / 2.0, image=img, anchor="center", tags=tags + ("picture",))
    y += dh + gap
    for text, px, weight, fill in lines:
        cv.create_text(cx, y, text=_fit_text(text, fam, px, weight, sx1 - sx0), anchor="n", fill=fill,
                       font=(fam, -px, weight), tags=tags)
        y += px * 1.28


def render_component(cv, rd, comp, T, z, fam, state="normal", connected=frozenset(),
                     cid=None, show_pin_labels=True, show_pins=True, extra_tags=(), closed=False):
    """Draw one component on a Tk canvas.  T maps world grid units -> canvas px.
    closed=True draws a switch closed / a push button pressed."""
    tags = ("comp",) + (("c:" + cid,) if cid else ()) + tuple(extra_tags)
    hot = state in ("selected", "ghost")
    stroke = C["select"] if hot else C["stroke"]
    lw = max(1.0, 1.6 * z)

    def tp(pt):
        wx, wy = local_to_world(comp, rd, pt[0], pt[1])
        return T(wx, wy)

    if state == "selected":
        x0, y0, x1, y1 = rd.bbox
        corners = [tp((x0 - 0.35, y0 - 0.35)), tp((x1 + 0.35, y1 + 0.35))]
        cx0, cx1 = sorted([corners[0][0], corners[1][0]])
        cy0, cy1 = sorted([corners[0][1], corners[1][1]])
        cv.create_rectangle(cx0, cy0, cx1, cy1, fill=C["sel_fill"], outline=C["select"],
                            dash=(4, 3), tags=tags)

    def fill_of(f):
        if f == "stroke":
            return stroke
        if f == "body":
            return C["accent_light"] if state == "ghost" else body_fill(rd.color)
        if f == "white":
            return C["sym_fill"]
        return f or ""

    prims = rd.alt_prims if (closed and rd.alt_prims) else rd.prims
    for p in prims:
        t = p["t"]
        if t == "line":
            pts = [c for q in p["pts"] for c in tp(q)]
            cv.create_line(*pts, fill=stroke, width=lw * p.get("w", 1.0), capstyle="round",
                           joinstyle="round", tags=tags)
        elif t == "poly":
            pts = [c for q in p["pts"] for c in tp(q)]
            cv.create_polygon(*pts, fill=fill_of(p.get("fill")), outline=stroke, width=lw,
                              joinstyle="round", tags=tags)
        elif t == "circle":
            cx, cy = tp(p["c"])
            r = p["r"] * G * z
            cv.create_oval(cx - r, cy - r, cx + r, cy + r, outline=stroke, width=lw,
                           fill=fill_of(p.get("fill")), tags=tags)
        elif t == "text":
            px = dpx(p.get("size", 11), z)
            if px < 5:
                continue
            x, y = tp(p["p"])
            cv.create_text(x, y, text=p["s"], fill=stroke, tags=tags,
                           font=(fam, -px, "bold" if p.get("bold") else "normal"))
        elif t == "pintext":
            px = dpx(9, z)
            if not show_pin_labels or px < 6:
                continue
            x, y = tp(p["p"])
            ux, uy = dir_to_world(comp, *p["inward"])
            if ux != 0:
                anchor, angle = ("w" if ux > 0 else "e"), 0
            else:
                anchor, angle = ("e" if uy > 0 else "w"), 90
            cv.create_text(x, y, text=p["s"], anchor=anchor, angle=angle, fill=C["pinlabel"],
                           font=(fam, -px), tags=tags)

    label = comp.get("label", "")
    value = comp.get("value", "")
    if rd.box and rd.pic_region:
        _draw_picture_body(cv, rd, comp, tp, z, fam, stroke, label, value, tags)
    elif rd.box:
        w, h = rd.box
        if comp.get("rot", 0) % 2 == 0:
            tx0, tx1 = rd.text_region
            cx, cy = tp(((tx0 + tx1) / 2.0, h / 2.0))
            wrap = max(20, (tx1 - tx0) * G * z - 4)
        else:
            cx, cy = tp((w / 2.0, h / 2.0))
            wrap = max(20, h * G * z * 0.85)
        big, small = dpx(11, z), dpx(9, z)
        if big >= 5:
            cv.create_text(cx, cy, text=label or rd.name, anchor="s", fill=stroke,
                           font=(fam, -big, "bold"), width=wrap, justify="center", tags=tags)
            if label and small >= 5:
                sub = rd.name + (("\n" + value) if value else "")
                cv.create_text(cx, cy + 1, text=sub, anchor="n", fill=C["muted"],
                               font=(fam, -small), width=wrap, justify="center", tags=tags)
    elif rd.label_pt is not None:
        lines = []
        if rd.label_mode in ("both", "label") and label:
            lines.append(label)
        if rd.label_mode in ("both", "value") and value:
            lines.append(value)
        px = dpx(11, z)
        if lines and px >= 5:
            x, y = tp(rd.label_pt)
            ox, oy = rd.label_pt[0] - rd.pivot[0], rd.label_pt[1] - rd.pivot[1]
            dx, dy = dir_to_world(comp, ox, oy)
            anc = anchor_for(dx, dy)
            just = {"w": "left", "e": "right"}.get(anc, "center")
            cv.create_text(x, y, text="\n".join(lines), anchor=anc, justify=just,
                           fill=C["select"] if hot else C["text"], font=(fam, -px), tags=tags)

    if show_pins:
        r = max(2.6, 3.3 * z)
        for i, p in enumerate(rd.pins):
            x, y = tp((p["x"], p["y"]))
            on = (cid, i) in connected
            cv.create_oval(x - r, y - r, x + r, y + r,
                           fill=C["pin_on"] if on else C["pin_free"],
                           outline=C["pin_on"] if on else C["pin_off"],
                           width=max(1.0, 1.2 * z), tags=tags + ("pin",))


def _axis_pref(d, dx, dy, start):
    """True = run horizontally next to this pin, False = vertically.
    Leave a pin in the direction it points; arrive at a pin from outside the part."""
    sign = 1 if start else -1
    if d[0] != 0:
        return dx * d[0] * sign >= 0
    return not (dy * d[1] * sign >= 0)


def route_points(pts, da, db, style):
    """Turn control points into the drawn polyline (orthogonal or straight)."""
    if style == "straight" or len(pts) < 2:
        return list(pts), list(range(max(0, len(pts) - 1)))
    out = [pts[0]]
    owner = []
    n = len(pts) - 1
    for i in range(n):
        (x0, y0), (x1, y1) = pts[i], pts[i + 1]
        if abs(x0 - x1) < 1e-9 or abs(y0 - y1) < 1e-9:
            out.append((x1, y1))
            owner.append(i)
            continue
        sh = _axis_pref(da, x1 - x0, y1 - y0, True) if (i == 0 and da) else None
        eh = _axis_pref(db, x1 - x0, y1 - y0, False) if (i == n - 1 and db) else None
        if sh is not None and eh is not None:
            if sh and eh:
                mx = (x0 + x1) / 2.0
                mids = [(mx, y0), (mx, y1)]
            elif not sh and not eh:
                my = (y0 + y1) / 2.0
                mids = [(x0, my), (x1, my)]
            elif sh:
                mids = [(x1, y0)]
            else:
                mids = [(x0, y1)]
        elif sh is not None:
            mids = [(x1, y0)] if sh else [(x0, y1)]
        elif eh is not None:
            mids = [(x0, y1)] if eh else [(x1, y0)]
        else:
            mids = [(x1, y0)]
        for m in mids:
            out.append(m)
            owner.append(i)
        out.append((x1, y1))
        owner.append(i)
    return out, owner


def seg_dist(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    l2 = dx * dx + dy * dy
    if l2 == 0:
        return math.hypot(px - ax, py - ay)
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / l2))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))


# --------------------------------------------------------------------------
# Files & settings
# --------------------------------------------------------------------------
def data_dir():
    if os.name == "nt":
        base = os.environ.get("APPDATA") or os.path.expanduser("~")
        path = os.path.join(base, "CircuitBuilder")
    else:
        path = os.path.join(os.path.expanduser("~"), ".circuit_builder")
    try:
        os.makedirs(path, exist_ok=True)
    except OSError:
        pass
    return path


def load_json(path, default):
    try:
        with open(path, "r", encoding="utf-8-sig") as f:   # -sig: files saved by Notepad start with a BOM
            return json.load(f)
    except (OSError, ValueError, RecursionError):
        return default


def save_json(path, data):
    tmp = path + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        os.replace(tmp, path)
    except BaseException:
        try:
            os.remove(tmp)
        except OSError:
            pass
        raise


def new_id():
    return uuid.uuid4().hex[:8]


# ---- error log: Tk swallows errors in button/mouse handlers, and the windowed .exe has no console,
# so problems are written to a file students can send in.
def error_log_path():
    return os.path.join(data_dir(), "errors.log")


def log_exception(exc_type, exc, tb, context=""):
    """Write a traceback to errors.log (and the console, if there is one).  Never raises."""
    text = "".join(traceback.format_exception(exc_type, exc, tb))
    try:
        if sys.stderr is not None:
            sys.stderr.write(text)
    except Exception:
        pass
    path = error_log_path()
    try:
        if os.path.getsize(path) > 256 * 1024:
            os.replace(path, path + ".old")
    except OSError:
        pass
    try:
        with open(path, "a", encoding="utf-8") as f:
            f.write("---- %s  %s %s  Python %s  %s\n%s\n" % (
                time.strftime("%Y-%m-%d %H:%M:%S"), APP_NAME, APP_VERSION, sys.version.split()[0], context, text))
    except OSError:
        pass
    return path


# --------------------------------------------------------------------------
# Checking data read from files
# --------------------------------------------------------------------------
# .circuit and .cblib files are plain JSON that students share, hand-edit and save with older
# versions.  Everything read from one goes through these functions first, so a damaged file gives
# a message instead of an error in the middle of drawing.
PIN_SIDES = ("left", "right", "top", "bottom")
MAX_PINS = 512   # most pins a part read from a file may have (a placeholder is drawn with this many at most)
_HEX_RX = re.compile(r"^#(?:[0-9a-fA-F]{3}|[0-9a-fA-F]{6})$")


def _as_list(v):
    return v if isinstance(v, list) else []


def _num(v, default=None):
    """A finite float, or default (bools and text that isn't a number count as missing)."""
    if isinstance(v, bool):
        return default
    try:
        f = float(v)
    except (TypeError, ValueError, OverflowError):
        return default
    return f if math.isfinite(f) else default


def _grid(v, default=0):
    """A grid coordinate: whole numbers stay ints so files stay tidy."""
    f = _num(v)
    if f is None:
        return default
    return int(f) if f == int(f) else f


def _text(v, default=""):
    if v is None:
        return default
    return v if isinstance(v, str) else str(v)


def _pin_index(v):
    f = _num(v)
    if f is None or f < 0 or f != int(f):
        return None
    return int(f)


def is_color(v):
    return isinstance(v, str) and bool(_HEX_RX.match(v))


def clean_comp(c):
    """A placed part read from a file -> a safe copy, or None if it can't be used."""
    if not isinstance(c, dict):
        return None
    cid, did = c.get("id"), c.get("def")
    if not isinstance(cid, str) or not cid or not isinstance(did, str) or not did:
        return None
    out = dict(c)
    out["x"], out["y"] = _grid(c.get("x")), _grid(c.get("y"))
    out["rot"] = int(_num(c.get("rot"), 0)) % 4
    out["flip"] = bool(c.get("flip"))
    for k in ("label", "value", "notes"):
        out[k] = _text(c.get(k))
    for k in ("wiper", "light", "temp"):          # simulation sliders
        if k in out:
            v = _num(out[k])
            if v is None:
                del out[k]
            else:
                out[k] = v
    if "closed" in out:
        out["closed"] = bool(out["closed"])
    if out.get("mcu") is None:
        out.pop("mcu", None)
    else:
        out["mcu"] = bool(out["mcu"])
    if not isinstance(out.get("unpacked_from"), str):
        out.pop("unpacked_from", None)
    return out


def clean_wire(w, pin_count=None):
    """A wire read from a file -> a safe copy, or None.
    pin_count(part id) gives how many pins that part has (None: no such part).  Without it only the
    shape of the wire is checked."""
    if not isinstance(w, dict):
        return None
    ends = []
    for key in ("a", "b"):
        e = w.get(key)
        if not isinstance(e, (list, tuple)) or len(e) != 2 or not isinstance(e[0], str):
            return None
        i = _pin_index(e[1])
        if i is None:
            return None
        if pin_count is not None:
            n = pin_count(e[0])
            if n is None or i >= n:
                return None
        ends.append([e[0], i])
    if ends[0] == ends[1]:
        return None
    out = dict(w)
    out["a"], out["b"] = ends
    bends = []
    for b in _as_list(w.get("bends")):
        if isinstance(b, (list, tuple)) and len(b) == 2:
            x, y = _num(b[0]), _num(b[1])
            if x is not None and y is not None:
                bends.append([_grid(x), _grid(y)])
    out["bends"] = bends
    if not is_color(out.get("color")):
        out.pop("color", None)
    if not isinstance(out.get("id"), str) or not out["id"]:
        out.pop("id", None)
    return out


def clean_subcircuit(sub):
    if not isinstance(sub, dict):
        return None
    comps, seen = [], set()
    for c in _as_list(sub.get("comps")):
        cc = clean_comp(c)
        if cc is not None and cc["id"] not in seen:
            seen.add(cc["id"])
            comps.append(cc)
    wires = []
    for w in _as_list(sub.get("wires")):
        cw = clean_wire(w, lambda cid: MAX_PINS if cid in seen else None)
        if cw is not None:
            wires.append(cw)
    return {"comps": comps, "wires": wires}


def clean_def(d):
    """A component definition read from a library or circuit file -> a safe copy, or None.
    Pins are repaired rather than dropped, so wires keep pointing at the same pin numbers."""
    if not isinstance(d, dict):
        return None
    did = d.get("id")
    if not isinstance(did, str) or not did or not isinstance(d.get("pins"), list):
        return None
    out = dict(d)
    for k in ("name", "category", "prefix", "value", "description"):
        if k in out:
            out[k] = _text(out[k])
    if not out.get("name"):
        out["name"] = "Part"
    sym = d.get("symbol", "box")
    out["symbol"] = sym = sym if isinstance(sym, str) and sym else "box"
    pins = []
    for i, p in enumerate(d["pins"]):
        q = dict(p) if isinstance(p, dict) else {}
        q["name"] = _text(q.get("name"), str(i + 1))
        if sym == "box":
            if q.get("side") not in PIN_SIDES:
                q["side"] = "left"
            q["pos"] = _num(q.get("pos"), float(i + 1))
        else:
            q["x"], q["y"] = _num(q.get("x"), 0.0), _num(q.get("y"), 0.0)
            if q.get("dir") not in DIRS:
                q["dir"] = "L"
        inn = q.get("inner")
        if inn is not None:
            if (isinstance(inn, (list, tuple)) and len(inn) == 2 and isinstance(inn[0], str)
                    and _pin_index(inn[1]) is not None):
                q["inner"] = [inn[0], _pin_index(inn[1])]
            else:
                del q["inner"]
        pins.append(q)
    out["pins"] = pins
    if sym == "box":
        out["w"] = int(max(2, min(400, _num(d.get("w"), 4))))
        out["h"] = int(max(2, min(400, _num(d.get("h"), 3))))
    for k in ("pivot", "label_pt"):
        v = out.get(k)
        if v is not None and not (isinstance(v, (list, tuple)) and len(v) == 2
                                  and all(_num(a) is not None for a in v)):
            del out[k]
    if "color" in out and not is_color(out["color"]):
        del out["color"]
    if "image" in out and not valid_picture(out["image"]):
        del out["image"]
    for k in ("logic", "sim", "label_mode"):
        if k in out and not isinstance(out[k], str):
            del out[k]
    if "optional_pins" in out:
        out["optional_pins"] = [p for p in _as_list(out["optional_pins"]) if isinstance(p, str)]
    if "subcircuit" in out:
        sub = clean_subcircuit(out["subcircuit"])
        if sub is None:
            del out["subcircuit"]
        else:
            out["subcircuit"] = sub
    return out


def clean_settings(s):
    """settings.json -> a dict with sensible types (a damaged file must not stop the app starting)."""
    if not isinstance(s, dict):
        return {}
    out = dict(s)
    checks = {"wire_style": lambda v: v in ("orthogonal", "straight"),
              "wire_color": is_color,
              "text_size": lambda v: v in [k for k, _n, _f in TEXT_SIZES],
              "theme": lambda v: v in ("light", "dark"),
              "show_grid": lambda v: isinstance(v, bool),
              "show_volts": lambda v: isinstance(v, bool)}
    for k, ok in checks.items():
        if k in out and not ok(out[k]):
            del out[k]
    out["recent"] = [p for p in _as_list(out.get("recent")) if isinstance(p, str)][:8]
    return out


# --------------------------------------------------------------------------
# Pictures on components
# --------------------------------------------------------------------------
# A picture is stored inside a component definition as
#     "image": {"data": "<base64 PNG>", "w": width_px, "h": height_px}
# so it travels with .cblib and .circuit files.  Pictures are shrunk to at most
# PICTURE_MAX pixels when they are added, which keeps those files small.
PICTURE_MAX = 400
PICTURE_FILETYPES = [("Pictures", "*.png *.jpg *.jpeg *.gif *.bmp *.webp *.tif *.tiff"),
                     ("All files", "*.*")]
PIC_SIZE = 4.0       # default picture size (longer side, in grid squares) when a part sizes itself
PIC_LABEL_H = 1.15   # room kept under the picture for the part's label (grid squares)

if _PILImage is not None:
    _LANCZOS = getattr(getattr(_PILImage, "Resampling", _PILImage), "LANCZOS")
else:
    _LANCZOS = None


class PictureError(Exception):
    pass


def valid_picture(img):
    try:
        return bool(isinstance(img, dict) and isinstance(img.get("data"), str) and img["data"]
                    and int(img.get("w", 0)) > 0 and int(img.get("h", 0)) > 0)
    except (TypeError, ValueError):
        return False


def picture_key(img):
    return hashlib.sha1(img["data"].encode("ascii", "ignore")).hexdigest()[:16]


def fit_size(w, h, max_w, max_h):
    """Largest (w, h) with the same shape as w x h that fits inside max_w x max_h."""
    s = min(max_w / float(w), max_h / float(h))
    return max(1, int(w * s)), max(1, int(h * s))


def pin_label_room(n_chars):
    """Room (grid squares) that a pin name of n_chars takes up inside a box part."""
    return (n_chars * 5.3 + 9) / G if n_chars else 0.15


def picture_auto_size(img, room):
    """Smallest box (w, h) that shows the picture at its default size.
    room: space taken by pin names on each side ("left", "right", "top", "bottom")."""
    a = img["w"] / float(img["h"])
    pw, ph = (PIC_SIZE, PIC_SIZE / a) if a >= 1 else (PIC_SIZE * a, PIC_SIZE)
    pw, ph = max(pw, 1.5), max(ph, 1.5)
    w = room["left"] + room["right"] + pw + 0.6
    h = room["top"] + room["bottom"] + ph + PIC_LABEL_H + 0.6
    return int(math.ceil(w - 1e-6)), int(math.ceil(h - 1e-6))


# ---- tiny PNG reader/writer (8-bit, non-interlaced), used when Pillow is not installed
_PNG_SIG = b"\x89PNG\r\n\x1a\n"


def _png_chunk(tag, data):
    return struct.pack(">I", len(data)) + tag + data + struct.pack(">I", zlib.crc32(tag + data) & 0xffffffff)


def _sub255(a, b):
    return (a - b) & 255


def png_encode(px, w, h, n, level=6, up_filter=False):
    """Encode w*h*n bytes (n = 3 for RGB, 4 for RGBA) as a PNG file."""
    stride = w * n
    parts, prev = [], None
    for y in range(h):
        row = px[y * stride:(y + 1) * stride]
        if up_filter and prev is not None:
            parts.append(b"\x02" + bytes(map(_sub255, row, prev)))
        else:
            parts.append(b"\x00" + bytes(row))
        prev = row
    ihdr = struct.pack(">IIBBBBB", w, h, 8, 6 if n == 4 else 2, 0, 0, 0)
    return (_PNG_SIG + _png_chunk(b"IHDR", ihdr)
            + _png_chunk(b"IDAT", zlib.compress(b"".join(parts), level)) + _png_chunk(b"IEND", b""))


def png_size(raw):
    if raw[:8] != _PNG_SIG or raw[12:16] != b"IHDR":
        raise ValueError("not a PNG file")
    return struct.unpack(">II", raw[16:24])


def _png_unfilter(dec, h, stride, bpp):
    out = bytearray(h * stride)
    prev = bytearray(stride)
    pos = 0
    for y in range(h):
        f = dec[pos]
        line = bytearray(dec[pos + 1:pos + 1 + stride])
        pos += stride + 1
        if f == 1:
            for i in range(bpp, stride):
                line[i] = (line[i] + line[i - bpp]) & 255
        elif f == 2:
            line = bytearray((a + b) & 255 for a, b in zip(line, prev))
        elif f == 3:
            for i in range(stride):
                left = line[i - bpp] if i >= bpp else 0
                line[i] = (line[i] + ((left + prev[i]) >> 1)) & 255
        elif f == 4:
            for i in range(stride):
                a = line[i - bpp] if i >= bpp else 0
                b = prev[i]
                c = prev[i - bpp] if i >= bpp else 0
                p = a + b - c
                pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
                line[i] = (line[i] + (a if pa <= pb and pa <= pc else b if pb <= pc else c)) & 255
        out[y * stride:(y + 1) * stride] = line
        prev = line
    return out


def png_decode(raw):
    """Decode an 8-bit PNG -> (w, h, n, pixels) with n = 3 (RGB) or 4 (RGBA)."""
    if raw[:8] != _PNG_SIG:
        raise ValueError("not a PNG file")
    pos, idat, hdr = 8, [], None
    while pos + 8 <= len(raw):
        ln, tag = struct.unpack(">I4s", raw[pos:pos + 8])
        body = raw[pos + 8:pos + 8 + ln]
        if tag == b"IHDR":
            hdr = struct.unpack(">IIBBBBB", body)
        elif tag == b"IDAT":
            idat.append(body)
        elif tag == b"IEND":
            break
        pos += 12 + ln
    if not hdr:
        raise ValueError("damaged PNG file")
    w, h, depth, ctype, _comp, _filt, interlace = hdr
    chans = {0: 1, 2: 3, 4: 2, 6: 4}.get(ctype)
    if depth != 8 or chans is None or interlace:
        raise ValueError("unsupported PNG type")
    stride = w * chans
    dec = zlib.decompress(b"".join(idat))
    if all(dec[y * (stride + 1)] == 0 for y in range(h)):  # unfiltered rows (this is what Tk writes)
        px = b"".join(dec[y * (stride + 1) + 1:(y + 1) * (stride + 1)] for y in range(h))
    else:
        px = bytes(_png_unfilter(dec, h, stride, chans))
    if chans in (1, 2):  # grey (+ alpha) -> RGB(A)
        g = px[0::chans]
        n = 3 if chans == 1 else 4
        out = bytearray(w * h * n)
        out[0::n], out[1::n], out[2::n] = g, g, g
        if n == 4:
            out[3::4] = px[1::2]
        return w, h, n, bytes(out)
    return w, h, chans, px


def _mul_alpha(v, a):
    return (v * a + 127) // 255


def _div_alpha(v, a):
    return min(255, (v * 255 + a // 2) // a) if a else 0


def _alpha_from(on_black, on_white):
    return max(0, min(255, 255 - (on_white - on_black)))


def _premultiply(w, h, n, px):
    """Straight RGBA -> premultiplied RGBA (fully opaque pictures become plain RGB)."""
    if n != 4:
        return w, h, n, bytes(px)
    alpha = px[3::4]
    if alpha.count(255) == len(alpha):
        rgb = bytearray(w * h * 3)
        rgb[0::3], rgb[1::3], rgb[2::3] = px[0::4], px[1::4], px[2::4]
        return w, h, 3, bytes(rgb)
    out = bytearray(px)
    for c in range(3):
        out[c::4] = bytes(map(_mul_alpha, px[c::4], alpha))
    return w, h, 4, bytes(out)


def _unpremultiply(n, px):
    if n != 4:
        return px
    alpha = px[3::4]
    out = bytearray(px)
    for c in range(3):
        out[c::4] = bytes(map(_div_alpha, px[c::4], alpha))
    return bytes(out)


def _photo_pixels(photo):
    """Pixels of a Tk photo image -> (w, h, n, straight RGB/RGBA bytes)."""
    try:
        raw = photo.tk.call(photo.name, "data", "-format", "png")
        if isinstance(raw, str):
            raw = base64.b64decode(raw)
        return png_decode(bytes(raw))
    except Exception:
        pass
    # Fallback: read the colours over black and over white to recover the transparency.
    w, h = photo.width(), photo.height()

    def grab(bg):
        rows = photo.tk.call(photo.name, "data", "-background", bg)
        if isinstance(rows, str):
            rows = photo.tk.splitlist(rows)
        txt = " ".join(r if isinstance(r, str) else " ".join(r) for r in rows)
        return bytes.fromhex(txt.replace("#", " "))

    black, white = grab("#000000"), grab("#ffffff")
    alpha = bytes(map(_alpha_from, black[1::3], white[1::3]))
    if alpha.count(255) == len(alpha):
        return w, h, 3, black
    out = bytearray(w * h * 4)
    out[0::4], out[1::4], out[2::4], out[3::4] = black[0::3], black[1::3], black[2::3], alpha
    return w, h, 4, _unpremultiply(4, bytes(out))


def _box_shrink(px, w, h, n, kx, ky):
    """Average kx x ky blocks of pixels (premultiplied) -> (pixels, new_w, new_h)."""
    nw, nh = w // kx, h // ky
    stride, span, step, cnt = w * n, nw * kx * n, kx * n, kx * ky

    def div(v, c=cnt, half=cnt // 2):
        return (v + half) // c

    out = bytearray(nw * nh * n)
    for oy in range(nh):
        acc = [None] * n
        for dy in range(ky):
            off = (oy * ky + dy) * stride
            row = px[off:off + span]
            for dx in range(kx):
                for c in range(n):
                    part = row[dx * n + c::step]
                    acc[c] = list(part) if acc[c] is None else list(map(_op_add, acc[c], part))
        line = bytearray(nw * n)
        for c in range(n):
            line[c::n] = bytes(map(div, acc[c]))
        out[oy * nw * n:(oy + 1) * nw * n] = line
    return bytes(out), nw, nh


def _axis(src, dst):
    i0, i1, f = [], [], []
    sc = src / float(dst)
    for d in range(dst):
        s = (d + 0.5) * sc - 0.5
        if s <= 0:
            a, t = 0, 0.0
        elif s >= src - 1:
            a, t = src - 1, 0.0
        else:
            a = int(s)
            t = s - a
        i0.append(a)
        i1.append(min(a + 1, src - 1))
        f.append(int(t * 256 + 0.5))
    return i0, i1, f


def _lerp(a, b, wa, wb):
    return (a * wa + b * wb + 128) >> 8


def _bilinear(px, w, h, n, dw, dh):
    """Resize pixels to exactly dw x dh with linear interpolation."""
    if (w, h) == (dw, dh):
        return px
    stride = w * n
    yi0, yi1, yf = _axis(h, dh)
    rows = {}
    if dw == w:
        def hrow(y):
            return px[y * stride:(y + 1) * stride]
    else:
        xi0, xi1, xf = _axis(w, dw)
        g0 = itemgetter(*[x * n + c for x in xi0 for c in range(n)])
        g1 = itemgetter(*[x * n + c for x in xi1 for c in range(n)])
        wb = [f for f in xf for _ in range(n)]
        wa = [256 - f for f in wb]

        def hrow(y):
            r = px[y * stride:(y + 1) * stride]
            return bytes(map(_lerp, g0(r), g1(r), wa, wb))
    out = bytearray()
    for y in range(dh):
        a, b, f = yi0[y], yi1[y], yf[y]
        if a not in rows:
            rows[a] = hrow(a)
        if f == 0:
            out += rows[a]
            continue
        if b not in rows:
            rows[b] = hrow(b)
        fa = 256 - f
        out += bytes(map(_lerp, rows[a], rows[b], repeat(fa), repeat(f)))
    return bytes(out)


def _resize_pixels(px, w, h, n, dw, dh):
    kx, ky = max(1, w // dw), max(1, h // dh)
    if kx > 1 or ky > 1:
        px, w, h = _box_shrink(px, w, h, n, kx, ky)
    return _bilinear(px, w, h, n, dw, dh)


def _pil_from_file(path, max_side):
    im = _PILImage.open(path)
    try:
        im = _PILOps.exif_transpose(im)  # photos taken sideways on a phone
    except Exception:
        pass
    im.load()
    alpha = im.mode in ("RGBA", "LA", "PA", "La", "RGBa") or (im.mode == "P" and "transparency" in im.info)
    im = im.convert("RGBA" if alpha else "RGB")
    if im.mode == "RGBA" and im.getextrema()[3][0] == 255:
        im = im.convert("RGB")
    if max(im.size) > max_side:
        im.thumbnail((max_side, max_side), _LANCZOS)
    buf = io.BytesIO()
    im.save(buf, "PNG", optimize=True)
    return buf.getvalue(), im.size


# Windows can convert JPG/BMP/TIFF pictures itself (no Pillow needed) through PowerShell.
_PS_CONVERT = r"""
$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.Drawing
$src = '%(src)s'
$dst = '%(dst)s'
$max = %(max)d
$img = [System.Drawing.Image]::FromFile($src)
try {
  if ($img.PropertyIdList -contains 274) {
    $o = [int][BitConverter]::ToUInt16($img.GetPropertyItem(274).Value, 0)
    $t = @{2='RotateNoneFlipX'; 3='Rotate180FlipNone'; 4='Rotate180FlipX'; 5='Rotate90FlipX';
           6='Rotate90FlipNone'; 7='Rotate270FlipX'; 8='Rotate270FlipNone'}
    if ($t.ContainsKey($o)) { $img.RotateFlip([System.Drawing.RotateFlipType]$t[$o]) }
  }
  $s = [Math]::Min(1.0, $max / [double][Math]::Max($img.Width, $img.Height))
  $w = [Math]::Max(1, [int][Math]::Round($img.Width * $s))
  $h = [Math]::Max(1, [int][Math]::Round($img.Height * $s))
  $bmp = New-Object System.Drawing.Bitmap -ArgumentList $w, $h, ([System.Drawing.Imaging.PixelFormat]::Format32bppArgb)
  $g = [System.Drawing.Graphics]::FromImage($bmp)
  $g.InterpolationMode = [System.Drawing.Drawing2D.InterpolationMode]::HighQualityBicubic
  $g.PixelOffsetMode = [System.Drawing.Drawing2D.PixelOffsetMode]::HighQuality
  $g.CompositingQuality = [System.Drawing.Drawing2D.CompositingQuality]::HighQuality
  $ia = New-Object System.Drawing.Imaging.ImageAttributes
  $ia.SetWrapMode([System.Drawing.Drawing2D.WrapMode]::TileFlipXY)
  $rect = New-Object System.Drawing.Rectangle -ArgumentList 0, 0, $w, $h
  $g.DrawImage($img, $rect, 0, 0, $img.Width, $img.Height, [System.Drawing.GraphicsUnit]::Pixel, $ia)
  $g.Dispose()
  $bmp.Save($dst, [System.Drawing.Imaging.ImageFormat]::Png)
  $bmp.Dispose()
} finally {
  $img.Dispose()
}
"""


def _windows_convert(path, max_side):
    """Convert any picture Windows understands to a resized PNG (bytes), or None."""
    if os.name != "nt":
        return None
    tmp = tempfile.mkdtemp(prefix="circuit_pic_")
    try:
        dst = os.path.join(tmp, "picture.png")
        script = _PS_CONVERT % {"src": os.path.abspath(path).replace("'", "''"),
                                "dst": dst.replace("'", "''"), "max": max_side}
        enc = base64.b64encode(script.encode("utf-16-le")).decode("ascii")
        si = subprocess.STARTUPINFO()
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        subprocess.run(["powershell.exe", "-NoProfile", "-NonInteractive", "-EncodedCommand", enc],
                       stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       timeout=60, startupinfo=si,
                       creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0x08000000))
        if os.path.isfile(dst):
            with open(dst, "rb") as f:
                return f.read()
    except (OSError, ValueError, subprocess.SubprocessError):
        pass
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return None


def _picture_dict(png):
    w, h = png_size(png)
    return {"data": base64.b64encode(png).decode("ascii"), "w": w, "h": h}


def load_picture(path, max_side=PICTURE_MAX):
    """Read a picture file -> {"data": base64 PNG, "w": .., "h": ..}.  Raises PictureError."""
    if not os.path.isfile(path):
        raise PictureError("The file could not be found:\n%s" % path)
    if _PILImage is not None:
        try:
            return _picture_dict(_pil_from_file(path, max_side)[0])
        except Exception:
            pass
    ext = os.path.splitext(path)[1].lower()
    if ext in (".png", ".gif", ".ppm", ".pgm", ".pnm"):
        try:
            photo = tk.PhotoImage(file=path)
            w, h, n, px = _premultiply(*_photo_pixels(photo))
            del photo
            if max(w, h) > max_side:
                dw, dh = fit_size(w, h, max_side, max_side)
                px, w, h = _resize_pixels(px, w, h, n, dw, dh), dw, dh
            return _picture_dict(png_encode(_unpremultiply(n, px), w, h, n, level=9, up_filter=True))
        except (tk.TclError, ValueError, zlib.error, struct.error):
            pass
    png = _windows_convert(path, max_side)
    if png:
        try:
            return _picture_dict(png)
        except (ValueError, struct.error):
            pass
    msg = ("Circuit Builder couldn't read this picture.\n\n"
           "Save it as a PNG file and try again (for example, open it in Paint "
           "and choose File › Save as › PNG picture).")
    if os.name != "nt" and _PILImage is None:
        msg += "\n\nInstalling Pillow (pip install pillow) also lets Circuit Builder open JPG files."
    raise PictureError(msg)


class PictureCache:
    """Turns stored pictures into Tk images of any size.  Results are cached."""
    LIMIT = 96

    def __init__(self):
        self._src = {}                 # picture key -> decoded picture
        self._shrunk = OrderedDict()   # (key, kx, ky) -> block-averaged pixels (no-Pillow path)
        self._photos = OrderedDict()   # (key, w, h) -> tk.PhotoImage (or None if it failed)
        self.sources = {}              # Tk image name -> base64 PNG of the full picture (SVG export)

    def photo(self, img, w, h, key=None):
        key = key or picture_key(img)
        k = (key, int(w), int(h))
        if k in self._photos:
            self._photos.move_to_end(k)
            return self._photos[k]
        try:
            ph = self._make(key, img, int(w), int(h))
        except Exception:
            ph = None
        self._photos[k] = ph
        if ph is not None:
            self.sources[str(ph)] = img["data"]
        while len(self._photos) > self.LIMIT:
            _k, old = self._photos.popitem(last=False)
            if old is not None:
                self.sources.pop(str(old), None)
        return ph

    def _make(self, key, img, w, h):
        src = self._src.get(key)
        if _PILImage is not None:
            if src is None:
                src = _PILImage.open(io.BytesIO(base64.b64decode(img["data"])))
                src.load()
                if src.mode not in ("RGB", "RGBA"):
                    src = src.convert("RGBA")
                self._src[key] = src
            im = src if src.size == (w, h) else src.resize((w, h), _LANCZOS)
            buf = io.BytesIO()
            im.save(buf, "PNG", compress_level=1)
            return tk.PhotoImage(data=buf.getvalue())
        if src is None:
            photo = tk.PhotoImage(data=img["data"])
            src = _premultiply(*_photo_pixels(photo))
            del photo
            self._src[key] = src
        sw, sh, n, px = src
        kx, ky = max(1, sw // w), max(1, sh // h)
        if kx > 1 or ky > 1:
            sk = (key, kx, ky)
            if sk not in self._shrunk:
                self._shrunk[sk] = _box_shrink(px, sw, sh, n, kx, ky)
                while len(self._shrunk) > 24:
                    self._shrunk.popitem(last=False)
            px, sw, sh = self._shrunk[sk]
        out = _bilinear(px, sw, sh, n, w, h)
        return tk.PhotoImage(data=png_encode(_unpremultiply(n, out), w, h, n, level=1))


PICTURES = PictureCache()


def picture_photo(img, max_w, max_h, key=None):
    """Tk image of a stored picture, scaled to fit inside max_w x max_h pixels."""
    w, h = fit_size(img["w"], img["h"], max(1, max_w), max(1, max_h))
    return PICTURES.photo(img, w, h, key)


class Library:
    def __init__(self):
        self.path = os.path.join(data_dir(), "my_components" + LIB_EXT)
        self.builtin = {d["id"]: d for d in BUILTIN_DEFS}
        self.custom = {}
        self._cache = {}
        self.problem = None   # message for the student if the library file was damaged
        data = {}
        if os.path.exists(self.path):
            data = load_json(self.path, None)
            if not isinstance(data, dict) or not isinstance(data.get("components", []), list):
                # Don't start from an empty library and overwrite the file on the next save:
                # keep a copy so the parts can be recovered.
                self.problem = self._backup("Your component library file could not be read")
                data = {}
        bad = 0
        for d in data.get("components", []):
            cd = clean_def(d)
            if cd is None or cd["id"] in self.builtin:
                bad += 1
                continue
            cd["custom"] = True
            self.custom[cd["id"]] = cd
        if bad and not self.problem:
            self.problem = self._backup("%d damaged component%s in your library could not be loaded"
                                        % (bad, "" if bad == 1 else "s"))

    def _backup(self, what):
        dst = "%s.damaged-%s" % (self.path, time.strftime("%Y%m%d-%H%M%S"))
        try:
            shutil.copy2(self.path, dst)
            return "%s. A copy of the old file was saved as:\n%s" % (what, dst)
        except OSError:
            return "%s." % what

    def get(self, did):
        return self.custom.get(did) or self.builtin.get(did)

    def resolve(self, did):
        if did not in self._cache:
            d = self.get(did)
            if d is None:
                return None
            self._cache[did] = RDef(d)
        return self._cache[did]

    def all(self):
        return list(self.builtin.values()) + list(self.custom.values())

    def categories(self):
        cats = list(CATEGORY_ORDER)
        for d in self.custom.values():
            if d.get("category") and d["category"] not in cats:
                cats.append(d["category"])
        return cats

    def save_def(self, d, persist=True):
        d["custom"] = True
        self.custom[d["id"]] = d
        self._cache.pop(d["id"], None)
        if persist:
            self.persist()

    def remap_nested(self, did, mapping):
        """Part type `did` changed its pins (old pin number -> new pin number in `mapping`).  Fix the
        circuits inside other components that use it, so their wires stay on the same-named pins.
        Returns how many inner wires had to be removed because their pin is gone."""
        dropped, touched = 0, False
        for od in self.custom.values():
            sub = od.get("subcircuit")
            if not sub or od["id"] == did:
                continue
            users = {c.get("id") for c in sub.get("comps", []) if c.get("def") == did}
            if not users:
                continue
            touched = True
            keep = []
            for w in sub.get("wires", []):
                ok = True
                for end in ("a", "b"):
                    e = w.get(end)
                    if e and e[0] in users:
                        if e[1] in mapping:
                            w[end] = [e[0], mapping[e[1]]]
                        else:
                            ok = False
                if ok:
                    keep.append(w)
                else:
                    dropped += 1
            sub["wires"] = keep
            for p in od.get("pins", []):
                inn = p.get("inner")
                if inn and inn[0] in users:
                    if inn[1] in mapping:
                        p["inner"] = [inn[0], mapping[inn[1]]]
                    else:
                        p.pop("inner", None)
            self._cache.pop(od["id"], None)
        if touched:
            self.persist()
        return dropped

    def delete(self, did):
        self.custom.pop(did, None)
        self._cache.pop(did, None)
        self.persist()

    def persist(self):
        try:
            save_json(self.path, {"format": "circuit-builder-library", "version": 1,
                                  "components": list(self.custom.values())})
        except OSError as e:
            messagebox.showerror(APP_NAME, "Could not save your component library:\n%s" % e)

    def parts_inside(self, did):
        """Ids of every part type used inside a component built from a circuit (all levels)."""
        out, todo = set(), [did]
        while todo:
            d = self.get(todo.pop())
            for c in ((d or {}).get("subcircuit") or {}).get("comps", []):
                if c.get("def") not in out:
                    out.add(c.get("def"))
                    todo.append(c.get("def"))
        return out

    def with_dependencies(self, ids):
        """These custom definitions plus every custom part used inside them (for saving and sharing)."""
        ids = set(ids)
        for did in list(ids):
            ids |= self.parts_inside(did)
        return [self.custom[d] for d in ids if d in self.custom]

    def used_inside(self, did):
        """Names of custom components whose circuit contains this part type."""
        return [d.get("name", "?") for d in self.custom.values()
                if d["id"] != did and did in self.parts_inside(d["id"])]


# --------------------------------------------------------------------------
# Nets, and components built from circuits
# --------------------------------------------------------------------------
def compute_nets_of(comps, wires):
    """Group connected pins into nets.  comps: {id: comp}; wires: iterable of wire dicts.
    Every Ground is one net, and so is every Power Rail with the same value."""
    parent = {}

    def find(k):
        parent.setdefault(k, k)
        while parent[k] != k:
            parent[k] = parent[parent[k]]
            k = parent[k]
        return k

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    wires = list(wires)
    wired = set()
    for w in wires:
        a, b = tuple(w["a"]), tuple(w["b"])
        if a[0] in comps and b[0] in comps:
            union(a, b)
            wired.update((a, b))
    rails = {}
    for cid, c in comps.items():
        if c["def"] == "ground" and (cid, 0) in wired:
            rails.setdefault("GND", []).append((cid, 0))
        elif c["def"] == "vcc" and (cid, 0) in wired:
            # "+5 V", "5V" and "5 v" are the same rail (spaces, capitals and a leading + don't matter)
            key = re.sub(r"\s+", "", c.get("value") or "VCC").upper().lstrip("+")
            rails.setdefault("PWR:" + key, []).append((cid, 0))
    for keys in rails.values():
        for k in keys[1:]:
            union(keys[0], k)
    groups = {}
    for k in list(parent):
        groups.setdefault(find(k), []).append(k)
    order = {cid: i for i, cid in enumerate(comps)}
    nets = []
    for g in groups.values():
        g.sort(key=lambda k: (order.get(k[0], 0), k[1]))
        nets.append(g)
    nets.sort(key=lambda g: (order.get(g[0][0], 0), g[0][1]))
    group_of = {k: gi for gi, g in enumerate(nets) for k in g}
    wires_of = [[] for _ in nets]
    for w in wires:
        gi = group_of.get(tuple(w["a"])) if "id" in w else None
        if gi is not None:
            wires_of[gi].append(w["id"])
    out, n, used = [], 1, set()
    for gi, g in enumerate(nets):
        defs = [comps[k[0]]["def"] for k in g]
        name = None
        if "ground" in defs:
            name = "GND"
        else:
            for k in g:
                c = comps[k[0]]
                if c["def"] == "vcc":
                    name = re.sub(r"\s+", "", c.get("value") or "VCC")
                    break
            else:
                # a net with a Component Pin on it takes that pin's name
                for k in g:
                    c = comps[k[0]]
                    if c["def"] == PORT_DEF and c.get("label", "").strip():
                        name = re.sub(r"\s+", "_", c["label"].strip())
                        break
        if not name:
            name = "N%d" % n
            n += 1
        base, i = name, 2
        while name in used:
            name = "%s_%d" % (base, i)
            i += 1
        used.add(name)
        out.append({"name": name, "pins": g, "wires": wires_of[gi]})
    return out


def flatten_circuit(library, comps, wires):
    """Expand every part built from a circuit into the parts inside it (for the simulator).

    Inner parts get ids like  "<instance id>/<inner id>"  and labels like  "HA1/U2".  Each pin of the
    instance is joined to the inner pin it stands for by an extra wire, so the instance's pins share a
    net with the circuit inside.  Returns (comps {id: comp}, wires [..], blocks {instance id: def},
    problems [(instance id, message)])."""
    flat, fw, blocks, problems = {}, [], {}, []

    def add(items, wire_items, pre, lpre, depth, stack):
        for c in items:
            cid = pre + c["id"]
            if pre:
                nc = dict(c)
                nc["id"] = cid
                nc["label"] = lpre + (c.get("label") or "?")
            else:
                nc = c   # the canvas's own part: switches and sliders change it while simulating
            flat[cid] = nc
            d = library.get(c.get("def"))
            sub = (d or {}).get("subcircuit")
            if not sub:
                continue
            if c["def"] in stack or depth >= MAX_NESTING:
                problems.append((pre.split("/", 1)[0] if pre else cid,
                                 "%s isn’t simulated: “%s” contains itself (or is nested more than %d levels "
                                 "deep)." % (nc.get("label") or d.get("name", "?"), d.get("name", "?"), MAX_NESTING)))
                continue
            if not pre:
                blocks[cid] = d
            inner = sub.get("comps", [])
            ipre = cid + "/"
            add(inner, sub.get("wires", []), ipre, (nc.get("label") or d.get("name", "?")) + "/",
                depth + 1, stack | {c["def"]})
            ids = {ic["id"] for ic in inner}
            for k, p in enumerate(d.get("pins", [])):
                inn = p.get("inner")
                if inn and inn[0] in ids:
                    fw.append({"a": [cid, k], "b": [ipre + inn[0], int(inn[1])]})
        for w in wire_items:
            fw.append({"a": [pre + w["a"][0], w["a"][1]], "b": [pre + w["b"][0], w["b"][1]]})

    add(list(comps.values()), list(wires.values()), "", "", 0, frozenset())
    return flat, fw, blocks, problems


# --------------------------------------------------------------------------
# Small widgets
# --------------------------------------------------------------------------
class Tooltip:
    def __init__(self, widget, text):
        self.widget, self.text, self.tip, self.job = widget, text, None, None
        widget.bind("<Enter>", self._enter, add="+")
        widget.bind("<Leave>", self._leave, add="+")
        widget.bind("<ButtonPress>", self._leave, add="+")

    def _enter(self, _e):
        self.job = self.widget.after(550, self._show)

    def _show(self):
        if self.tip:
            return
        x = self.widget.winfo_rootx() + 8
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
        self.tip = tk.Toplevel(self.widget)
        self.tip.wm_overrideredirect(True)
        self.tip.wm_geometry("+%d+%d" % (x, y))
        tk.Label(self.tip, text=self.text, bg=C["tip_bg"], fg=C["tip_fg"], padx=8, pady=4,
                 font=("Segoe UI", 9)).pack()

    def _leave(self, _e=None):
        if self.job:
            self.widget.after_cancel(self.job)
            self.job = None
        if self.tip:
            self.tip.destroy()
            self.tip = None


# ---- switching themes while windows are open
_MENU_DEFAULTS = {}   # the platform's own menu colors, used in light mode
_MENU_OPTS = ("-background", "-foreground", "-activebackground", "-activeforeground",
              "-disabledforeground", "-selectcolor")
_RETHEME_OPTS = ("-background", "-foreground", "-highlightbackground", "-highlightcolor",
                 "-insertbackground", "-activebackground", "-activeforeground", "-disabledforeground",
                 "-troughcolor")
# palette keys that classic widgets use, checked first when two keys share a color
_RETHEME_FIRST = ("bg", "panel", "field", "text", "muted", "border", "canvas", "accent", "accent_dark",
                  "accent_light", "ok", "danger", "warn", "sim_bg", "sim_border", "plot_bg", "tip_bg", "tip_fg")


def remember_menu_defaults(root):
    if _MENU_DEFAULTS:
        return
    m = tk.Menu(root)
    for opt in _MENU_OPTS:
        try:
            _MENU_DEFAULTS[opt] = str(m.cget(opt[1:]))
        except tk.TclError:
            pass
    m.destroy()


def menu_colors():
    if not THEME["dark"]:
        return dict(_MENU_DEFAULTS)
    return {"-background": C["panel"], "-foreground": C["text"], "-activebackground": C["accent_light"],
            "-activeforeground": C["text"], "-disabledforeground": C["disabled"], "-selectcolor": C["text"]}


def apply_option_db(root):
    """Default colors for widgets created from now on (menus, text boxes, drop-down lists)."""
    mc = menu_colors()
    for opt, res in (("-background", "background"), ("-foreground", "foreground"),
                     ("-activebackground", "activeBackground"), ("-activeforeground", "activeForeground"),
                     ("-disabledforeground", "disabledForeground"), ("-selectcolor", "selectColor")):
        if opt in mc:
            root.option_add("*Menu." + res, mc[opt])
    for pat in ("*TCombobox*Listbox", "*Listbox"):
        root.option_add(pat + ".background", C["field"])
        root.option_add(pat + ".foreground", C["text"])
        root.option_add(pat + ".selectBackground", C["accent_btn"])
        root.option_add(pat + ".selectForeground", C["on_btn"])
    root.option_add("*Text.background", C["field"])
    root.option_add("*Text.foreground", C["text"])
    root.option_add("*Text.insertBackground", C["text"])
    root.option_add("*Toplevel.background", C["bg"])


def text_colors():
    """Colors for a tk.Text box."""
    return {"bg": C["field"], "fg": C["text"], "insertbackground": C["text"],
            "selectbackground": C["accent_light"], "selectforeground": C["text"],
            "highlightbackground": C["border"], "highlightcolor": C["accent"]}


def retheme_widgets(root, old, new):
    """Recolor the classic Tk widgets in every open window from the old palette to the new one.
    (ttk widgets follow their styles; canvases are redrawn by their owners.)"""
    tkapp = root.tk
    cmap = {}
    for k in _RETHEME_FIRST + tuple(old):
        if k in old and k in new and k != "arrow":   # "arrow" is Tk's default black: leave it alone
            cmap.setdefault(str(old[k]).lower(), new[k])
    cmap.setdefault("white", new["panel"])
    menu = [x for kv in menu_colors().items() for x in kv]

    def opt_names(path):
        try:
            return {str(tkapp.splitlist(item)[0]) for item in tkapp.splitlist(tkapp.call(path, "configure"))}
        except (tk.TclError, IndexError):
            return set()

    def remap(path, names):
        for opt in _RETHEME_OPTS:
            if opt not in names:
                continue
            try:
                v = str(tkapp.call(path, "cget", opt)).lower()
            except tk.TclError:
                continue
            nv = cmap.get(v)
            if nv and nv.lower() != v:
                try:
                    tkapp.call(path, "configure", opt, nv)
                except tk.TclError:
                    pass

    def walk(path):
        try:
            cls = str(tkapp.call("winfo", "class", path))
        except tk.TclError:
            return
        try:
            if cls == "Menu":
                if menu:
                    tkapp.call(path, "configure", *menu)
            elif cls == "Text":
                tc = text_colors()
                tkapp.call(path, "configure", *[x for k, v in tc.items() for x in ("-" + k, v)])
            elif cls == "Listbox":
                tkapp.call(path, "configure", "-background", C["field"], "-foreground", C["text"],
                           "-selectbackground", C["accent_btn"], "-selectforeground", C["on_btn"])
            else:
                remap(path, opt_names(path))
                if cls == "Treeview":
                    try:
                        tags = tkapp.splitlist(tkapp.call(path, "tag", "names"))
                    except tk.TclError:
                        tags = ("cat", "custom", "gap", "Error", "Warning", "Info")
                    for t in tags:
                        for opt in ("-foreground", "-background"):
                            try:
                                v = str(tkapp.call(path, "tag", "configure", t, opt)).lower()
                            except tk.TclError:
                                continue
                            if v in cmap:
                                tkapp.call(path, "tag", "configure", t, opt, cmap[v])
        except tk.TclError:
            pass
        try:
            kids = tkapp.splitlist(tkapp.call("winfo", "children", path))
        except tk.TclError:
            kids = ()
        for k in kids:
            walk(str(k))

    walk(".")


def set_title_bar_theme(win, dark):
    """Windows 10/11: give the window a dark (or light) title bar to match the app."""
    if os.name != "nt":
        return
    try:
        if win.wm_overrideredirect():
            return
        import ctypes
        hwnd = ctypes.windll.user32.GetParent(win.winfo_id())
        if not hwnd:
            return
        val = ctypes.c_int(1 if dark else 0)
        for attr in (20, 19):   # DWMWA_USE_IMMERSIVE_DARK_MODE (19 on early Windows 10 builds)
            if ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(val), ctypes.sizeof(val)) == 0:
                break
        # NOSIZE | NOMOVE | NOZORDER | NOACTIVATE | FRAMECHANGED: repaint the frame now
        ctypes.windll.user32.SetWindowPos(hwnd, 0, 0, 0, 0, 0, 0x37)
    except Exception:
        pass


def fit_preview(cv, rd, fam, label=None, value=None, max_zoom=1.4):
    """Draw a definition centred and scaled to fit a preview canvas."""
    cv.delete("all")
    W = max(cv.winfo_width(), int(cv.cget("width")))
    H = max(cv.winfo_height(), int(cv.cget("height")))
    if W < 20 or H < 20:
        W, H = int(cv.cget("width")), int(cv.cget("height"))
    x0, y0, x1, y1 = rd.bbox
    bw, bh = (x1 - x0) + 2.4, (y1 - y0) + 2.4
    z = min(W / (bw * G), H / (bh * G), max_zoom)
    comp = {"x": 0, "y": 0, "rot": 0, "flip": False,
            "label": label if label is not None else rd.prefix + "1",
            "value": rd.value if value is None else value}
    cx = (x0 + x1) / 2.0 - rd.pivot[0]
    cy = (y0 + y1) / 2.0 - rd.pivot[1]
    ox = W / 2.0 - cx * G * z
    oy = H / 2.0 - cy * G * z
    render_component(cv, rd, comp, lambda wx, wy: (ox + wx * G * z, oy + wy * G * z), z, fam)


# --------------------------------------------------------------------------
# Chip logic: Boolean equations that make a part simulate as a digital chip
# --------------------------------------------------------------------------
# A part's "logic" is plain text, one statement per line, for example
#
#     Y = A & B                 # an output that follows its inputs (combinational)
#     Q = D on CLK              # Q takes the value of D on each rising edge of CLK
#     Q = 0 when !CLR           # while CLR is LOW, Q is forced to 0 (overrides the clock)
#     S = A ^ B                 # XOR;  !A  ~A  A'  not A  all mean NOT A
#
# Names are the part's pin names; any other name on the left of "=" is an internal signal.
# Pins called VCC / GND (and similar) power the chip: outputs swing between them.

LOGIC_HELP = (
    "One statement per line.  # starts a comment.\n"
    "\n"
    "Y = A & B          output follows its inputs\n"
    "Q = D on CLK       Q takes D at each rising edge of CLK\n"
    "Q = D on fall CLK  … at each falling edge instead\n"
    "Q = 1 when !PRE    forced while the condition is 1\n"
    "Q = D when EN      a latch: follows D while EN is 1\n"
    "\n"
    "AND   A & B    A * B    A and B\n"
    "OR    A | B    A + B    A or B\n"
    "XOR   A ^ B    A xor B\n"
    "NOT   !A   ~A   A'   not A\n"
    "Constants 0 and 1.  Brackets ( ) group.\n"
    "Order: NOT first, then AND, then XOR, then OR.\n"
    "\n"
    "Use the pin names exactly. Write a name with spaces\n"
    "or symbols in quotes, e.g. \"D0 RX\".\n"
    "Other names on the left of = are internal signals.\n"
    "Pins named VCC and GND power the chip.")

LOGIC_TEMPLATES = [
    ("Quad 2-input NAND (like 74HC00)",
     ["1A", "1B", "1Y", "2A", "2B", "2Y", "GND", "3Y", "3A", "3B", "4Y", "4A", "4B", "VCC"],
     "# Four NAND gates. VCC and GND power the chip.\n"
     "1Y = !(1A & 1B)\n2Y = !(2A & 2B)\n3Y = !(3A & 3B)\n4Y = !(4A & 4B)\n"),
    ("Half adder", ["A", "B", "SUM", "CARRY"],
     "# Adds two bits\nSUM = A ^ B\nCARRY = A & B\n"),
    ("Full adder", ["A", "B", "CIN", "SUM", "COUT"],
     "# Adds two bits plus a carry in\nSUM = A ^ B ^ CIN\nCOUT = (A & B) | (CIN & (A ^ B))\n"),
    ("2-to-1 multiplexer", ["A", "B", "SEL", "Y"],
     "# Y = A when SEL is 0, B when SEL is 1\nY = (A & !SEL) | (B & SEL)\n"),
    ("2-to-4 decoder", ["A0", "A1", "EN", "Y0", "Y1", "Y2", "Y3"],
     "# Exactly one output is 1 (while EN is 1)\n"
     "Y0 = EN & !A1 & !A0\nY1 = EN & !A1 & A0\nY2 = EN & A1 & !A0\nY3 = EN & A1 & A0\n"),
    ("Majority vote (3 inputs)", ["A", "B", "C", "Y"],
     "# 1 when at least two inputs are 1\nY = (A & B) | (A & C) | (B & C)\n"),
    ("D latch", ["D", "EN", "Q", "Q'"],
     "# Q follows D while EN is 1, and holds when EN goes to 0\nQ = D when EN\nQ' = !Q\n"),
    ("D flip-flop with reset", ["D", "CLK", "RST", "Q", "Q'"],
     "# Q takes D on each rising edge of CLK; RST = 1 clears it\nQ = 0 when RST\nQ = D on CLK\nQ' = !Q\n"),
    ("4-bit binary counter", ["CLK", "RST", "Q0", "Q1", "Q2", "Q3"],
     "# Counts 0, 1, 2 … 15 on each rising edge of CLK. RST = 1 clears it.\n"
     "Q0 = 0 when RST\nQ1 = 0 when RST\nQ2 = 0 when RST\nQ3 = 0 when RST\n"
     "Q0 = !Q0 on CLK\nQ1 = Q1 ^ Q0 on CLK\nQ2 = Q2 ^ (Q1 & Q0) on CLK\nQ3 = Q3 ^ (Q2 & Q1 & Q0) on CLK\n"),
    ("4-bit shift register", ["DIN", "CLK", "Q0", "Q1", "Q2", "Q3"],
     "# On each rising edge every bit moves one place along\n"
     "Q0 = DIN on CLK\nQ1 = Q0 on CLK\nQ2 = Q1 on CLK\nQ3 = Q2 on CLK\n"),
    ("Traffic light sequencer", ["CLK", "RED", "AMBER", "GREEN"],
     "# Steps RED → GREEN → AMBER → RED on each clock edge (two internal state bits)\n"
     "S0 = !S0 & !S1 on CLK\nS1 = S0 on CLK\n"
     "RED = !S0 & !S1\nGREEN = S0\nAMBER = S1\n"),
]


class LogicError(Exception):
    def __init__(self, msg, line=None):
        Exception.__init__(self, msg)
        self.msg = msg
        self.line = line

    def __str__(self):
        return ("Line %d: %s" % (self.line, self.msg)) if self.line else self.msg


_KEYWORDS = {"and": "AND", "or": "OR", "xor": "XOR", "not": "NOT", "on": "ON", "when": "WHEN", "if": "WHEN",
             "rise": "RISE", "rising": "RISE", "fall": "FALL", "falling": "FALL"}
_OPS = {"&": "AND", "*": "AND", "·": "AND", "∧": "AND", "|": "OR", "+": "OR", "∨": "OR", "^": "XOR", "⊕": "XOR",
        "!": "NOT", "~": "NOT", "¬": "NOT", "'": "POST", "’": "POST", "(": "(", ")": ")", "=": "="}
_IDENT_RX = re.compile(r"[A-Za-z0-9_]+")


def _ident_char(ch):
    return ch.isalnum() or ch == "_"


def _tokenize(s, pin_names, line):
    """Split one statement into (kind, value) tokens.  Pin names (even ones with symbols) win."""
    names = sorted({n for n in pin_names if n}, key=len, reverse=True)
    out, i, n = [], 0, len(s)
    while i < n:
        ch = s[i]
        if ch.isspace():
            i += 1
            continue
        if ch in "\"“”":
            j = i + 1
            while j < n and s[j] not in "\"“”":
                j += 1
            if j >= n:
                raise LogicError("a name in quotes is missing its closing \"", line)
            out.append(("NAME", s[i + 1:j].strip()))
            i = j + 1
            continue
        if s.startswith(":=", i) or s.startswith("<=", i):
            out.append(("=", "="))
            i += 2
            continue
        hit = None
        for nm in names:
            if s.startswith(nm, i) and (i + len(nm) >= n or not (_ident_char(s[i + len(nm)]) and _ident_char(nm[-1]))):
                if _ident_char(nm[0]) and i > 0 and _ident_char(s[i - 1]):
                    continue
                hit = nm
                break
        m = _IDENT_RX.match(s, i)
        word = m.group(0) if m else None
        if word and word in _KEYWORDS and not (hit and len(hit) > len(word)):
            out.append((_KEYWORDS[word], word))
            i += len(word)
            continue
        if hit and (not word or len(hit) >= len(word)):
            out.append(("NAME", hit))
            i += len(hit)
            continue
        if word:
            if word.isdigit():
                if word not in ("0", "1"):
                    raise LogicError("only the numbers 0 and 1 can be used (found %s)" % word, line)
                out.append(("NUM", int(word)))
            else:
                out.append(("NAME", word))
            i += len(word)
            continue
        if ch in _OPS:
            out.append((_OPS[ch], ch))
            i += 1
            continue
        raise LogicError("didn’t understand “%s”" % ch, line)
    return out


class _Parser:
    def __init__(self, toks, line):
        self.t = toks
        self.i = 0
        self.line = line
        self.used = []

    def peek(self):
        return self.t[self.i][0] if self.i < len(self.t) else None

    def take(self, kind=None):
        if self.i >= len(self.t):
            raise LogicError("the line ends too early" + (" (expected %s)" % kind.lower() if kind and kind != "NAME" else ""), self.line)
        tok = self.t[self.i]
        if kind and tok[0] != kind:
            raise LogicError("expected %s but found “%s”" % ({"NAME": "a name", ")": "“)”", "=": "“=”"}.get(kind, kind.lower()),
                                                             tok[1]), self.line)
        self.i += 1
        return tok

    # expr := xor ('OR' xor)* ; xor := and ('XOR' and)* ; and := unary ('AND' unary)*
    def expr(self):
        a = self.xor()
        while self.peek() == "OR":
            self.take()
            a = ("or", a, self.xor())
        return a

    def xor(self):
        a = self.and_()
        while self.peek() == "XOR":
            self.take()
            a = ("xor", a, self.and_())
        return a

    def and_(self):
        a = self.unary()
        while self.peek() == "AND":
            self.take()
            a = ("and", a, self.unary())
        return a

    def unary(self):
        if self.peek() == "NOT":
            self.take()
            return ("not", self.unary())
        a = self.atom()
        while self.peek() == "POST":
            self.take()
            a = ("not", a)
        return a

    def atom(self):
        k = self.peek()
        if k == "(":
            self.take()
            a = self.expr()
            self.take(")")
            return a
        if k == "NUM":
            return ("num", self.take()[1])
        if k == "NAME":
            nm = self.take()[1]
            self.used.append(nm)
            return ("name", nm)
        if k is None:
            raise LogicError("the line ends too early", self.line)
        tok = self.t[self.i]
        if tok[0] == "NAME" or tok[1].isalnum():
            raise LogicError("expected a signal name but found “%s”" % tok[1], self.line)
        raise LogicError("expected a signal name, 0, 1 or “(” but found “%s”" % tok[1], self.line)


def _code(node, idx):
    k = node[0]
    if k == "num":
        return str(node[1])
    if k == "name":
        return "s[%d]" % idx[node[1]]
    if k == "not":
        return "(1-%s)" % _code(node[1], idx)
    op = {"and": "&", "or": "|", "xor": "^"}[k]
    return "(%s%s%s)" % (_code(node[1], idx), op, _code(node[2], idx))


class LogicProgram:
    """Parsed chip logic, ready to evaluate.  pins: the part's pin names in order."""

    def __init__(self, text, pins):
        self.text = text or ""
        self.pins = list(pins)
        self.power = [p for p in self.pins if is_power_pin(p)]
        self.ground = [p for p in self.pins if is_ground_pin(p)]
        stmts = []
        for ln, raw in enumerate(self.text.splitlines(), 1):
            line = re.split(r"#|//", raw, 1)[0]
            for part in line.split(";"):
                if part.strip():
                    stmts.append((ln, part))
        self.comb, self.when, self.clocked = {}, {}, {}
        used = []
        targets_line = {}
        for ln, src in stmts:
            toks = _tokenize(src, self.pins, ln)
            if len(toks) < 3 or toks[0][0] != "NAME" or toks[1][0] != "=":
                if toks and toks[0][0] == "NAME" and (len(toks) < 2 or toks[1][0] != "="):
                    raise LogicError("expected “=” after %s (write it like  Y = A & B)" % toks[0][1], ln)
                raise LogicError("each line should look like  Y = A & B", ln)
            name = toks[0][1]
            if name in self.power or name in self.ground:
                raise LogicError("%s is a power pin, so it can’t be set by the logic" % name, ln)
            p = _Parser(toks, ln)
            p.i = 2
            ex = p.expr()
            kind, extra = "comb", None
            if p.peek() == "ON":
                p.take()
                edge = "rise"
                if p.peek() in ("RISE", "FALL"):
                    edge = "rise" if p.take()[0] == "RISE" else "fall"
                paren = p.peek() == "("
                if paren:
                    p.take()
                clk = p.take("NAME")[1]
                if paren:
                    p.take(")")
                p.used.append(clk)
                kind, extra = "clocked", (clk, edge)
            elif p.peek() == "WHEN":
                p.take()
                kind, extra = "when", p.expr()
            if p.peek() is not None:
                tok = p.t[p.i]
                hint = ""
                if tok[0] == "NAME" and p.t[p.i - 1][0] == "NAME":
                    hint = " (put an operator such as & or | between two names)"
                raise LogicError("didn’t expect “%s” here%s" % (tok[1], hint), ln)
            used += [(u, ln) for u in p.used]
            prev = targets_line.get(name)
            if kind == "comb":
                if prev is not None:
                    raise LogicError("%s is already set on line %d. A signal that follows its inputs can only be "
                                     "set once." % (name, prev[0]), ln)
                self.comb[name] = (ex, ln)
            else:
                if prev is not None and prev[1] == "comb":
                    raise LogicError("%s is already set on line %d without “on” or “when”." % (name, prev[0]), ln)
                if kind == "clocked":
                    if name in self.clocked:
                        raise LogicError("%s already has a clock on line %d" % (name, self.clocked[name][2]), ln)
                    self.clocked[name] = (ex, extra, ln)
                else:
                    self.when.setdefault(name, []).append((ex, extra, ln))
            targets_line.setdefault(name, (ln, kind))
        if not stmts:
            raise LogicError("there is no logic yet")
        assigned = set(targets_line)
        dup = {p for p in self.pins if self.pins.count(p) > 1 and not (is_power_pin(p) or is_ground_pin(p))}
        for nm, ln in used:
            if nm not in assigned and nm not in self.pins:
                hint = ""
                if len(nm) > 1 and all(c in self.pins for c in nm):
                    hint = " To AND signals together write %s." % " & ".join(nm)
                else:
                    close = [p for p in self.pins if p.lower() == nm.lower()]
                    if close:
                        hint = " Did you mean %s? Names must match exactly." % close[0]
                raise LogicError("there is no pin or signal called %s.%s" % (nm, hint), ln)
            if nm in self.power or nm in self.ground:
                raise LogicError("%s is a power pin; use a logic input instead" % nm, ln)
        for nm in list(assigned) + [u for u, _ in used]:
            if nm in dup:
                raise LogicError("more than one pin is called %s, so the logic can’t tell them apart. "
                                 "Rename the pins first." % nm, targets_line.get(nm, (None,))[0])
        self.states = [n for n in assigned if n not in self.comb]
        self.outputs = [p for p in dict.fromkeys(self.pins) if p in assigned]
        self.internal = [n for n in assigned if n not in self.pins]
        self.inputs = [p for p in dict.fromkeys(self.pins) if p not in assigned and p in {u for u, _ in used}]
        self.clocks = list(dict.fromkeys(c for (_e, (c, _g), _l) in self.clocked.values()))
        self.names = list(dict.fromkeys(self.inputs + self.outputs + self.internal))
        idx = {n: i for i, n in enumerate(self.names)}
        self.idx = idx
        # combinational signals in an order where each only uses ones computed before it
        deps = {n: {u for u in self._names_in(e) if u in self.comb} for n, (e, _l) in self.comb.items()}
        order, done, visiting = [], set(), []

        def visit(n):
            if n in done:
                return
            if n in visiting:
                loop = visiting[visiting.index(n):] + [n]
                raise LogicError("%s depend on each other in a loop (%s). Break the loop with a clock "
                                 "(“on CLK”) or a latch (“when”)." % (" and ".join(sorted(set(loop))), " → ".join(loop)),
                                 self.comb[n][1])
            visiting.append(n)
            for m in sorted(deps[n]):
                visit(m)
            visiting.pop()
            done.add(n)
            order.append(n)

        for n in self.comb:
            visit(n)
        # each equation becomes a small Python function of the signal list s (built from the parsed
        # equation, never from the raw text, so only s[..], 0, 1 and & | ^ - can appear in it)
        def comp(e):
            try:
                return eval("lambda s: %s" % _code(e, idx), {"__builtins__": {}})
            except (SyntaxError, RecursionError, MemoryError):
                raise LogicError("an equation is too deeply nested (use fewer brackets)")
        self.comb_code = [(idx[n], comp(self.comb[n][0])) for n in order]
        self.when_code = {n: [(comp(e), comp(c)) for e, c, _l in lst] for n, lst in self.when.items()}
        self.clock_code = {n: (comp(e), idx[c], g) for n, (e, (c, g), _l) in self.clocked.items()}
        self.state_idx = [idx[n] for n in self.states]

    @staticmethod
    def _names_in(e):
        if e[0] == "name":
            return {e[1]}
        if e[0] == "num":
            return set()
        return set().union(*(LogicProgram._names_in(x) for x in e[1:]))

    @staticmethod
    def _ev(fn, s):
        return fn(s) & 1

    def settle(self, s):
        for i, code in self.comb_code:
            s[i] = self._ev(code, s)

    def step(self, s, prev_clk):
        """s: values (inputs already set, states hold their stored values).  prev_clk: {index: level}
        from the previous call (updated here).  Computes new states and outputs.  Returns s."""
        for _round in range(16):
            self.settle(s)
            edges = {}
            for name in self.clocks:
                i = self.idx[name]
                old = prev_clk.get(i)
                edges[i] = (None if old is None else ("rise" if (not old and s[i]) else "fall" if (old and not s[i]) else None))
                prev_clk[i] = s[i]
            new = {}
            for name in self.states:
                i = self.idx[name]
                val = None
                for e, c in self.when_code.get(name, ()):
                    if self._ev(c, s):
                        val = self._ev(e, s)
                        break
                if val is None and name in self.clock_code:
                    e, ci, g = self.clock_code[name]
                    if edges.get(ci) == g:
                        val = self._ev(e, s)
                if val is not None and val != s[i]:
                    new[i] = val
            for i, v in new.items():
                s[i] = v
            self.settle(s)
            # a state change may have moved an internal clock (e.g. a ripple counter): go round again
            again = any(prev_clk.get(self.idx[c]) != s[self.idx[c]] for c in self.clocks)
            if not new or not again:
                break
        return s

    def summary(self):
        parts = []
        if self.inputs:
            parts.append("Inputs: " + ", ".join(self.inputs))
        if self.outputs:
            parts.append("Outputs: " + ", ".join(self.outputs))
        if self.internal:
            parts.append("Internal: " + ", ".join(self.internal))
        if self.power or self.ground:
            parts.append("Power: " + ", ".join(dict.fromkeys(self.power + self.ground)))
        else:
            parts.append("No VCC/GND pins: runs as 5 V logic")
        return "   ·   ".join(parts)

    def truth_table(self, limit=8):
        """(columns, rows) for the table shown in the editor, or (None, message) when it is too big."""
        clock_only = [c for c in self.clocks if c in self.inputs and
                      all(c not in self._names_in(e) for e, _l in self.comb.values()) and
                      all(c not in self._names_in(e) and c not in self._names_in(cn)
                          for lst in self.when.values() for e, cn, _l in lst) and
                      all(c not in self._names_in(e) for e, _c, _l in self.clocked.values())]
        ins = [n for n in self.inputs if n not in clock_only]
        st = list(self.states)
        variables = ins + st
        if len(variables) > limit:
            return None, ("Too many inputs for a table (%d). Up to %d fit; try the part in the simulator instead."
                          % (len(variables), limit))
        comb_names = [nm for nm in self.names if nm in self.comb]
        cols = ([(n, "in") for n in ins] + [(n + " now", "in") for n in st]
                + [(n, "out") for n in comb_names]
                + [(n + (" after %s%s" % (self.clocked[n][1][0], "↑" if self.clocked[n][1][1] == "rise" else "↓")
                         if n in self.clocked else " next"), "out") for n in st])
        rows = []
        for k in range(2 ** len(variables)):
            s = [0] * len(self.names)
            bits = [(k >> (len(variables) - 1 - j)) & 1 for j in range(len(variables))]
            for n, b in zip(variables, bits):
                s[self.idx[n]] = b
            self.settle(s)
            out = [s[self.idx[n]] for n in comb_names]
            nxt = []
            for n in st:
                val = None
                for e, c in self.when_code.get(n, ()):
                    if self._ev(c, s):
                        val = self._ev(e, s)
                        break
                if val is None and n in self.clock_code:
                    val = self._ev(self.clock_code[n][0], s)
                nxt.append(s[self.idx[n]] if val is None else val)
            rows.append(bits + out + nxt)
        return cols, rows


_LOGIC_CACHE = {}


def logic_program(text, pins):
    """Cached LogicProgram (or the LogicError it raises)."""
    key = (text, tuple(pins))
    if key not in _LOGIC_CACHE:
        if len(_LOGIC_CACHE) > 200:
            _LOGIC_CACHE.clear()
        try:
            _LOGIC_CACHE[key] = LogicProgram(text, pins)
        except LogicError as e:
            _LOGIC_CACHE[key] = e
        except RecursionError:
            _LOGIC_CACHE[key] = LogicError("an equation is too deeply nested")
    return _LOGIC_CACHE[key]


# --------------------------------------------------------------------------
# Component editor
# --------------------------------------------------------------------------
class ComponentEditor(tk.Toplevel):
    SIDES = ["left", "right", "top", "bottom"]

    def __init__(self, app, d=None, duplicate=False, image=None, use_for=None, from_selection=None):
        """image: start with this picture.  use_for: id of a placed part that should switch
        to the saved component (used when adding a picture to a built-in part).
        from_selection: made by App._selection_spec when the student turns selected parts into a component."""
        super().__init__(app.root)
        self.app = app
        self.fam = app.fam
        s = app.ui_scale
        self.from_sel = from_selection
        self.title(("Make a Component from Your Circuit — " if from_selection else "Component Editor — ") + APP_NAME)
        self.configure(bg=C["bg"])
        self.transient(app.root)
        self.geometry("%dx%d" % (int(1100 * s), int(700 * s)))
        self.minsize(int(960 * s), int(640 * s))
        d = copy.deepcopy(d) if d else {"name": "", "category": "My Components", "prefix": "U",
                                        "value": "", "description": "", "color": BODY_COLORS[0],
                                        "pins": [], "symbol": "box", "w": 4, "h": 3}
        self.edit_id = d.get("id") if (d.get("custom") and not duplicate) else None
        self.source_name = d.get("name", "")
        self.use_for = use_for
        # a component built from a circuit works like the circuit inside it
        self.subcircuit = copy.deepcopy(d.get("subcircuit")) or None
        # a copy of a built-in part keeps that part's simulation model (it is matched by pin names)
        self.sim_model = None if self.subcircuit else (
            d.get("sim") or (d.get("id") if (not d.get("custom") and d.get("id") in SIM_MODELS) else None))
        if image is not None:
            d["image"] = image
        if duplicate:
            if image is None:
                d["name"] = d.get("name", "") + " (copy)"
            if not d.get("custom"):
                d["category"] = "My Components"
        self.image = d.get("image") if valid_picture(d.get("image")) else None
        self.logic = d.get("logic", "") or ""
        self._thumb = None
        self.rows = self._rows_from_def(d)
        self._sync = False

        self.v_name = tk.StringVar(value=d.get("name", ""))
        self.v_cat = tk.StringVar(value=d.get("category", "My Components"))
        self.v_prefix = tk.StringVar(value=d.get("prefix", "U"))
        self.v_value = tk.StringVar(value=d.get("value", ""))
        self.v_color = tk.StringVar(value=d.get("color", BODY_COLORS[0]))
        need_w, need_h = self._needed_size()
        w0, h0 = int(d.get("w", need_w)), int(d.get("h", need_h))
        is_new = not d.get("id")
        self.v_auto = tk.BooleanVar(value=is_new or (d.get("symbol", "box") != "box") or (w0 <= need_w and h0 <= need_h))
        self.v_w = tk.IntVar(value=max(w0, need_w))
        self.v_h = tk.IntVar(value=max(h0, need_h))
        self.v_pin = tk.StringVar()
        self.v_side = tk.StringVar(value="left")
        self.v_dip = tk.IntVar(value=8)
        self.v_mcu = tk.BooleanVar(value=bool(d.get("microcontroller")))
        self.v_replace = tk.BooleanVar(value=True)

        self._build(d)
        for v in (self.v_name, self.v_prefix, self.v_value, self.v_color, self.v_auto, self.v_w, self.v_h):
            v.trace_add("write", lambda *_: self._changed())
        self._refresh_rows()
        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.bind("<Escape>", lambda e: self.destroy())
        self.after(50, self._changed)
        self.after(60, lambda: self.e_name.focus_set())
        self.grab_set()

    # ---- data helpers ----
    @staticmethod
    def _rows_from_def(d):
        rows = []
        pins = d.get("pins", [])
        if d.get("symbol", "box") == "box":
            last = {}
            for p in pins:
                side = p.get("side", "left")
                pos = int(round(float(p.get("pos", 1))))
                if side in last:
                    for _ in range(max(0, pos - last[side] - 1)):
                        rows.append({"kind": "gap", "name": "", "side": side})
                last[side] = pos
                rows.append({"kind": "pin", "name": p.get("name", ""), "side": side, "inner": p.get("inner")})
        else:
            for p in pins:
                rows.append({"kind": "pin", "name": p.get("name", ""),
                             "side": SIDE_OF_DIR.get(p.get("dir", "L"), "left")})
        return rows

    def _needed_size(self, picture=True):
        """Smallest size that fits the pins and name (and, if picture=True, the picture)."""
        sides = {s: [r for r in self.rows if r["side"] == s] for s in self.SIDES}
        def maxlen(s):
            return max([len(r["name"]) for r in sides[s] if r["kind"] == "pin"] or [0])
        nL, nR, nT, nB = (len(sides[s]) for s in self.SIDES)
        need_h = max(nL, nR) + 1
        if nT or nB:
            need_h = max(need_h, int(math.ceil(((maxlen("top") + maxlen("bottom")) * 5.4 + 44) / G)))
        name = getattr(self, "v_name", None)
        name_len = len(name.get()) if name else 8
        text_w = min(name_len, 16) * 6.3 + 14 + (maxlen("left") + maxlen("right")) * 5.4 + 18
        need_w = max(max(nT, nB) + 1, int(math.ceil(text_w / G)), 3)
        if picture and self.image:
            pw, ph = picture_auto_size(self.image, {s: pin_label_room(maxlen(s)) for s in self.SIDES})
            need_w, need_h = max(need_w, pw), max(need_h, ph)
        return need_w, max(need_h, 2)

    def build_def(self):
        need_w, need_h = self._needed_size()
        if self.v_auto.get():
            w, h = need_w, need_h
        else:
            min_w, min_h = self._needed_size(picture=False)
            try:
                w, h = max(min_w, int(self.v_w.get())), max(min_h, int(self.v_h.get()))
            except (tk.TclError, ValueError):
                w, h = need_w, need_h
        counts = {s: sum(1 for r in self.rows if r["side"] == s) for s in self.SIDES}
        idx = {s: 0 for s in self.SIDES}
        pins = []
        for r in self.rows:
            s = r["side"]
            length = h if s in ("left", "right") else w
            start = 1 + max(0, (length - 1 - counts[s]) // 2)
            pos = start + idx[s]
            idx[s] += 1
            if r["kind"] == "pin":
                pins.append({"name": r["name"], "side": s, "pos": pos})
                if self.subcircuit and r.get("inner"):
                    pins[-1]["inner"] = list(r["inner"])
        d = {"id": self.edit_id or "preview", "name": self.v_name.get().strip() or "New Part",
             "category": self.v_cat.get().strip() or "My Components",
             "prefix": re.sub(r"[^A-Za-z_]", "", self.v_prefix.get()) or "U",
             "value": self.v_value.get().strip(),
             "description": self.t_desc.get("1.0", "end").strip(),
             "symbol": "box", "w": w, "h": h, "color": self.v_color.get(), "pins": pins}
        if self.v_mcu.get():
            d["microcontroller"] = True
        if self.image:
            d["image"] = self.image
        if self.subcircuit:
            d["subcircuit"] = self.subcircuit
        else:
            if self.sim_model:
                d["sim"] = self.sim_model
            if self.logic.strip():
                d["logic"] = self.logic
        return d

    # ---- logic ----
    def _pin_names(self):
        return [r["name"] for r in self.rows if r["kind"] == "pin" and r["name"]]

    def _edit_logic(self):
        if self.subcircuit:
            if not messagebox.askyesno(APP_NAME, "This part works like the circuit inside it.\n\nStop using that "
                                                 "circuit and describe the part with logic equations instead?",
                                       parent=self):
                return
            self.subcircuit = None
            for r in self.rows:
                r.pop("inner", None)
            self._refresh_rows()
        LogicDialog(self)

    def _inside_text(self, r):
        """What a pin of a component built from a circuit is joined to inside it."""
        if r["kind"] != "pin":
            return ""
        inn = r.get("inner")
        comps = {c["id"]: c for c in (self.subcircuit or {}).get("comps", [])}
        c = comps.get(inn[0]) if inn else None
        if c is None:
            return "— (not connected inside)"
        rd = self.app.rdef(c)
        if c["def"] == PORT_DEF:
            return "Component Pin “%s”" % (c.get("label") or "?")
        pn = rd.pins[inn[1]]["name"] if inn[1] < len(rd.pins) else "?"
        return "%s · pin %s" % (c.get("label") or rd.name, pn)

    def set_logic(self, text):
        self.logic = text or ""
        self._changed()

    def add_logic_pins(self, names, text):
        """Add pins that a logic example needs: inputs left, outputs right, VCC top, GND bottom."""
        try:
            prog = LogicProgram(text, self._pin_names() + list(names))
            outs = set(prog.outputs)
        except LogicError:
            outs = set()
        for nm in names:
            side = ("top" if is_power_pin(nm) else "bottom" if is_ground_pin(nm)
                    else "right" if nm in outs else "left")
            self.rows.append({"kind": "pin", "name": nm, "side": side})
        self._refresh_rows()

    def _logic_status(self):
        lbl = getattr(self, "logic_lbl", None)
        if lbl is None:
            return
        if self.subcircuit:
            sub = self.subcircuit
            n = sum(1 for c in sub.get("comps", []) if c.get("def") != PORT_DEF)
            free = sum(1 for r in self.rows if r["kind"] == "pin" and not r.get("inner"))
            txt = ("✓  Works like the circuit inside it (%d part%s, %d wire%s). To change that circuit, "
                   "right-click the part on the canvas › Show the circuit inside."
                   % (n, "" if n == 1 else "s", len(sub.get("wires", [])), "" if len(sub.get("wires", [])) == 1 else "s"))
            if free:
                txt += "  %d pin%s you added here %s not connected inside." % (free, "" if free == 1 else "s",
                                                                             "is" if free == 1 else "are")
            lbl.configure(text=txt, foreground=C["ok"])
            self.b_logic.configure(text="Use equations instead…")
            return
        if not self.logic.strip():
            if self.sim_model:
                txt, col = ("Simulates like the built-in part it was copied from. Add logic equations to "
                            "replace that with your own behaviour."), C["muted"]
            else:
                txt, col = ("Not simulated yet. To make it work, build its circuit on the canvas, select it and "
                            "click Make component. For a digital chip you can instead describe it with logic "
                            "equations (like  Y = A & B)."), C["muted"]
            self.b_logic.configure(text="Add logic…")
        else:
            prog = logic_program(self.logic, self._pin_names())
            if isinstance(prog, LogicError):
                txt, col = "⚠  " + str(prog), C["danger"]
            else:
                txt, col = "✓  " + prog.summary(), C["ok"]
            self.b_logic.configure(text="Edit logic…")
        lbl.configure(text=txt, foreground=col)

    # ---- UI ----
    def _build(self, d):
        fam = self.fam
        if self.from_sel:
            self._build_banner()
        outer = ttk.Frame(self, style="Bg.TFrame", padding=12)
        outer.pack(fill="both", expand=True)
        outer.columnconfigure(1, weight=1)
        outer.rowconfigure(0, weight=1)

        # left: details
        left = ttk.Frame(outer, style="Card.TFrame", padding=14)
        left.grid(row=0, column=0, sticky="nsw", padx=(0, 10))
        ttk.Label(left, text="1. Details", style="CardTitle.TLabel").grid(row=0, column=0, columnspan=2, sticky="w")
        r = 1
        def field(label, widget, hint=None):
            nonlocal r
            ttk.Label(left, text=label, style="Card.TLabel").grid(row=r, column=0, sticky="w", pady=(8, 0))
            r += 1
            widget.grid(row=r, column=0, columnspan=2, sticky="ew")
            r += 1
            if hint:
                ttk.Label(left, text=hint, style="Hint.TLabel").grid(row=r, column=0, columnspan=2, sticky="w")
                r += 1
        self.e_name = ttk.Entry(left, textvariable=self.v_name, width=30)
        field("Name *", self.e_name)
        cb = ttk.Combobox(left, textvariable=self.v_cat, values=self.app.library.categories() + ["My Components"])
        field("Category", cb)
        field("Label prefix", ttk.Entry(left, textvariable=self.v_prefix, width=10),
              "Parts are numbered automatically, e.g. U1, U2 …")
        field("Default value", ttk.Entry(left, textvariable=self.v_value),
              "Optional, e.g. 5 V, 10 kΩ, ATmega328P")
        self.t_desc = tk.Text(left, height=3, width=30, wrap="word", font=(fam, 9), relief="flat",
                              highlightthickness=1, padx=6, pady=4, **text_colors())
        self.t_desc.insert("1.0", d.get("description", ""))
        self.t_desc.bind("<KeyRelease>", lambda e: None)
        field("Description", self.t_desc)

        ttk.Label(left, text="Body color", style="Card.TLabel").grid(row=r, column=0, sticky="w", pady=(10, 2))
        r += 1
        sw = ttk.Frame(left, style="Inner.TFrame")
        sw.grid(row=r, column=0, columnspan=2, sticky="w")
        r += 1
        self.swatches = []
        for i, col in enumerate(BODY_COLORS):
            f = tk.Frame(sw, width=22, height=22, bg=body_fill(col), highlightthickness=2, cursor="hand2",
                         highlightbackground=C["border"])
            f.grid(row=0, column=i, padx=2)
            f.bind("<Button-1>", lambda e, c=col: self.v_color.set(c))
            self.swatches.append((f, col))
        ttk.Button(sw, text="…", width=3, command=self._pick_color).grid(row=0, column=len(BODY_COLORS), padx=(4, 0))

        sc = self.app.ui_scale
        ttk.Label(left, text="Picture", style="Card.TLabel").grid(row=r, column=0, sticky="w", pady=(12, 2))
        r += 1
        pf = ttk.Frame(left, style="Inner.TFrame")
        pf.grid(row=r, column=0, columnspan=2, sticky="w")
        r += 1
        self.pic_cv = tk.Canvas(pf, width=int(110 * sc), height=int(72 * sc), bg=C["canvas"], cursor="hand2",
                                highlightthickness=1, highlightbackground=C["border"])
        self.pic_cv.grid(row=0, column=0, rowspan=2, padx=(0, 10))
        tip = Tooltip(self.pic_cv, "Click to choose a picture")
        self.pic_cv.bind("<Button-1>", lambda e: (tip._leave(), self._choose_picture()))
        self.b_pic = ttk.Button(pf, text="Choose…", command=self._choose_picture)
        self.b_pic.grid(row=0, column=1, sticky="ew")
        self.b_pic_rm = ttk.Button(pf, text="Remove", command=self._remove_picture)
        self.b_pic_rm.grid(row=1, column=1, sticky="ew", pady=(4, 0))
        ttk.Label(left, text="Optional. A photo or drawing of the part (PNG, JPG …) shown inside it.",
                  style="Hint.TLabel", wraplength=int(230 * sc), justify="left").grid(
            row=r, column=0, columnspan=2, sticky="w", pady=(4, 0))
        r += 1

        ttk.Label(left, text="Size (grid squares)", style="Card.TLabel").grid(row=r, column=0, sticky="w", pady=(12, 2))
        r += 1
        szf = ttk.Frame(left, style="Inner.TFrame")
        szf.grid(row=r, column=0, columnspan=2, sticky="w")
        r += 1
        ttk.Checkbutton(szf, text="Automatic", variable=self.v_auto, style="Card.TCheckbutton").grid(row=0, column=0, padx=(0, 10))
        ttk.Label(szf, text="W", style="Card.TLabel").grid(row=0, column=1)
        self.sp_w = ttk.Spinbox(szf, from_=2, to=60, width=4, textvariable=self.v_w)
        self.sp_w.grid(row=0, column=2, padx=(2, 8))
        ttk.Label(szf, text="H", style="Card.TLabel").grid(row=0, column=3)
        self.sp_h = ttk.Spinbox(szf, from_=2, to=80, width=4, textvariable=self.v_h)
        self.sp_h.grid(row=0, column=4, padx=(2, 0))
        left.columnconfigure(0, weight=1)

        # middle: pins
        mid = ttk.Frame(outer, style="Card.TFrame", padding=14)
        mid.grid(row=0, column=1, sticky="nsew", padx=(0, 10))
        mid.columnconfigure(0, weight=1)
        mid.rowconfigure(4, weight=1)
        ttk.Label(mid, text="2. Pins", style="CardTitle.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(mid, text="Each pin is a connection point for wires. The side sets where it sticks out.",
                  style="Hint.TLabel", wraplength=int(400 * self.app.ui_scale)).grid(row=1, column=0, sticky="w")
        add = ttk.Frame(mid, style="Inner.TFrame")
        add.grid(row=2, column=0, sticky="ew", pady=(10, 2))
        add.columnconfigure(1, weight=1)
        ttk.Label(add, text="Pin name", style="Card.TLabel").grid(row=0, column=0, sticky="w", padx=(0, 6))
        self.e_pin = ttk.Entry(add, textvariable=self.v_pin)
        self.e_pin.grid(row=0, column=1, sticky="ew")
        self.e_pin.bind("<Return>", lambda e: self._add_pins())
        ttk.Label(add, text="Side", style="Card.TLabel").grid(row=0, column=2, padx=(10, 6))
        ttk.Combobox(add, textvariable=self.v_side, values=self.SIDES, state="readonly", width=8).grid(row=0, column=3)
        ttk.Button(add, text="Add pin", style="Accent.TButton", command=self._add_pins).grid(row=0, column=4, padx=(8, 0))
        ttk.Label(mid, text="Tip: type several names separated by commas (e.g.  VCC, GND, SDA, SCL) and press Enter.",
                  style="Hint.TLabel", wraplength=int(400 * self.app.ui_scale)).grid(row=3, column=0, sticky="w", pady=(0, 6))

        tf = ttk.Frame(mid, style="Inner.TFrame")
        tf.grid(row=4, column=0, sticky="nsew")
        tf.columnconfigure(0, weight=1)
        tf.rowconfigure(0, weight=1)
        self.tree = ttk.Treeview(tf, columns=("n", "name", "side", "inside"), show="headings", selectmode="extended")
        self.tree.heading("n", text="#")
        self.tree.heading("name", text="Pin name")
        self.tree.heading("side", text="Side")
        self.tree.heading("inside", text="Connects inside to")
        self.tree.column("n", width=40, stretch=False, anchor="center")
        self.tree.column("name", width=140)
        self.tree.column("side", width=70, stretch=False)
        self.tree.column("inside", width=170)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        sb.grid(row=0, column=1, sticky="ns")
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.bind("<<TreeviewSelect>>", self._on_row_select)
        self.tree.bind("<Delete>", lambda e: self._remove())

        btns = ttk.Frame(mid, style="Inner.TFrame")
        btns.grid(row=5, column=0, sticky="ew", pady=(8, 0))
        for i, (txt, cmd, tip) in enumerate([
                ("Move up", lambda: self._move(-1), "Pins higher in the list sit higher (or further left) on the part"),
                ("Move down", lambda: self._move(1), "Pins lower in the list sit lower (or further right) on the part"),
                ("Update selected", self._update_row, "Copy the name and side above onto the selected pin"),
                ("Add gap", self._add_gap, "Leave an empty space between pins on this side"),
                ("Remove", self._remove, "Delete the selected pins")]):
            b = ttk.Button(btns, text=txt, command=cmd, style="Danger.TButton" if txt == "Remove" else "TButton")
            b.grid(row=i // 3, column=i % 3, padx=(0, 6), pady=(0, 4), sticky="ew")
            Tooltip(b, tip)
        quick = ttk.Frame(mid, style="Inner.TFrame")
        quick.grid(row=6, column=0, sticky="ew", pady=(12, 0))
        ttk.Label(quick, text="Quick start: chip (DIP) with", style="Card.TLabel").grid(row=0, column=0)
        ttk.Spinbox(quick, from_=2, to=64, increment=2, width=4, textvariable=self.v_dip).grid(row=0, column=1, padx=6)
        ttk.Label(quick, text="pins", style="Card.TLabel").grid(row=0, column=2)
        ttk.Button(quick, text="Create pins", command=self._dip).grid(row=0, column=3, padx=(8, 0))
        mcf = ttk.Frame(mid, style="Inner.TFrame")
        mcf.grid(row=7, column=0, sticky="ew", pady=(12, 0))
        ttk.Checkbutton(mcf, text="This is a microcontroller or dev board (Arduino, ESP32, Pico …)",
                        variable=self.v_mcu, style="Card.TCheckbutton").grid(row=0, column=0, sticky="w")
        ttk.Label(mcf, text="Check circuit won’t list its unused pins; it checks that power and ground are wired instead.",
                  style="Hint.TLabel", wraplength=int(400 * self.app.ui_scale), justify="left").grid(
            row=1, column=0, sticky="w")
        lgf = ttk.Frame(mid, style="Inner.TFrame")
        lgf.grid(row=8, column=0, sticky="ew", pady=(12, 0))
        lgf.columnconfigure(0, weight=1)
        ttk.Label(lgf, text="How it works in the simulator", style="Card.TLabel").grid(row=0, column=0, sticky="w")
        self.b_logic = ttk.Button(lgf, text="Add logic…", command=self._edit_logic)
        self.b_logic.grid(row=2, column=0, sticky="w", pady=(6, 0))
        Tooltip(self.b_logic, "For digital chips: describe what it does with equations like  Y = A & B  "
                              "or  Q = D on CLK")
        self.logic_lbl = ttk.Label(lgf, text="", style="Hint.TLabel", wraplength=int(400 * self.app.ui_scale),
                                   justify="left")
        self.logic_lbl.grid(row=1, column=0, sticky="w")

        # right: preview
        right = ttk.Frame(outer, style="Card.TFrame", padding=14)
        right.grid(row=0, column=2, sticky="ns")
        ttk.Label(right, text="3. Preview", style="CardTitle.TLabel").pack(anchor="w")
        s = self.app.ui_scale
        self.pv = tk.Canvas(right, width=int(270 * s), height=int(330 * s), bg=C["canvas"],
                            highlightthickness=1, highlightbackground=C["border"])
        self.pv.pack(pady=(8, 6))
        self.pv.bind("<Configure>", lambda e: self._changed())
        self.pv_info = ttk.Label(right, text="", style="Hint.TLabel", wraplength=int(260 * s))
        self.pv_info.pack(anchor="w")
        if self.sim_model and not self.logic.strip():
            ttk.Label(right, text="Simulates like the built-in part it was copied from, as long as its "
                                  "pin names stay the same.", style="Hint.TLabel",
                      wraplength=int(260 * s), justify="left").pack(anchor="w", pady=(6, 0))

        bar = ttk.Frame(self, style="Bg.TFrame", padding=(12, 0, 12, 12))
        bar.pack(side="bottom", fill="x", before=outer)  # keep the buttons visible on small screens
        if self.from_sel:
            if self.edit_id:
                save_txt = "Update “%s”" % self.source_name
            else:
                save_txt = "Create component"
        else:
            save_txt = "Save to library"
        ttk.Button(bar, text=save_txt, style="Accent.TButton", command=self._save).pack(side="right")
        if self.from_sel and self.edit_id:
            b = ttk.Button(bar, text="Save as a new component", command=self._save_as_new)
            b.pack(side="right", padx=(0, 8))
            Tooltip(b, "Keep “%s” as it was and save this as a separate part" % self.source_name)
        ttk.Button(bar, text="Cancel", command=self.destroy).pack(side="right", padx=(0, 8))
        if self.from_sel:
            ttk.Checkbutton(bar, text="Replace the selected parts with the new component", variable=self.v_replace,
                            style="TCheckbutton").pack(side="left")
        note = None
        if self.from_sel:
            pass
        elif self.edit_id:
            note = "Changes also update every copy of this part in your circuit."
        elif self.use_for in self.app.comps:
            note = ("“%s” is built in, so this saves your own copy with the picture, and %s will use it."
                    % (self.source_name, self.app.comps[self.use_for].get("label") or "the selected part"))
        if note:
            ttk.Label(bar, text=note, style="Status.TLabel").pack(side="left")
        self._show_picture()

    def _show_picture(self):
        cv = self.pic_cv
        cv.delete("all")
        W, H = int(cv.cget("width")), int(cv.cget("height"))
        self._thumb = picture_photo(self.image, W - 8, H - 8) if self.image else None
        if self._thumb is not None:
            cv.create_image(W / 2.0 + 1, H / 2.0 + 1, image=self._thumb, anchor="center")
            self.b_pic.configure(text="Change…")
            self.b_pic_rm.state(["!disabled"])
        else:
            cv.create_text(W / 2.0, H / 2.0, text="No picture\n(click to add)", fill=C["muted"],
                           font=(self.fam, 8), justify="center")
            self.b_pic.configure(text="Choose…")
            self.b_pic_rm.state(["!disabled"] if self.image else ["disabled"])

    def _choose_picture(self):
        path = filedialog.askopenfilename(parent=self, title="Choose a picture for this part",
                                          filetypes=PICTURE_FILETYPES)
        if not path:
            return
        pic = self.app.read_picture(path, parent=self)
        if pic:
            self.image = pic
            self._show_picture()
            self._changed()

    def _remove_picture(self):
        self.image = None
        self._show_picture()
        self._changed()

    def _pick_color(self):
        c = colorchooser.askcolor(color=self.v_color.get(), parent=self, title="Body color")
        if c and c[1]:
            self.v_color.set(c[1])

    def on_theme(self):
        """The app switched between light and dark mode."""
        for f, col in self.swatches:
            f.configure(bg=body_fill(col))
        for cv in (self.pv, self.pic_cv):
            cv.configure(bg=C["canvas"], highlightbackground=C["border"])
        self._show_picture()
        self._changed()

    def _refresh_rows(self, select=None):
        self.tree.delete(*self.tree.get_children())
        n = 0
        for i, r in enumerate(self.rows):
            if r["kind"] == "pin":
                n += 1
                vals = (n, r["name"], r["side"], self._inside_text(r))
            else:
                vals = ("", "(gap)", r["side"], "")
            self.tree.insert("", "end", iid=str(i), values=vals, tags=(r["kind"],))
        self.tree.tag_configure("gap", foreground=C["muted"])
        self.tree.configure(displaycolumns=("n", "name", "side", "inside") if self.subcircuit
                            else ("n", "name", "side"))
        if select:
            sel = [str(i) for i in select if 0 <= i < len(self.rows)]
            if sel:
                self.tree.selection_set(sel)
                self.tree.see(sel[-1])
        self._changed()

    def _selected(self):
        return sorted(int(i) for i in self.tree.selection())

    def _on_row_select(self, _e=None):
        sel = self._selected()
        if len(sel) == 1:
            r = self.rows[sel[0]]
            self.v_pin.set(r["name"] if r["kind"] == "pin" else "")
            self.v_side.set(r["side"])

    def _add_pins(self):
        names = [n.strip() for n in self.v_pin.get().split(",") if n.strip()]
        if not names:
            self.e_pin.focus_set()
            return
        for n in names:
            self.rows.append({"kind": "pin", "name": n, "side": self.v_side.get()})
        self.v_pin.set("")
        self._refresh_rows(select=[len(self.rows) - 1])
        self.e_pin.focus_set()

    def _add_gap(self):
        self.rows.append({"kind": "gap", "name": "", "side": self.v_side.get()})
        self._refresh_rows(select=[len(self.rows) - 1])

    def _update_row(self):
        sel = self._selected()
        if not sel:
            return
        for i in sel:
            r = self.rows[i]
            if r["kind"] == "pin" and len(sel) == 1 and self.v_pin.get().strip():
                r["name"] = self.v_pin.get().strip()
            r["side"] = self.v_side.get()
        self._refresh_rows(select=sel)

    def _remove(self):
        sel = self._selected()
        for i in reversed(sel):
            del self.rows[i]
        self._refresh_rows(select=[min(sel[0], len(self.rows) - 1)] if sel and self.rows else None)

    def _move(self, delta):
        sel = self._selected()
        if not sel:
            return
        if delta < 0 and sel[0] == 0 or delta > 0 and sel[-1] == len(self.rows) - 1:
            return
        order = sel if delta < 0 else list(reversed(sel))
        for i in order:
            self.rows[i], self.rows[i + delta] = self.rows[i + delta], self.rows[i]
        self._refresh_rows(select=[i + delta for i in sel])

    def _dip(self):
        try:
            n = int(self.v_dip.get())
        except (tk.TclError, ValueError):
            return
        n = max(2, n - n % 2)
        if self.rows and not messagebox.askyesno(APP_NAME, "Replace the current pins with %d numbered pins?" % n, parent=self):
            return
        half = n // 2
        self.rows = ([{"kind": "pin", "name": str(i), "side": "left"} for i in range(1, half + 1)]
                     + [{"kind": "pin", "name": str(i), "side": "right"} for i in range(n, half, -1)])
        self._refresh_rows()

    def _changed(self):
        if self._sync:
            return
        for f, col in self.swatches:
            f.configure(highlightbackground=C["accent"] if col == self.v_color.get() else C["border"])
        try:
            d = self.build_def()
        except tk.TclError:
            return
        self._sync = True
        try:
            try:
                cur = (int(self.v_w.get()), int(self.v_h.get()))
            except (tk.TclError, ValueError):
                cur = None
            if self.v_auto.get() or cur is None or cur[0] < d["w"] or cur[1] < d["h"]:
                if cur != (d["w"], d["h"]):
                    self.v_w.set(d["w"])
                    self.v_h.set(d["h"])
            state = "disabled" if self.v_auto.get() else "normal"
            self.sp_w.configure(state=state)
            self.sp_h.configure(state=state)
        finally:
            self._sync = False
        rd = RDef(d)
        fit_preview(self.pv, rd, self.fam, label=(d["prefix"] + "1"), value=d["value"])
        npins = len(d["pins"])
        self.pv_info.configure(text="%d pin%s · %d × %d grid squares" % (npins, "" if npins == 1 else "s", d["w"], d["h"]))
        self._logic_status()

    def _save(self):
        d = self.build_def()
        if not self.v_name.get().strip():
            messagebox.showwarning(APP_NAME, "Please give the component a name.", parent=self)
            self.e_name.focus_set()
            return
        if not d["pins"]:
            messagebox.showwarning(APP_NAME, "Add at least one pin so the part can be wired.", parent=self)
            self.e_pin.focus_set()
            return
        if any(not p["name"] for p in d["pins"]):
            messagebox.showwarning(APP_NAME, "Every pin needs a name.", parent=self)
            return
        if self.logic.strip() and not self.subcircuit:
            prog = logic_program(self.logic, self._pin_names())
            if isinstance(prog, LogicError) and not messagebox.askyesno(
                    APP_NAME, "The part’s logic has a problem:\n\n%s\n\nSave anyway? It won’t simulate until the "
                              "logic is fixed (Edit logic…)." % prog, parent=self):
                return
        if self.subcircuit and self.edit_id:
            inside = set()
            for c in self.subcircuit.get("comps", []):
                inside.add(c.get("def"))
                inside |= self.app.library.parts_inside(c.get("def"))
            if self.edit_id in inside:
                messagebox.showwarning(APP_NAME, "The circuit contains “%s” itself, and a component can’t be "
                                                 "built from itself.\n\nRemove that part from the circuit, or "
                                                 "click Save as a new component." % self.source_name, parent=self)
                return
        if self.from_sel and not any(r.get("inner") for r in self.rows if r["kind"] == "pin"):
            messagebox.showwarning(APP_NAME, "None of the pins is connected to the circuit inside, so the part "
                                             "couldn’t do anything. Keep at least one of the pins that were "
                                             "found for you.", parent=self)
            return
        d["id"] = self.edit_id or ("custom_" + uuid.uuid4().hex[:10])
        from_sel, replace = self.from_sel, self.from_sel and self.v_replace.get()
        app = self.app
        self.destroy()
        app.save_definition(d, use_for=self.use_for)
        if replace:
            n = len(from_sel["cs"])
            dropped = app.replace_selection_with(from_sel, d["id"])
            msg = "Saved “%s” to your library and put it in place of the %d selected part%s." % (
                d["name"], n, "" if n == 1 else "s")
            if dropped:
                msg += (" %d wire%s leaving the selection had no matching pin, so %s removed."
                        % (dropped, "" if dropped == 1 else "s", "it was" if dropped == 1 else "they were"))
            app.flash(msg, 8000)

    def _save_as_new(self):
        """Save the circuit as a separate part instead of updating the one it was unpacked from."""
        if self.v_name.get().strip() == self.source_name:
            self.v_name.set(self.source_name + " (new)")
        self.edit_id = None
        self._save()

    def _build_banner(self):
        """Explains what is happening when a selection is turned into a component."""
        spec = self.from_sel
        n = len(spec["cs"])
        if spec.get("base"):
            head = "Update “%s” with the circuit you changed" % self.source_name
            body = ("Its pins come from the Component Pins in your selection. Saving updates every copy of “%s” "
                    "in your circuit (wires stay on pins with the same name)." % self.source_name
                    if spec["mode"] == "ports" else
                    "Its pins come from the wires that leave your selection. Saving updates every copy of “%s”."
                    % self.source_name)
        elif spec["mode"] == "ports":
            head = "Make a component from the %d selected part%s" % (n, "" if n == 1 else "s")
            body = ("Each Component Pin in your selection became a pin, named after its label. Give the part a "
                    "name, check which side each pin is on, and click Create component. It will work in the "
                    "simulator exactly like the circuit inside it.")
        else:
            head = "Make a component from the %d selected part%s" % (n, "" if n == 1 else "s")
            body = ("Every wire that leaves your selection, and every unconnected pin, became a pin. Rename them "
                    "(select one, type a name above the list, click Update selected) and remove any you don’t "
                    "need. Tip: to choose the pins yourself, add Component Pins (under Building Blocks) to your "
                    "circuit before selecting it.")
        bn = tk.Frame(self, bg=C["accent_light"], padx=14, pady=8)
        bn.pack(side="top", fill="x")
        self._banner = bn
        tk.Label(bn, text=head, bg=C["accent_light"], fg=C["accent_dark"], font=(self.fam, 11, "bold"),
                 anchor="w").pack(fill="x")
        tk.Label(bn, text=body, bg=C["accent_light"], fg=C["text"], anchor="w", justify="left",
                 wraplength=int(1040 * self.app.ui_scale)).pack(fill="x")


class LogicDialog(tk.Toplevel):
    """Write the logic equations of a part; shows problems and a truth table as you type."""

    def __init__(self, editor):
        super().__init__(editor)
        self.ed = editor
        self.app = editor.app
        s = self.app.ui_scale
        fam = self.app.fam
        self.title("Chip logic — " + APP_NAME)
        self.configure(bg=C["bg"])
        self.transient(editor)
        self.geometry("%dx%d" % (int(1060 * s), int(680 * s)))
        self.minsize(int(820 * s), int(520 * s))
        self._job = None
        mono = ("Consolas", 11) if os.name == "nt" else ("DejaVu Sans Mono", 10)

        bar = ttk.Frame(self, style="Bg.TFrame", padding=(12, 0, 12, 12))
        bar.pack(side="bottom", fill="x")
        ttk.Button(bar, text="OK", style="Accent.TButton", command=self._ok).pack(side="right")
        ttk.Button(bar, text="Cancel", command=self.destroy).pack(side="right", padx=(0, 8))
        ttk.Button(bar, text="Remove logic", style="Danger.TButton", command=self._clear).pack(side="left")

        outer = ttk.Frame(self, style="Bg.TFrame", padding=12)
        outer.pack(fill="both", expand=True)
        outer.columnconfigure(0, weight=11, uniform="logic")
        outer.columnconfigure(1, weight=9, uniform="logic")
        outer.rowconfigure(0, weight=1)

        left = ttk.Frame(outer, style="Card.TFrame", padding=14)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        left.columnconfigure(0, weight=1)
        left.rowconfigure(4, weight=1)
        left.grid_propagate(False)
        top = ttk.Frame(left, style="Inner.TFrame")
        top.grid(row=0, column=0, sticky="ew")
        top.columnconfigure(0, weight=1)
        ttk.Label(top, text="Logic equations", style="CardTitle.TLabel").grid(row=0, column=0, sticky="w")
        mb = ttk.Menubutton(top, text="Start from an example ▾")
        menu = tk.Menu(mb, tearoff=0)
        for title, pins, text in LOGIC_TEMPLATES:
            menu.add_command(label=title, command=lambda p=pins, t=text, n=title: self._template(n, p, t))
        mb["menu"] = menu
        mb.grid(row=0, column=1, sticky="e")
        ttk.Label(left, text="Describe what the chip does, one line per output. Inputs are the pins you read, "
                             "outputs are the pins you set. The truth table on the right updates as you type.",
                  style="Hint.TLabel", wraplength=int(470 * s), justify="left").grid(row=1, column=0, sticky="w", pady=(4, 6))
        pf = ttk.Frame(left, style="Inner.TFrame")
        pf.grid(row=2, column=0, sticky="ew", pady=(0, 6))
        ttk.Label(pf, text="Pins (click to insert):", style="Card.TLabel").pack(side="left", anchor="n")
        self.pin_txt = tk.Text(pf, height=2, wrap="word", relief="flat", font=(fam, 9), cursor="arrow",
                               borderwidth=0, highlightthickness=0, bg=C["panel"], fg=C["text"], padx=6)
        self.pin_txt.pack(side="left", fill="x", expand=True)
        self._fill_pins()
        tf = ttk.Frame(left, style="Inner.TFrame")
        tf.grid(row=4, column=0, sticky="nsew")
        tf.columnconfigure(0, weight=1)
        tf.rowconfigure(0, weight=1)
        self.txt = tk.Text(tf, wrap="none", font=mono, undo=True, relief="flat", highlightthickness=1,
                           padx=8, pady=6, **text_colors())
        self.txt.grid(row=0, column=0, sticky="nsew")
        sb = ttk.Scrollbar(tf, orient="vertical", command=self.txt.yview)
        sb.grid(row=0, column=1, sticky="ns")
        self.txt.configure(yscrollcommand=sb.set)
        self.txt.insert("1.0", editor.logic or "# Example:  Y = A & B\n")
        self.txt.edit_reset()
        self.txt.bind("<KeyRelease>", lambda e: self._schedule())
        self.txt.bind("<<Paste>>", lambda e: self._schedule())
        self.status = tk.Label(left, text="", bg=C["panel"], anchor="w", justify="left", font=self.app.f_bold,
                               wraplength=int(470 * s))
        self.status.grid(row=5, column=0, sticky="ew", pady=(8, 0))
        self.roles = ttk.Label(left, text="", style="Hint.TLabel", wraplength=int(470 * s), justify="left")
        self.roles.grid(row=6, column=0, sticky="w", pady=(2, 0))

        right = ttk.Frame(outer, style="Card.TFrame", padding=14)
        right.grid(row=0, column=1, sticky="nsew")
        right.columnconfigure(0, weight=1)
        right.rowconfigure(1, weight=1)
        right.grid_propagate(False)
        ttk.Label(right, text="Truth table", style="CardTitle.TLabel").grid(row=0, column=0, sticky="w")
        tt = ttk.Frame(right, style="Inner.TFrame")
        tt.grid(row=1, column=0, sticky="nsew", pady=(6, 0))
        tt.columnconfigure(0, weight=1)
        tt.rowconfigure(0, weight=1)
        self.table = ttk.Treeview(tt, show="headings", selectmode="none", height=10)
        self.table.grid(row=0, column=0, sticky="nsew")
        tsb = ttk.Scrollbar(tt, orient="vertical", command=self.table.yview)
        tsb.grid(row=0, column=1, sticky="ns")
        txs = ttk.Scrollbar(tt, orient="horizontal", command=self.table.xview)
        txs.grid(row=1, column=0, sticky="ew")
        self.table.configure(yscrollcommand=tsb.set, xscrollcommand=txs.set)
        self.table_note = ttk.Label(right, text="", style="Hint.TLabel", wraplength=int(360 * s), justify="left")
        self.table_note.grid(row=2, column=0, sticky="w", pady=(6, 0))
        ttk.Label(right, text="How to write it", style="Card.TLabel").grid(row=3, column=0, sticky="w", pady=(12, 2))
        tk.Label(right, text=LOGIC_HELP, bg=C["panel"], fg=C["muted"], font=(mono[0], max(8, mono[1] - 2)),
                 justify="left", anchor="w").grid(row=4, column=0, sticky="w")

        self.protocol("WM_DELETE_WINDOW", self.destroy)
        self.bind("<Escape>", lambda e: self.destroy())
        self._validate()
        self.txt.focus_set()
        self.grab_set()

    # ---- helpers
    def _pins(self):
        return [r["name"] for r in self.ed.rows if r["kind"] == "pin" and r["name"]]

    def _fill_pins(self):
        t = self.pin_txt
        t.configure(state="normal")
        t.delete("1.0", "end")
        pins = list(dict.fromkeys(self._pins()))
        if not pins:
            t.insert("end", "(none yet: add pins in the Component Editor, or start from an example)")
        for i, nm in enumerate(pins):
            tag = "p%d" % i
            label = ('"%s"' % nm) if re.search(r"\s", nm) else nm
            t.insert("end", " %s " % nm, (tag, "pin"))
            t.insert("end", "  ")
            t.tag_bind(tag, "<Button-1>", lambda e, s_=label: self._insert(s_))
        t.tag_configure("pin", background=C["accent_light"], foreground=C["accent_dark"])
        t.configure(state="disabled", height=2 if len(pins) < 14 else 3)

    def _insert(self, text):
        self.txt.insert("insert", text)
        self.txt.focus_set()
        self._schedule()

    def _schedule(self):
        if self._job:
            self.after_cancel(self._job)
        self._job = self.after(250, self._validate)

    def _text(self):
        return self.txt.get("1.0", "end").rstrip() + "\n"

    def _validate(self):
        self._job = None
        txt = self.txt
        txt.tag_remove("err", "1.0", "end")
        txt.tag_configure("err", background=_mix(C["field"], C["danger"], 0.22))
        prog = logic_program(self._text(), self._pins())
        self.table.delete(*self.table.get_children())
        if isinstance(prog, LogicError):
            self.status.configure(text="⚠  " + str(prog), fg=C["danger"], bg=C["panel"])
            self.roles.configure(text="")
            if prog.line:
                txt.tag_add("err", "%d.0" % prog.line, "%d.end" % prog.line)
            self.table["columns"] = ()
            self.table_note.configure(text="Fix the problem on the left to see the table.")
            return
        self.status.configure(text="✓  The logic is OK.", fg=C["ok"], bg=C["panel"])
        self.roles.configure(text=prog.summary())
        cols, rows = prog.truth_table()
        if cols is None:
            self.table["columns"] = ()
            self.table_note.configure(text=rows)
            return
        ids = ["c%d" % i for i in range(len(cols))]
        self.table["columns"] = ids
        for cid, (name, kind) in zip(ids, cols):
            head = ("→ " if kind == "out" else "") + name
            self.table.heading(cid, text=head)
            w = max(46, 9 * len(head) + 20)
            self.table.column(cid, width=int(w * self.app.ui_scale), anchor="center", stretch=False)
        for r in rows:
            self.table.insert("", "end", values=r)
        notes = ["Columns marked → are what the chip outputs for each combination of inputs."]
        if prog.states:
            notes.append("“now” is what a stored signal holds before the clock edge; “after” is its new value.")
        clk_only = [c for c in prog.clocks if c in prog.inputs and c not in [n for n, _k in cols]]
        if clk_only:
            notes.append("The clock (%s) isn’t a column: it only matters at the moment it rises or falls."
                         % ", ".join(clk_only))
        self.table_note.configure(text=" ".join(notes))

    def _template(self, title, pins, text):
        have = set(self._pins())
        missing = [p for p in pins if p not in have]
        cur = self.txt.get("1.0", "end").strip()
        if cur and not cur.startswith("# Example:"):
            if not messagebox.askyesno(APP_NAME, "Replace the logic you have written with “%s”?" % title, parent=self):
                return
        if missing:
            r = messagebox.askyesnocancel(APP_NAME, "This example uses the pins %s, which this part doesn’t have yet.\n\n"
                                          "Add them now? (Inputs go on the left, outputs on the right, VCC on top "
                                          "and GND at the bottom.)" % ", ".join(missing), parent=self)
            if r is None:
                return
            if r:
                self.ed.add_logic_pins(missing, text)
                self._fill_pins()
        self.txt.delete("1.0", "end")
        self.txt.insert("1.0", text)
        self._validate()

    def _clear(self):
        if self.txt.get("1.0", "end").strip() and not messagebox.askyesno(
                APP_NAME, "Remove the logic? The part won’t simulate any more.", parent=self):
            return
        self.ed.set_logic("")
        self.destroy()

    def _ok(self):
        text = self._text()
        if not re.sub(r"(#|//).*", "", text).strip():
            text = ""
        else:
            prog = logic_program(text, self._pins())
            if isinstance(prog, LogicError) and not messagebox.askyesno(
                    APP_NAME, "The logic still has a problem:\n\n%s\n\nKeep it anyway? The part won’t simulate until "
                              "it’s fixed." % prog, parent=self):
                return
        self.ed.set_logic(text)
        self.destroy()


# --------------------------------------------------------------------------
# Netlist window
# --------------------------------------------------------------------------
class NetlistWindow(tk.Toplevel):
    def __init__(self, app):
        super().__init__(app.root)
        self.app = app
        s = app.ui_scale
        self.title("Connections (Netlist) — " + APP_NAME)
        self.configure(bg=C["bg"])
        self.geometry("%dx%d" % (int(640 * s), int(440 * s)))
        top = ttk.Frame(self, style="Bg.TFrame", padding=(12, 12, 12, 6))
        top.pack(fill="x")
        ttk.Label(top, text="Each net is a group of pins that are wired together (same voltage). "
                            "Click a net to highlight it.", style="Status.TLabel",
                  wraplength=int(600 * s)).pack(anchor="w")
        mid = ttk.Frame(self, style="Bg.TFrame", padding=(12, 0))
        mid.pack(fill="both", expand=True)
        mid.columnconfigure(0, weight=1)
        mid.rowconfigure(0, weight=1)
        self.tree = ttk.Treeview(mid, columns=("net", "n", "pins"), show="headings")
        for col, txt, w, st in (("net", "Net", 80, False), ("n", "Pins", 50, False), ("pins", "Connected pins", 400, True)):
            self.tree.heading(col, text=txt)
            self.tree.column(col, width=int(w * s), stretch=st, anchor="w" if col != "n" else "center")
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb = ttk.Scrollbar(mid, orient="vertical", command=self.tree.yview)
        sb.grid(row=0, column=1, sticky="ns")
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.bind("<<TreeviewSelect>>", self._select)
        bar = ttk.Frame(self, style="Bg.TFrame", padding=12)
        bar.pack(fill="x")
        ttk.Button(bar, text="Copy as text", command=self._copy).pack(side="left")
        ttk.Button(bar, text="Export…", command=app.export_netlist).pack(side="left", padx=6)
        ttk.Button(bar, text="Close", command=self.close).pack(side="right")
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.nets = []
        self.refresh()

    def refresh(self):
        sel = self.tree.selection()
        sel_name = self.tree.item(sel[0], "values")[0] if sel else None
        self.tree.delete(*self.tree.get_children())
        self.nets = self.app.compute_nets()
        for i, net in enumerate(self.nets):
            names = ", ".join(self.app.pin_name(k) for k in net["pins"])
            self.tree.insert("", "end", iid=str(i), values=(net["name"], len(net["pins"]), names))
            if net["name"] == sel_name:
                self.tree.selection_set(str(i))

    def _select(self, _e=None):
        sel = self.tree.selection()
        if not sel:
            self.app.set_highlight(None)
            return
        self.app.set_highlight(self.nets[int(sel[0])])

    def _copy(self):
        self.clipboard_clear()
        self.clipboard_append(self.app.netlist_text())
        self.app.flash("Netlist copied to the clipboard.")

    def close(self):
        self.app.set_highlight(None)
        self.app.netlist_win = None
        self.destroy()


# --------------------------------------------------------------------------
# Main application
# --------------------------------------------------------------------------
SHORTCUTS = [
    ("Click a pin, then another pin", "Connect them with a wire"),
    ("Click empty space while wiring", "Add a bend to the wire"),
    ("Esc / right-click", "Cancel the wire or placement"),
    ("R  /  Shift+R", "Rotate selected part"),
    ("F", "Flip (mirror) selected part"),
    ("Delete", "Delete selection"),
    ("Ctrl+D", "Duplicate"),
    ("Ctrl+C / Ctrl+V", "Copy / paste"),
    ("Ctrl+G", "Make a component from the selected circuit"),
    ("Ctrl+Shift+G", "Show the circuit inside a component"),
    ("Ctrl+Z / Ctrl+Y", "Undo / redo"),
    ("Mouse wheel", "Zoom in / out"),
    ("Right- or middle-drag", "Move around (pan)"),
    ("Arrow keys", "Nudge selected parts"),
    ("Double-click a wire", "Add a bend you can drag"),
    ("F5", "Start / stop the simulation"),
]

SPICE_MAP = {
    "resistor": ("R", ["1", "2"], ""), "ldr": ("R", ["1", "2"], ""),
    "capacitor": ("C", ["1", "2"], ""), "capacitor_pol": ("C", ["+", "−"], ""),
    "inductor": ("L", ["1", "2"], ""), "fuse": ("R", ["1", "2"], "0.01"),
    "battery": ("V", ["+", "−"], "DC"), "dc_source": ("V", ["+", "−"], "DC"),
    "ac_source": ("V", ["1", "2"], "AC"), "current_source": ("I", ["−", "+"], "DC"),
    "ammeter": ("V", ["+", "−"], "AMMETER"),
    "diode": ("D", ["A", "K"], "DMOD"), "led": ("D", ["A", "K"], "DLED"),
    "zener": ("D", ["A", "K"], "DZEN"),
    "npn": ("Q", ["C", "B", "E"], "QNPN"), "pnp": ("Q", ["C", "B", "E"], "QPNP"),
}


class App:
    def __init__(self, root, open_path=None):
        self.root = root
        self.settings_path = os.path.join(data_dir(), "settings.json")
        self.settings = clean_settings(load_json(self.settings_path, {}))
        self.library = Library()
        self.comps = {}
        self.wires = {}
        self.sel = set()
        self.undo_stack, self.redo_stack = [], []
        self.path = None
        self.dirty = False
        self.wire_style = self.settings.get("wire_style", "orthogonal")
        self.wire_color = self.settings.get("wire_color", WIRE_COLORS[0][1])
        self.show_grid = self.settings.get("show_grid", True)
        self.text_size = self.settings.get("text_size", "normal")
        set_diagram_text_size(self.text_size)
        try:
            self.ui_scale = max(1.0, min(3.0, root.winfo_fpixels("1i") / 96.0))
        except tk.TclError:
            self.ui_scale = 1.0
        self.zoom = self.ui_scale
        self.panx = self.pany = None
        self.mode = "idle"
        self.wiring = None
        self.drag = None
        self.place_def = None
        self.ghost = None
        self.hover_pin = None
        self.highlight = None
        self.clipboard = None
        self.paste_n = 0
        self.netlist_win = None
        self.prop_vars = None
        self.space_down = False
        self._redraw_pending = False
        self._nets_cache = None
        self._pin_net = None
        self._error_shown = 0.0
        self._lib_drag = None
        self._flash_job = None
        self._missing = {}
        self.load_notes = []
        # simulation
        self.sim = None
        self.sim_paused = False
        self.sim_hover = None
        self.sim_vars = None
        self.scope_win = None
        self.freq_win = None
        self.scope_traces = []
        self.show_volts = self.settings.get("show_volts", True)
        self._sim_job = None
        self._sim_pb = None
        self._sim_click = None
        self._sim_last = 0.0
        self._sim_ui_t = 0.0
        self._sim_warn_sig = None
        self._last_sample = -1.0
        self._spin = {}
        self._mouse = (0, 0)

        remember_menu_defaults(root)
        set_palette(self.settings.get("theme") == "dark")
        self._setup_fonts()
        self._setup_style()
        self._build_menu()
        self._build_ui()
        self._bind_keys()
        # new windows (editor, oscilloscope …) get a title bar that matches the theme (Windows)
        root.bind_class("Toplevel", "<Map>", lambda e: set_title_bar_theme(e.widget, THEME["dark"]), add="+")
        root.after(50, lambda: set_title_bar_theme(root, THEME["dark"]))
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        root.report_callback_exception = self._on_tk_error
        self.update_title()
        self.refresh_props()
        if self.library.problem:
            root.after(300, lambda: messagebox.showwarning(APP_NAME, self.library.problem))
        if open_path:
            root.after(100, lambda: self.open_file(open_path))

    def _on_tk_error(self, exc_type, exc, tb):
        """An error in a button, menu or mouse handler: log it and tell the student, instead of the
        click silently doing nothing (the windowed app has no console to print to)."""
        path = log_exception(exc_type, exc, tb, "in the editor")
        now = time.time()
        if now - self._error_shown < 5.0:   # one message per burst (e.g. an error on every redraw)
            return
        self._error_shown = now
        try:
            self.flash("Something went wrong (%s). Details were saved to %s — please send that file "
                       "to your instructor." % (exc_type.__name__, path), 12000)
        except Exception:
            pass

    # ------------------------------------------------------------------ setup
    def _setup_fonts(self):
        fams = set(tkfont.families(self.root))
        for f in ("Segoe UI", "Helvetica Neue", "Inter", "Arial", "DejaVu Sans"):
            if f in fams:
                self.fam = f
                break
        else:
            self.fam = tkfont.nametofont("TkDefaultFont").actual("family")
        for name in ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont"):
            try:
                tkfont.nametofont(name).configure(family=self.fam, size=9)
            except tk.TclError:
                pass
        self.f_ui = (self.fam, 9)
        self.f_bold = (self.fam, 9, "bold")
        self.f_title = (self.fam, 12, "bold")
        self.f_small = (self.fam, 8)

    def _setup_style(self):
        s = ttk.Style(self.root)
        try:
            s.theme_use("clam")
        except tk.TclError:
            pass
        sc = self.ui_scale
        self.root.configure(bg=C["bg"])
        apply_option_db(self.root)
        s.configure(".", background=C["bg"], foreground=C["text"], font=self.f_ui,
                    bordercolor=C["border"], lightcolor=C["panel"], darkcolor=C["border"],
                    troughcolor=C["bg"], focuscolor=C["accent"], arrowcolor=C["arrow"])
        s.map(".", background=[("disabled", C["clam_frame"]), ("active", C["clam_active"])],
              foreground=[("disabled", C["clam_disabled"])])
        s.configure("Bg.TFrame", background=C["bg"])
        s.configure("Panel.TFrame", background=C["panel"])
        s.configure("Card.TFrame", background=C["panel"], relief="solid", borderwidth=1)
        s.configure("Toolbar.TFrame", background=C["panel"])
        s.configure("Inner.TFrame", background=C["panel"], borderwidth=0, relief="flat")
        s.configure("TLabel", background=C["bg"])
        s.configure("Panel.TLabel", background=C["panel"])
        s.configure("Card.TLabel", background=C["panel"], font=self.f_bold)
        s.configure("CardTitle.TLabel", background=C["panel"], font=(self.fam, 11, "bold"))
        s.configure("Hint.TLabel", background=C["panel"], foreground=C["muted"], font=self.f_small)
        s.configure("Muted.TLabel", background=C["panel"], foreground=C["muted"])
        s.configure("Head.TLabel", background=C["panel"], foreground=C["muted"], font=(self.fam, 8, "bold"))
        s.configure("Title.TLabel", background=C["panel"], font=self.f_title)
        s.configure("Status.TLabel", background=C["bg"], foreground=C["muted"])
        s.configure("TButton", padding=(10, 4), width=0, background=C["button"], bordercolor=C["border"],
                    lightcolor=C["button"], darkcolor=C["button"], relief="flat")
        s.map("TButton", background=[("pressed", C["accent_light"]), ("active", C["button_hover"]),
                                     ("disabled", C["button"])],
              foreground=[("disabled", C["disabled"])])
        s.configure("TMenubutton", background=C["button"], bordercolor=C["border"], lightcolor=C["button"],
                    darkcolor=C["button"], relief="flat", arrowcolor=C["arrow"])
        s.map("TMenubutton", background=[("pressed", C["accent_light"]), ("active", C["button_hover"])])
        s.configure("Tool.TButton", padding=(9, 4), width=0, background=C["panel"], lightcolor=C["panel"],
                    darkcolor=C["panel"], bordercolor=C["panel"])
        s.map("Tool.TButton", background=[("pressed", C["accent_light"]), ("active", C["tool_hover"])],
              bordercolor=[("active", C["border"])], foreground=[("disabled", C["disabled"])])
        s.configure("Theme.Tool.TButton", padding=(7, 2), font=(self.fam, 11))
        s.configure("Accent.TButton", background=C["accent_btn"], foreground=C["on_btn"], bordercolor=C["accent_btn"],
                    lightcolor=C["accent_btn"], darkcolor=C["accent_btn"], font=self.f_bold)
        s.map("Accent.TButton", background=[("pressed", C["accent_btn_press"]), ("active", C["accent_btn_press"])],
              foreground=[("disabled", C["accent_btn_off"])])
        s.configure("Sim.TButton", background=C["ok_btn"], foreground=C["on_btn"], bordercolor=C["ok_btn"],
                    lightcolor=C["ok_btn"], darkcolor=C["ok_btn"], font=self.f_bold)
        s.map("Sim.TButton", background=[("pressed", C["ok_btn_press"]), ("active", C["ok_btn_press"])])
        s.configure("Stop.TButton", background=C["danger_btn"], foreground=C["on_btn"], bordercolor=C["danger_btn"],
                    lightcolor=C["danger_btn"], darkcolor=C["danger_btn"], font=self.f_bold)
        s.map("Stop.TButton", background=[("pressed", C["danger_btn_press"]), ("active", C["danger_btn_press"])])
        s.configure("SimBar.TButton", padding=(9, 3), width=0, background=C["sim_btn"], lightcolor=C["sim_btn"],
                    darkcolor=C["sim_btn"], bordercolor=C["sim_border"])
        s.map("SimBar.TButton", background=[("pressed", C["accent_light"]), ("active", C["sim_btn_hover"])])
        s.configure("Danger.TButton", foreground=C["danger"])
        s.configure("TEntry", fieldbackground=C["field"], padding=4, bordercolor=C["border"],
                    lightcolor=C["field"], darkcolor=C["field"], insertcolor=C["text"])
        s.map("TEntry", bordercolor=[("focus", C["accent"])], lightcolor=[("focus", C["accent"])],
              background=[("readonly", C["clam_frame"])])
        s.configure("TCombobox", fieldbackground=C["field"], padding=3, arrowsize=int(12 * sc),
                    insertcolor=C["text"], arrowcolor=C["arrow"])
        s.map("TCombobox", fieldbackground=[("readonly", "focus", "#4a6984"), ("readonly", C["clam_frame"])],
              foreground=[("readonly", "focus", "#ffffff")],
              background=[("active", C["clam_active"]), ("pressed", C["clam_active"])],
              arrowcolor=[("disabled", C["clam_disabled"])])
        s.configure("TSpinbox", fieldbackground=C["field"], padding=3, arrowsize=int(10 * sc),
                    insertcolor=C["text"], arrowcolor=C["arrow"])
        s.map("TSpinbox", background=[("readonly", C["clam_frame"])], arrowcolor=[("disabled", C["clam_disabled"])])
        s.configure("TCheckbutton", indicatorbackground=C["field"], indicatorforeground=C["text"],
                    upperbordercolor=C["chk_hi"], lowerbordercolor=C["chk_lo"])
        s.map("TCheckbutton", indicatorbackground=[("pressed", C["clam_frame"]), ("disabled", C["clam_frame"])])
        s.configure("Card.TCheckbutton", background=C["panel"])
        s.map("Card.TCheckbutton", background=[("active", C["panel"])])
        s.configure("Panel.Horizontal.TScale", background=C["panel"], troughcolor=C["trough"])
        s.configure("Treeview", background=C["panel"], fieldbackground=C["panel"], foreground=C["text"],
                    borderwidth=0, rowheight=int(22 * sc), font=self.f_ui)
        s.configure("Treeview.Heading", background=C["heading"], foreground=C["text"], font=self.f_bold,
                    relief="flat", padding=(6, 3))
        s.map("Treeview.Heading", background=[("active", C["clam_active"])])
        s.map("Treeview", background=[("selected", C["accent_light"])],
              foreground=[("selected", C["text"])])
        s.configure("Lib.Treeview", rowheight=int(24 * sc))
        s.configure("TPanedwindow", background=C["border"])
        s.configure("TSeparator", background=C["border"])
        s.configure("Vertical.TScrollbar", arrowsize=int(12 * sc), background=C["thumb"],
                    bordercolor=C["bg"], troughcolor=C["bg"], gripcount=0, arrowcolor=C["arrow"])

    def _build_menu(self):
        m = tk.Menu(self.root)
        self.root.config(menu=m)
        fm = tk.Menu(m, tearoff=0)
        fm.add_command(label="New", accelerator="Ctrl+N", command=self.new_file)
        fm.add_command(label="Open…", accelerator="Ctrl+O", command=self.open_dialog)
        ex = tk.Menu(fm, tearoff=0)
        ex.add_command(label="LED with resistor", command=lambda: self.load_example("led"))
        ex.add_command(label="Voltage divider", command=lambda: self.load_example("divider"))
        ex.add_command(label="Arduino blink", command=lambda: self.load_example("blink"))
        ex.add_separator()
        ex.add_command(label="RC low-pass filter (simulate)", command=lambda: self.load_example("rc"))
        ex.add_command(label="Transistor switch (simulate)", command=lambda: self.load_example("transistor"))
        ex.add_command(label="555 LED blinker (simulate)", command=lambda: self.load_example("blinker"))
        ex.add_command(label="2-bit counter with flip-flops (simulate)", command=lambda: self.load_example("counter"))
        ex.add_separator()
        ex.add_command(label="Half adder: make your own component", command=lambda: self.load_example("halfadder"))
        fm.add_cascade(label="Open example", menu=ex)
        self.recent_menu = tk.Menu(fm, tearoff=0)
        fm.add_cascade(label="Recent files", menu=self.recent_menu)
        fm.add_separator()
        fm.add_command(label="Save", accelerator="Ctrl+S", command=self.save)
        fm.add_command(label="Save as…", accelerator="Ctrl+Shift+S", command=self.save_as)
        fm.add_separator()
        fm.add_command(label="Export image (SVG)…", command=self.export_svg)
        fm.add_command(label="Export netlist…", command=self.export_netlist)
        fm.add_separator()
        fm.add_command(label="Exit", command=self.on_close)
        m.add_cascade(label="File", menu=fm)
        self._update_recent_menu()

        em = tk.Menu(m, tearoff=0)
        em.add_command(label="Undo", accelerator="Ctrl+Z", command=self.undo)
        em.add_command(label="Redo", accelerator="Ctrl+Y", command=self.redo)
        em.add_separator()
        em.add_command(label="Copy", accelerator="Ctrl+C", command=self.copy_sel)
        em.add_command(label="Paste", accelerator="Ctrl+V", command=self.paste)
        em.add_command(label="Duplicate", accelerator="Ctrl+D", command=self.duplicate)
        em.add_command(label="Delete", accelerator="Del", command=self.delete_sel)
        em.add_separator()
        em.add_command(label="Rotate right", accelerator="R", command=lambda: self.rotate_sel(1))
        em.add_command(label="Rotate left", accelerator="Shift+R", command=lambda: self.rotate_sel(-1))
        em.add_command(label="Flip", accelerator="F", command=self.flip_sel)
        em.add_separator()
        em.add_command(label="Select all", accelerator="Ctrl+A", command=self.select_all)
        em.add_separator()
        em.add_command(label="Make component from selection…", accelerator="Ctrl+G",
                       command=self.make_component_from_selection)
        em.add_command(label="Show the circuit inside", accelerator="Ctrl+Shift+G", command=self.unpack_component)
        m.add_cascade(label="Edit", menu=em)

        vm = tk.Menu(m, tearoff=0)
        vm.add_command(label="Zoom in", accelerator="+", command=lambda: self.zoom_by(1.2))
        vm.add_command(label="Zoom out", accelerator="−", command=lambda: self.zoom_by(1 / 1.2))
        vm.add_command(label="Fit circuit to window", accelerator="0", command=self.fit)
        vm.add_separator()
        self.v_grid = tk.BooleanVar(value=self.show_grid)
        vm.add_checkbutton(label="Show grid", variable=self.v_grid, command=self._toggle_grid)
        self.v_style = tk.StringVar(value=self.wire_style)
        vm.add_radiobutton(label="Right-angle wires", variable=self.v_style, value="orthogonal",
                           command=lambda: self.set_wire_style(self.v_style.get()))
        vm.add_radiobutton(label="Straight wires", variable=self.v_style, value="straight",
                           command=lambda: self.set_wire_style(self.v_style.get()))
        vm.add_separator()
        tsm = tk.Menu(vm, tearoff=0)
        self.v_text_size = tk.StringVar(value=self.text_size)
        for key, name, _f in TEXT_SIZES:
            tsm.add_radiobutton(label=name, variable=self.v_text_size, value=key,
                                command=lambda: self.set_text_size(self.v_text_size.get()))
        vm.add_cascade(label="Diagram text size", menu=tsm)
        vm.add_separator()
        self.v_dark = tk.BooleanVar(value=THEME["dark"])
        vm.add_checkbutton(label="Dark mode", variable=self.v_dark, command=lambda: self.set_theme(self.v_dark.get()))
        m.add_cascade(label="View", menu=vm)

        cm = tk.Menu(m, tearoff=0)
        cm.add_command(label="Make component from selection…", accelerator="Ctrl+G",
                       command=self.make_component_from_selection)
        cm.add_command(label="Show the circuit inside selected component", accelerator="Ctrl+Shift+G",
                       command=self.unpack_component)
        cm.add_separator()
        cm.add_command(label="New component (draw pins only)…", command=self.new_component)
        cm.add_command(label="Edit selected component type…", command=self.edit_selected_def)
        cm.add_separator()
        cm.add_command(label="Import components…", command=self.import_library)
        cm.add_command(label="Export my components…", command=self.export_library)
        m.add_cascade(label="Components", menu=cm)

        tm = tk.Menu(m, tearoff=0)
        tm.add_command(label="Show connections (netlist)", command=self.show_netlist)
        tm.add_command(label="Check circuit", command=self.check_circuit)
        m.add_cascade(label="Tools", menu=tm)

        sm = tk.Menu(m, tearoff=0)
        sm.add_command(label="Start / stop simulation", accelerator="F5", command=self.sim_toggle)
        sm.add_command(label="Pause / resume", command=self.sim_pause)
        sm.add_command(label="Restart from zero", command=self.sim_restart)
        sm.add_separator()
        sm.add_command(label="Oscilloscope…", command=self.open_scope)
        sm.add_command(label="Frequency response (Bode plot)…", command=self.open_freq)
        sm.add_separator()
        self.v_volts = tk.BooleanVar(value=self.show_volts)
        sm.add_checkbutton(label="Show voltages on wires", variable=self.v_volts, command=self._toggle_volts)
        sm.add_command(label="What gets simulated?", command=self.show_sim_help)
        m.add_cascade(label="Simulate", menu=sm)

        hm = tk.Menu(m, tearoff=0)
        hm.add_command(label="Quick start", command=self.show_help)
        hm.add_command(label="What gets simulated?", command=self.show_sim_help)
        hm.add_command(label="About", command=self.show_about)
        m.add_cascade(label="Help", menu=hm)

    def _tool(self, parent, text, cmd, tip, style="Tool.TButton"):
        b = ttk.Button(parent, text=text, command=cmd, style=style, takefocus=False)
        b.pack(side="left", padx=1)
        Tooltip(b, tip)
        return b

    def _sep(self, parent):
        ttk.Separator(parent, orient="vertical").pack(side="left", fill="y", padx=8, pady=4)

    def _build_ui(self):
        sc = self.ui_scale
        # toolbar
        tb = ttk.Frame(self.root, style="Toolbar.TFrame", padding=(8, 5))
        tb.pack(side="top", fill="x")
        # right-hand buttons are packed first so they stay visible in a narrow window
        nb = ttk.Button(tb, text="+ New Component", style="Accent.TButton", takefocus=False,
                        command=lambda: self.new_component_menu(nb))
        nb.pack(side="right")
        Tooltip(nb, "Make your own part from the circuit you selected (Ctrl+G),\n"
                    "or draw a part with pins only")
        self.b_sim = ttk.Button(tb, text="▶  Simulate", style="Sim.TButton", command=self.sim_toggle, takefocus=False)
        self.b_sim.pack(side="right", padx=(0, 8))
        Tooltip(self.b_sim, "Run the circuit: live voltages and currents (F5)")
        self.b_theme = ttk.Button(tb, style="Theme.Tool.TButton", command=lambda: self.set_theme(not THEME["dark"]),
                                  takefocus=False)
        self.b_theme.pack(side="right", padx=(0, 4))
        self.b_theme_tip = Tooltip(self.b_theme, "")
        self._theme_button_text()
        self._tool(tb, "New", self.new_file, "New circuit (Ctrl+N)")
        self._tool(tb, "Open", self.open_dialog, "Open a circuit (Ctrl+O)")
        self._tool(tb, "Save", self.save, "Save (Ctrl+S)")
        self._sep(tb)
        self.b_undo = self._tool(tb, "Undo", self.undo, "Undo (Ctrl+Z)")
        self.b_redo = self._tool(tb, "Redo", self.redo, "Redo (Ctrl+Y)")
        self._sep(tb)
        self._tool(tb, "Rotate", lambda: self.rotate_sel(1), "Rotate selected part 90° (R)")
        self._tool(tb, "Flip", self.flip_sel, "Mirror selected part (F)")
        self._tool(tb, "Delete", self.delete_sel, "Delete selection (Del)")
        self._sep(tb)
        ttk.Label(tb, text="Wire color", background=C["panel"]).pack(side="left", padx=(2, 6))
        self.wire_sw = tk.Frame(tb, width=int(16 * sc), height=int(16 * sc), bg=ink(self.wire_color),
                                highlightthickness=1, highlightbackground=C["border"])
        self.wire_sw.pack(side="left")
        self.v_wcolor = tk.StringVar(value=WIRE_COLOR_NAMES.get(self.wire_color, "Blue"))
        cb = ttk.Combobox(tb, textvariable=self.v_wcolor, values=[n for n, _ in WIRE_COLORS],
                          state="readonly", width=8, takefocus=False)
        cb.pack(side="left", padx=(4, 0))
        cb.bind("<<ComboboxSelected>>", lambda e: self.set_wire_color(dict(WIRE_COLORS)[self.v_wcolor.get()]))
        Tooltip(cb, "Color for new wires (also recolors selected wires)")
        self._sep(tb)
        self._tool(tb, "−", lambda: self.zoom_by(1 / 1.2), "Zoom out")
        self.zoom_lbl = ttk.Label(tb, text="100%", width=5, anchor="center", background=C["panel"])
        self.zoom_lbl.pack(side="left")
        self._tool(tb, "+", lambda: self.zoom_by(1.2), "Zoom in")
        self._tool(tb, "Fit", self.fit, "Fit the whole circuit in the window (0)")
        self._sep(tb)
        self._tool(tb, "Connections", self.show_netlist, "List which pins are connected (netlist)")
        self._tool(tb, "Check circuit", self.check_circuit, "Look for shorts and unconnected parts")
        self._tb_line = tk.Frame(self.root, height=1, bg=C["border"])
        self._tb_line.pack(side="top", fill="x")
        self._build_simbar()

        # status bar
        sb = ttk.Frame(self.root, style="Bg.TFrame", padding=(10, 3))
        sb.pack(side="bottom", fill="x")
        self.status_var = tk.StringVar()
        self.count_var = tk.StringVar()
        ttk.Label(sb, textvariable=self.status_var, style="Status.TLabel").pack(side="left")
        ttk.Label(sb, textvariable=self.count_var, style="Status.TLabel").pack(side="right")

        pw = ttk.Panedwindow(self.root, orient="horizontal")
        pw.pack(side="top", fill="both", expand=True)

        # ---- library panel
        lib = ttk.Frame(pw, style="Panel.TFrame", padding=(10, 10, 6, 10))
        lib.columnconfigure(0, weight=1)
        lib.rowconfigure(2, weight=1)
        ttk.Label(lib, text="Components", style="Title.TLabel").grid(row=0, column=0, sticky="w")
        self.search_var = tk.StringVar()
        se = ttk.Entry(lib, textvariable=self.search_var)
        se.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(6, 6))
        self._placeholder(se, self.search_var, "Search parts…")
        self.search_var.trace_add("write", lambda *_: self.populate_library())
        self.lib_tree = ttk.Treeview(lib, show="tree", style="Lib.Treeview", selectmode="browse")
        self.lib_tree.grid(row=2, column=0, sticky="nsew")
        lsb = ttk.Scrollbar(lib, orient="vertical", command=self.lib_tree.yview)
        lsb.grid(row=2, column=1, sticky="ns")
        self.lib_tree.configure(yscrollcommand=lsb.set)
        self.lib_tree.column("#0", width=int(225 * sc))
        self.lib_tree.tag_configure("cat", font=self.f_bold, foreground=C["muted"])
        self.lib_tree.tag_configure("custom", foreground=C["accent_dark"])
        self.lib_tree.bind("<<TreeviewSelect>>", self._lib_select)
        self.lib_tree.bind("<ButtonPress-1>", self._lib_press)
        self.lib_tree.bind("<B1-Motion>", self._lib_motion)
        self.lib_tree.bind("<ButtonRelease-1>", self._lib_release)
        self.lib_tree.bind("<Double-1>", self._lib_double)
        self.lib_tree.bind("<Button-3>", self._lib_context)
        lb = ttk.Frame(lib, style="Panel.TFrame")
        lb.grid(row=3, column=0, columnspan=2, sticky="ew", pady=(6, 0))
        ttk.Button(lb, text="New…", command=self.new_component).pack(side="left")
        self.b_lib_edit = ttk.Button(lb, text="Edit…", command=self.edit_lib_def)
        self.b_lib_edit.pack(side="left", padx=4)
        Tooltip(self.b_lib_edit, "Edit your own part, or start a new part from a copy of a built-in one")
        self.b_lib_del = ttk.Button(lb, text="Delete", style="Danger.TButton", command=self.delete_lib_def)
        self.b_lib_del.pack(side="left")
        prev = ttk.Frame(lib, style="Card.TFrame", padding=8)
        prev.grid(row=4, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        prev.columnconfigure(0, weight=1)
        self.lib_pv = tk.Canvas(prev, width=int(210 * sc), height=int(120 * sc), bg=C["canvas"],
                                highlightthickness=0)
        self.lib_pv.grid(row=0, column=0, sticky="ew")
        self.lib_pv.bind("<Configure>", lambda e: self._lib_select())
        self.lib_name = ttk.Label(prev, text="", style="Card.TLabel")
        self.lib_name.grid(row=1, column=0, sticky="w", pady=(6, 0))
        self.lib_desc = ttk.Label(prev, text="", style="Hint.TLabel", wraplength=int(210 * sc), justify="left")
        self.lib_desc.grid(row=2, column=0, sticky="w")
        self.b_add = ttk.Button(prev, text="Add to circuit", style="Accent.TButton", command=self._lib_add)
        self.b_add.grid(row=3, column=0, sticky="ew", pady=(8, 0))
        ttk.Label(prev, text="or drag it onto the canvas", style="Hint.TLabel").grid(row=4, column=0)
        pw.add(lib, weight=0)

        # ---- canvas
        cf = ttk.Frame(pw, style="Panel.TFrame")
        self.cv = tk.Canvas(cf, bg=C["canvas"], highlightthickness=0, takefocus=True, cursor="arrow")
        self.cv.pack(fill="both", expand=True)
        pw.add(cf, weight=1)

        # ---- properties
        pr = ttk.Frame(pw, style="Panel.TFrame", padding=(12, 10, 12, 10))
        pr.columnconfigure(0, weight=1)
        self.props = pr
        pw.add(pr, weight=0)
        self.props_width = int(270 * sc)
        pr.configure(width=self.props_width)

        cv = self.cv
        cv.bind("<Configure>", lambda e: self.request_redraw())
        cv.bind("<ButtonPress-1>", self.on_press)
        cv.bind("<B1-Motion>", self.on_drag)
        cv.bind("<ButtonRelease-1>", self.on_release)
        cv.bind("<Double-Button-1>", self.on_double)
        cv.bind("<Motion>", self.on_motion)
        cv.bind("<Leave>", self.on_leave)
        cv.bind("<ButtonPress-3>", self.on_rpress)
        cv.bind("<B3-Motion>", self.on_rdrag)
        cv.bind("<ButtonRelease-3>", self.on_rrelease)
        cv.bind("<ButtonPress-2>", self.on_mpress)
        cv.bind("<B2-Motion>", self.on_rdrag)
        cv.bind("<ButtonRelease-2>", lambda e: self._end_pan())
        self.root.bind_all("<MouseWheel>", self.on_wheel, add="+")
        self.root.bind_all("<Button-4>", lambda e: self.on_wheel(e, 120), add="+")
        self.root.bind_all("<Button-5>", lambda e: self.on_wheel(e, -120), add="+")
        self.populate_library()
        self.set_status_hint()

    def _placeholder(self, entry, var, text):
        def show(_e=None):
            if not var.get():
                entry.configure(foreground=C["muted"])
                self._ph_active = True
                var.set(text)
        def hide(_e=None):
            if getattr(self, "_ph_active", False):
                self._ph_active = False
                entry.configure(foreground=C["text"])
                var.set("")
        self._ph_text = text
        entry.bind("<FocusIn>", hide)
        entry.bind("<FocusOut>", show)
        show()

    def search_text(self):
        if getattr(self, "_ph_active", False):
            return ""
        return self.search_var.get().strip().lower()

    def _bind_keys(self):
        r = self.root
        typing = (tk.Entry, ttk.Entry, tk.Text, ttk.Combobox, ttk.Spinbox)

        def make(fn, strict):
            # strict=True: only when the canvas (not a list or a text box) has the keyboard
            # strict=False: anywhere except text boxes;  strict=None: anywhere
            def h(e):
                w = self.root.focus_get()
                if w is not None and w.winfo_toplevel() is not self.root:
                    return None
                if strict is not None and isinstance(w, typing):
                    return None
                if strict and isinstance(w, (ttk.Treeview, tk.Listbox)):
                    return None
                fn(e)
                return "break"
            return h

        def shifted(e):
            return bool(e.state & 0x0001)

        anywhere = lambda fn: make(fn, None)
        text_safe = lambda fn: make(fn, False)
        canvas = lambda fn: make(fn, True)
        for k in ("n", "N"):
            r.bind("<Control-%s>" % k, anywhere(lambda e: self.new_file()))
        for k in ("o", "O"):
            r.bind("<Control-%s>" % k, anywhere(lambda e: self.open_dialog()))
        for k in ("s", "S"):
            r.bind("<Control-%s>" % k, anywhere(lambda e: self.save_as() if shifted(e) else self.save()))
        for k in ("z", "Z"):
            r.bind("<Control-%s>" % k, text_safe(lambda e: self.redo() if shifted(e) else self.undo()))
        for k in ("y", "Y"):
            r.bind("<Control-%s>" % k, text_safe(lambda e: self.redo()))
        for k in ("c", "C"):
            r.bind("<Control-%s>" % k, text_safe(lambda e: self.copy_sel()))
        for k in ("v", "V"):
            r.bind("<Control-%s>" % k, text_safe(lambda e: self.paste()))
        for k in ("d", "D"):
            r.bind("<Control-%s>" % k, text_safe(lambda e: self.duplicate()))
        for k in ("a", "A"):
            r.bind("<Control-%s>" % k, canvas(lambda e: self.select_all()))
        for k in ("g", "G"):
            r.bind("<Control-%s>" % k, text_safe(lambda e: self.unpack_component() if shifted(e)
                                                  else self.make_component_from_selection()))
        r.bind("<Delete>", canvas(lambda e: self.delete_sel()))
        r.bind("<BackSpace>", canvas(lambda e: self.backspace()))
        r.bind("<Escape>", anywhere(lambda e: self.escape()))
        r.bind("<F5>", anywhere(lambda e: self.sim_toggle()))
        for k in ("r", "R"):
            r.bind("<Key-%s>" % k, canvas(lambda e: self.rotate_sel(-1 if shifted(e) else 1)))
        for k in ("f", "F"):
            r.bind("<Key-%s>" % k, canvas(lambda e: self.flip_sel()))
        r.bind("<Key-plus>", canvas(lambda e: self.zoom_by(1.2)))
        r.bind("<Key-equal>", canvas(lambda e: self.zoom_by(1.2)))
        r.bind("<Key-minus>", canvas(lambda e: self.zoom_by(1 / 1.2)))
        r.bind("<Key-0>", canvas(lambda e: self.fit()))
        for key, d in (("Left", (-1, 0)), ("Right", (1, 0)), ("Up", (0, -1)), ("Down", (0, 1))):
            r.bind("<Key-%s>" % key, canvas(lambda e, d=d: self.nudge(*d)))
        r.bind("<KeyPress-space>", canvas(lambda e: self._space(True)))
        r.bind("<KeyRelease-space>", lambda e: self._space(False))

    def _space(self, down):
        self.space_down = down
        self.cv.configure(cursor="fleur" if down else "arrow")

    # ------------------------------------------------------------ utilities
    def rdef(self, comp):
        rd = self.library.resolve(comp["def"])
        if rd is None:
            did = comp["def"]
            if did not in self._missing:
                n = 1
                for w in self.wires.values():
                    for end in (w["a"], w["b"]):
                        if self.comps.get(end[0], {}).get("def") == did:
                            n = max(n, min(end[1] + 1, MAX_PINS))
                self._missing[did] = RDef({"id": did, "name": "Missing part", "prefix": "X",
                                           "symbol": "box", "w": 4, "h": n + 1, "color": "#fde2e4",
                                           "pins": [{"name": str(i + 1), "side": "left", "pos": i + 1}
                                                    for i in range(n)]})
            rd = self._missing[did]
        return rd

    def T(self, wx, wy):
        s = G * self.zoom
        return wx * s + self.panx, wy * s + self.pany

    def to_world(self, x, y):
        s = G * self.zoom
        return (x - self.panx) / s, (y - self.pany) / s

    def pin_world(self, key):
        c = self.comps[key[0]]
        rd = self.rdef(c)
        p = rd.pins[key[1]]
        return local_to_world(c, rd, p["x"], p["y"])

    def pin_dir(self, key):
        c = self.comps[key[0]]
        p = self.rdef(c).pins[key[1]]
        return dir_to_world(c, *DIRS[p["dir"]])

    def pin_name(self, key):
        c = self.comps.get(key[0])
        if not c:
            return "?"
        rd = self.rdef(c)
        pn = rd.pins[key[1]]["name"] if key[1] < len(rd.pins) else "?"
        return "%s.%s" % (c.get("label") or rd.name, pn)

    def comp_bbox(self, c, pad=0.0):
        rd = self.rdef(c)
        x0, y0, x1, y1 = rd.bbox
        pts = [local_to_world(c, rd, x, y) for x, y in ((x0, y0), (x1, y0), (x0, y1), (x1, y1))]
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        return min(xs) - pad, min(ys) - pad, max(xs) + pad, max(ys) + pad

    def wire_route(self, w):
        a, b = tuple(w["a"]), tuple(w["b"])
        pts = [self.pin_world(a)] + [tuple(p) for p in w.get("bends", [])] + [self.pin_world(b)]
        return route_points(pts, self.pin_dir(a), self.pin_dir(b), self.wire_style)

    def pin_at(self, wx, wy, tol_px=9):
        tol = tol_px / (G * self.zoom)
        best, bd = None, tol
        for cid in reversed(list(self.comps)):
            c = self.comps[cid]
            rd = self.rdef(c)
            for i, p in enumerate(rd.pins):
                px, py = local_to_world(c, rd, p["x"], p["y"])
                d = math.hypot(px - wx, py - wy)
                if d < bd:
                    best, bd = (cid, i), d
        return best

    def comp_at(self, wx, wy):
        for cid in reversed(list(self.comps)):
            x0, y0, x1, y1 = self.comp_bbox(self.comps[cid], 0.15)
            if x0 <= wx <= x1 and y0 <= wy <= y1:
                return cid
        return None

    def wire_at(self, wx, wy, tol_px=6):
        tol = tol_px / (G * self.zoom)
        best, bd = None, tol
        for wid in reversed(list(self.wires)):
            pts, _ = self.wire_route(self.wires[wid])
            for i in range(len(pts) - 1):
                d = seg_dist(wx, wy, pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1])
                if d < bd:
                    best, bd = wid, d
        return best

    def bend_at(self, wx, wy):
        tol = 7 / (G * self.zoom)
        for k in self.sel:
            if k[0] == "w" and k[1] in self.wires:
                for i, b in enumerate(self.wires[k[1]].get("bends", [])):
                    if abs(b[0] - wx) <= tol and abs(b[1] - wy) <= tol:
                        return k[1], i
        return None

    def connected_pins(self):
        s = set()
        for w in self.wires.values():
            s.add(tuple(w["a"]))
            s.add(tuple(w["b"]))
        return s

    def next_label(self, prefix):
        n = 0
        rx = re.compile(r"^%s(\d+)$" % re.escape(prefix))
        for c in self.comps.values():
            m = rx.match(c.get("label", ""))
            if m:
                n = max(n, int(m.group(1)))
        return "%s%d" % (prefix, n + 1)

    # ------------------------------------------------------------ undo
    def snapshot(self):
        return json.dumps({"comps": self.comps, "wires": self.wires})

    def checkpoint(self, snap=None):
        self.undo_stack.append(snap or self.snapshot())
        if len(self.undo_stack) > 200:
            self.undo_stack.pop(0)
        self.redo_stack.clear()

    def _restore(self, snap):
        d = json.loads(snap)
        self.comps, self.wires = d["comps"], d["wires"]
        # a part type may have been edited since this snapshot: drop wires on pins it no longer has
        for wid in [wid for wid, w in self.wires.items() if not self._wire_ok(w)]:
            del self.wires[wid]
        self.sel = {k for k in self.sel if (k[0] == "c" and k[1] in self.comps) or (k[0] == "w" and k[1] in self.wires)}
        self.highlight = None
        self.changed()

    def _wire_ok(self, w):
        """Both ends are on a part in the circuit, on a pin that part has."""
        for end in (w.get("a"), w.get("b")):
            c = self.comps.get(end[0]) if end else None
            if c is None or not 0 <= end[1] < len(self.rdef(c).pins):
                return False
        return True

    def undo(self):
        self.commit_props()
        if self.mode == "wiring":
            self.cancel_mode()
            return
        if not self.undo_stack:
            self.flash("Nothing to undo.")
            return
        self.redo_stack.append(self.snapshot())
        self._restore(self.undo_stack.pop())

    def redo(self):
        if not self.redo_stack:
            self.flash("Nothing to redo.")
            return
        self.undo_stack.append(self.snapshot())
        self._restore(self.redo_stack.pop())

    def changed(self, props=True):
        self.dirty = True
        self._nets_cache = None
        if self.sim is not None:
            self._sim_rebuild()
        self.update_title()
        self.request_redraw()
        if props:
            self.refresh_props()
        if self.netlist_win:
            self.netlist_win.refresh()

    # ------------------------------------------------------------ drawing
    def request_redraw(self):
        if not self._redraw_pending:
            self._redraw_pending = True
            self.root.after_idle(self._redraw)

    def _redraw(self):
        self._redraw_pending = False
        cv = self.cv
        cv.delete("all")
        W, H = cv.winfo_width(), cv.winfo_height()
        if self.panx is None:
            if W <= 1:   # not on screen yet: the canvas's <Configure> event redraws it once it has a size
                return
            self.panx, self.pany = W * 0.25, H * 0.3
        z = self.zoom
        s = G * z
        if self.show_grid and s >= 5:
            step = 1 if s >= 9 else 5
            gx0, gx1 = int(math.floor(-self.panx / s)), int(math.ceil((W - self.panx) / s))
            gy0, gy1 = int(math.floor(-self.pany / s)), int(math.ceil((H - self.pany) / s))
            for gx in range(gx0, gx1 + 1):
                if gx % step == 0:
                    X = gx * s + self.panx
                    cv.create_line(X, 0, X, H, fill=C["grid_major"] if gx % 5 == 0 else C["grid"], tags="grid")
            for gy in range(gy0, gy1 + 1):
                if gy % step == 0:
                    Y = gy * s + self.pany
                    cv.create_line(0, Y, W, Y, fill=C["grid_major"] if gy % 5 == 0 else C["grid"], tags="grid")
        if not self.comps:
            fs = int(15 * self.ui_scale)
            cv.create_text(W / 2, H / 2 - 30 * self.ui_scale, text="Start by dragging a part from the left onto this canvas",
                           fill=C["muted"], font=(self.fam, -fs, "bold"), tags="hint")
            cv.create_text(W / 2, H / 2 + 6 * self.ui_scale, fill=C["muted"], font=(self.fam, -int(12 * self.ui_scale)),
                           tags="hint", justify="center",
                           text="Then click a pin (small circle) and click another pin to connect them.\n"
                                "Or open a ready-made circuit:  File › Open example")
        connected = self.connected_pins()
        hl = self.highlight or {}
        hl_w = set(hl.get("wires", []))
        lw = max(1.5, 2.4 * z)
        for wid, w in self.wires.items():
            try:
                pts, _ = self.wire_route(w)
            except (KeyError, IndexError):
                continue
            cp = [c for p in pts for c in self.T(*p)]
            if wid in hl_w:
                cv.create_line(*cp, fill=C["highlight"], width=lw * 4, capstyle="round", joinstyle="round")
            if ("w", wid) in self.sel:
                cv.create_line(*cp, fill=C["sel_wire"], width=lw * 3.2, capstyle="round", joinstyle="round")
            cv.create_line(*cp, fill=ink(w.get("color") or WIRE_COLORS[0][1]), width=lw, capstyle="round",
                           joinstyle="round", tags=("wire", "w:" + wid))
        broken = None
        for cid, c in self.comps.items():
            try:
                render_component(cv, self.rdef(c), c, self.T, z, self.fam,
                                 state="selected" if ("c", cid) in self.sel else "normal",
                                 connected=connected, cid=cid, show_pin_labels=z >= 0.55,
                                 closed=self.is_closed(cid, c))
            except Exception:
                broken = broken or sys.exc_info()   # draw the rest; report the first problem below
        for key in hl.get("pins", []):
            if key[0] in self.comps and key[1] < len(self.rdef(self.comps[key[0]]).pins):
                x, y = self.T(*self.pin_world(key))
                r = 7 * z
                cv.create_oval(x - r, y - r, x + r, y + r, outline=C["net_pin"], width=2)
        wsel = [k[1] for k in self.sel if k[0] == "w" and k[1] in self.wires]
        if len(wsel) == 1:
            for b in self.wires[wsel[0]].get("bends", []):
                x, y = self.T(*b)
                r = max(3.5, 4.5 * z)
                cv.create_rectangle(x - r, y - r, x + r, y + r, fill=C["handle"], outline=C["select"], width=1.5)
        self._sim_draw()
        self.draw_overlay()
        self.update_counts()
        if broken:
            raise broken[1].with_traceback(broken[2])

    def is_closed(self, cid, c):
        """Draw this switch closed / push button pressed?"""
        sym = self.rdef(c).symbol
        if sym == "switch":
            return bool(c.get("closed"))
        if sym == "pushbutton":
            return self.sim is not None and cid in self.sim.pressed
        return False

    def draw_overlay(self):
        cv = self.cv
        cv.delete("overlay")
        z = self.zoom
        if self.mode == "wiring" and self.wiring:
            start = self.wiring["start"]
            mx, my = self.wiring.get("mouse", self.pin_world(start))
            target = self.pin_at(mx, my)
            if target and target != start:
                end = self.pin_world(target)
                db = self.pin_dir(target)
            else:
                end = (round(mx), round(my))
                db = None
            pts = [self.pin_world(start)] + list(self.wiring["bends"]) + [end]
            rp, _ = route_points(pts, self.pin_dir(start), db, self.wire_style)
            cp = [c for p in rp for c in self.T(*p)]
            if len(cp) >= 4:
                cv.create_line(*cp, fill=ink(self.wire_color), width=max(1.5, 2.4 * z), dash=(6, 4),
                               capstyle="round", tags="overlay")
            for key in (start, target):
                if key:
                    x, y = self.T(*self.pin_world(key))
                    r = 7 * max(z, 0.8)
                    cv.create_oval(x - r, y - r, x + r, y + r, outline=C["hover"], width=2.5, tags="overlay")
            if target and target != start:
                self._pin_tip(target)
        elif self.mode == "rubber" and self.drag:
            (x0, y0), (x1, y1) = self.drag["start"], self.drag["cur"]
            cv.create_rectangle(x0, y0, x1, y1, outline=C["select"], dash=(4, 3), fill="", tags="overlay")
        elif self.ghost:
            did, gx, gy = self.ghost
            rd = self.library.resolve(did)
            if rd:
                comp = {"x": gx, "y": gy, "rot": 0, "flip": False, "label": self.next_label(rd.prefix),
                        "value": rd.value}
                render_component(cv, rd, comp, self.T, z, self.fam, state="ghost", extra_tags=("overlay",))
        elif self.mode == "idle" and self.hover_pin and self.hover_pin[0] in self.comps:
            x, y = self.T(*self.pin_world(self.hover_pin))
            r = 7 * max(z, 0.8)
            cv.create_oval(x - r, y - r, x + r, y + r, outline=C["hover"], width=2.5, tags="overlay")
            self._pin_tip(self.hover_pin)
        elif self.mode == "idle" and self.sim is not None and self.sim_hover in self.comps:
            self._sim_tip(self.sim_hover)

    def _pin_tip(self, key):
        cv = self.cv
        x, y = self.T(*self.pin_world(key))
        net = self.pin_net_map().get(key)
        txt = self.pin_name(key).replace(".", " · pin ")
        if net:
            txt += "   (net %s)" % net["name"]
        else:
            txt += "   (not connected)"
        if self.sim is not None:
            v = self.sim.pin_v(key)
            if v is not None:
                txt += "   =  " + fmt_si(v, "V")
        t = cv.create_text(x + 14, y - 14, text=txt, anchor="sw", fill=C["tip_fg"],
                           font=(self.fam, -int(11 * self.ui_scale)), tags="overlay")
        bx = cv.bbox(t)
        if bx:
            r = cv.create_rectangle(bx[0] - 6, bx[1] - 3, bx[2] + 6, bx[3] + 3, fill=C["tip_bg"],
                                    outline="", tags="overlay")
            cv.tag_lower(r, t)

    def update_counts(self):
        nets = self.compute_nets()
        pct = int(round(100 * self.zoom / self.ui_scale))
        self.count_var.set("%d parts · %d wires · %d nets" % (len(self.comps), len(self.wires), len(nets)))
        self.zoom_lbl.configure(text="%d%%" % pct)

    def set_status_hint(self, text=None):
        if text is None:
            if self.mode == "wiring":
                text = "Wiring: click another pin to finish • click empty space to add a bend • Backspace removes a bend • Esc cancels"
            elif self.mode == "place" or self.ghost:
                text = "Click on the canvas to place the part (hold Shift to place several) • Esc cancels"
            elif self.sim is not None:
                text = ("Simulating: click switches, hold push buttons, hover over parts for readings • "
                        "you can keep editing • F5 stops")
            elif self.sel:
                text = "Drag to move • R rotate • F flip • Del delete • Ctrl+D duplicate"
            else:
                text = "Click a pin to start a wire • drag parts to move them • wheel to zoom • right-drag to pan"
        self.status_var.set(text)

    def flash(self, text, ms=3500):
        self.status_var.set(text)
        if self._flash_job:
            self.root.after_cancel(self._flash_job)
        self._flash_job = self.root.after(ms, lambda: self.set_status_hint())

    def update_title(self):
        name = os.path.basename(self.path) if self.path else "Untitled"
        self.root.title("%s%s — %s" % (name, " *" if self.dirty else "", APP_NAME))

    # ------------------------------------------------------------ nets
    def compute_nets(self):
        if self._nets_cache is not None:
            return self._nets_cache
        self._nets_cache = compute_nets_of(self.comps, self.wires.values())
        return self._nets_cache

    def pin_net_map(self):
        """(part id, pin number) -> net.  Cached with the nets (it is used on every mouse move)."""
        nets = self.compute_nets()
        if self._pin_net is None or self._pin_net[0] is not nets:
            self._pin_net = (nets, {k: net for net in nets for k in net["pins"]})
        return self._pin_net[1]

    def set_highlight(self, net):
        self.highlight = net
        self.request_redraw()

    # ------------------------------------------------------------ library panel
    def populate_library(self):
        tree = self.lib_tree
        q = self.search_text()
        open_state = {iid: tree.item(iid, "open") for iid in tree.get_children()}
        tree.delete(*tree.get_children())
        cats = {}
        for d in self.library.all():
            hay = " ".join([d.get("name", ""), d.get("category", ""), d.get("description", ""), d.get("value", "")]).lower()
            if q and q not in hay:
                continue
            cats.setdefault(d.get("category") or "My Components", []).append(d)
        for cat in self.library.categories() + sorted(set(cats) - set(self.library.categories())):
            if cat not in cats:
                continue
            iid = "cat:" + cat
            tree.insert("", "end", iid=iid, text=cat.upper(), open=bool(q) or open_state.get(iid, True), tags=("cat",))
            for d in cats[cat]:
                tree.insert(iid, "end", iid="def:" + d["id"], text="  " + d["name"] + ("  ★" if d.get("custom") else ""),
                            tags=("custom" if d.get("custom") else "builtin",))
        self._lib_select()

    def lib_selected_def(self):
        sel = self.lib_tree.selection()
        if sel and sel[0].startswith("def:"):
            return sel[0][4:]
        return None

    def _lib_select(self, _e=None):
        did = self.lib_selected_def()
        rd = self.library.resolve(did) if did else None
        if not rd:
            self.lib_pv.delete("all")
            self.lib_pv.create_text(self.lib_pv.winfo_width() / 2 or 100, 60 * self.ui_scale,
                                    text="Select a part to preview it", fill=C["muted"], font=self.f_ui)
            self.lib_name.configure(text="")
            self.lib_desc.configure(text="")
            self.b_add.state(["disabled"])
            self.b_lib_edit.configure(text="Edit…")
            self.b_lib_edit.state(["disabled"])
            self.b_lib_del.state(["disabled"])
            return
        fit_preview(self.lib_pv, rd, self.fam, max_zoom=1.2)
        self.lib_name.configure(text=rd.name)
        npins = len(rd.pins)
        self.lib_desc.configure(text="%s%s\n%d pin%s: %s" % (rd.description,
                                                             "\nMicrocontroller board" if rd.microcontroller else "",
                                                             npins, "" if npins == 1 else "s",
                                                             ", ".join(p["name"] for p in rd.pins[:12]) + ("…" if npins > 12 else "")))
        self.b_add.state(["!disabled"])
        self.b_lib_edit.state(["!disabled"])
        self.b_lib_edit.configure(text="Edit…")
        self.b_lib_del.state(["!disabled"] if rd.custom else ["disabled"])

    def _lib_press(self, e):
        iid = self.lib_tree.identify_row(e.y)
        self._lib_drag = None
        if iid.startswith("def:"):
            self._lib_drag = {"did": iid[4:], "x": e.x_root, "y": e.y_root, "active": False}

    def _over_canvas(self, xr, yr):
        w = self.root.winfo_containing(xr, yr)
        return w is self.cv

    def _lib_motion(self, e):
        d = self._lib_drag
        if not d:
            return
        if not d["active"] and math.hypot(e.x_root - d["x"], e.y_root - d["y"]) > 8:
            d["active"] = True
            self.lib_tree.configure(cursor="hand2")
        if d["active"]:
            if self._over_canvas(e.x_root, e.y_root):
                wx, wy = self.to_world(e.x_root - self.cv.winfo_rootx(), e.y_root - self.cv.winfo_rooty())
                self.ghost = (d["did"], round(wx), round(wy))
            else:
                self.ghost = None
            self.draw_overlay()

    def _lib_release(self, e):
        d = self._lib_drag
        self._lib_drag = None
        self.lib_tree.configure(cursor="")
        if d and d["active"]:
            self.ghost = None
            if self._over_canvas(e.x_root, e.y_root):
                wx, wy = self.to_world(e.x_root - self.cv.winfo_rootx(), e.y_root - self.cv.winfo_rooty())
                self.place_component(d["did"], wx, wy)
                self.cv.focus_set()
            self.draw_overlay()

    def _lib_double(self, e):
        iid = self.lib_tree.identify_row(e.y)
        if iid.startswith("def:"):
            self.start_place(iid[4:])
            return "break"

    def _lib_add(self):
        did = self.lib_selected_def()
        if did:
            self.start_place(did)

    def _lib_context(self, e):
        iid = self.lib_tree.identify_row(e.y)
        if not iid.startswith("def:"):
            return
        self.lib_tree.selection_set(iid)
        rd = self.library.resolve(iid[4:])
        m = tk.Menu(self.root, tearoff=0)
        m.add_command(label="Add to circuit", command=self._lib_add)
        m.add_command(label="Edit…" if rd.custom else "Copy & edit…", command=self.edit_lib_def)
        if self.can_add_picture(rd.id):
            m.add_command(label=("Change picture…" if rd.image else "Add picture…") if rd.custom
                          else "Copy with a picture…", command=lambda: self.add_picture(rd.id))
        if rd.custom:
            m.add_command(label="Delete from library", command=self.delete_lib_def)
        try:
            m.tk_popup(e.x_root, e.y_root)
        finally:
            m.grab_release()

    def start_place(self, did):
        self.cancel_mode()
        self.mode = "place"
        self.place_def = did
        self.cv.focus_set()
        x = self.root.winfo_pointerx() - self.cv.winfo_rootx()
        y = self.root.winfo_pointery() - self.cv.winfo_rooty()
        if 0 <= x < self.cv.winfo_width() and 0 <= y < self.cv.winfo_height():
            wx, wy = self.to_world(x, y)
        else:
            wx, wy = self.to_world(self.cv.winfo_width() / 2, self.cv.winfo_height() / 2)
        self.ghost = (did, round(wx), round(wy))
        self.set_status_hint()
        self.draw_overlay()

    def place_component(self, did, wx, wy):
        rd = self.library.resolve(did)
        if not rd:
            return None
        self.checkpoint()
        cid = new_id()
        self.comps[cid] = {"id": cid, "def": did, "x": int(round(wx)), "y": int(round(wy)), "rot": 0,
                           "flip": False, "label": self.next_label(rd.prefix), "value": rd.value, "notes": ""}
        self.sel = {("c", cid)}
        self.changed()
        self.flash("Added %s. Click its pins to wire it up." % self.comps[cid]["label"])
        return cid

    # ------------------------------------------------------------ mouse
    def _mods(self, e):
        return bool(e.state & 0x0001), bool(e.state & 0x0004)

    def on_press(self, e):
        self.commit_props()
        self.cv.focus_set()
        wx, wy = self.to_world(e.x, e.y)
        shift, ctrl = self._mods(e)
        if self.space_down:
            self._start_pan(e)
            return
        if self.mode == "place":
            self.place_component(self.place_def, wx, wy)
            if not shift:
                self.mode = "idle"
                self.place_def = None
                self.ghost = None
                self.set_status_hint()
            self.draw_overlay()
            return
        if self.mode == "wiring":
            pin = self.pin_at(wx, wy)
            if pin:
                if pin != self.wiring["start"]:
                    self.finish_wire(pin)
                return
            b = [round(wx), round(wy)]
            last = self.wiring["bends"][-1] if self.wiring["bends"] else self.pin_world(self.wiring["start"])
            if (b[0], b[1]) != (round(last[0]), round(last[1])):
                self.wiring["bends"].append((b[0], b[1]))
            self.wiring["mouse"] = (wx, wy)
            self.draw_overlay()
            return
        pin = self.pin_at(wx, wy)
        if pin:
            self.mode = "wiring"
            self.wiring = {"start": pin, "bends": [], "mouse": (wx, wy), "press": (e.x, e.y), "dragging": True}
            self.hover_pin = None
            self.set_status_hint()
            self.draw_overlay()
            return
        h = self.bend_at(wx, wy)
        if h:
            self.mode = "bend"
            self.drag = {"wire": h[0], "idx": h[1], "snap": self.snapshot(), "moved": False}
            return
        cid = self.comp_at(wx, wy)
        if cid:
            self._sim_press(cid)
            key = ("c", cid)
            if shift or ctrl:
                if key in self.sel:
                    self.sel.discard(key)
                    self.selection_changed()
                    return
                self.sel.add(key)
                self.selection_changed()
            elif key not in self.sel:
                self.sel = {key}
                self.selection_changed()
            self._begin_move(wx, wy)
            return
        wid = self.wire_at(wx, wy)
        if wid:
            key = ("w", wid)
            if shift or ctrl:
                self.sel ^= {key}
            else:
                self.sel = {key}
            self.selection_changed()
            return
        if not (shift or ctrl) and self.sel:
            self.sel = set()
            self.selection_changed()
        self.mode = "rubber"
        self.drag = {"start": (e.x, e.y), "cur": (e.x, e.y), "add": shift or ctrl}

    def _begin_move(self, wx, wy):
        csel = {k[1] for k in self.sel if k[0] == "c"}
        bends = {}
        for wid, w in self.wires.items():
            if w["a"][0] in csel and w["b"][0] in csel:
                bends[wid] = [list(b) for b in w.get("bends", [])]
        self.mode = "drag"
        self.drag = {"start": (wx, wy), "orig": {cid: (self.comps[cid]["x"], self.comps[cid]["y"]) for cid in csel},
                     "bends": bends, "snap": self.snapshot(), "moved": False, "d": (0, 0)}

    def on_drag(self, e):
        wx, wy = self.to_world(e.x, e.y)
        if self.mode == "pan":
            self._do_pan(e)
        elif self.mode == "wiring" and self.wiring:
            self.wiring["mouse"] = (wx, wy)
            self.draw_overlay()
        elif self.mode == "drag" and self.drag:
            sx, sy = self.drag["start"]
            dx, dy = int(round(wx - sx)), int(round(wy - sy))
            if (dx, dy) == self.drag["d"]:
                return
            self.drag["d"] = (dx, dy)
            self.drag["moved"] = self.drag["moved"] or dx != 0 or dy != 0
            for cid, (ox, oy) in self.drag["orig"].items():
                if cid in self.comps:
                    self.comps[cid]["x"], self.comps[cid]["y"] = ox + dx, oy + dy
            for wid, bl in self.drag["bends"].items():
                if wid in self.wires:
                    self.wires[wid]["bends"] = [[b[0] + dx, b[1] + dy] for b in bl]
            self._nets_cache = None
            self.request_redraw()
        elif self.mode == "bend" and self.drag:
            w = self.wires.get(self.drag["wire"])
            if w:
                nb = [round(wx), round(wy)]
                if w["bends"][self.drag["idx"]] != nb:
                    w["bends"][self.drag["idx"]] = nb
                    self.drag["moved"] = True
                    self.request_redraw()
        elif self.mode == "rubber" and self.drag:
            self.drag["cur"] = (e.x, e.y)
            self.draw_overlay()

    def on_release(self, e):
        wx, wy = self.to_world(e.x, e.y)
        if self._sim_pb is not None:
            if self.sim is not None:
                self.sim.pressed.discard(self._sim_pb)
                self.sim.bump()
            self._sim_pb = None
            self.request_redraw()
        click, self._sim_click = self._sim_click, None
        if self.mode == "pan":
            self._end_pan()
        elif self.mode == "wiring" and self.wiring and self.wiring.get("dragging"):
            self.wiring["dragging"] = False
            px, py = self.wiring["press"]
            if math.hypot(e.x - px, e.y - py) > 6:
                pin = self.pin_at(wx, wy)
                if pin and pin != self.wiring["start"]:
                    self.finish_wire(pin)
        elif self.mode in ("drag", "bend"):
            if self.drag and self.drag["moved"]:
                self.checkpoint(self.drag["snap"])
                self.changed()
            elif click and self.mode == "drag" and self.sim is not None:
                self.toggle_switch(click)
            self.mode = "idle"
            self.drag = None
        elif self.mode == "rubber" and self.drag:
            (x0, y0), (x1, y1) = self.drag["start"], (e.x, e.y)
            if abs(x1 - x0) > 3 or abs(y1 - y0) > 3:
                a = self.to_world(min(x0, x1), min(y0, y1))
                b = self.to_world(max(x0, x1), max(y0, y1))
                new = set()
                for cid, c in self.comps.items():
                    bx0, by0, bx1, by1 = self.comp_bbox(c)
                    if bx1 >= a[0] and bx0 <= b[0] and by1 >= a[1] and by0 <= b[1]:
                        new.add(("c", cid))
                for wid, w in self.wires.items():
                    pts, _ = self.wire_route(w)
                    if all(a[0] <= p[0] <= b[0] and a[1] <= p[1] <= b[1] for p in pts):
                        new.add(("w", wid))
                self.sel = (self.sel | new) if self.drag["add"] else new
                self.selection_changed()
            self.mode = "idle"
            self.drag = None
            self.draw_overlay()

    def on_double(self, e):
        if self.mode != "idle":
            self.on_press(e)
            return
        wx, wy = self.to_world(e.x, e.y)
        if self.pin_at(wx, wy):
            return
        cid = self.comp_at(wx, wy)
        if cid:
            if self.sim is not None and self.rdef(self.comps[cid]).symbol in ("switch", "pushbutton"):
                self.on_press(e)  # treat as another click on the switch
                return
            self.focus_label_entry()
            return
        wid = self.wire_at(wx, wy)
        if wid:
            w = self.wires[wid]
            pts, owner = self.wire_route(w)
            best, bi = None, 0
            for i in range(len(pts) - 1):
                d = seg_dist(wx, wy, pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1])
                if best is None or d < best:
                    best, bi = d, i
            ctrl_seg = owner[bi] if bi < len(owner) else 0
            self.checkpoint()
            w.setdefault("bends", []).insert(ctrl_seg, [round(wx), round(wy)])
            self.sel = {("w", wid)}
            self.changed()
            self.flash("Bend added — drag the white square to reshape the wire.")

    def on_motion(self, e):
        wx, wy = self.to_world(e.x, e.y)
        self._mouse = (e.x, e.y)
        if self.mode == "wiring" and self.wiring:
            self.wiring["mouse"] = (wx, wy)
            self.draw_overlay()
        elif self.mode == "place":
            self.ghost = (self.place_def, round(wx), round(wy))
            self.draw_overlay()
        elif self.mode == "idle":
            pin = self.pin_at(wx, wy)
            hov = None
            if self.sim is not None and not pin:
                hov = self.comp_at(wx, wy)
            clicky = hov and self.rdef(self.comps[hov]).symbol in ("switch", "pushbutton")
            cursor = "crosshair" if pin else ("hand2" if clicky else ("fleur" if self.space_down else "arrow"))
            if self.cv.cget("cursor") != cursor:
                self.cv.configure(cursor=cursor)
            if pin != self.hover_pin:
                self.hover_pin = pin
                self.draw_overlay()
            if hov or self.sim_hover:
                self.sim_hover = hov
                self.draw_overlay()

    def on_leave(self, _e):
        if self.mode == "place":
            self.ghost = None
        if self.hover_pin:
            self.hover_pin = None
        self.sim_hover = None
        self.draw_overlay()

    def _start_pan(self, e):
        self._pan_prev_mode = self.mode if self.mode in ("wiring", "place") else "idle"
        self._pan_from = (e.x, e.y, self.panx, self.pany)
        self.mode = "pan"
        self.cv.configure(cursor="fleur")

    def _do_pan(self, e):
        x0, y0, px, py = self._pan_from
        self.panx, self.pany = px + e.x - x0, py + e.y - y0
        self.request_redraw()

    def _end_pan(self):
        if self.mode == "pan":
            self.mode = getattr(self, "_pan_prev_mode", "idle")
            self.cv.configure(cursor="fleur" if self.space_down else "arrow")

    def on_mpress(self, e):
        self._start_pan(e)

    def on_rpress(self, e):
        self._rpress = (e.x, e.y, False)
        self._pan_from = (e.x, e.y, self.panx, self.pany)

    def on_rdrag(self, e):
        if self.mode != "pan":
            if getattr(self, "_rpress", None) and math.hypot(e.x - self._rpress[0], e.y - self._rpress[1]) > 4:
                self._pan_prev_mode = self.mode if self.mode in ("wiring", "place") else "idle"
                self._pan_from = (self._rpress[0], self._rpress[1], self.panx, self.pany)
                self.mode = "pan"
                self.cv.configure(cursor="fleur")
            elif not getattr(self, "_rpress", None):
                return
        if self.mode == "pan":
            self._do_pan(e)

    def on_rrelease(self, e):
        if self.mode == "pan":
            self._end_pan()
            self._rpress = None
            return
        self._rpress = None
        if self.mode in ("wiring", "place"):
            self.cancel_mode()
            return
        self.context_menu(e)

    def on_wheel(self, e, delta=None):
        if not self._over_canvas(e.x_root, e.y_root):
            return
        d = delta if delta is not None else e.delta
        if d == 0:
            return
        x = e.x_root - self.cv.winfo_rootx()
        y = e.y_root - self.cv.winfo_rooty()
        self.zoom_by(1.15 if d > 0 else 1 / 1.15, x, y)

    def zoom_by(self, f, x=None, y=None):
        if x is None:
            x, y = self.cv.winfo_width() / 2, self.cv.winfo_height() / 2
        nz = max(0.25 * self.ui_scale, min(4.0 * self.ui_scale, self.zoom * f))
        wx, wy = self.to_world(x, y)
        self.zoom = nz
        s = G * nz
        self.panx, self.pany = x - wx * s, y - wy * s
        self.request_redraw()

    def fit(self):
        if not self.comps:
            self.zoom = self.ui_scale
            self.panx, self.pany = self.cv.winfo_width() * 0.25, self.cv.winfo_height() * 0.3
            self.request_redraw()
            return
        xs, ys = [], []
        for c in self.comps.values():
            b = self.comp_bbox(c, 1.5)
            xs += [b[0], b[2]]
            ys += [b[1], b[3]]
        for w in self.wires.values():
            for b in w.get("bends", []):
                xs.append(b[0])
                ys.append(b[1])
        x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
        W, H = max(100, self.cv.winfo_width()), max(100, self.cv.winfo_height())
        z = min(W / ((x1 - x0) * G), H / ((y1 - y0) * G)) * 0.92
        self.zoom = max(0.25 * self.ui_scale, min(2.0 * self.ui_scale, z))
        s = G * self.zoom
        self.panx = W / 2 - (x0 + x1) / 2 * s
        self.pany = H / 2 - (y0 + y1) / 2 * s
        self.request_redraw()

    # ------------------------------------------------------------ actions
    def finish_wire(self, pin):
        start = self.wiring["start"]
        for w in self.wires.values():
            if {tuple(w["a"]), tuple(w["b"])} == {start, pin}:
                self.cancel_mode()
                self.flash("Those two pins are already connected.")
                return
        self.checkpoint()
        wid = new_id()
        self.wires[wid] = {"id": wid, "a": list(start), "b": list(pin),
                           "bends": [list(b) for b in self.wiring["bends"]], "color": self.wire_color}
        self.mode = "idle"
        self.wiring = None
        self.changed()
        self.flash("Connected %s → %s" % (self.pin_name(start), self.pin_name(pin)))

    def cancel_mode(self):
        if self.mode == "pan":
            self._end_pan()
        self.mode = "idle"
        self.wiring = None
        self.place_def = None
        self.ghost = None
        self.drag = None
        self.set_status_hint()
        self.draw_overlay()

    def escape(self):
        if self.mode != "idle":
            self.cancel_mode()
        elif self.sel:
            self.sel = set()
            self.selection_changed()
        if self.netlist_win and self.highlight:
            self.set_highlight(None)

    def backspace(self):
        if self.mode == "wiring" and self.wiring:
            if self.wiring["bends"]:
                self.wiring["bends"].pop()
                self.draw_overlay()
            return
        self.delete_sel()

    def selection_changed(self):
        self.request_redraw()
        self.refresh_props()
        self.set_status_hint()

    def sel_comps(self):
        return [k[1] for k in self.sel if k[0] == "c" and k[1] in self.comps]

    def sel_wires(self):
        return [k[1] for k in self.sel if k[0] == "w" and k[1] in self.wires]

    def delete_sel(self):
        self.commit_props()
        cs, ws = set(self.sel_comps()), set(self.sel_wires())
        if not cs and not ws:
            return
        self.checkpoint()
        for wid in list(self.wires):
            w = self.wires[wid]
            if wid in ws or w["a"][0] in cs or w["b"][0] in cs:
                del self.wires[wid]
        for cid in cs:
            del self.comps[cid]
        self.sel = set()
        self.changed()
        self.set_status_hint()

    def delete_wire(self, wid):
        if wid in self.wires:
            self.checkpoint()
            del self.wires[wid]
            self.sel.discard(("w", wid))
            self.changed()

    def rotate_sel(self, d=1):
        self.commit_props()
        cs = self.sel_comps()
        if not cs:
            self.flash("Select a part first, then press R to rotate it.")
            return
        self.checkpoint()
        for cid in cs:
            c = self.comps[cid]
            c["rot"] = (c.get("rot", 0) + d) % 4
        self.changed(props=False)

    def flip_sel(self):
        self.commit_props()
        cs = self.sel_comps()
        if not cs:
            self.flash("Select a part first, then press F to flip it.")
            return
        self.checkpoint()
        for cid in cs:
            self.comps[cid]["flip"] = not self.comps[cid].get("flip", False)
        self.changed(props=False)

    def nudge(self, dx, dy):
        cs = set(self.sel_comps())
        if not cs:
            s = G * self.zoom
            self.panx -= dx * s * 3
            self.pany -= dy * s * 3
            self.request_redraw()
            return
        self.checkpoint()
        for cid in cs:
            self.comps[cid]["x"] += dx
            self.comps[cid]["y"] += dy
        for w in self.wires.values():
            if w["a"][0] in cs and w["b"][0] in cs:
                w["bends"] = [[b[0] + dx, b[1] + dy] for b in w.get("bends", [])]
        self.changed(props=False)

    def select_all(self):
        self.sel = {("c", c) for c in self.comps} | {("w", w) for w in self.wires}
        self.selection_changed()

    def copy_sel(self):
        cs = set(self.sel_comps())
        if not cs:
            return
        self.clipboard = {
            "comps": [copy.deepcopy(self.comps[c]) for c in self.comps if c in cs],
            "wires": [copy.deepcopy(w) for w in self.wires.values() if w["a"][0] in cs and w["b"][0] in cs],
        }
        self.paste_n = 0
        self.flash("Copied %d part%s." % (len(cs), "" if len(cs) == 1 else "s"))

    def paste(self):
        if not self.clipboard:
            return
        self.paste_n += 1
        off = 2 * self.paste_n
        self.checkpoint()
        idmap = {}
        newsel = set()
        for c in self.clipboard["comps"]:
            nc = copy.deepcopy(c)
            nid = new_id()
            idmap[c["id"]] = nid
            nc["id"] = nid
            nc["x"] += off
            nc["y"] += off
            rd = self.rdef(nc)
            if re.match(r"^%s\d+$" % re.escape(rd.prefix), nc.get("label", "")):
                nc["label"] = self.next_label(rd.prefix)
            self.comps[nid] = nc
            newsel.add(("c", nid))
        for w in self.clipboard["wires"]:
            nw = copy.deepcopy(w)
            nid = new_id()
            nw["id"] = nid
            nw["a"][0] = idmap[w["a"][0]]
            nw["b"][0] = idmap[w["b"][0]]
            nw["bends"] = [[b[0] + off, b[1] + off] for b in w.get("bends", [])]
            self.wires[nid] = nw
            newsel.add(("w", nid))
        self.sel = newsel
        self.changed()

    def duplicate(self):
        saved = self.clipboard
        self.copy_sel()
        if self.clipboard is not saved:
            self.paste()
            self.clipboard = saved if saved else self.clipboard

    def set_wire_color(self, col):
        self.wire_color = col
        self.wire_sw.configure(bg=ink(col))
        self.v_wcolor.set(WIRE_COLOR_NAMES.get(col, "Blue"))
        self.settings["wire_color"] = col
        self.save_settings()
        ws = self.sel_wires()
        if ws:
            self.checkpoint()
            for wid in ws:
                self.wires[wid]["color"] = col
            self.changed()

    def recolor_wires(self, wids, col):
        self.checkpoint()
        for wid in wids:
            if wid in self.wires:
                self.wires[wid]["color"] = col
        self.changed()

    def set_wire_style(self, style):
        self.wire_style = style
        self.settings["wire_style"] = style
        self.save_settings()
        self.request_redraw()

    def set_text_size(self, key):
        self.text_size = key
        set_diagram_text_size(key)
        self.settings["text_size"] = key
        self.save_settings()
        self.request_redraw()
        try:
            self._lib_select()  # library preview uses the same text size
        except tk.TclError:
            pass

    def _toggle_grid(self):
        self.show_grid = self.v_grid.get()
        self.settings["show_grid"] = self.show_grid
        self.save_settings()
        self.request_redraw()

    def save_settings(self):
        try:
            save_json(self.settings_path, self.settings)
        except OSError:
            pass

    # ------------------------------------------------------------ light / dark mode
    def _theme_button_text(self):
        dark = THEME["dark"]
        self.b_theme.configure(text="☀" if dark else "☾")
        self.b_theme_tip.text = ("Switch to light mode  (View › Dark mode)" if dark
                                 else "Switch to dark mode  (View › Dark mode)")

    def set_theme(self, dark):
        """Switch between light and dark mode, live, in every open window."""
        dark = bool(dark)
        self.v_dark.set(dark)
        if dark == THEME["dark"]:
            return
        self.commit_props()
        old = dict(C)
        set_palette(dark)
        self._setup_style()
        retheme_widgets(self.root, old, C)
        self.wire_sw.configure(bg=ink(self.wire_color), highlightbackground=C["border"])
        self._theme_button_text()
        self.settings["theme"] = "dark" if dark else "light"
        self.save_settings()
        set_title_bar_theme(self.root, dark)
        for w in self.root.winfo_children():
            if isinstance(w, tk.Toplevel):
                set_title_bar_theme(w, dark)
                if hasattr(w, "on_theme"):
                    try:
                        w.on_theme()
                    except tk.TclError:
                        pass
        self.refresh_props()
        self._lib_select()
        self._redraw()

    def context_menu(self, e):
        wx, wy = self.to_world(e.x, e.y)
        cid = self.comp_at(wx, wy)
        wid = None if cid else self.wire_at(wx, wy)
        m = tk.Menu(self.root, tearoff=0)
        if cid:
            if ("c", cid) not in self.sel:
                self.sel = {("c", cid)}
                self.selection_changed()
            m.add_command(label="Rotate right   R", command=lambda: self.rotate_sel(1))
            m.add_command(label="Rotate left   Shift+R", command=lambda: self.rotate_sel(-1))
            m.add_command(label="Flip   F", command=self.flip_sel)
            m.add_separator()
            m.add_command(label="Duplicate   Ctrl+D", command=self.duplicate)
            m.add_command(label="Copy   Ctrl+C", command=self.copy_sel)
            rd = self.rdef(self.comps[cid])
            m.add_command(label="Edit component type…" if rd.custom else "Copy as new component type…",
                          command=self.edit_selected_def)
            m.add_separator()
            n = len(self.sel_comps())
            m.add_command(label="Make component from %s…   Ctrl+G" % ("these %d parts" % n if n > 1 else "this part"),
                          command=self.make_component_from_selection)
            if self.is_block(cid) and n == 1:
                m.add_command(label="Show the circuit inside   Ctrl+Shift+G", command=lambda: self.unpack_component(cid))
            self._plot_menu_items(m, cid)
            m.add_separator()
            m.add_command(label="Delete   Del", command=self.delete_sel)
        elif wid:
            if ("w", wid) not in self.sel:
                self.sel = {("w", wid)}
                self.selection_changed()
            cm = tk.Menu(m, tearoff=0)
            for name, col in WIRE_COLORS:
                cm.add_command(label=name, command=lambda c=col: self.recolor_wires(self.sel_wires(), c))
            m.add_cascade(label="Wire color", menu=cm)
            m.add_command(label="Remove bends", command=lambda: self.straighten(self.sel_wires()))
            m.add_separator()
            m.add_command(label="Plot this voltage (oscilloscope)", command=lambda: self.plot_net(wid))
            m.add_separator()
            m.add_command(label="Delete wire   Del", command=self.delete_sel)
        else:
            m.add_command(label="Paste   Ctrl+V", command=self.paste,
                          state="normal" if self.clipboard else "disabled")
            m.add_command(label="Select all   Ctrl+A", command=self.select_all)
            m.add_command(label="Fit to window   0", command=self.fit)
            m.add_separator()
            m.add_command(label="Make component from selection…   Ctrl+G", command=self.make_component_from_selection,
                          state="normal" if self.sel_comps() else "disabled")
            m.add_command(label="New component (draw pins only)…", command=self.new_component)
        try:
            m.tk_popup(e.x_root, e.y_root)
        finally:
            m.grab_release()

    def straighten(self, wids):
        if not wids:
            return
        self.checkpoint()
        for wid in wids:
            self.wires[wid]["bends"] = []
        self.changed()

    # ------------------------------------------------------------ properties panel
    def refresh_props(self):
        for w in self.props.winfo_children():
            w.destroy()
        self.prop_vars = None
        self.sim_vars = None
        cs, ws = self.sel_comps(), self.sel_wires()
        if not cs and not ws:
            if self.sim is not None:
                self._props_sim_summary()
            else:
                self._props_project()
        elif len(cs) == 1 and not ws:
            self._props_component(cs[0])
        elif len(ws) == 1 and not cs:
            self._props_wire(ws[0])
        else:
            self._props_multi(cs, ws)

    def _head(self, text, row):
        ttk.Label(self.props, text=text.upper(), style="Head.TLabel").grid(row=row, column=0, columnspan=2, sticky="w", pady=(14, 4))

    def _props_project(self):
        f = self.props
        wl = self.props_width - 30
        name = os.path.splitext(os.path.basename(self.path))[0] if self.path else "Untitled circuit"
        ttk.Label(f, text=name, style="Title.TLabel", wraplength=wl).grid(row=0, column=0, sticky="w")
        nets = self.compute_nets()
        ttk.Label(f, text="%d parts · %d wires · %d nets" % (len(self.comps), len(self.wires), len(nets)),
                  style="Muted.TLabel").grid(row=1, column=0, sticky="w")
        self._head("Getting started", 2)
        steps = [
            ("1", "Drag a part from the left onto the canvas (or double-click it)."),
            ("2", "Click a pin (small circle), then click a pin on another part to connect them."),
            ("3", "While wiring, click empty space to add bends."),
            ("4", "Click a part to change its label and value here, or give it a picture."),
            ("5", "Press  ▶ Simulate  to see the circuit run: live voltages, currents and glowing LEDs."),
            ("6", "Make your own part: build its circuit, select it, then  + New Component › From the "
                  "selected circuit  (Ctrl+G). Component Pins (Building Blocks) set its pins."),
        ]
        sf = ttk.Frame(f, style="Panel.TFrame")
        sf.grid(row=3, column=0, sticky="ew")
        for i, (n, t) in enumerate(steps):
            tk.Label(sf, text=n, bg=C["accent_light"], fg=C["accent_dark"], font=self.f_bold, width=2).grid(
                row=i, column=0, sticky="nw", pady=3, padx=(0, 8))
            ttk.Label(sf, text=t, style="Panel.TLabel", wraplength=wl - 30, justify="left").grid(row=i, column=1, sticky="w", pady=3)
        self._head("Shortcuts", 4)
        kf = ttk.Frame(f, style="Panel.TFrame")
        kf.grid(row=5, column=0, sticky="ew")
        for i, (k, d) in enumerate(SHORTCUTS[3:]):
            ttk.Label(kf, text=k, style="Card.TLabel").grid(row=i, column=0, sticky="w", padx=(0, 10), pady=1)
            ttk.Label(kf, text=d, style="Muted.TLabel").grid(row=i, column=1, sticky="w", pady=1)

    def _props_component(self, cid):
        f = self.props
        c = self.comps[cid]
        rd = self.rdef(c)
        wl = self.props_width - 30
        simming = self.sim is not None
        r = 0
        self.prop_title = ttk.Label(f, text=c.get("label") or rd.name, style="Title.TLabel")
        self.prop_title.grid(row=r, column=0, columnspan=2, sticky="w")
        r += 1
        ttk.Label(f, text="%s · %s%s" % (rd.name, rd.category, "  ★ custom" if rd.custom else ""),
                  style="Muted.TLabel", wraplength=wl).grid(row=r, column=0, columnspan=2, sticky="w")
        r += 1
        if simming:
            r = self._props_sim_readings(cid, c, rd, r)
        else:
            info = ttk.Frame(f, style="Panel.TFrame")
            info.grid(row=r, column=0, columnspan=2, sticky="ew")
            r += 1
            if rd.image:
                iw, ih = rd.image["w"], rd.image["h"]
                mw = min(wl, int(iw * 2 * self.ui_scale))
                mh = min(int(120 * self.ui_scale), int(ih * 2 * self.ui_scale))
                ph = picture_photo(rd.image, mw, mh, rd.image_key)
                if ph is not None:
                    pl = tk.Label(info, image=ph, bg=C["panel"], bd=0, cursor="hand2")
                    pl.image = ph
                    pl.pack(anchor="w", pady=(8, 2))
                    tip = Tooltip(pl, "Click to see the picture bigger")
                    pl.bind("<Button-1>", lambda e, r_=rd, t=tip: (t._leave(), self.show_picture(r_)))
            if rd.description:
                ttk.Label(info, text=rd.description, style="Hint.TLabel", wraplength=wl, justify="left").pack(
                    anchor="w", pady=(4, 0))
            if self.is_block(cid):
                ib = ttk.Button(info, text="Show the circuit inside", command=lambda: self.unpack_component(cid))
                ib.pack(anchor="w", pady=(6, 0))
                Tooltip(ib, "Put the circuit this part is made of back on the canvas to change it.\n"
                            "Then keep it selected and click Make component to update every copy.")
            v_mcu = tk.BooleanVar(value=self.is_mcu(c))
            mc = ttk.Checkbutton(info, text="Microcontroller / dev board", variable=v_mcu, style="Card.TCheckbutton",
                                 command=lambda: self.set_mcu(cid, v_mcu.get()))
            mc.pack(anchor="w", pady=(6, 0))
            Tooltip(mc, "Check circuit won’t list unused pins on a microcontroller;\n"
                        "it checks that its power and ground are wired instead.")
            if self.can_add_picture(c["def"]):
                pb = ttk.Button(info, text="Change picture…" if rd.image else "Add picture…",
                                command=lambda: self.add_picture(c["def"], use_for=cid))
                pb.pack(anchor="w", pady=(6, 0))
                Tooltip(pb, "Show a photo or drawing of the part inside it" if rd.custom
                        else "Saves your own copy of this part with a picture")
        r = self._props_sim_controls(cid, c, rd, r)
        self._head("Properties", r)
        r += 1
        v_label = tk.StringVar(value=c.get("label", ""))
        v_value = tk.StringVar(value=c.get("value", ""))
        ttk.Label(f, text="Label", style="Panel.TLabel").grid(row=r, column=0, sticky="w")
        e1 = ttk.Entry(f, textvariable=v_label)
        e1.grid(row=r + 1, column=0, columnspan=2, sticky="ew", pady=(2, 6))
        ttk.Label(f, text="Value", style="Panel.TLabel").grid(row=r + 2, column=0, sticky="w")
        e2 = ttk.Entry(f, textvariable=v_value)
        e2.grid(row=r + 3, column=0, columnspan=2, sticky="ew", pady=(2, 6))
        r += 4
        t = None
        if not simming:
            ttk.Label(f, text="Notes", style="Panel.TLabel").grid(row=r, column=0, sticky="w")
            t = tk.Text(f, height=3, width=24, wrap="word", font=self.f_ui, relief="flat", highlightthickness=1,
                        padx=6, pady=4, **text_colors())
            t.insert("1.0", c.get("notes", ""))
            t.grid(row=r + 1, column=0, columnspan=2, sticky="ew", pady=(2, 0))
            t.bind("<FocusOut>", lambda e: self.commit_props())
            r += 2
        for w in (e1, e2):
            w.bind("<Return>", lambda e: (self.commit_props(), self.cv.focus_set()))
            w.bind("<FocusOut>", lambda e: self.commit_props())
        self.prop_vars = {"cid": cid, "label": v_label, "value": v_value, "notes": t, "label_entry": e1}
        of = ttk.Frame(f, style="Panel.TFrame")
        of.grid(row=r, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        r += 1
        ttk.Button(of, text="Rotate left", command=lambda: self.rotate_sel(-1)).pack(side="left")
        ttk.Button(of, text="Rotate right", command=lambda: self.rotate_sel(1)).pack(side="left", padx=4)
        ttk.Button(of, text="Flip", command=self.flip_sel).pack(side="left")
        self._head("Pins (%d)" % len(rd.pins), r)
        r += 1
        rows = min(9, max(2, len(rd.pins)))
        if simming:
            tv = ttk.Treeview(f, columns=("pin", "v", "i"), show="headings", height=rows, selectmode="browse")
            tv.heading("pin", text="Pin")
            tv.heading("v", text="Voltage")
            tv.heading("i", text="Current in")
            tv.column("pin", width=int(56 * self.ui_scale), stretch=False)
            tv.column("v", width=int(84 * self.ui_scale), anchor="e")
            tv.column("i", width=int(84 * self.ui_scale), anchor="e")
            for i, p in enumerate(rd.pins):
                tv.insert("", "end", iid=str(i), values=(p["name"], "", ""))
            tv.bind("<Double-1>", lambda e, tv=tv: self._plot_pin_row(cid, tv))
            if self.sim_vars is not None:
                self.sim_vars["tree"] = tv
            self._sim_update_props()
        else:
            tv = ttk.Treeview(f, columns=("pin", "to"), show="headings", height=rows, selectmode="none")
            tv.heading("pin", text="Pin")
            tv.heading("to", text="Connected to")
            tv.column("pin", width=int(60 * self.ui_scale), stretch=False)
            tv.column("to", width=int(170 * self.ui_scale))
            conn = {}
            for w in self.wires.values():
                a, b = tuple(w["a"]), tuple(w["b"])
                if a[0] == cid:
                    conn.setdefault(a[1], []).append(self.pin_name(b))
                if b[0] == cid:
                    conn.setdefault(b[1], []).append(self.pin_name(a))
            for i, p in enumerate(rd.pins):
                tv.insert("", "end", values=(p["name"], ", ".join(conn.get(i, [])) or "—"))
        tv.grid(row=r, column=0, sticky="ew")
        if len(rd.pins) > 9:
            sb = ttk.Scrollbar(f, orient="vertical", command=tv.yview)
            sb.grid(row=r, column=1, sticky="ns")
            tv.configure(yscrollcommand=sb.set)
        r += 1
        bf = ttk.Frame(f, style="Panel.TFrame")
        bf.grid(row=r, column=0, columnspan=2, sticky="ew", pady=(14, 0))
        r += 1
        ttk.Button(bf, text="Duplicate", command=self.duplicate).pack(side="left")
        ttk.Button(bf, text="Delete", style="Danger.TButton", command=self.delete_sel).pack(side="left", padx=4)
        if rd.custom:
            ttk.Button(f, text="Edit component type…", command=self.edit_selected_def).grid(
                row=r, column=0, columnspan=2, sticky="w", pady=(8, 0))
            r += 1
        if self.comps[cid]["def"] == PORT_DEF and not simming:
            self._head("Component Pin", r)
            ttk.Label(f, text="Its label is the pin name. Select it together with your circuit and click Make "
                              "component: it becomes a pin of the new part.", style="Hint.TLabel",
                      wraplength=wl, justify="left").grid(row=r + 1, column=0, columnspan=2, sticky="w")
            r += 2
        f.columnconfigure(0, weight=1)

    def show_picture(self, rd):
        """Small window with the part's picture at full size."""
        if not rd.image:
            return
        win = tk.Toplevel(self.root)
        win.title("%s — %s" % (rd.name, APP_NAME))
        win.configure(bg=C["panel"])
        win.transient(self.root)
        s = self.ui_scale
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        ph = picture_photo(rd.image, min(int(rd.image["w"] * s), sw - 120), min(int(rd.image["h"] * s), sh - 160),
                           rd.image_key)
        if ph is None:
            win.destroy()
            return
        lbl = tk.Label(win, image=ph, bg=C["panel"], bd=0)
        lbl.image = ph
        lbl.pack(padx=14, pady=(14, 6))
        ttk.Label(win, text=rd.name, style="Card.TLabel").pack(pady=(0, 12))
        win.bind("<Escape>", lambda e: win.destroy())
        win.bind("<Button-1>", lambda e: win.destroy())
        win.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() - win.winfo_reqwidth()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - win.winfo_reqheight()) // 3
        win.geometry("+%d+%d" % (max(0, x), max(0, y)))
        win.focus_set()

    def focus_label_entry(self):
        if self.prop_vars:
            e = self.prop_vars["label_entry"]
            e.focus_set()
            e.select_range(0, "end")

    def commit_props(self):
        pv = self.prop_vars
        if not pv or pv["cid"] not in self.comps:
            return
        c = self.comps[pv["cid"]]
        try:
            label = pv["label"].get().strip()
            value = pv["value"].get().strip()
            notes = pv["notes"].get("1.0", "end").strip() if pv["notes"] is not None else c.get("notes", "")
        except tk.TclError:
            return
        if (label, value, notes) != (c.get("label", ""), c.get("value", ""), c.get("notes", "")):
            self.checkpoint()
            c["label"], c["value"], c["notes"] = label, value, notes
            try:
                self.prop_title.configure(text=label or self.rdef(c).name)
            except tk.TclError:
                pass
            self.changed(props=False)

    def _props_wire(self, wid):
        f = self.props
        w = self.wires[wid]
        a, b = tuple(w["a"]), tuple(w["b"])
        ttk.Label(f, text="Wire", style="Title.TLabel").grid(row=0, column=0, sticky="w")
        net = self.pin_net_map().get(a)
        txt = "On net %s" % net["name"] if net else ""
        if self.sim is not None and net:
            v = self.sim.pin_v(a)
            if v is not None:
                txt += "  ·  %s" % fmt_si(v, "V")
        ttk.Label(f, text=txt, style="Muted.TLabel").grid(row=1, column=0, sticky="w")
        self._head("Connects", 2)
        cf = ttk.Frame(f, style="Panel.TFrame")
        cf.grid(row=3, column=0, sticky="ew")
        for i, (lbl, k) in enumerate((("From", a), ("To", b))):
            ttk.Label(cf, text=lbl, style="Muted.TLabel", width=6).grid(row=i, column=0, sticky="w")
            ttk.Label(cf, text=self.pin_name(k).replace(".", "  ·  pin "), style="Card.TLabel").grid(row=i, column=1, sticky="w", pady=2)
        self._head("Color", 4)
        self._color_swatches(5, [wid], w.get("color"))
        self._head("Shape", 6)
        nb = len(w.get("bends", []))
        ttk.Label(f, text="%d bend%s. Double-click the wire to add one; drag the white squares to move them."
                  % (nb, "" if nb == 1 else "s"), style="Hint.TLabel", wraplength=self.props_width - 30,
                  justify="left").grid(row=7, column=0, sticky="w")
        bf = ttk.Frame(f, style="Panel.TFrame")
        bf.grid(row=8, column=0, sticky="ew", pady=(8, 0))
        rb = ttk.Button(bf, text="Remove bends", command=lambda: self.straighten([wid]))
        rb.pack(side="left")
        if not nb:
            rb.state(["disabled"])
        ttk.Button(bf, text="Delete wire", style="Danger.TButton", command=lambda: self.delete_wire(wid)).pack(side="left", padx=4)
        ttk.Button(f, text="Plot this voltage", command=lambda: self.plot_net(wid)).grid(
            row=9, column=0, sticky="w", pady=(10, 0))
        f.columnconfigure(0, weight=1)

    def _color_swatches(self, row, wids, current):
        sf = ttk.Frame(self.props, style="Panel.TFrame")
        sf.grid(row=row, column=0, sticky="w")
        sz = int(20 * self.ui_scale)
        for i, (name, col) in enumerate(WIRE_COLORS):
            fr = tk.Frame(sf, width=sz, height=sz, bg=ink(col), cursor="hand2", highlightthickness=2,
                          highlightbackground=C["text"] if col == current else C["panel"])
            fr.grid(row=i // 5, column=i % 5, padx=2, pady=2)
            fr.bind("<Button-1>", lambda e, c=col: self.recolor_wires(wids, c))
            Tooltip(fr, name)

    def _props_multi(self, cs, ws):
        f = self.props
        parts = []
        if cs:
            parts.append("%d part%s" % (len(cs), "" if len(cs) == 1 else "s"))
        if ws:
            parts.append("%d wire%s" % (len(ws), "" if len(ws) == 1 else "s"))
        ttk.Label(f, text=" + ".join(parts), style="Title.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(f, text="selected", style="Muted.TLabel").grid(row=1, column=0, sticky="w")
        bf = ttk.Frame(f, style="Panel.TFrame")
        bf.grid(row=2, column=0, sticky="w", pady=(12, 0))
        if cs:
            ttk.Button(bf, text="Rotate", command=lambda: self.rotate_sel(1)).pack(side="left")
            ttk.Button(bf, text="Duplicate", command=self.duplicate).pack(side="left", padx=4)
        ttk.Button(bf, text="Delete", style="Danger.TButton", command=self.delete_sel).pack(side="left")
        row = 3
        if cs:
            self._make_component_box(row, cs)
            row += 2
        if ws:
            self._head("Wire color", row)
            self._color_swatches(row + 1, ws, None)

    def _make_component_box(self, row, cs):
        """Properties panel: turn the selection into a component."""
        wl = self.props_width - 30
        self._head("Make your own component", row)
        bx = ttk.Frame(self.props, style="Panel.TFrame")
        bx.grid(row=row + 1, column=0, sticky="ew")
        chosen = set(cs)
        ports = [c.get("label") or "?" for cid, c in self.comps.items() if cid in chosen and c["def"] == PORT_DEF]
        if ports:
            txt = ("Turn this circuit into one reusable part. Its pins will be the %d Component Pin%s you "
                   "selected: %s." % (len(ports), "" if len(ports) == 1 else "s", ", ".join(ports[:8])
                                       + (" …" if len(ports) > 8 else "")))
        else:
            txt = ("Turn this circuit into one reusable part that works in the simulator. Wires leaving the "
                   "selection become its pins. To choose and name the pins yourself, add Component Pins "
                   "(under Building Blocks) first.")
        ttk.Label(bx, text=txt, style="Hint.TLabel", wraplength=wl, justify="left").pack(anchor="w")
        ttk.Button(bx, text="Make component…", style="Accent.TButton",
                   command=self.make_component_from_selection).pack(anchor="w", pady=(6, 0))

    # ------------------------------------------------------------ components (definitions)
    def new_component(self):
        self.commit_props()
        ComponentEditor(self)

    def new_component_menu(self, button):
        """The + New Component button: build a part from the selected circuit, or draw one."""
        n = len(self.sel_comps())
        m = tk.Menu(self.root, tearoff=0)
        m.add_command(label=("From the selected circuit (%d part%s)…" % (n, "" if n == 1 else "s")) if n
                      else "From a circuit… (select its parts first)", accelerator="Ctrl+G",
                      command=self.make_component_from_selection)
        m.add_command(label="Show the circuit inside the selected part", accelerator="Ctrl+Shift+G",
                      command=self.unpack_component,
                      state="normal" if n == 1 and self.is_block(self.sel_comps()[0]) else "disabled")
        m.add_separator()
        m.add_command(label="Draw a part with pins only…", command=self.new_component)
        try:
            m.tk_popup(button.winfo_rootx(), button.winfo_rooty() + button.winfo_height())
        finally:
            m.grab_release()

    def edit_lib_def(self):
        did = self.lib_selected_def()
        if not did:
            return
        d = self.library.get(did)
        ComponentEditor(self, d, duplicate=not d.get("custom"))

    def edit_selected_def(self):
        cs = self.sel_comps()
        if len(cs) != 1:
            messagebox.showinfo(APP_NAME, "Select one part on the canvas first.")
            return
        d = self.library.get(self.comps[cs[0]]["def"])
        if d:
            ComponentEditor(self, d, duplicate=not d.get("custom"))

    def delete_lib_def(self):
        did = self.lib_selected_def()
        if not did:
            return
        d = self.library.get(did)
        if not d or not d.get("custom"):
            return
        used = [c.get("label") or "?" for c in self.comps.values() if c["def"] == did]
        if used:
            messagebox.showwarning(APP_NAME, "“%s” is used in this circuit (%s).\nDelete those parts first."
                                   % (d["name"], ", ".join(used[:8])))
            return
        inside = self.library.used_inside(did)
        if inside:
            messagebox.showwarning(APP_NAME, "“%s” is used inside %s, so it can’t be deleted.\nDelete %s first."
                                   % (d["name"], ", ".join("“%s”" % n for n in inside[:5]),
                                      "that component" if len(inside) == 1 else "those components"))
            return
        if messagebox.askyesno(APP_NAME, "Delete “%s” from your component library?" % d["name"]):
            self.library.delete(did)
            self.populate_library()

    @staticmethod
    def _pin_mapping(old_names, new_pins):
        """Old pin number -> new pin number, matching pins by name."""
        avail = {}
        for i, p in enumerate(new_pins):
            avail.setdefault(p["name"], []).append(i)
        mapping, used = {}, {}
        for i, n in enumerate(old_names):
            lst = avail.get(n, [])
            k = used.get(n, 0)
            if k < len(lst):
                mapping[i] = lst[k]
                used[n] = k + 1
        return mapping

    def _remap_wires(self, cids, mapping):
        """Move wire ends on these parts to the new pin numbers; remove wires whose pin is gone."""
        dropped = 0
        for wid in list(self.wires):
            w = self.wires[wid]
            ok = True
            for end in ("a", "b"):
                if w[end][0] in cids:
                    if w[end][1] in mapping:
                        w[end][1] = mapping[w[end][1]]
                    else:
                        ok = False
            if not ok:
                del self.wires[wid]
                dropped += 1
        return dropped

    def _switch_type(self, cid, did):
        """Make one placed part use another component type, keeping wires on same-named pins."""
        c = self.comps[cid]
        old_names = [p["name"] for p in self.rdef(c).pins]
        new = self.library.resolve(did)
        self.checkpoint()
        c["def"] = did
        dropped = self._remap_wires({cid}, self._pin_mapping(old_names, new.pins))
        self.sel = {("c", cid)}
        self.changed()
        return dropped

    def _store_definition(self, d, persist=True):
        """Put d in the library.  If it replaces a part type with different pins, wires on the
        same-named pins are kept, both on the canvas and inside components built from a circuit
        that contain this part.  Returns how many wires had to be removed."""
        custom = self.library.custom.get(d["id"])
        old = self.library.resolve(d["id"]) if custom else None
        old_names = [p["name"] for p in old.pins] if old else None
        users = {cid for cid, c in self.comps.items() if c["def"] == d["id"]}
        if old_names is not None and users:
            self.checkpoint()
        self.library.save_def(d, persist=persist)
        if old_names is None:
            return 0
        mapping = self._pin_mapping(old_names, self.library.resolve(d["id"]).pins)
        dropped = self.library.remap_nested(d["id"], mapping)
        if users:
            dropped += self._remap_wires(users, mapping)
            self.changed()
        return dropped

    def save_definition(self, d, use_for=None):
        """Called by the editor. Adds/updates a custom definition and remaps existing wires.
        use_for: a placed part that should switch to this definition."""
        self.commit_props()
        dropped = self._store_definition(d)
        switched = None
        if use_for in self.comps and self.comps[use_for]["def"] != d["id"]:
            dropped += self._switch_type(use_for, d["id"])
            switched = self.comps[use_for].get("label") or d["name"]
        self.populate_library()
        if self.lib_tree.exists("def:" + d["id"]):
            self.lib_tree.selection_set("def:" + d["id"])
            self.lib_tree.see("def:" + d["id"])
        if self.sim is not None:
            self._sim_rebuild()
        self.request_redraw()
        self.refresh_props()
        msg = "Saved “%s” to your library." % d["name"]
        if switched:
            msg += " %s now uses it." % switched
        if dropped:
            msg += " %d wire%s removed because a pin was deleted or renamed." % (dropped, "" if dropped == 1 else "s")
        self.flash(msg, 6000)

    # ------------------------------------------------------------ components built from a circuit
    def is_block(self, cid):
        """Is this placed part one the student made from a circuit?"""
        c = self.comps.get(cid)
        d = self.library.get(c["def"]) if c else None
        return bool(d and d.get("subcircuit"))

    def make_component_from_selection(self):
        """Turn the selected parts, and the wires between them, into a new component."""
        self.commit_props()
        if self.mode != "idle":
            self.cancel_mode()
        cs = [cid for cid in self.comps if ("c", cid) in self.sel]
        if not cs:
            messagebox.showinfo(APP_NAME, "First select the circuit that should go inside your component: drag a "
                                          "box around it, or Ctrl+click its parts.\n\nTip: add a Component Pin "
                                          "(under Building Blocks) for each connection the new part needs, and "
                                          "name it A, B, OUT …")
            return
        spec = self._selection_spec(cs)
        if isinstance(spec, str):
            messagebox.showinfo(APP_NAME, spec)
            return
        ComponentEditor(self, spec["def"], from_selection=spec)

    @staticmethod
    def _net_key(root, k):
        k = tuple(k)
        return ("net", root[k]) if k in root else ("pin",) + k

    def _selection_spec(self, cs):
        """Work out the new component's pins and inside circuit from the selected parts.

        Pins come from the Component Pins in the selection.  Without any, every wire that leaves the
        selection becomes a pin, and so does every unconnected pin of the selected parts."""
        cset = set(cs)
        inner = {}
        for cid in cs:
            c = copy.deepcopy(self.comps[cid])
            c.pop("unpacked_from", None)
            inner[cid] = c
        iw = {wid: copy.deepcopy(w) for wid, w in self.wires.items() if w["a"][0] in cset and w["b"][0] in cset}
        crossing = []
        for wid, w in self.wires.items():
            ina, inb = w["a"][0] in cset, w["b"][0] in cset
            if ina != inb:
                crossing.append((wid, "a" if ina else "b"))
        root = {}
        for i, net in enumerate(compute_nets_of(inner, iw.values())):
            for k in net["pins"]:
                root[tuple(k)] = i

        def box(ids):
            bs = [self.comp_bbox(self.comps[cid]) for cid in ids]
            return (min(b[0] for b in bs), min(b[1] for b in bs), max(b[2] for b in bs), max(b[3] for b in bs))
        ports = [cid for cid in cs if self.comps[cid]["def"] == PORT_DEF]
        core = box([cid for cid in cs if cid not in ports] or cs)

        def outside_side(px, py):
            # which side of the circuit this point is furthest outside of
            far = {"left": core[0] - px, "right": px - core[2], "top": core[1] - py, "bottom": py - core[3]}
            return max(("left", "right", "top", "bottom"), key=lambda s: far[s])

        pins = []
        if ports:
            mode = "ports"
            for cid in ports:
                c = self.comps[cid]
                pins.append({"name": (c.get("label") or "").strip() or "P", "inner": [cid, 0],
                             "side": outside_side(c["x"], c["y"]), "at": (c["x"], c["y"])})
        else:
            mode = "auto"
            seen = set()
            for wid, end in crossing:
                w = self.wires[wid]
                k = tuple(w[end])
                if self._net_key(root, k) in seen:
                    continue
                seen.add(self._net_key(root, k))
                out = self.pin_world(tuple(w["b" if end == "a" else "a"]))
                pins.append({"name": self.rdef(self.comps[k[0]]).pins[k[1]]["name"], "inner": list(k),
                             "owner": self.comps[k[0]].get("label") or "", "side": outside_side(*out), "at": out})
            wired = self.connected_pins()
            for cid in cs:
                c = self.comps[cid]
                if c["def"] in ("ground", "vcc", "probe"):
                    continue
                rd = self.rdef(c)
                opt = rd.raw.get("optional_pins", ())
                for i, p in enumerate(rd.pins):
                    if (cid, i) in wired or p["name"] in opt:
                        continue
                    dx, dy = dir_to_world(c, *DIRS[p["dir"]])
                    side = ("right" if dx > 0 else "left") if dx else ("bottom" if dy > 0 else "top")
                    pins.append({"name": p["name"], "inner": [cid, i], "owner": c.get("label") or "",
                                 "side": side, "at": self.pin_world((cid, i))})
            # pins called 1, 2 … or used twice get their part's label in front (R1_2, U1_A)
            counts = {}
            for p in pins:
                counts[p["name"]] = counts.get(p["name"], 0) + 1
            used = set()
            for p in pins:
                nm = p["name"]
                if (counts[nm] > 1 or re.fullmatch(r"\d+", nm)) and p["owner"]:
                    nm = "%s_%s" % (p["owner"], nm)
                base, n = nm, 2
                while nm in used:
                    nm, n = "%s_%d" % (base, n), n + 1
                used.add(nm)
                p["name"] = nm
        if not pins:
            return ("Nothing in the selection can become a pin of the new part.\n\nAdd a Component Pin (under "
                    "Building Blocks) for each connection the part needs, wire it to your circuit, give it a "
                    "name (A, B, OUT …), then select everything again and click Make component.")
        for p in pins:
            if is_ground_pin(p["name"]):
                p["side"] = "bottom"
            elif is_power_pin(p["name"]):
                p["side"] = "top"

        # updating a component that was unpacked onto the canvas: keep its name, look and pin order
        unpacked = {self.comps[cid].get("unpacked_from") for cid in cs} - {None}
        base = self.library.get(unpacked.pop()) if len(unpacked) == 1 else None
        if not (base and base.get("custom") and base.get("subcircuit")):
            base = None
        order = {}
        if base:
            for i, bp in enumerate(base.get("pins", [])):
                order.setdefault(bp["name"], (i, bp.get("side", "left")))
            for p in pins:
                if p["name"] in order:
                    p["side"] = order[p["name"]][1]
        sides = {s: [] for s in ComponentEditor.SIDES}
        for p in pins:
            sides[p["side"]].append(p)
        pins_def = []
        for s in ComponentEditor.SIDES:
            along = 1 if s in ("left", "right") else 0
            sides[s].sort(key=lambda p: (order.get(p["name"], (10 ** 6,))[0], p["at"][along], p["at"][1 - along]))
            for i, p in enumerate(sides[s]):
                pins_def.append({"name": p["name"], "side": s, "pos": i + 1, "inner": p["inner"]})

        # store the circuit with its top-left corner near (0, 0)
        x0, y0, _x1, _y1 = box(cs)
        ox, oy = -int(math.floor(x0)), -int(math.floor(y0))
        for c in inner.values():
            c["x"] += ox
            c["y"] += oy
        for w in iw.values():
            w["bends"] = [[b[0] + ox, b[1] + oy] for b in w.get("bends", [])]
        kinds = {}
        for c in inner.values():
            if c["def"] != PORT_DEF:
                nm = self.rdef(c).name
                kinds[nm] = kinds.get(nm, 0) + 1
        desc = "Built from a circuit: " + ", ".join("%d × %s" % (n, k) for k, n in kinds.items()) + "." if kinds else ""
        sub = {"comps": list(inner.values()), "wires": list(iw.values())}
        if base:
            d = copy.deepcopy(base)
            d.update({"pins": pins_def, "subcircuit": sub})
            d.pop("logic", None)
            d.pop("sim", None)
        else:
            d = {"name": "", "category": "My Components", "prefix": "U", "value": "", "description": desc,
                 "color": "#dbeafe", "symbol": "box", "pins": pins_def, "subcircuit": sub}
        cx0, cy0, cx1, cy1 = box(cs)
        return {"def": d, "cs": cs, "crossing": crossing, "root": root, "mode": mode,
                "base": base["id"] if base else None, "center": ((cx0 + cx1) / 2.0, (cy0 + cy1) / 2.0)}

    def replace_selection_with(self, spec, did):
        """Swap the selected circuit for one copy of the component made from it; wires that left the
        selection are moved onto the matching pins."""
        d = self.library.get(did)
        rd = self.library.resolve(did)
        cset = {cid for cid in spec["cs"] if cid in self.comps}
        if not d or not cset:
            return 0
        pin_of = {}
        for i, p in enumerate(d.get("pins", [])):
            if p.get("inner"):
                pin_of.setdefault(self._net_key(spec["root"], p["inner"]), i)
        self.checkpoint()
        nid = new_id()
        dropped = 0
        crossing = set()
        for wid, end in spec["crossing"]:
            w = self.wires.get(wid)
            if not w or w[end][0] not in cset:
                continue
            k = pin_of.get(self._net_key(spec["root"], w[end]))
            if k is None:
                del self.wires[wid]
                dropped += 1
                continue
            w[end] = [nid, k]
            w["bends"] = []
            crossing.add(wid)
        for wid in list(self.wires):
            w = self.wires[wid]
            if wid not in crossing and (w["a"][0] in cset or w["b"][0] in cset):
                del self.wires[wid]
        for cid in cset:
            del self.comps[cid]
        cx, cy = spec["center"]
        self.comps[nid] = {"id": nid, "def": did, "x": int(round(cx)), "y": int(round(cy)), "rot": 0,
                           "flip": False, "label": self.next_label(rd.prefix), "value": rd.value}
        self.sel = {("c", nid)}
        self.changed()
        return dropped

    def _free_spot(self, box, c, skip):
        """Offset that puts a circuit with bounding box `box` as close to part `c` as possible
        without landing on any other part."""
        others = [self.comp_bbox(o, 0.8) for oid, o in self.comps.items() if oid != skip]
        bx0, by0, bx1, by1 = box
        cx, cy = int(round(c["x"] - (bx0 + bx1) / 2.0)), int(round(c["y"] - (by0 + by1) / 2.0))

        def clear(dx, dy):
            x0, y0, x1, y1 = bx0 + dx, by0 + dy, bx1 + dx, by1 + dy
            return not any(x0 < o[2] and o[0] < x1 and y0 < o[3] and o[1] < y1 for o in others)
        best = None
        for r in range(0, 61, 2):
            for dx in range(-r, r + 1, 2):
                for dy in range(-r, r + 1, 2):
                    if max(abs(dx), abs(dy)) != r:
                        continue
                    if clear(cx + dx, cy + dy):
                        d = dx * dx + dy * dy
                        if best is None or d < best[0]:
                            best = (d, cx + dx, cy + dy)
            if best is not None:
                return best[1], best[2]
        return cx, cy

    def unpack_component(self, cid=None):
        """Put the circuit inside a component back on the canvas in its place, wired up, so it can be
        changed.  Selecting it again and clicking Make component updates the component."""
        if cid is None:
            cs = self.sel_comps()
            cid = cs[0] if len(cs) == 1 else None
        c = self.comps.get(cid)
        d = self.library.get(c["def"]) if c else None
        sub = (d or {}).get("subcircuit")
        if not sub or not sub.get("comps"):
            self.flash("Select one part you made from a circuit, then choose Show the circuit inside.")
            return
        self.commit_props()
        if self.mode != "idle":
            self.cancel_mode()
        inner = sub["comps"]
        bs = [self.comp_bbox(ic) for ic in inner]
        x0, y0 = min(b[0] for b in bs), min(b[1] for b in bs)
        x1, y1 = max(b[2] for b in bs), max(b[3] for b in bs)
        ox, oy = self._free_spot((x0, y0, x1, y1), c, skip=cid)
        labels = {cc.get("label") for cc in self.comps.values() if cc["id"] != cid}
        self.checkpoint()
        idmap, newsel = {}, set()
        for ic in inner:
            nc = copy.deepcopy(ic)
            nid = new_id()
            idmap[ic["id"]] = nid
            nc.update({"id": nid, "x": ic["x"] + ox, "y": ic["y"] + oy, "unpacked_from": d["id"]})
            prefix = self.rdef(nc).prefix
            if (nc["def"] != PORT_DEF and nc.get("label") in labels
                    and re.match(r"^%s\d+$" % re.escape(prefix), nc.get("label", ""))):
                nc["label"] = self.next_label(prefix)
            labels.add(nc.get("label"))
            self.comps[nid] = nc
            newsel.add(("c", nid))
        for w in sub.get("wires", []):
            if w["a"][0] in idmap and w["b"][0] in idmap:
                nw = copy.deepcopy(w)
                nid = new_id()
                nw.update({"id": nid, "a": [idmap[w["a"][0]], w["a"][1]], "b": [idmap[w["b"][0]], w["b"][1]],
                           "bends": [[b[0] + ox, b[1] + oy] for b in w.get("bends", [])]})
                nw.setdefault("color", self.wire_color)
                self.wires[nid] = nw
                newsel.add(("w", nid))
        for wid in [k[1] for k in newsel if k[0] == "w"]:
            if not self._wire_ok(self.wires[wid]):   # an inner part type changed since it was saved
                del self.wires[wid]
                newsel.discard(("w", wid))
        dropped = 0
        pins = d.get("pins", [])
        for wid in list(self.wires):
            w = self.wires[wid]
            for end in ("a", "b"):
                if w[end][0] != cid:
                    continue
                k = w[end][1]
                inn = pins[k].get("inner") if k < len(pins) else None
                if inn and inn[0] in idmap:
                    w[end] = [idmap[inn[0]], inn[1]]
                    w["bends"] = []
                else:
                    del self.wires[wid]
                    dropped += 1
                    break
        del self.comps[cid]
        self.sel = newsel
        self.changed()
        self.set_status_hint()
        # make sure the circuit that came out is on screen
        vx0, vy0 = self.to_world(0, 0)
        vx1, vy1 = self.to_world(self.cv.winfo_width(), self.cv.winfo_height())
        if not (vx0 <= x0 + ox and vy0 <= y0 + oy and x1 + ox <= vx1 and y1 + oy <= vy1):
            self.fit()
        msg = ("Here is the circuit inside “%s”. Change it, then keep it selected and click Make component "
               "to update “%s”." % (d["name"], d["name"]))
        if dropped:
            msg += " %d wire%s removed (pin not connected inside)." % (dropped, "" if dropped == 1 else "s")
        self.flash(msg, 9000)

    def read_picture(self, path, parent=None):
        """Load a picture file for a component; shows a message and returns None if it fails."""
        parent = parent or self.root
        try:
            parent.configure(cursor="watch")
            parent.update_idletasks()
        except tk.TclError:
            pass
        try:
            return load_picture(path)
        except PictureError as e:
            messagebox.showerror(APP_NAME, str(e), parent=parent)
            return None
        finally:
            try:
                parent.configure(cursor="")
            except tk.TclError:
                pass

    def can_add_picture(self, did):
        """Pictures go on box-shaped parts.  Built-in schematic symbols keep their standard drawing."""
        d = self.library.get(did)
        return bool(d) and (d.get("custom") or d.get("symbol", "box") == "box")

    def add_picture(self, did, use_for=None):
        """Choose a picture file, then open the Component Editor with it so the result can be checked
        before saving.  Built-in parts get saved as the student's own copy."""
        self.commit_props()
        d = self.library.get(did)
        if not d:
            return
        path = filedialog.askopenfilename(parent=self.root, title="Choose a picture for “%s”" % d.get("name", "part"),
                                          filetypes=PICTURE_FILETYPES)
        if not path:
            return
        pic = self.read_picture(path)
        if pic:
            ComponentEditor(self, d, duplicate=not d.get("custom"), image=pic,
                            use_for=None if d.get("custom") else use_for)

    def import_library(self):
        path = filedialog.askopenfilename(title="Import components", filetypes=[
            ("Component library", "*" + LIB_EXT), ("Circuit file", "*" + FILE_EXT), ("JSON", "*.json"), ("All files", "*.*")])
        if not path:
            return
        data = load_json(path, None)
        if not isinstance(data, dict):
            messagebox.showerror(APP_NAME, "That file could not be read.")
            return
        defs = data.get("components") if data.get("format") == "circuit-builder-library" else data.get("definitions", [])
        n = skipped = dropped = 0
        for d in _as_list(defs):
            if isinstance(d, dict) and not d.get("id"):
                d = dict(d, id="custom_" + uuid.uuid4().hex[:10])
            d = clean_def(copy.deepcopy(d))
            if d is None or not d["pins"] or d["id"] in self.library.builtin:
                skipped += 1
                continue
            dropped += self._store_definition(d, persist=False)
            n += 1
        if n:
            self.library.persist()
        self.populate_library()
        if self.sim is not None:
            self._sim_rebuild()
        msg = "Imported %d component%s." % (n, "" if n == 1 else "s")
        if skipped:
            msg += "\n\n%d entr%s in the file could not be used." % (skipped, "y" if skipped == 1 else "ies")
        if dropped:
            msg += ("\n\nSome imported parts have different pins from your old copies: %d wire%s on pins that "
                    "no longer exist %s removed." % (dropped, "" if dropped == 1 else "s",
                                                      "was" if dropped == 1 else "were"))
        messagebox.showinfo(APP_NAME, msg)

    def export_library(self):
        if not self.library.custom:
            messagebox.showinfo(APP_NAME, "You haven’t created any components yet.\nUse  + New Component  first.")
            return
        path = filedialog.asksaveasfilename(title="Export my components", defaultextension=LIB_EXT,
                                            initialfile="my_components" + LIB_EXT,
                                            filetypes=[("Component library", "*" + LIB_EXT)])
        if not path:
            return
        try:
            save_json(path, {"format": "circuit-builder-library", "version": 1,
                             "components": list(self.library.custom.values())})
        except OSError as e:
            messagebox.showerror(APP_NAME, "Could not export:\n%s" % e)
            return
        self.flash("Exported %d components to %s" % (len(self.library.custom), os.path.basename(path)))

    # ------------------------------------------------------------ files
    def serialize(self):
        # custom parts used here, and the custom parts inside components built from a circuit
        defs = self.library.with_dependencies({c["def"] for c in self.comps.values()})
        return {"format": "circuit-builder", "version": 1, "app_version": APP_VERSION,
                "components": list(self.comps.values()), "wires": list(self.wires.values()),
                "definitions": defs,
                "view": {"zoom": self.zoom / self.ui_scale, "panx": self.panx, "pany": self.pany}}

    def load_data(self, data):
        """Replace the circuit with the one in `data` (a parsed .circuit file).  Everything is checked
        first, so a damaged file leaves the current circuit as it was.  Returns the number of custom
        parts added to the library; problems found are left in self.load_notes."""
        if not isinstance(data, dict) or data.get("format") != "circuit-builder":
            raise ValueError("This is not a Circuit Builder file.")
        notes = []
        defs = [cd for cd in (clean_def(copy.deepcopy(d)) for d in _as_list(data.get("definitions"))) if cd]
        comps, bad_parts = {}, 0
        for c in _as_list(data.get("components")):
            cc = clean_comp(c)
            if cc is None or cc["id"] in comps:
                bad_parts += 1
            else:
                comps[cc["id"]] = cc
        if bad_parts:
            notes.append("%d damaged part%s skipped" % (bad_parts, " was" if bad_parts == 1 else "s were"))
        if not comps and _as_list(data.get("components")):
            raise ValueError("None of the parts in this file could be read.")

        # ---- nothing below can fail on bad data
        self.sim_stop()
        self.scope_traces = []
        if self.scope_win is not None:
            self.scope_win.build_legend()
        added = 0
        remap = {}   # part type -> {pin number in the file: pin number now}
        for d in defs:
            if d["id"] in self.library.builtin:
                continue
            have = self.library.resolve(d["id"]) if d["id"] in self.library.custom else None
            if have is None:
                self.library.save_def(d, persist=False)
                added += 1
            else:
                # The library already has this part, maybe changed since the file was saved
                # (pins added, removed or reordered): keep the file's wires on same-named pins.
                file_names = [p["name"] for p in d["pins"]]
                if file_names != [p["name"] for p in have.pins]:
                    remap[d["id"]] = self._pin_mapping(file_names, have.pins)
        if added:
            self.library.persist()

        def pin_count(cid):
            c = comps.get(cid)
            if c is None:
                return None
            rd = self.library.resolve(c["def"])
            return len(rd.pins) if rd else MAX_PINS   # part type missing: drawn as a placeholder

        wires, bad_wires = {}, 0
        for w in _as_list(data.get("wires")):
            if isinstance(w, dict) and remap:
                w = dict(w)
                for end in ("a", "b"):
                    e = w.get(end)
                    if isinstance(e, (list, tuple)) and len(e) == 2 and e[0] in comps:
                        m = remap.get(comps[e[0]]["def"])
                        if m is not None:
                            k = m.get(_pin_index(e[1]))
                            w[end] = [e[0], -1 if k is None else k]
            cw = clean_wire(w, pin_count)
            if cw is None:
                bad_wires += 1
                continue
            if cw.get("id") is None or cw["id"] in wires:
                cw["id"] = new_id()
            wires[cw["id"]] = cw
        if bad_wires:
            notes.append("%d wire%s pointed at a pin that doesn’t exist and %s removed"
                         % (bad_wires, "" if bad_wires == 1 else "s", "was" if bad_wires == 1 else "were"))
        if remap:
            names = ", ".join("“%s”" % self.library.get(did).get("name", "?") for did in remap)
            notes.append("your library’s version of %s has different pins from the one in this file, so its "
                         "wires were moved to the pins with the same names" % names)
        self.load_notes = notes
        self.comps = comps
        self.wires = wires
        self._missing = {}
        self.sel = set()
        self.highlight = None
        self.undo_stack.clear()
        self.redo_stack.clear()
        self._nets_cache = None
        if added:
            self.populate_library()
        return added

    def confirm_discard(self):
        if not self.dirty or not self.comps and not self.wires:
            return True
        r = messagebox.askyesnocancel(APP_NAME, "Save changes to your circuit first?")
        if r is None:
            return False
        if r:
            return self.save()
        return True

    def new_file(self):
        self.commit_props()
        if not self.confirm_discard():
            return
        self.sim_stop()
        self.cancel_mode()
        self.comps, self.wires, self.sel = {}, {}, set()
        self.undo_stack.clear()
        self.redo_stack.clear()
        self.path = None
        self.highlight = None
        self.scope_traces = []
        if self.scope_win is not None:
            self.scope_win.build_legend()
        self.changed()
        self.dirty = False
        self.update_title()
        self.fit()

    def open_dialog(self):
        self.commit_props()
        if not self.confirm_discard():
            return
        path = filedialog.askopenfilename(title="Open circuit", filetypes=[("Circuit files", "*" + FILE_EXT), ("All files", "*.*")])
        if path:
            self.open_file(path)

    def open_file(self, path):
        data = load_json(path, None)
        if not isinstance(data, dict):
            messagebox.showerror(APP_NAME, "Could not open:\n%s" % path)
            return
        try:
            added = self.load_data(data)
        except (ValueError, KeyError, TypeError, IndexError, AttributeError) as e:
            messagebox.showerror(APP_NAME, "Could not open the file:\n%s" % e)
            return
        self.path = path
        self.cancel_mode()
        self.changed()
        self.dirty = False
        self.update_title()
        self.add_recent(path)
        self.root.after(30, self.fit)
        if self.load_notes:
            messagebox.showwarning(APP_NAME, "The circuit was opened, but:\n\n• " + "\n• ".join(
                n[0].upper() + n[1:] + "." for n in self.load_notes)
                + "\n\nCheck the circuit, then save it to keep the repaired version.")
        if added:
            self.flash("Added %d custom component%s from this file to your library." % (added, "" if added == 1 else "s"), 6000)

    def save(self):
        self.commit_props()
        if not self.path:
            return self.save_as()
        try:
            save_json(self.path, self.serialize())
        except OSError as e:
            messagebox.showerror(APP_NAME, "Could not save:\n%s" % e)
            return False
        self.dirty = False
        self.update_title()
        self.add_recent(self.path)
        self.flash("Saved %s" % os.path.basename(self.path))
        if not self.sel:
            self.refresh_props()
        return True

    def save_as(self):
        self.commit_props()
        path = filedialog.asksaveasfilename(title="Save circuit as", defaultextension=FILE_EXT,
                                            initialfile=os.path.basename(self.path) if self.path else "my_circuit" + FILE_EXT,
                                            filetypes=[("Circuit files", "*" + FILE_EXT)])
        if not path:
            return False
        self.path = path
        return self.save()

    def add_recent(self, path):
        rec = [p for p in self.settings.get("recent", []) if p != path]
        rec.insert(0, path)
        self.settings["recent"] = rec[:8]
        self.save_settings()
        self._update_recent_menu()

    def _update_recent_menu(self):
        self.recent_menu.delete(0, "end")
        rec = [p for p in self.settings.get("recent", []) if os.path.exists(p)]
        if not rec:
            self.recent_menu.add_command(label="(none yet)", state="disabled")
        for p in rec:
            self.recent_menu.add_command(label=p, command=lambda p=p: self._open_recent(p))

    def _open_recent(self, p):
        if self.confirm_discard():
            self.open_file(p)

    def on_close(self):
        self.commit_props()
        if self.confirm_discard():
            self.sim_stop()
            self.root.destroy()

    def load_example(self, name):
        self.commit_props()
        if not self.confirm_discard():
            return
        data = build_example(name)
        self.load_data(data)
        self.path = None
        self.cancel_mode()
        self.changed()
        self.dirty = False
        self.update_title()
        self.root.after(30, self.fit)
        tips = {"rc": "Press ▶ Simulate, then open the Oscilloscope or Simulate › Frequency response.",
                "transistor": "Press ▶ Simulate, then hold the push button down to switch the LED on.",
                "blinker": "Press ▶ Simulate to watch the LED blink about once a second.",
                "counter": "Press ▶ Simulate: the red and green LEDs count 0, 1, 2, 3 in binary, one step per second.",
                "halfadder": "Select everything (Ctrl+A), then press Ctrl+G to turn this half adder into your own "
                             "part. The four Component Pins become its pins A, B, SUM and CARRY."}
        if name in tips:
            self.flash(tips[name], 8000)

    # ------------------------------------------------------------ netlist & checks
    def show_netlist(self):
        if self.netlist_win and self.netlist_win.winfo_exists():
            self.netlist_win.lift()
            self.netlist_win.refresh()
            return
        self.netlist_win = NetlistWindow(self)

    def netlist_text(self):
        nets = self.compute_nets()
        lines = ["%s netlist — %s" % (APP_NAME, os.path.basename(self.path) if self.path else "Untitled"), "",
                 "PARTS"]
        for c in self.comps.values():
            rd = self.rdef(c)
            lines.append("  %-8s %-26s %s" % (c.get("label", ""), rd.name, c.get("value", "")))
        lines += ["", "NETS"]
        for n in nets:
            lines.append("  %-8s %s" % (n["name"], ", ".join(self.pin_name(k) for k in n["pins"])))
        return "\n".join(lines) + "\n"

    def export_netlist(self):
        path = filedialog.asksaveasfilename(title="Export netlist", defaultextension=".txt",
                                            initialfile=(os.path.splitext(os.path.basename(self.path))[0] if self.path else "circuit") + "_netlist",
                                            filetypes=[("Text netlist", "*.txt"), ("Spreadsheet (CSV)", "*.csv"),
                                                       ("SPICE netlist (basic parts)", "*.cir")])
        if not path:
            return
        ext = os.path.splitext(path)[1].lower()
        try:
            if ext == ".csv":
                with open(path, "w", newline="", encoding="utf-8-sig") as f:
                    wr = csv.writer(f)
                    wr.writerow(["Net", "Part", "Part type", "Pin", "Value"])
                    for n in self.compute_nets():
                        for k in n["pins"]:
                            c = self.comps[k[0]]
                            rd = self.rdef(c)
                            wr.writerow([n["name"], c.get("label", ""), rd.name, rd.pins[k[1]]["name"], c.get("value", "")])
            elif ext in (".cir", ".sp", ".spice", ".net"):
                with open(path, "w", encoding="utf-8") as f:
                    f.write(self.spice_text())
            else:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(self.netlist_text())
        except OSError as e:
            messagebox.showerror(APP_NAME, "Could not export:\n%s" % e)
            return
        self.flash("Netlist exported to %s" % os.path.basename(path))

    def spice_text(self):
        pm = self.pin_net_map()
        lines = ["* %s SPICE netlist (basic parts only) — %s" % (APP_NAME, os.path.basename(self.path) if self.path else "Untitled")]
        models = set()
        has_gnd = False
        for cid, c in self.comps.items():
            rd = self.rdef(c)
            spec = SPICE_MAP.get(c["def"])
            label = re.sub(r"\W", "_", c.get("label") or "X")
            if c["def"] == "ground":
                has_gnd = True
                continue
            if c["def"] == "vcc":
                continue
            if not spec:
                lines.append("* %s (%s) not exported" % (label, rd.name))
                continue
            letter, pin_names, kind = spec
            nodes = []
            for pn in pin_names:
                idx = next((i for i, p in enumerate(rd.pins) if p["name"] == pn), None)
                net = pm.get((cid, idx)) if idx is not None else None
                if net is None:
                    nodes.append("NC_%s_%s" % (label, re.sub(r"\W", "", pn) or "p"))
                else:
                    nodes.append("0" if net["name"] == "GND" else re.sub(r"\W", "_", net["name"]))
            name = label if label.upper().startswith(letter) else letter + "_" + label
            val = spice_value(c.get("value", ""))
            if letter in ("R", "C", "L"):
                lines.append("%s %s %s" % (name, " ".join(nodes), val or "1"))
            elif letter in ("V", "I"):
                if kind == "AMMETER":
                    lines.append("%s %s DC 0" % (name, " ".join(nodes)))
                elif kind == "AC":
                    lines.append("%s %s AC %s" % (name, " ".join(nodes), val or "1"))
                else:
                    lines.append("%s %s DC %s" % (name, " ".join(nodes), val or "0"))
            else:
                lines.append("%s %s %s" % (name, " ".join(nodes), kind))
                models.add(kind)
        model_lines = {"DMOD": ".model DMOD D", "DLED": ".model DLED D(IS=1e-22 N=1.5 RS=2)",
                       "DZEN": ".model DZEN D(BV=5.1)",
                       "QNPN": ".model QNPN NPN(BF=100)", "QPNP": ".model QPNP PNP(BF=100)"}
        for m in sorted(models):
            lines.append(model_lines.get(m, "* model %s" % m))
        if not has_gnd:
            lines.insert(1, "* WARNING: no Ground symbol — SPICE needs a node named 0.")
        lines += [".op", ".end"]
        return "\n".join(lines) + "\n"

    def is_mcu(self, c):
        """Is this placed part treated as a microcontroller?  A part can override its type's setting."""
        v = c.get("mcu")
        return self.rdef(c).microcontroller if v is None else bool(v)

    def set_mcu(self, cid, on):
        self.commit_props()
        c = self.comps.get(cid)
        if c is None or self.is_mcu(c) == bool(on):
            return
        self.checkpoint()
        if bool(on) == self.rdef(c).microcontroller:
            c.pop("mcu", None)  # same as the part type: no override needed
        else:
            c["mcu"] = bool(on)
        self.changed(props=False)
        self.flash("%s is %s treated as a microcontroller." % (c.get("label") or self.rdef(c).name,
                                                               "now" if on else "no longer"))

    def check_circuit(self):
        self.commit_props()
        issues = []
        pm = self.pin_net_map()
        wired = self.connected_pins()
        has_source = False
        has_gnd = False
        for cid, c in self.comps.items():
            rd = self.rdef(c)
            lbl = c.get("label") or rd.name
            if c["def"] == "ground":
                has_gnd = True
            if c["def"] in ("battery", "dc_source", "ac_source", "square_source", "current_source", "vcc"):
                has_source = True
            keys = [(cid, i) for i in range(len(rd.pins))]
            nets = [pm.get(k)["name"] if pm.get(k) else None for k in keys]
            n_conn = sum(1 for k in keys if k in wired)
            if c["def"] in ("battery", "dc_source", "ac_source", "square_source") and nets[0] and nets[0] == nets[1]:
                issues.append(("Error", cid, "Short circuit: the two terminals of %s are wired directly together." % lbl))
                continue
            if len(keys) >= 2 and n_conn == len(keys) and len(set(nets)) == 1 and c["def"] not in ("ground", "vcc"):
                issues.append(("Warning", cid, "%s is shorted: all its pins are on the same net (%s)." % (lbl, nets[0])))
            if n_conn == 0:
                issues.append(("Warning", cid, "%s is not connected to anything." % lbl))
            elif self.is_mcu(c):
                # Microcontroller: unused I/O pins are normal. Check power and ground instead.
                gnd = [i for i, p in enumerate(rd.pins) if is_ground_pin(p["name"])]
                pwr = [i for i, p in enumerate(rd.pins) if is_power_pin(p["name"])]
                if gnd and not any((cid, i) in wired for i in gnd):
                    issues.append(("Warning", cid, "%s: no GND pin is connected. The board’s ground must be shared "
                                                   "with the parts it controls." % lbl))
                if pwr and not any((cid, i) in wired for i in pwr):
                    names = ", ".join(dict.fromkeys(rd.pins[i]["name"] for i in pwr))
                    issues.append(("Info", cid, "%s: no power pin (%s) is wired. That’s fine if the board is "
                                                "powered over USB." % (lbl, names)))
            elif n_conn < len(keys) and [i for i in range(len(keys)) if (cid, i) not in wired
                                         and rd.pins[i]["name"] not in rd.raw.get("optional_pins", ())]:
                free = [rd.pins[i]["name"] for i in range(len(keys)) if (cid, i) not in wired
                        and rd.pins[i]["name"] not in rd.raw.get("optional_pins", ())]
                sev = "Warning" if len(keys) <= 3 and c["def"] not in ("potentiometer",) else "Info"
                txt = ", ".join(free[:10]) + (" …" if len(free) > 10 else "")
                msg = "%s: pin%s %s not connected." % (lbl, "s" if len(free) > 1 else "", txt)
                if len(keys) >= 8 and len(free) >= 4:
                    msg += " If this is a microcontroller, tick “Microcontroller” in its properties."
                issues.append((sev, cid, msg))
        if has_source and not has_gnd:
            issues.append(("Info", None, "No Ground symbol. Add one to mark the 0 V reference (needed for SPICE)."))
        CheckDialog(self, issues)


class CheckDialog(tk.Toplevel):
    def __init__(self, app, issues):
        super().__init__(app.root)
        self.app = app
        s = app.ui_scale
        self.title("Check circuit — " + APP_NAME)
        self.configure(bg=C["bg"])
        self.transient(app.root)
        self.geometry("%dx%d" % (int(620 * s), int(380 * s)))
        top = ttk.Frame(self, style="Bg.TFrame", padding=(14, 12))
        top.pack(fill="x")
        errs = sum(1 for i in issues if i[0] == "Error")
        warns = sum(1 for i in issues if i[0] == "Warning")
        if not issues:
            head, col = "Looks good! No problems found.", C["ok"]
            self.geometry("%dx%d" % (int(520 * s), int(170 * s)))
        elif errs:
            head, col = "%d error%s, %d warning%s" % (errs, "" if errs == 1 else "s", warns, "" if warns == 1 else "s"), C["danger"]
        else:
            head, col = "%d warning%s, %d note%s" % (warns, "" if warns == 1 else "s", len(issues) - warns,
                                                     "" if len(issues) - warns == 1 else "s"), C["warn"]
        tk.Label(top, text=head, bg=C["bg"], fg=col, font=(app.fam, 12, "bold")).pack(anchor="w")
        ttk.Label(top, text="Double-click a line to select that part. Unused pins on microcontrollers are not listed.",
                  style="Status.TLabel").pack(anchor="w")
        mid = ttk.Frame(self, style="Bg.TFrame", padding=(14, 0))
        mid.pack(fill="both", expand=True)
        mid.columnconfigure(0, weight=1)
        mid.rowconfigure(0, weight=1)
        tv = ttk.Treeview(mid, columns=("sev", "msg"), show="headings")
        tv.heading("sev", text="Type")
        tv.heading("msg", text="Message")
        tv.column("sev", width=int(80 * s), stretch=False)
        tv.column("msg", width=int(480 * s))
        tv.tag_configure("Error", foreground=C["danger"])
        tv.tag_configure("Warning", foreground=C["warn"])
        tv.tag_configure("Info", foreground=C["muted"])
        order = {"Error": 0, "Warning": 1, "Info": 2}
        self.items = {}
        for i, (sev, cid, msg) in enumerate(sorted(issues, key=lambda x: order[x[0]])):
            tv.insert("", "end", iid=str(i), values=(sev, msg), tags=(sev,))
            self.items[str(i)] = cid
        if issues:
            tv.grid(row=0, column=0, sticky="nsew")
            sb = ttk.Scrollbar(mid, orient="vertical", command=tv.yview)
            sb.grid(row=0, column=1, sticky="ns")
            tv.configure(yscrollcommand=sb.set)
            tv.bind("<Double-1>", lambda e: self._go(tv))
        else:
            msg = ("Every part is connected and no power source is shorted." if app.comps
                   else "The circuit is empty — add some parts first.")
            ttk.Label(mid, text=msg, style="Status.TLabel").grid(row=0, column=0, sticky="nw", pady=10)
        bar = ttk.Frame(self, style="Bg.TFrame", padding=12)
        bar.pack(fill="x")
        ttk.Button(bar, text="Close", command=self.destroy).pack(side="right")

    def _go(self, tv):
        sel = tv.selection()
        if not sel:
            return
        cid = self.items.get(sel[0])
        if cid and cid in self.app.comps:
            self.app.sel = {("c", cid)}
            self.app.selection_changed()


def spice_value(v):
    s = (v or "").strip()
    s = s.replace("Ω", "").replace("ohms", "").replace("ohm", "").replace("Ohm", "")
    s = s.replace("µ", "u").replace("μ", "u").replace(" ", "")
    m = re.match(r"^([0-9]*\.?[0-9]+(?:[eE][-+]?\d+)?)([a-zA-Z]*)", s)
    if not m:
        return ""
    num, suf = m.group(1), m.group(2)
    if suf.startswith("M") and not suf.lower().startswith("meg"):
        suf = "Meg" + suf[1:]
    suf = re.sub(r"(?i)(hz|v|a|f|h)$", "", suf) if suf.lower() not in ("meg",) else suf
    return num + suf


# ==========================================================================
# Simulation engine
# ==========================================================================
# The circuit is solved with modified nodal analysis (MNA): one unknown per
# net voltage plus one per voltage-source-like branch current.  Non-linear
# parts (diodes, transistors, op-amps, logic gates, the regulator) are handled
# with Newton-Raphson iteration; capacitors and inductors are integrated with
# BDF2 (Gear) steps, and backward-Euler right after anything switches.  The
# same matrices give the small-signal AC response used for Bode plots.
# Everything is plain Python, so it is fast enough for classroom-sized circuits.

_SI = {"p": 1e-12, "n": 1e-9, "u": 1e-6, "µ": 1e-6, "μ": 1e-6, "m": 1e-3,
       "k": 1e3, "K": 1e3, "M": 1e6, "G": 1e9}
_UNITS = {"v": "v", "vrms": "v", "vpp": "v", "vp": "v", "a": "a", "hz": "hz", "f": "f", "h": "h",
          "w": "w", "ohm": "ohm", "ohms": "ohm", "ω": "ohm", "r": "ohm", "s": "s", "%": "%",
          "°c": "c", "c": "c"}
_UNIT_SYM = {"ohm": "Ω", "f": "F", "h": "H", "v": "V", "a": "A", "hz": "Hz", "w": "W"}
_QTY_RX = re.compile(r"([-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?)\s*([a-zA-ZΩΩµμ°%]*)")


def parse_quantities(text):
    """'10 V 60 Hz' -> [(10.0, 'v'), (60.0, 'hz')];  '4.7 kΩ' -> [(4700.0, 'ohm')]."""
    s = (text or "").replace("−", "-").replace(",", ".")
    out = []
    for m in _QTY_RX.finditer(s):
        try:
            num = float(m.group(1))
        except ValueError:
            continue
        letters = m.group(2)
        mult = 1.0
        if letters.lower().startswith("meg"):
            mult, letters = 1e6, letters[3:]
        elif letters and letters[0] in _SI and (len(letters) == 1 or letters[1:].lower() in _UNITS):
            mult, letters = _SI[letters[0]], letters[1:]
        unit = _UNITS.get(letters.lower(), letters.lower())
        out.append((num * mult, unit))
    return out


def qty(text, unit, allow_bare=True):
    """First number in text with this unit (or with no unit, if allow_bare)."""
    qs = parse_quantities(text)
    for v, u in qs:
        if u == unit:
            return v
    if allow_bare:
        for v, u in qs:
            if u == "":
                return v
    return None


_FMT_PFX = ((1e9, "G"), (1e6, "M"), (1e3, "k"), (1.0, ""), (1e-3, "m"), (1e-6, "µ"), (1e-9, "n"), (1e-12, "p"))


def fmt_si(v, unit="", tiny=1e-12):
    """4.7e-3, 'A' -> '4.70 mA'."""
    if v is None or v != v:
        return "—"
    if abs(v) < tiny:
        return "0 " + unit
    a = abs(v)
    p, s = _FMT_PFX[-1]
    for p, s in _FMT_PFX:
        if a >= p * 0.9995:
            break
    val = v / p
    av = abs(val)
    txt = "%.0f" % val if av >= 99.95 else "%.1f" % val if av >= 9.995 else "%.2f" % val
    return ("%s %s%s" % (txt, s, unit)).replace("-", "−")


def _mix(c1, c2, t):
    """Blend two #rrggbb colors (t = 0 -> c1, 1 -> c2)."""
    t = max(0.0, min(1.0, t))
    a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(int(round(x + (y - x) * t)) for x, y in zip(a, b))


class SimError(Exception):
    pass


class NoConvergence(Exception):
    pass


class _Singular(Exception):
    def __init__(self, col):
        Exception.__init__(self, col)
        self.col = col


class _MissingPin(Exception):
    pass


def lu_factor(A, tol=1e-13):
    """Gaussian elimination with partial pivoting (works for real or complex matrices)."""
    n = len(A)
    M = [list(r) for r in A]
    perm = list(range(n))
    for k in range(n):
        p, big = k, abs(M[k][k])
        for i in range(k + 1, n):
            a = abs(M[i][k])
            if a > big:
                p, big = i, a
        if big < tol:
            raise _Singular(k)
        if p != k:
            M[k], M[p] = M[p], M[k]
            perm[k], perm[p] = perm[p], perm[k]
        rk = M[k]
        piv = rk[k]
        tail = rk[k + 1:]
        for i in range(k + 1, n):
            ri = M[i]
            f = ri[k]
            if f:
                f = f / piv
                ri[k] = f
                ri[k + 1:] = [a - f * b for a, b in zip(ri[k + 1:], tail)]
    return M, perm


def lu_solve(LU, b):
    M, perm = LU
    n = len(M)
    y = [b[p] for p in perm]
    for i in range(1, n):
        ri = M[i]
        y[i] -= sum(a * c for a, c in zip(ri[:i], y[:i]))
    for i in range(n - 1, -1, -1):
        ri = M[i]
        s = y[i] - sum(a * c for a, c in zip(ri[i + 1:], y[i + 1:]))
        y[i] = s / ri[i]
    return y


VT = 0.025852    # thermal voltage at 27 °C
GMIN = 1e-12     # tiny conductance to ground on every node (keeps floating nodes solvable)
_E60 = math.exp(60.0)


def _exp(x):
    """exp(x) that grows linearly past 60 (no overflow while Newton is still searching)."""
    if x > 60.0:
        return _E60 * (1.0 + x - 60.0), _E60
    e = math.exp(x) if x > -700 else 0.0
    return e, e


def pnjlim(vnew, vold, vt, vcrit):
    """SPICE's junction-voltage limiter: stops Newton jumping far up an exponential."""
    if vnew > vcrit and abs(vnew - vold) > 2 * vt:
        if vold > 0:
            arg = 1 + (vnew - vold) / vt
            vnew = vold + vt * math.log(arg) if arg > 0 else vcrit
        else:
            vnew = vt * math.log(vnew / vt)
        return vnew, True
    return vnew, False


class Stamp:
    """Matrix A and right-hand side b being built, plus the solve settings."""

    def __init__(self, N):
        self.A = [[0.0] * N for _ in range(N)]
        self.b = [0.0] * N
        self.dc = True        # DC: capacitors open, inductors shorted
        self.h = 1e-3         # time step
        self.method = "be"    # "be" (backward Euler) or "bdf2"
        self.t = 0.0          # time at the end of this step
        self.scale = 1.0      # source stepping
        self.open = None      # an inductor to leave open (time-constant estimate)
        self.limited = False  # a non-linear part limited its voltage this iteration

    def g(self, a, b, g):
        """Conductance g between nodes a and b (0 = ground)."""
        A = self.A
        if a:
            A[a - 1][a - 1] += g
        if b:
            A[b - 1][b - 1] += g
            if a:
                A[a - 1][b - 1] -= g
                A[b - 1][a - 1] -= g

    def cur(self, a, b, i):
        """Current i flowing from node a, through the part, to node b."""
        if a:
            self.b[a - 1] -= i
        if b:
            self.b[b - 1] += i

    def branch(self, k, p, n, r=0.0):
        """Matrix part of a voltage source in row k:  V(p) - V(n) - r*I = b[k]."""
        A = self.A
        if p:
            A[p - 1][k] += 1.0
            A[k][p - 1] += 1.0
        if n:
            A[n - 1][k] -= 1.0
            A[k][n - 1] -= 1.0
        if r:
            A[k][k] -= r

    def nl(self, nodes, I, J, V):
        """Linearised non-linear part.  I[t] = current into the part at terminal t,
        J[t][s] = dI[t]/dV[s], V = terminal voltages the values were computed at."""
        A, b = self.A, self.b
        for t, nt in enumerate(nodes):
            if not nt:
                continue
            row = A[nt - 1]
            rhs = I[t]
            Jt = J[t]
            for s, ns in enumerate(nodes):
                d = Jt[s]
                if d:
                    rhs -= d * V[s]
                    if ns:
                        row[ns - 1] += d
            b[nt - 1] -= rhs


# ---------------------------------------------------------------- devices
class Dev:
    nonlinear = False
    reactive = False
    timevar = False
    nbr = 0           # extra branch-current unknowns

    def __init__(self, sim, comp, nodes):
        self.sim = sim
        self.comp = comp
        self.cid = comp["id"]
        self.n = list(nodes)
        self.pidx = list(range(len(nodes)))
        self.label = comp.get("label") or "?"
        self.br = None

    def V(self, x, i):
        n = self.n[i]
        return x[n - 1] if n else 0.0

    def vd(self, x):
        return self.V(x, 0) - self.V(x, 1)

    # solver hooks
    def stamp_lin(self, S):
        pass

    def rhs(self, S):
        pass

    def stamp_nl(self, S, x):
        pass

    def begin(self, x):
        pass

    def accept(self, S, x):
        pass

    def discrete(self, x):
        return False

    def ac(self, A, w):
        pass

    def periods(self):
        return []

    def export(self):
        return None

    def restore(self, st):
        pass

    # read-outs
    def currents(self, x):
        return [0.0] * len(self.n)

    def info(self, x):
        out = []
        if len(self.n) == 2:
            v = self.vd(x)
            i = self.currents(x)[0]
            out += [("Voltage across", fmt_si(v, "V")), ("Current", fmt_si(i, "A")),
                    ("Power", fmt_si(v * i, "W"))]
        return out + self.extra(x)

    def extra(self, x):
        return []

    def view(self, x):
        return None

    def warn(self, x):
        return []


def _ac_g(A, a, b, y):
    if a:
        A[a - 1][a - 1] += y
    if b:
        A[b - 1][b - 1] += y
        if a:
            A[a - 1][b - 1] -= y
            A[b - 1][a - 1] -= y


class Resistor(Dev):
    def __init__(self, sim, comp, nodes, R, kind="resistor", rated=None):
        Dev.__init__(self, sim, comp, nodes)
        self.R = max(float(R), 1e-6)
        self.kind = kind
        self.rated = rated or (0.0, 0.0)

    def res(self):
        return self.R

    def stamp_lin(self, S):
        S.g(self.n[0], self.n[1], 1.0 / self.res())

    def currents(self, x):
        i = self.vd(x) / self.res()
        return [i, -i]

    def info(self, x):
        if self.kind == "voltmeter":
            return [("Reading", fmt_si(self.vd(x), "V"))]
        return Dev.info(self, x)

    def extra(self, x):
        v = self.vd(x)
        rv, rp = self.rated
        if self.kind == "lamp" and rp:
            return [("Brightness", "%d %%" % min(999, round(100 * v * v / self.R / rp)))]
        if self.kind == "motor" and rv:
            return [("Speed", "%d %% of full speed" % round(100 * v / rv))]
        if self.kind == "buzzer":
            return [("Sound", "On" if rv and v > 0.3 * rv else "Off")]
        return []

    def view(self, x):
        v = self.vd(x)
        rv, rp = self.rated
        if self.kind == "lamp" and rp:
            return {"glow": ("#fbbf24", min(1.0, v * v / self.R / rp))}
        if self.kind == "motor" and rv:
            return {"spin": v / rv}
        if self.kind == "buzzer" and rv and v > 0.3 * rv:
            return {"sound": True}
        if self.kind == "voltmeter":
            return {"reading": fmt_si(v, "V")}
        return None

    def warn(self, x):
        v = self.vd(x)
        p = v * v / self.res()
        rv, rp = self.rated
        if self.kind == "resistor" and p > 0.25:
            return [("Warning", "%s turns %s into heat. An ordinary ¼-watt resistor would overheat; "
                                "use a bigger resistor (higher wattage or more ohms)." % (self.label, fmt_si(p, "W")))]
        if self.kind == "lamp" and rp and p > 1.5 * rp:
            return [("Warning", "%s gets %s but is rated %s, so a real bulb would burn out."
                     % (self.label, fmt_si(p, "W"), fmt_si(rp, "W")))]
        if self.kind == "motor" and rv and abs(v) > 1.5 * rv:
            return [("Warning", "%s has %s across it but is rated %s." % (self.label, fmt_si(abs(v), "V"), fmt_si(rv, "V")))]
        if self.kind == "buzzer" and v < -0.5:
            return [("Warning", "%s is connected backwards: a buzzer only sounds with + at the higher voltage." % self.label)]
        return []


class LDR(Resistor):
    def res(self):
        light = max(0.0, min(100.0, float(self.comp.get("light", 50)))) / 100.0
        return 1e6 * (1e3 / 1e6) ** light   # 1 MΩ dark ... 1 kΩ bright

    def extra(self, x):
        return [("Light level", "%d %%" % round(float(self.comp.get("light", 50)))),
                ("Resistance", fmt_si(self.res(), "Ω"))]


class Switch(Dev):
    def __init__(self, sim, comp, nodes, push=False):
        Dev.__init__(self, sim, comp, nodes)
        self.push = push

    def closed(self):
        return (self.cid in self.sim.pressed) if self.push else bool(self.comp.get("closed"))

    def g_(self):
        return 100.0 if self.closed() else 1e-10

    def stamp_lin(self, S):
        S.g(self.n[0], self.n[1], self.g_())

    def currents(self, x):
        i = self.vd(x) * self.g_()
        return [i, -i]

    def extra(self, x):
        return [("State", ("Pressed (closed)" if self.closed() else "Released (open)") if self.push
                 else ("Closed (on)" if self.closed() else "Open (off)"))]


class Fuse(Dev):
    def __init__(self, sim, comp, nodes, rating):
        Dev.__init__(self, sim, comp, nodes)
        self.rating = rating
        self.blown = False

    def g_(self):
        return 1e-10 if self.blown else 20.0

    def stamp_lin(self, S):
        S.g(self.n[0], self.n[1], self.g_())

    def currents(self, x):
        i = self.vd(x) * self.g_()
        return [i, -i]

    def discrete(self, x):
        if not self.blown and abs(self.vd(x) * self.g_()) > self.rating:
            self.blown = True
            return True
        return False

    def export(self):
        return {"blown": self.blown}

    def restore(self, st):
        self.blown = bool(st.get("blown"))

    def extra(self, x):
        return [("State", "BLOWN" if self.blown else "OK (rated %s)" % fmt_si(self.rating, "A"))]

    def view(self, x):
        return {"cross": C["danger"]} if self.blown else None

    def warn(self, x):
        if self.blown:
            return [("Warning", "%s has blown: more than %s flowed through it. Fix the cause, then press "
                                "Restart to fit a new fuse." % (self.label, fmt_si(self.rating, "A")))]
        return []


class Pot(Dev):
    def __init__(self, sim, comp, nodes, R):
        Dev.__init__(self, sim, comp, nodes)
        self.R = max(R, 1.0)

    def parts(self):
        p = max(0.0, min(1.0, float(self.comp.get("wiper", 0.5))))
        lo = self.R * 1e-4 + 0.01
        return max(self.R * p, lo), max(self.R * (1 - p), lo)

    def stamp_lin(self, S):
        r1, r2 = self.parts()
        S.g(self.n[0], self.n[1], 1.0 / r1)
        S.g(self.n[1], self.n[2], 1.0 / r2)

    def currents(self, x):
        r1, r2 = self.parts()
        i1 = (self.V(x, 0) - self.V(x, 1)) / r1
        i2 = (self.V(x, 1) - self.V(x, 2)) / r2
        return [i1, i2 - i1, -i2]

    def info(self, x):
        cs = self.currents(x)
        return [("Wiper position", "%d %%" % round(100 * float(self.comp.get("wiper", 0.5)))),
                ("Wiper voltage", fmt_si(self.V(x, 1), "V")),
                ("Current (pin 1)", fmt_si(cs[0], "A"))]


class Capacitor(Dev):
    reactive = True

    def __init__(self, sim, comp, nodes, Cval, polar=False):
        Dev.__init__(self, sim, comp, nodes)
        self.C = max(Cval, 1e-18)
        self.polar = polar
        self.v = self.v1 = self.i = 0.0
        self._g = self._ieq = 0.0

    def stamp_lin(self, S):
        if not S.dc:
            S.g(self.n[0], self.n[1], (1.0 if S.method == "be" else 1.5) * self.C / S.h)

    def rhs(self, S):
        if S.dc:
            self._g = self._ieq = 0.0
            return
        if S.method == "be":
            g = self.C / S.h
            ieq = g * self.v
        else:
            g = 1.5 * self.C / S.h
            ieq = self.C / (2 * S.h) * (4 * self.v - self.v1)
        self._g, self._ieq = g, ieq
        S.cur(self.n[1], self.n[0], ieq)

    def accept(self, S, x):
        v = self.vd(x)
        if S.dc:
            self.i = 0.0
            self.v1 = v
        else:
            self.i = self._g * v - self._ieq
            self.v1 = self.v
        self.v = v

    def currents(self, x):
        return [self.i, -self.i]

    def ac(self, A, w):
        _ac_g(A, self.n[0], self.n[1], 1j * w * self.C)

    def export(self):
        return {"v": self.v}

    def restore(self, st):
        self.v = self.v1 = float(st.get("v", 0.0))

    def extra(self, x):
        return [("Stored charge", fmt_si(self.C * self.vd(x), "C"))]

    def warn(self, x):
        if self.polar and self.vd(x) < -1.0:
            return [("Warning", "%s is connected backwards (%s across it). An electrolytic capacitor can be "
                                "damaged when its − pin is at the higher voltage." % (self.label, fmt_si(self.vd(x), "V")))]
        return []


class Inductor(Dev):
    reactive = True
    nbr = 1

    def __init__(self, sim, comp, nodes, Lval):
        Dev.__init__(self, sim, comp, nodes)
        self.L = max(Lval, 1e-15)
        self.j = self.j1 = 0.0

    def stamp_lin(self, S):
        k = self.br
        if S.open is self:
            S.A[k][k] += 1.0
            return
        r = 0.0 if S.dc else (1.0 if S.method == "be" else 1.5) * self.L / S.h
        S.branch(k, self.n[0], self.n[1], r)

    def rhs(self, S):
        if S.dc or S.open is self:
            return
        if S.method == "be":
            S.b[self.br] -= self.L / S.h * self.j
        else:
            S.b[self.br] -= self.L / (2 * S.h) * (4 * self.j - self.j1)

    def accept(self, S, x):
        j = x[self.br]
        if S.dc:
            self.j1 = j
        else:
            self.j1 = self.j
        self.j = j

    def currents(self, x):
        j = x[self.br]
        return [j, -j]

    def ac(self, A, w):
        A[self.br][self.br] -= 1j * w * self.L

    def export(self):
        return {"j": self.j}

    def restore(self, st):
        self.j = self.j1 = float(st.get("j", 0.0))


class VSource(Dev):
    nbr = 1

    def __init__(self, sim, comp, nodes, V, wave="dc", f=0.0, R=0.0, kind="source"):
        Dev.__init__(self, sim, comp, nodes)
        self.V0 = V
        self.wave = wave
        self.f = f
        self.R = R
        self.kind = kind
        self.timevar = wave != "dc"

    def value(self, S):
        if self.wave == "sine":
            return 0.0 if S.dc else self.V0 * math.sin(2 * math.pi * self.f * S.t)
        if self.wave == "square":
            if S.dc:
                return 0.0
            return self.V0 if (self.f * S.t) % 1.0 < 0.5 else 0.0
        return self.V0

    def stamp_lin(self, S):
        S.branch(self.br, self.n[0], self.n[1], self.R)

    def rhs(self, S):
        S.b[self.br] += S.scale * self.value(S)

    def periods(self):
        return [1.0 / self.f] if self.wave != "dc" and self.f > 0 else []

    def currents(self, x):
        j = x[self.br]
        return [j, -j]

    def info(self, x):
        j = x[self.br]
        v = self.vd(x)
        if self.kind == "ammeter":
            return [("Reading", fmt_si(j, "A"))]
        out = [("Voltage", fmt_si(v, "V")), ("Current out of +", fmt_si(-j, "A")),
               ("Power delivered", fmt_si(-v * j, "W"))]
        if self.kind == "battery":
            out.append(("Internal resistance", fmt_si(self.R, "Ω")))
        return out

    def view(self, x):
        if self.kind == "ammeter":
            return {"reading": fmt_si(x[self.br], "A")}
        return None

    def warn(self, x):
        j = abs(x[self.br])
        if self.kind == "battery" and j > 1.0:
            return [("Warning", "%s is delivering %s. That is close to a short circuit and would drain or "
                                "overheat a real battery." % (self.label, fmt_si(j, "A")))]
        if self.kind in ("source", "rail") and j > 5.0:
            return [("Warning", "%s is supplying %s. Check for a short circuit (a wire or a very small "
                                "resistance across the supply)." % (self.label, fmt_si(j, "A")))]
        return []


class ISource(Dev):
    def __init__(self, sim, comp, nodes, I):
        Dev.__init__(self, sim, comp, nodes)
        self.I = I

    def rhs(self, S):
        S.cur(self.n[1], self.n[0], S.scale * self.I)  # flows out of the + pin

    def currents(self, x):
        return [-self.I, self.I]

    def info(self, x):
        v = self.vd(x)
        return [("Current out of +", fmt_si(self.I, "A")), ("Voltage across", fmt_si(v, "V")),
                ("Power delivered", fmt_si(v * self.I, "W"))]

    def warn(self, x):
        if abs(self.vd(x)) > 1e4:
            return [("Warning", "%s has nowhere to send its current, so its voltage shoots up. Give it a "
                                "complete loop to push current around." % self.label)]
        return []


LED_COLORS = [("infrared", 1.2, "#7f1d1d"), ("ir", 1.2, "#7f1d1d"), ("red", 1.8, "#ef4444"),
              ("orange", 1.9, "#f97316"), ("amber", 1.95, "#f59e0b"), ("yellow", 1.95, "#facc15"),
              ("green", 2.1, "#22c55e"), ("blue", 2.9, "#3b82f6"), ("white", 2.9, "#e5e7eb"),
              ("purple", 3.1, "#a855f7"), ("violet", 3.1, "#a855f7"), ("uv", 3.2, "#8b5cf6"),
              ("pink", 2.9, "#ec4899")]


class Diode(Dev):
    nonlinear = True
    IZT = 5e-3   # Zener current at the Zener voltage

    def __init__(self, sim, comp, nodes, Is=2.52e-9, N=1.75, bv=None, led=None):
        Dev.__init__(self, sim, comp, nodes)
        self.Is, self.N, self.bv, self.led = Is, N, bv, led
        self.vt = N * VT
        self.vcrit = self.vt * math.log(self.vt / (math.sqrt(2) * Is))
        self.vcritz = VT * math.log(VT / (math.sqrt(2) * self.IZT))
        self.vdl = 0.0

    def iv(self, v):
        e, de = _exp(v / self.vt)
        i = self.Is * (e - 1.0)
        g = self.Is * de / self.vt
        if self.bv is not None:
            e2, de2 = _exp(-(v + self.bv) / VT)
            i -= self.IZT * e2
            g += self.IZT * de2 / VT
        return i + GMIN * v, g + GMIN

    def begin(self, x):
        self.vdl = min(self.vd(x), self.vcrit)

    def stamp_nl(self, S, x):
        v = self.vd(x)
        vold = self.vdl
        if self.bv is not None and v < min(0.0, -self.bv + 10 * VT):
            u, lim = pnjlim(-(v + self.bv), -(vold + self.bv), VT, self.vcritz)
            v = -(u + self.bv)
        else:
            v, lim = pnjlim(v, vold, self.vt, self.vcrit)
        self.vdl = v
        if lim:
            S.limited = True
        i, g = self.iv(v)
        a, k = self.n
        S.g(a, k, g)
        S.cur(a, k, i - g * v)

    def currents(self, x):
        i = self.iv(self.vd(x))[0]
        return [i, -i]

    def extra(self, x):
        i = self.currents(x)[0]
        if self.led:
            return [("Brightness", "%d %%" % max(0, min(999, round(100 * i / 0.015))))]
        if self.bv is not None and self.vd(x) < -0.5 * self.bv and i < -1e-5:
            return [("State", "Conducting backwards (Zener)")]
        return [("State", "Conducting" if i > 1e-5 else "Blocking")]

    def view(self, x):
        if self.led:
            i = self.currents(x)[0]
            if i > 5e-5:
                return {"glow": (self.led, min(1.0, i / 0.015)),
                        "cross": "#111827" if i > 0.05 else None}
        return None

    def warn(self, x):
        i = self.currents(x)[0]
        out = []
        if self.led and i > 0.03:
            out.append(("Warning", "%s has %s flowing through it. A real LED would burn out: add or increase "
                                   "its series resistor to keep it near 10–20 mA." % (self.label, fmt_si(i, "A"))))
        if self.led and self.vd(x) < -5.0:
            out.append(("Warning", "%s has %s across it backwards. Most LEDs are damaged above about 5 V reverse."
                        % (self.label, fmt_si(-self.vd(x), "V"))))
        if not self.led and self.bv is None and i > 1.0:
            out.append(("Warning", "%s is carrying %s, more than a small diode can handle." % (self.label, fmt_si(i, "A"))))
        return out


class BJT(Dev):
    nonlinear = True

    def __init__(self, sim, comp, nodes, pol=1, Is=1e-14, BF=150.0, BR=5.0):
        Dev.__init__(self, sim, comp, nodes)   # nodes: C, B, E
        self.pol, self.Is, self.BF, self.BR = pol, Is, BF, BR
        self.vcrit = VT * math.log(VT / (math.sqrt(2) * Is))
        self.vbe = self.vbc = 0.0

    def _eval(self, vbe, vbc):
        Is, BF, BR = self.Is, self.BF, self.BR
        ef, d1 = _exp(vbe / VT)
        er, d2 = _exp(vbc / VT)
        gf, gr = Is * d1 / VT, Is * d2 / VT
        ic = Is * (ef - er) - Is / BR * (er - 1.0) - GMIN * vbc
        ib = Is / BF * (ef - 1.0) + Is / BR * (er - 1.0) + GMIN * (vbe + vbc)
        return ic, ib, gf, -gr - gr / BR - GMIN, gf / BF + GMIN, gr / BR + GMIN

    def _volts(self, x):
        vC, vB, vE = self.V(x, 0), self.V(x, 1), self.V(x, 2)
        return vC, vB, vE, self.pol * (vB - vE), self.pol * (vB - vC)

    def begin(self, x):
        _c, _b, _e, vbe, vbc = self._volts(x)
        self.vbe, self.vbc = min(vbe, self.vcrit), min(vbc, self.vcrit)

    def stamp_nl(self, S, x):
        p = self.pol
        _c, _b, vE, vbe, vbc = self._volts(x)
        vbe, l1 = pnjlim(vbe, self.vbe, VT, self.vcrit)
        vbc, l2 = pnjlim(vbc, self.vbc, VT, self.vcrit)
        self.vbe, self.vbc = vbe, vbc
        if l1 or l2:
            S.limited = True
        ic, ib, a, bb, c, d = self._eval(vbe, vbc)
        Jc = [-bb, a + bb, -a]      # d/dV(C, B, E)
        Jb = [-d, c + d, -c]
        Je = [-(Jc[i] + Jb[i]) for i in range(3)]
        VB = vE + p * vbe
        VC = VB - p * vbc
        S.nl(self.n, [p * ic, p * ib, -p * (ic + ib)], [Jc, Jb, Je], [VC, VB, vE])

    def currents(self, x):
        _c, _b, _e, vbe, vbc = self._volts(x)
        ic, ib = self._eval(vbe, vbc)[:2]
        p = self.pol
        return [p * ic, p * ib, -p * (ic + ib)]

    def info(self, x):
        _c, _b, _e, vbe, vbc = self._volts(x)
        ic, ib = self._eval(vbe, vbc)[:2]
        if vbe < 0.45 or ic < 1e-7:
            region = "Off (cut-off)"
        elif vbc > 0.3:
            region = "Saturated (fully on)"
        else:
            region = "Active (amplifying)"
        gain = ("%.0f" % (ic / ib)) if ib > 1e-12 and ic > 0 else "—"
        return [("State", region), ("Base current", fmt_si(ib, "A")), ("Collector current", fmt_si(ic, "A")),
                ("V(BE)", fmt_si(vbe * self.pol, "V")), ("Current gain Ic/Ib", gain)]


class NMOS(Dev):
    nonlinear = True

    def __init__(self, sim, comp, nodes, vth=2.1, K=0.05, lam=0.01):
        Dev.__init__(self, sim, comp, nodes)   # nodes: G, D, S
        self.vth, self.K, self.lam = vth, K, lam
        self.vgs = self.vds = 0.0

    def _ids(self, vgs, vds):
        """Square-law model with a smooth turn-on.  vds >= 0.  Returns (Id, gm, gds)."""
        s = 0.04
        u = (vgs - self.vth) / s
        if u > 40:
            vov, sg = vgs - self.vth, 1.0
        elif u < -40:
            vov, sg = s * math.exp(u), math.exp(u)
        else:
            e = math.exp(u)
            vov, sg = s * math.log1p(e), e / (1.0 + e)
        K, lam = self.K, self.lam
        cl = 1.0 + lam * vds
        if vds < vov:
            base = vov * vds - 0.5 * vds * vds
            i = K * base * cl
            dvov = K * vds * cl
            gds = K * (vov - vds) * cl + K * base * lam
        else:
            base = 0.5 * vov * vov
            i = K * base * cl
            dvov = K * vov * cl
            gds = K * base * lam
        return i, dvov * sg, gds

    def _eval(self, vgs, vds):
        """Drain current and its derivatives d/dV(G, D, S) for any sign of vds."""
        if vds >= 0:
            i, gm, gds = self._ids(vgs, vds)
            return i + GMIN * vds, [gm, gds + GMIN, -gm - gds - GMIN]
        i, gm, gds = self._ids(vgs - vds, -vds)   # source and drain swap roles
        return -i + GMIN * vds, [-gm, gm + gds + GMIN, -gds - GMIN]

    def begin(self, x):
        vG, vD, vS = self.V(x, 0), self.V(x, 1), self.V(x, 2)
        self.vgs, self.vds = vG - vS, vD - vS

    def stamp_nl(self, S, x):
        vG, vD, vS = self.V(x, 0), self.V(x, 1), self.V(x, 2)
        vgs, vds = vG - vS, vD - vS
        if abs(vgs - self.vgs) > 1.0:
            vgs = self.vgs + math.copysign(1.0, vgs - self.vgs)
            S.limited = True
        if abs(vds - self.vds) > 3.0:
            vds = self.vds + math.copysign(3.0, vds - self.vds)
            S.limited = True
        self.vgs, self.vds = vgs, vds
        Id, Jd = self._eval(vgs, vds)
        S.nl(self.n, [0.0, Id, -Id], [[0.0, 0.0, 0.0], Jd, [-v for v in Jd]], [vS + vgs, vS + vds, vS])

    def currents(self, x):
        vG, vD, vS = self.V(x, 0), self.V(x, 1), self.V(x, 2)
        Id = self._eval(vG - vS, vD - vS)[0]
        return [0.0, Id, -Id]

    def info(self, x):
        vG, vD, vS = self.V(x, 0), self.V(x, 1), self.V(x, 2)
        Id = self.currents(x)[1]
        on = vG - vS > self.vth
        return [("State", "On" if on else "Off"), ("V(GS)", fmt_si(vG - vS, "V")),
                ("Drain current", fmt_si(Id, "A")), ("V(DS)", fmt_si(vD - vS, "V"))]


class OpAmp(Dev):
    nonlinear = True
    nbr = 1
    GAIN = 2e5
    ROUT = 50.0

    def __init__(self, sim, comp, nodes, fixed_hi=None, fixed_lo=None, drop_hi=1.5, drop_lo=1.5):
        Dev.__init__(self, sim, comp, nodes)   # nodes: IN−, IN+, OUT, V+, V−
        self.fixed_hi, self.fixed_lo = fixed_hi, fixed_lo
        self.drop_hi, self.drop_lo = drop_hi, drop_lo

    def _rails(self, x):
        vc = self.fixed_hi if self.fixed_hi is not None else self.V(x, 3)
        ve = self.fixed_lo if self.fixed_lo is not None else self.V(x, 4)
        return vc, ve

    def _f(self, vn, vp, vc, ve):
        hi, lo = vc - self.drop_hi, ve + self.drop_lo
        if hi < lo:
            hi = lo = 0.5 * (hi + lo)
        half = max(0.5 * (hi - lo), 1e-3)
        mid = 0.5 * (hi + lo)
        u = self.GAIN * (vp - vn) / half
        T = math.tanh(u)
        Tp = 1.0 - T * T
        q = T - u * Tp
        return mid + half * T, self.GAIN * Tp, 0.5 + 0.5 * q, 0.5 - 0.5 * q, T

    def stamp_nl(self, S, x):
        k = self.br
        nN, nP, nO, nC, nE = self.n
        vn, vp = self.V(x, 0), self.V(x, 1)
        vc, ve = self._rails(x)
        f, gd, dh, dl, _T = self._f(vn, vp, vc, ve)
        A = S.A
        if nO:
            A[nO - 1][k] += 1.0
            A[k][nO - 1] += 1.0
        A[k][k] -= self.ROUT
        rhs = f
        terms = [(nP, gd, vp), (nN, -gd, vn)]
        if self.fixed_hi is None:
            terms.append((nC, dh, vc))
        if self.fixed_lo is None:
            terms.append((nE, dl, ve))
        for node, d, v in terms:
            if node:
                A[k][node - 1] -= d
            rhs -= d * v
        S.b[k] += rhs

    def currents(self, x):
        return [0.0, 0.0, x[self.br], 0.0, 0.0]

    def info(self, x):
        vn, vp = self.V(x, 0), self.V(x, 1)
        vc, ve = self._rails(x)
        T = self._f(vn, vp, vc, ve)[4]
        state = "Saturated high" if T > 0.98 else "Saturated low" if T < -0.98 else "Linear (amplifying)"
        return [("State", state), ("Output", fmt_si(self.V(x, 2), "V")),
                ("V(+) − V(−)", fmt_si(vp - vn, "V")), ("Output current", fmt_si(-x[self.br], "A"))]


class Gate(Dev):
    nonlinear = True
    nbr = 1
    VDD = 5.0
    ROUT = 50.0
    FUNCS = {
        "and": lambda a, b: (a * b, b, a),
        "nand": lambda a, b: (1 - a * b, -b, -a),
        "or": lambda a, b: (a + b - a * b, 1 - b, 1 - a),
        "nor": lambda a, b: (1 - (a + b - a * b), b - 1, a - 1),
        "xor": lambda a, b: (a + b - 2 * a * b, 1 - 2 * b, 1 - 2 * a),
        "not": lambda a, b: (1 - a, -1.0, 0.0),
    }

    def __init__(self, sim, comp, nodes, kind):
        Dev.__init__(self, sim, comp, nodes)   # inputs..., output (last)
        self.kind = kind

    def stamp_lin(self, S):
        for node in self.n[:-1]:   # weak pull-down: an input left floating (e.g. by an open switch) reads 0
            S.g(node, 0, LOGIC_PULLDOWN)

    @staticmethod
    def _s(v):
        u = max(-40.0, min(40.0, (v - 2.5) * 8.0))
        s = 1.0 / (1.0 + math.exp(-u))
        return s, 8.0 * s * (1.0 - s)

    def stamp_nl(self, S, x):
        k = self.br
        ins = self.n[:-1]
        nO = self.n[-1]
        vs = [self.V(x, i) for i in range(len(ins))]
        sa, da = self._s(vs[0])
        sb, db = self._s(vs[1]) if len(ins) > 1 else (0.0, 0.0)
        f, dfa, dfb = self.FUNCS[self.kind](sa, sb)
        A = S.A
        if nO:
            A[nO - 1][k] += 1.0
            A[k][nO - 1] += 1.0
        A[k][k] -= self.ROUT
        rhs = self.VDD * f
        for node, d, v in ((ins[0], self.VDD * dfa * da, vs[0]),
                           (ins[1] if len(ins) > 1 else 0, self.VDD * dfb * db, vs[1] if len(ins) > 1 else 0.0)):
            if node:
                A[k][node - 1] -= d
            rhs -= d * v
        S.b[k] += rhs

    def currents(self, x):
        return [self.V(x, i) * LOGIC_PULLDOWN for i in range(len(self.n) - 1)] + [x[self.br]]

    def info(self, x):
        names = ["A", "B"][:len(self.n) - 1]
        ins = ", ".join("%s = %d" % (nm, 1 if self.V(x, i) > 2.5 else 0) for i, nm in enumerate(names))
        vo = self.V(x, len(self.n) - 1)
        return [("Inputs", ins), ("Output Y", "%d  (%s)" % (1 if vo > 2.5 else 0, fmt_si(vo, "V")))]


LOGIC_PULLDOWN = 1e-6   # 1 MΩ: floating logic inputs read LOW


class FlipFlop(Dev):
    """Edge-triggered D / T / JK flip-flops and the SR latch (5 V logic, outputs Q and Q').
    The stored bit only changes between time steps, so feedback (Q' wired to D) and chains of
    flip-flops (counters) behave like the real thing."""
    nbr = 2
    VDD = 5.0
    ROUT = 50.0
    INPUTS = {"dff": ("D", "CLK", "SET", "CLR"), "tff": ("T", "CLK", "SET", "CLR"),
              "jkff": ("J", "K", "CLK", "SET", "CLR"), "srlatch": ("S", "R")}

    def __init__(self, sim, comp, nodes, kind):
        Dev.__init__(self, sim, comp, nodes)   # inputs (see INPUTS), then Q, Q'
        self.kind = kind
        self.names = self.INPUTS[kind]
        self.nin = len(self.names)
        self.Q = False
        self.clk = None        # clock level at the previous check (None = not seen yet)
        self.invalid = None    # None, or the value both outputs are forced to
        self.edges = 0

    def level(self, x, name):
        return self.V(x, self.names.index(name)) > 2.5

    def outs(self):
        if self.invalid is not None:
            return self.invalid, self.invalid
        return self.Q, not self.Q

    def stamp_lin(self, S):
        for node in self.n[:self.nin]:
            S.g(node, 0, LOGIC_PULLDOWN)
        A = S.A
        for j, node in enumerate(self.n[self.nin:]):
            k = self.br + j
            if node:
                A[node - 1][k] += 1.0
                A[k][node - 1] += 1.0
            A[k][k] -= self.ROUT

    def rhs(self, S):
        q, qb = self.outs()
        S.b[self.br] += self.VDD if q else 0.0
        S.b[self.br + 1] += self.VDD if qb else 0.0

    def discrete(self, x):
        before = (self.Q, self.invalid)
        lv = lambda name: self.level(x, name)
        if self.kind == "srlatch":
            s, r = lv("S"), lv("R")
            self.invalid = False if (s and r) else None
            if s and not r:
                self.Q = True
            elif r and not s:
                self.Q = False
        else:
            clk = lv("CLK")
            edge = self.clk is False and clk
            self.clk = clk
            st, cl = lv("SET"), lv("CLR")
            self.invalid = True if (st and cl) else None
            if st and not cl:
                self.Q = True
            elif cl and not st:
                self.Q = False
            elif edge and not st:
                self.edges += 1
                if self.kind == "dff":
                    self.Q = lv("D")
                elif self.kind == "tff":
                    if lv("T"):
                        self.Q = not self.Q
                else:
                    j, k = lv("J"), lv("K")
                    if j and k:
                        self.Q = not self.Q
                    elif j:
                        self.Q = True
                    elif k:
                        self.Q = False
        return (self.Q, self.invalid) != before

    def currents(self, x):
        return ([self.V(x, i) * LOGIC_PULLDOWN for i in range(self.nin)]
                + [x[self.br], x[self.br + 1]])

    def info(self, x):
        q, qb = self.outs()
        lv = lambda nm: 1 if self.level(x, nm) else 0
        main = [nm for nm in self.names if nm not in ("SET", "CLR")]
        out = [("Q", "%d  (%s)" % (q, "HIGH" if q else "LOW")), (QBAR, "%d" % qb),
               ("Inputs", "   ".join("%s %d" % (nm, lv(nm)) for nm in main))]
        if "SET" in self.names:
            out.append(("SET / CLR", "%d / %d" % (lv("SET"), lv("CLR"))))
        if self.kind != "srlatch":
            out.append(("Clock edges so far", "%d" % self.edges))
        if self.invalid is not None:
            out.append(("State", "Not allowed: %s both HIGH" % ("S and R" if self.kind == "srlatch" else "SET and CLR")))
        return out

    def view(self, x):
        q = self.outs()[0]
        return {"reading": "Q = %d" % q}

    def warn(self, x):
        if self.invalid is None:
            return []
        if self.kind == "srlatch":
            return [("Warning", "%s: S and R are both HIGH, which an SR latch doesn’t allow (Q and Q' are both 0, "
                                "and what it remembers afterwards depends on which input goes LOW first)." % self.label)]
        return [("Warning", "%s: SET and CLR are both HIGH, which isn’t allowed (Q and Q' are both 1). "
                            "Only use one of them at a time." % self.label)]

    def export(self):
        return {"Q": self.Q, "clk": self.clk, "edges": self.edges}

    def restore(self, st):
        self.Q = bool(st.get("Q"))
        self.clk = st.get("clk")
        self.edges = int(st.get("edges", 0))


class LogicChip(Dev):
    """A part whose behaviour comes from its logic equations (see LogicProgram).
    With VCC / GND pins the outputs switch between those pins, so the chip only works when powered
    and its supply current really flows through VCC.  Without them it runs as 5 V logic."""
    ROUT = 50.0          # output resistance (about what a 74HC output has)
    VINT = 5.0           # internal supply when the part has no power pins
    TIE = 10.0           # extra VCC / GND pins are tied to the first one (0.1 Ω)

    def __init__(self, sim, comp, nodes, prog, pin_names):
        Dev.__init__(self, sim, comp, nodes)   # one node per pin, in pin order
        self.prog = prog
        self.pin_names = pin_names
        first = {}
        for i, nm in enumerate(pin_names):
            first.setdefault(nm, i)
        self.pin_of = first
        self.in_pins = [first[n] for n in prog.inputs]
        self.out_pins = [first[n] for n in prog.outputs]
        pw = [i for i, nm in enumerate(pin_names) if is_power_pin(nm)]
        gd = [i for i, nm in enumerate(pin_names) if is_ground_pin(nm)]
        self.vcc_pins, self.gnd_pins = pw, gd
        self.vg = nodes[gd[0]] if gd else 0
        if pw:
            self.vs = nodes[pw[0]]
            self.nbr = 0
        else:
            self.vs = sim.new_node("%s (5 V supply)" % self.label)
            self.nbr = 1
        self.s = [0] * len(prog.names)
        self.prev = {}
        self.high = {}     # output pin index -> driven HIGH?
        self.powered = None

    # ---- helpers
    def nv(self, x, node):
        return x[node - 1] if node else 0.0

    def supply(self, x):
        return self.nv(x, self.vs) - self.nv(x, self.vg)

    def stamp_lin(self, S):
        vs, vg = self.vs, self.vg
        if self.nbr:
            S.branch(self.br, vs, vg)
        S.g(vs, vg, 1e-6)                              # tiny quiescent current
        for k in self.in_pins:
            S.g(self.n[k], vg, LOGIC_PULLDOWN)
        for k in self.out_pins:
            S.g(self.n[k], vs if self.high.get(k) else vg, 1.0 / self.ROUT)
        for group, main in ((self.vcc_pins, self.vs), (self.gnd_pins, self.vg)):
            for k in group[1:]:
                S.g(self.n[k], main, self.TIE)

    def rhs(self, S):
        if self.nbr:
            S.b[self.br] += S.scale * self.VINT

    def discrete(self, x):
        sup = self.supply(x)
        on = sup > 1.5
        self.powered = on
        vg = self.nv(x, self.vg)
        s = self.s
        idx = self.prog.idx
        for name in self.prog.inputs:
            v = self.nv(x, self.n[self.pin_of[name]]) - vg
            s[idx[name]] = 1 if (on and v > 0.5 * sup) else 0
        self.prog.step(s, self.prev)
        changed = False
        for name in self.prog.outputs:
            k = self.pin_of[name]
            h = bool(s[idx[name]])
            if self.high.get(k) != h:
                self.high[k] = h
                changed = True
        return changed

    # ---- read-outs
    def currents(self, x):
        cur = [0.0] * len(self.n)
        V = lambda k: self.nv(x, self.n[k])
        vsv, vgv = self.nv(x, self.vs), self.nv(x, self.vg)
        own_vs = self.vcc_pins[0] if self.vcc_pins else None
        own_vg = self.gnd_pins[0] if self.gnd_pins else None

        def flow(k_in, k_out, i):
            if k_in is not None:
                cur[k_in] += i
            if k_out is not None:
                cur[k_out] -= i
        for k in self.in_pins:
            flow(k, own_vg, (V(k) - vgv) * LOGIC_PULLDOWN)
        for k in self.out_pins:
            if self.high.get(k):
                flow(own_vs, k, (vsv - V(k)) / self.ROUT)
            else:
                flow(k, own_vg, (V(k) - vgv) / self.ROUT)
        flow(own_vs, own_vg, (vsv - vgv) * 1e-6)
        for group, main, mv in ((self.vcc_pins, own_vs, vsv), (self.gnd_pins, own_vg, vgv)):
            for k in group[1:]:
                flow(k, main, (V(k) - mv) * self.TIE)
        return cur

    def _bits(self, names):
        return "   ".join("%s %d" % (n, self.s[self.prog.idx[n]]) for n in names)

    def info(self, x):
        out = []
        if self.vcc_pins:
            sup = self.supply(x)
            out.append(("Power", "%s  (%s)" % (fmt_si(sup, "V"), "on" if sup > 1.5 else "OFF: wire VCC and GND")))
        for title, names in (("Inputs", self.prog.inputs), ("Outputs", self.prog.outputs),
                             ("Internal", self.prog.internal)):
            names = names[:16]
            for k in range(0, len(names), 4):      # four per line so the panel doesn't cut them off
                out.append((title if k == 0 else "", self._bits(names[k:k + 4])))
        return out

    def view(self, x):
        on = self.supply(x) > 1.5
        return {"pinstate": [(k, bool(self.s[self.prog.idx[self.pin_names[k]]]) if on else None)
                             for k in self.in_pins + self.out_pins]}

    def warn(self, x):
        out = []
        sup = self.supply(x)
        used = any((self.cid, k) in self.sim.wired for k in self.out_pins)
        if self.vcc_pins and used and sup < 1.5:
            names = "/".join(dict.fromkeys(self.pin_names[k] for k in self.vcc_pins + self.gnd_pins))
            out.append(("Warning", "%s has no power, so its outputs stay LOW. Wire %s: VCC to +5 V and GND to "
                                   "ground. Real logic chips need power too." % (self.label, names)))
        if sup > 6.5:
            out.append(("Warning", "%s has %s between VCC and GND. Most logic chips are damaged above about "
                                   "6 V (74HC: 2–6 V, 74LS: 4.75–5.25 V)." % (self.label, fmt_si(sup, "V"))))
        if sup < -0.5:
            out.append(("Warning", "%s is powered backwards (GND is at the higher voltage). That destroys a "
                                   "real chip." % self.label))
        cur = self.currents(x)
        for k in self.out_pins:
            i = abs(cur[k])
            if i > 0.025:
                out.append(("Warning", "%s: output %s is supplying %s. A logic output can only give about "
                                       "20 mA; it may be shorted or driving a load without a resistor."
                            % (self.label, self.pin_names[k], fmt_si(i, "A"))))
                break
        return out

    def export(self):
        return {"s": dict(zip(self.prog.names, self.s)), "prev": {self.prog.names[i]: v for i, v in self.prev.items()}}

    def restore(self, st):
        sv = st.get("s", {})
        for n, v in sv.items():
            if n in self.prog.idx and n in self.prog.states:
                self.s[self.prog.idx[n]] = 1 if v else 0
        for n, v in st.get("prev", {}).items():
            if n in self.prog.idx:
                self.prev[self.prog.idx[n]] = v


class Timer555(Dev):
    nbr = 1

    def __init__(self, sim, comp, nodes, m, reset_wired):
        # nodes: TRIG, THRES, DISCH, CTRL, OUT, VCC, RESET, GND;  m = internal 1/3-VCC node
        Dev.__init__(self, sim, comp, nodes)
        self.m = m
        self.reset_wired = reset_wired
        self.Q = False

    def stamp_lin(self, S):
        nT, nTh, nD, nC, nO, nV, nR, nG = self.n
        S.g(nV, nC, 1 / 5000.0)
        S.g(nC, self.m, 1 / 5000.0)
        S.g(self.m, nG, 1 / 5000.0)
        S.g(nD, nG, 1e-10 if self.Q else 0.1)
        k = self.br
        A = S.A
        if nO:
            A[nO - 1][k] += 1.0
            A[k][nO - 1] += 1.0
        A[k][k] -= 10.0
        ref = nV if self.Q else nG
        if ref:
            A[k][ref - 1] -= 1.0

    def rhs(self, S):
        S.b[self.br] += -1.7 if self.Q else 0.05

    def discrete(self, x):
        V = lambda i: self.V(x, i)
        vcc = V(5) - V(7)
        if vcc < 3.0:
            q = False
        elif self.reset_wired and V(6) - V(7) < 0.7:
            q = False
        elif V(0) < x[self.m - 1]:
            q = True
        elif V(1) > V(3):
            q = False
        else:
            q = self.Q
        if q != self.Q:
            self.Q = q
            return True
        return False

    def currents(self, x):
        V = lambda i: self.V(x, i)
        vm = x[self.m - 1]
        gD = 1e-10 if self.Q else 0.1
        iD = (V(2) - V(7)) * gD
        iV = (V(5) - V(3)) / 5000.0
        iC = (V(3) - V(5)) / 5000.0 + (V(3) - vm) / 5000.0
        iG = -iD - (vm - V(7)) / 5000.0
        return [0.0, 0.0, iD, iC, x[self.br], iV, 0.0, iG]

    def info(self, x):
        vm = x[self.m - 1]
        return [("Output", "HIGH" if self.Q else "LOW"), ("OUT voltage", fmt_si(self.V(x, 4), "V")),
                ("Switches high below", fmt_si(vm, "V") + " (TRIG)"),
                ("Switches low above", fmt_si(self.V(x, 3), "V") + " (THRES)")]

    def export(self):
        return {"Q": self.Q}

    def restore(self, st):
        self.Q = bool(st.get("Q"))


class Regulator(Dev):
    nonlinear = True
    nbr = 1
    DROP = 2.0
    ROUT = 0.02

    def __init__(self, sim, comp, nodes, vreg=5.0):
        Dev.__init__(self, sim, comp, nodes)   # nodes: IN, OUT, GND
        self.vreg = vreg

    def _f(self, u):
        s = 0.05
        z = (u - self.DROP) / s
        if z > 40:
            g, dg = u - self.DROP, 1.0
        elif z < -40:
            g, dg = s * math.exp(z), math.exp(z)
        else:
            e = math.exp(z)
            g, dg = s * math.log1p(e), e / (1.0 + e)
        w = (self.vreg - g) / s
        if w > 40:
            return g, dg
        if w < -40:
            return self.vreg, 0.0
        e = math.exp(w)
        return self.vreg - s * math.log1p(e), e / (1.0 + e) * dg

    def stamp_nl(self, S, x):
        k = self.br
        nI, nO, nG = self.n
        u = self.V(x, 0) - self.V(x, 2)
        f, df = self._f(u)
        A = S.A
        if nI:
            A[nI - 1][k] += 1.0
        if nO:
            A[nO - 1][k] -= 1.0
            A[k][nO - 1] += 1.0
        if nG:
            A[k][nG - 1] -= 1.0 - df
        if nI:
            A[k][nI - 1] -= df
        A[k][k] += self.ROUT
        S.b[k] += f - df * u

    def currents(self, x):
        j = x[self.br]
        return [j, -j, 0.0]

    def info(self, x):
        return [("Input", fmt_si(self.V(x, 0) - self.V(x, 2), "V")),
                ("Output", fmt_si(self.V(x, 1) - self.V(x, 2), "V")),
                ("Load current", fmt_si(x[self.br], "A"))]

    def warn(self, x):
        u = self.V(x, 0) - self.V(x, 2)
        out = []
        if 1.0 < u < self.vreg + self.DROP - 0.1:
            out.append(("Warning", "%s needs at least about %s at IN to give a steady %s (it has %s)."
                        % (self.label, fmt_si(self.vreg + self.DROP, "V"), fmt_si(self.vreg, "V"), fmt_si(u, "V"))))
        if x[self.br] > 1.5:
            out.append(("Warning", "%s is asked for %s; a 7805 can only give about 1.5 A." % (self.label, fmt_si(x[self.br], "A"))))
        return out


class TempSensor(Dev):
    nbr = 1

    def __init__(self, sim, comp, nodes):
        Dev.__init__(self, sim, comp, nodes)   # nodes: +VS, VOUT, GND
        self.on = False

    def temp(self):
        return float(self.comp.get("temp", 25.0))

    def stamp_lin(self, S):
        k = self.br
        nS, nO, nG = self.n
        A = S.A
        if nO:
            A[nO - 1][k] += 1.0
            A[k][nO - 1] += 1.0
        if nG:
            A[k][nG - 1] -= 1.0
        A[k][k] -= 10.0

    def rhs(self, S):
        S.b[self.br] += (0.5 + 0.01 * self.temp()) if self.on else 0.0

    def discrete(self, x):
        on = self.V(x, 0) - self.V(x, 2) > 2.7
        if on != self.on:
            self.on = on
            return True
        return False

    def currents(self, x):
        return [0.0, x[self.br], 0.0]

    def info(self, x):
        return [("Temperature", "%.0f °C" % self.temp()),
                ("VOUT", fmt_si(self.V(x, 1) - self.V(x, 2), "V") if self.on else "0 V (needs 2.7 V or more at +VS)")]


class Relay(Dev):
    def __init__(self, sim, comp, nodes, rated=5.0):
        Dev.__init__(self, sim, comp, nodes)   # nodes: VCC, GND, IN, NO, COM, NC
        self.rated = rated
        self.on = False

    def stamp_lin(self, S):
        nV, nG, nI, nNO, nCOM, nNC = self.n
        S.g(nV, nG, 1 / 70.0 if self.on else 1e-4)
        S.g(nI, nG, 1e-4)
        S.g(nCOM, nNO, 20.0 if self.on else 1e-10)
        S.g(nCOM, nNC, 1e-10 if self.on else 20.0)

    def discrete(self, x):
        vs = self.V(x, 0) - self.V(x, 1)
        vin = self.V(x, 2) - self.V(x, 1)
        on = vs > 0.6 * self.rated and vin > (0.3 if self.on else 0.5) * vs
        if on != self.on:
            self.on = on
            return True
        return False

    def currents(self, x):
        V = lambda i: self.V(x, i)
        icoil = (V(0) - V(1)) * (1 / 70.0 if self.on else 1e-4)
        iin = (V(2) - V(1)) * 1e-4
        ino = (V(3) - V(4)) * (20.0 if self.on else 1e-10)
        inc = (V(5) - V(4)) * (1e-10 if self.on else 20.0)
        return [icoil, -icoil - iin, iin, ino, -ino - inc, inc]

    def info(self, x):
        return [("Relay", "ON (energised)" if self.on else "OFF"),
                ("Contacts", "COM–NO closed" if self.on else "COM–NC closed")]

    def view(self, x):
        return {"reading": "ON" if self.on else "OFF"}

    def export(self):
        return {"on": self.on}

    def restore(self, st):
        self.on = bool(st.get("on"))


class Probe(Dev):
    def __init__(self, sim, comp, nodes, wired):
        Dev.__init__(self, sim, comp, nodes)
        self.wired = wired

    def info(self, x):
        return [("Voltage", fmt_si(self.V(x, 0), "V") if self.wired else "not connected")]

    def view(self, x):
        return {"reading": fmt_si(self.V(x, 0), "V") if self.wired else "—"}


def _led_spec(value):
    v = (value or "").lower()
    for name, vf, col in LED_COLORS:
        if re.search(r"\b%s\b" % name, v):
            return vf, col
    return 1.8, "#ef4444"


def _make_device(sim, c, rd, model):
    """Create the simulation model for one placed part (None = nothing to simulate)."""
    val = c.get("value", "") or ""
    lab = c.get("label") or rd.name

    def pins(*names):
        return sim.pins(c, rd, names)

    def num(unit, default, positive=True):
        v = qty(val, unit)
        if v is None or (positive and v <= 0):
            if val.strip():
                sim.note("Warning", c["id"], "%s: couldn’t read the value “%s”, so %s is used."
                         % (lab, val, fmt_si(default, _UNIT_SYM.get(unit, ""))))
            return default
        return v

    def make(cls, names, *args, **kw):
        nodes, idx = pins(*names)
        d = cls(sim, c, nodes, *args, **kw)
        d.pidx = idx
        return d

    if model == "resistor":
        return make(Resistor, ("1", "2"), num("ohm", 1000.0))
    if model == "ldr":
        return make(LDR, ("1", "2"), 1.0)
    if model == "potentiometer":
        return make(Pot, ("1", "W", "2"), num("ohm", 10e3))
    if model == "fuse":
        return make(Fuse, ("1", "2"), num("a", 1.0))
    if model == "capacitor":
        return make(Capacitor, ("1", "2"), num("f", 100e-9))
    if model == "capacitor_pol":
        return make(Capacitor, ("+", "−"), num("f", 10e-6), polar=True)
    if model == "inductor":
        return make(Inductor, ("1", "2"), num("h", 1e-3))
    if model == "battery":
        V = num("v", 9.0, positive=False)
        return make(VSource, ("+", "−"), V, R=max(0.05, min(2.0, abs(V) / 6.0)), kind="battery")
    if model == "dc_source":
        return make(VSource, ("+", "−"), num("v", 5.0, positive=False))
    if model in ("ac_source", "square_source"):
        sq = model == "square_source"
        V = num("v", 5.0 if sq else 10.0, positive=False)
        low = val.lower()
        if not sq and "rms" in low:
            V *= math.sqrt(2)
        elif not sq and re.search(r"p-?p\b", low):
            V /= 2.0
        f = qty(val, "hz", allow_bare=False)
        if f is None or f <= 0:
            f = 1.0 if sq else 60.0
        names = ("+", "−") if sq else ("1", "2")
        return make(VSource, names, V, wave="square" if sq else "sine", f=f)
    if model == "current_source":
        return make(ISource, ("+", "−"), num("a", 1e-3, positive=False))
    if model == "voltmeter":
        return make(Resistor, ("+", "−"), 10e6, kind="voltmeter")
    if model == "ammeter":
        return make(VSource, ("+", "−"), 0.0, kind="ammeter")
    if model in ("switch", "pushbutton"):
        return make(Switch, ("1", "2"), push=(model == "pushbutton"))
    if model == "lamp":
        rv, rp = qty(val, "v", False) or 6.0, qty(val, "w", False) or 1.0
        return make(Resistor, ("1", "2"), rv * rv / rp, kind="lamp", rated=(rv, rp))
    if model == "motor":
        rv, ri = qty(val, "v", False) or 6.0, qty(val, "a", False) or 0.2
        return make(Resistor, ("1", "2"), rv / ri, kind="motor", rated=(rv, 0.0))
    if model == "buzzer":
        rv = qty(val, "v", False) or 5.0
        return make(Resistor, ("+", "−"), rv / 0.03, kind="buzzer", rated=(rv, 0.0))
    if model == "diode":
        low = val.lower()
        if re.search(r"400[1-7]", low):
            return make(Diode, ("A", "K"), Is=14.1e-9, N=1.98)
        if "5817" in low or "5819" in low or "schottky" in low:
            return make(Diode, ("A", "K"), Is=3e-6, N=1.3)
        return make(Diode, ("A", "K"))
    if model == "zener":
        return make(Diode, ("A", "K"), bv=num("v", 5.1))
    if model == "led":
        vf, col = _led_spec(val)
        n_ = 2.0
        Is = 0.01 / math.exp(vf / (n_ * VT))
        return make(Diode, ("A", "K"), Is=Is, N=n_, led=col)
    if model in ("npn", "pnp"):
        m = re.search(r"(?:hfe|β|beta)\s*=?\s*(\d+)", val, re.I)
        bf = float(m.group(1)) if m else 150.0
        return make(BJT, ("C", "B", "E"), pol=1 if model == "npn" else -1, BF=bf)
    if model == "nmos":
        low = val.lower()
        if "irl" in low:
            return make(NMOS, ("G", "D", "S"), vth=1.5, K=20.0)
        if "irf" in low:
            return make(NMOS, ("G", "D", "S"), vth=3.0, K=10.0)
        return make(NMOS, ("G", "D", "S"))
    if model == "opamp":
        low = val.lower()
        dh, dl = 1.5, 1.5
        if "358" in low or "324" in low:
            dl = 0.02
        if "rail" in low or "mcp6" in low or "tlv" in low:
            dh = dl = 0.02
        nodes, idx = pins("IN−", "IN+", "OUT", "V+", "V−")
        hi = None if sim.is_wired(c, idx[3]) else 15.0
        lo = None if sim.is_wired(c, idx[4]) else -15.0
        if hi is not None or lo is not None:
            sim.note("Info", c["id"], "%s: supply pin%s not connected, so ±15 V supplies are assumed."
                     % (lab, "s V+ and V− are" if (hi is not None and lo is not None) else (" V+ is" if hi is not None else " V− is")))
        d = OpAmp(sim, c, nodes, hi, lo, dh, dl)
        d.pidx = idx
        return d
    if model in Gate.FUNCS:
        names = ("A", "Y") if model == "not" else ("A", "B", "Y")
        nodes, idx = pins(*names)
        loose = [nm for nm, i in zip(names[:-1], idx[:-1]) if not sim.is_wired(c, i)]
        if loose:
            sim.note("Info", c["id"], "%s: input %s not connected, so it counts as 0 (LOW)." % (lab, " and ".join(loose)))
        d = Gate(sim, c, nodes, model)
        d.pidx = idx
        return d
    if model == "logic":
        names = [p["name"] for p in rd.pins]
        prog = logic_program(rd.raw.get("logic", ""), names)
        if isinstance(prog, LogicError):
            sim.note("Warning", c["id"], "%s isn’t simulated because its logic has a problem (%s). Fix it with "
                                         "Edit component type… › Edit logic…" % (lab, prog))
            return False
        nodes = []
        for i, nm in enumerate(names):
            key = (c["id"], i)
            if key not in sim.node_of:
                sim.node_of[key] = sim.new_node("%s.%s" % (lab, nm))
            nodes.append(sim.node_of[key])
        d = LogicChip(sim, c, nodes, prog, names)
        d.pidx = list(range(len(names)))
        loose = [n for n in prog.inputs if not sim.is_wired(c, names.index(n))]
        if loose and any(sim.is_wired(c, names.index(n)) for n in prog.outputs):
            sim.note("Info", c["id"], "%s: input%s %s not connected, so %s as LOW. (On a real chip, connect "
                                      "unused inputs to GND or VCC.)"
                     % (lab, "s" if len(loose) > 1 else "", ", ".join(loose[:8]) + (" …" if len(loose) > 8 else ""),
                        "they count" if len(loose) > 1 else "it counts"))
        return d
    if model in FlipFlop.INPUTS:
        names = FlipFlop.INPUTS[model] + ("Q", QBAR)
        nodes, idx = pins(*names)
        loose = [nm for nm, i in zip(names, idx) if not sim.is_wired(c, i) and nm not in ("SET", "CLR", "Q", QBAR)]
        if "CLK" in loose:
            sim.note("Info", c["id"], "%s: CLK isn’t connected, so the flip-flop never changes "
                                      "(except through SET / CLR)." % lab)
            loose.remove("CLK")
        if loose:
            sim.note("Info", c["id"], "%s: input %s not connected, so it counts as 0 (LOW)." % (lab, " and ".join(loose)))
        d = FlipFlop(sim, c, nodes, model)
        d.pidx = idx
        return d
    if model == "timer555":
        names = ("TRIG", "THRES", "DISCH", "CTRL", "OUT", "VCC", "RESET", "GND")
        nodes, idx = pins(*names)
        reset_wired = sim.is_wired(c, idx[6])
        if not reset_wired:
            sim.note("Info", c["id"], "%s: RESET isn’t connected, so it is treated as HIGH. "
                                      "In a real circuit, connect RESET to VCC." % lab)
        m = sim.new_node("%s (internal)" % lab)
        d = Timer555(sim, c, nodes, m, reset_wired)
        d.pidx = idx
        return d
    if model == "reg7805":
        return make(Regulator, ("IN", "OUT", "GND"), qty(val, "v", False) or 5.0)
    if model == "tmp36":
        return make(TempSensor, ("+VS", "VOUT", "GND"))
    if model == "relay":
        return make(Relay, ("VCC", "GND", "IN", "NO", "COM", "NC"), qty(val, "v") or 5.0)
    if model == "probe":
        nodes, idx = pins("V")
        d = Probe(sim, c, nodes, sim.is_wired(c, idx[0]))
        d.pidx = idx
        return d
    return None


SIM_MODELS = {"resistor", "ldr", "potentiometer", "fuse", "capacitor", "capacitor_pol", "inductor",
              "battery", "dc_source", "ac_source", "square_source", "current_source", "voltmeter",
              "ammeter", "switch", "pushbutton", "lamp", "motor", "buzzer", "diode", "zener", "led",
              "npn", "pnp", "nmos", "opamp", "and", "nand", "or", "nor", "xor", "not", "timer555",
              "dff", "tff", "jkff", "srlatch",
              "reg7805", "tmp36", "relay", "probe", "vcc", "ground"}


def sim_model_of(library, c):
    d = library.get(c["def"])
    if not d:
        return None
    if d.get("subcircuit"):
        return "subcircuit"
    if d.get("logic"):
        return "logic"
    return d.get("sim") or d.get("id")


class Block(Dev):
    """A part built from a circuit.  The parts inside it are simulated on their own (the circuit is
    flattened); this only reports on them: pin voltages, current into each pin, and an LED, lamp or
    buzzer inside that is on."""

    def __init__(self, sim, comp, nodes, inner, names, n_parts):
        super().__init__(sim, comp, nodes)
        self.inner = inner
        self.names = names
        self.n_parts = n_parts
        self.digital = any(isinstance(d, (Gate, FlipFlop, LogicChip)) for d in inner)
        # current is only reported for pins that aren't on Ground (ground is shared by everything)
        self.pidx = [k for k, n in enumerate(nodes) if n]

    def currents(self, x):
        out = []
        for k in self.pidx:
            node, s = self.n[k], 0.0
            for d in self.inner:
                try:
                    cur = d.currents(x)
                except Exception:
                    continue
                for j, nd in enumerate(d.n[:len(cur)]):
                    if nd == node:
                        s += cur[j]
            out.append(s)
        return out

    def info(self, x):
        out = [("Inside", "%d part%s" % (self.n_parts, "" if self.n_parts == 1 else "s"))]
        for k, nm in enumerate(self.names[:10]):
            out.append(("Pin " + nm, fmt_si(self.V(x, k), "V")))
        return out

    def view(self, x):
        out, glow = {}, None
        for d in self.inner:
            try:
                v = d.view(x)
            except Exception:
                v = None
            if not v:
                continue
            g = v.get("glow")
            if g and (glow is None or g[1] > glow[1]):
                glow = g
            if v.get("sound"):
                out["sound"] = True
            sp = v.get("spin")
            if sp is not None and abs(sp) > abs(out.get("spin", 0.0)):
                out["spin"] = sp
            if v.get("cross"):
                out["cross"] = v["cross"]
        if glow:
            out["glow"] = glow
        if self.digital:
            out["pinstate"] = [(k, self.V(x, k) > 2.5) for k in range(len(self.n)) if self.n[k]]
        return out


class Sim:
    """A running simulation of the app's current circuit."""

    def __init__(self, app, carry=None, t=0.0):
        self.app = app
        self.t = t
        self.version = 0
        self.error = None
        self.notes = []
        self.devs = []
        self.by_cid = {}
        self.node_of = {}
        self.node_names = ["GND"]
        self.nn = 0
        self.N = 0
        self.x = []
        self.nl = []
        self.reactive = []
        self.static = True
        self.dirty = True
        self.force_be = True
        self.pending = 0.0
        self.slow = False
        self.gextra = 0.0
        self.on_sample = None
        self.pressed = set((carry or {}).get("_pressed", ()))
        self._lin_key = None
        self._lin_A = None
        self._lin_LU = None
        self.T_disp = None
        self.h = 1e-3
        self.auto_speed = 1.0
        self.auto_window = 10.0
        self.ref_note = None
        try:
            self._build(carry or {})
            self.S = Stamp(0)
            self._timing()
        except SimError as e:
            self.error = str(e)
        except Exception as e:  # never let a simulator bug take the editor down
            log_exception(*sys.exc_info(), context="building the simulation")
            self.error = "The simulator hit an internal problem (%s)." % e
        if self.error and (self.N == 0 or len(self.x) != self.N):
            self.devs, self.by_cid, self.nl, self.reactive = [], {}, [], []
            self.N, self.x = 0, []
        if not hasattr(self, "S"):
            self.S = Stamp(0)

    # ---------------------------------------------------------------- building
    def note(self, sev, cid, msg):
        self.notes.append((sev, cid, msg))

    def new_node(self, name):
        self.nn += 1
        self.node_names.append(name)
        return self.nn

    def is_wired(self, c, idx):
        return (c["id"], idx) in self.wired

    def pins(self, c, rd, names):
        nodes, idx = [], []
        for nm in names:
            i = next((k for k, p in enumerate(rd.pins) if p["name"] == nm), None)
            if i is None:
                raise _MissingPin(nm)
            key = (c["id"], i)
            if key not in self.node_of:
                self.node_of[key] = self.new_node("%s.%s" % (c.get("label") or rd.name, nm))
            nodes.append(self.node_of[key])
            idx.append(i)
        return nodes, idx

    def _build(self, carry):
        app = self.app
        # parts built from a circuit are replaced by the circuit inside them
        comps, wires, blocks, problems = flatten_circuit(app.library, app.comps, app.wires)
        nets = compute_nets_of(comps, wires) if (blocks or problems) else app.compute_nets()
        for cid, msg in problems:
            self.note("Warning", cid, msg)
        net_of = {}
        gnd = None
        for i, net in enumerate(nets):
            if net["name"] == "GND":
                gnd = i
            for k in net["pins"]:
                net_of[k] = i
        self.wired = set(net_of)
        if gnd is None and nets:
            ref = None
            for cid, c in comps.items():
                pn = {"battery": "−", "dc_source": "−", "ac_source": "2", "square_source": "−",
                      "current_source": "−"}.get(sim_model_of(app.library, c))
                if pn:
                    rd = app.rdef(c)
                    i = next((k for k, p in enumerate(rd.pins) if p["name"] == pn), None)
                    if i is not None and (cid, i) in net_of:
                        ref = net_of[(cid, i)]
                        break
            has_rail = any(sim_model_of(app.library, c) == "vcc" and (cid, 0) in net_of
                           for cid, c in comps.items())
            if ref is None and has_rail:
                # only power rails: they are measured from an implied 0 V, like the logic parts' own ground
                gnd = -1
                self.note("Info", None, "There is no Ground symbol, so the power rails are measured from an "
                                        "imaginary 0 V. Add a Ground wherever your circuit returns to 0 V.")
            else:
                gnd = ref if ref is not None else 0
                self.ref_note = nets[gnd]["name"]
                self.note("Info", None, "There is no Ground symbol, so voltages are measured from net %s. "
                                        "Add a Ground (0 V) to choose the reference point yourself." % nets[gnd]["name"])
        net_node = {}
        for i, net in enumerate(nets):
            if i == gnd:
                net_node[i] = 0
                self.node_names[0] = net["name"]
            else:
                net_node[i] = self.new_node(net["name"])
        for k, i in net_of.items():
            self.node_of[k] = net_node[i]

        unsupported = []
        rails = {}
        for cid, c in comps.items():
            rd = app.rdef(c)
            model = sim_model_of(app.library, c)
            lab = c.get("label") or rd.name
            if model in ("ground", PORT_DEF, "subcircuit"):
                continue
            if model == "vcc":
                key = (cid, 0)
                if key not in net_of:
                    continue
                node = self.node_of[key]
                v = qty(c.get("value", ""), "v")
                if v is None:
                    v = 5.0
                    self.note("Warning", cid, "%s: couldn’t read the rail voltage “%s”, so +5 V is used."
                              % (lab, c.get("value", "")))
                if node == 0:
                    raise SimError("Short circuit: power rail %s is wired to Ground." % (c.get("value") or lab))
                if node in rails:
                    if abs(rails[node] - v) > 1e-9:
                        raise SimError("Two different power rails (%s and %s) are wired together."
                                       % (fmt_si(rails[node], "V"), fmt_si(v, "V")))
                    continue
                rails[node] = v
                d = VSource(self, c, [node, 0], v, kind="rail")
                d.pidx = [0, -1]
                self.devs.append(d)
                self.by_cid[cid] = d
                continue
            try:
                d = _make_device(self, c, rd, model)
            except _MissingPin as e:
                self.note("Warning", cid, "%s can’t be simulated: it has no pin named “%s”." % (lab, e.args[0]))
                continue
            if d is False:      # not simulated, already explained in a note
                continue
            if d is None:
                if any((cid, i) in self.wired for i in range(len(rd.pins))):
                    unsupported.append(lab)
                continue
            st = carry.get(cid)
            if st:
                d.restore(st)
            self.devs.append(d)
            self.by_cid[cid] = d
        if unsupported:
            self.note("Info", None, "Not simulated (their pins are left unconnected): %s. Microcontroller boards, "
                                    "digital modules and parts you drew yourself have no simulation model. To make "
                                    "your own part work, build its circuit, select it and click Make component."
                      % ", ".join(unsupported))
        # one read-out device per part built from a circuit, for its readings and glow
        for bid in blocks:
            c = comps[bid]
            rd = app.rdef(c)
            nodes = []
            for k in range(len(rd.pins)):
                key = (bid, k)
                if key not in self.node_of:
                    self.node_of[key] = self.new_node("%s.%s" % (c.get("label") or rd.name, rd.pins[k]["name"]))
                nodes.append(self.node_of[key])
            inner = [d for cid, d in self.by_cid.items() if cid.startswith(bid + "/")]
            n_parts = sum(1 for ic in blocks[bid]["subcircuit"].get("comps", []) if ic.get("def") != PORT_DEF)
            d = Block(self, c, nodes, inner, [p["name"] for p in rd.pins], n_parts)
            self.devs.append(d)
            self.by_cid[bid] = d
        k = self.nn
        for d in self.devs:
            if d.nbr:
                d.br = k
                k += d.nbr
        self.N = k
        self.x = [0.0] * k
        self.nl = [d for d in self.devs if d.nonlinear]
        self.reactive = [d for d in self.devs if d.reactive]
        self.static = not any(d.reactive or d.timevar for d in self.devs)
        if not self.devs:
            raise SimError("There is nothing to simulate yet. Add a power source and some parts, and wire them up.")

    # ---------------------------------------------------------------- solving
    def _factor(self, A):
        try:
            return lu_factor(A)
        except _Singular as e:
            raise SimError(self._singular_msg(e.col))

    def _singular_msg(self, col):
        if col >= self.nn:
            for d in self.devs:
                if d.br == col:
                    if isinstance(d, VSource) and d.kind == "ammeter":
                        return ("%s (ammeter) is short-circuiting a voltage source. An ammeter has almost no "
                                "resistance, so it goes in series with a part, never straight across a supply."
                                % d.label)
                    if isinstance(d, Inductor):
                        return ("%s (inductor) is connected straight across a voltage source. An inductor is "
                                "a plain wire for DC, so this is a short circuit." % d.label)
                    return ("Short circuit: %s is connected straight across another voltage source or a plain "
                            "wire, so the current would be infinite. Check its wiring." % d.label)
        return "The circuit can’t be solved. A voltage source may be short-circuited."

    def _base(self, S):
        key = (S.dc, 0.0 if S.dc else S.h, S.method, self.version, self.gextra, id(S.open) if S.open else 0)
        if key != self._lin_key:
            N = self.N
            S.A = [[0.0] * N for _ in range(N)]
            for d in self.devs:
                d.stamp_lin(S)
            g = GMIN + self.gextra
            for i in range(self.nn):
                S.A[i][i] += g
            self._lin_A = S.A
            self._lin_key = key
            self._lin_LU = None
        return self._lin_A

    def _check(self, x):
        for i in range(self.N):
            if not abs(x[i]) < 1e12:   # also catches NaN
                raise SimError(self._singular_msg(i if i >= self.nn else -1))
        return x

    def _solve(self, S, guess, maxit=100):
        A0 = self._base(S)
        N = self.N
        S.b = [0.0] * N
        for d in self.devs:
            d.rhs(S)
        b0 = S.b
        if not self.nl:
            if self._lin_LU is None:
                self._lin_LU = self._factor(A0)
            return self._check(lu_solve(self._lin_LU, b0))
        x = list(guess)
        for d in self.nl:
            d.begin(x)
        nn = self.nn
        for _it in range(maxit):
            S.A = [r[:] for r in A0]
            S.b = b0[:]
            S.limited = False
            for d in self.nl:
                d.stamp_nl(S, x)
            xn = lu_solve(self._factor(S.A), S.b)
            conv = not S.limited
            if conv:
                for i in range(N):
                    a, b = xn[i], x[i]
                    tol = (1e-6 if i < nn else 1e-9) + 1e-4 * max(abs(a), abs(b))
                    if abs(a - b) > tol:
                        conv = False
                        break
            x = xn
            if conv:
                return self._check(x)
            if not all(abs(v) < 1e12 for v in x):
                raise NoConvergence()
        raise NoConvergence()

    def _dc(self, S, guess):
        """DC operating point, with gmin stepping and source stepping as fall-backs."""
        S.dc, S.open, S.scale = True, None, 1.0
        try:
            return self._solve(S, guess)
        except NoConvergence:
            pass
        x = list(guess)
        try:
            for g in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10):
                self.gextra = g
                x = self._solve(S, x, 200)
            self.gextra = 0.0
            return self._solve(S, x, 200)
        except NoConvergence:
            pass
        finally:
            self.gextra = 0.0
        x = [0.0] * self.N
        try:
            for k in range(1, 21):
                S.scale = k / 20.0
                x = self._solve(S, x, 200)
            return x
        except NoConvergence:
            raise SimError("The simulator couldn’t find a steady state for this circuit. This can happen when "
                           "a logic gate’s output is wired straight back to its own input, or when parts are "
                           "wired in an unusual loop.")
        finally:
            S.scale = 1.0

    def solve_static(self):
        """Circuits without capacitors, inductors or changing sources: just the DC answer."""
        S = self.S
        S.t, S.method = self.t, "be"
        x = self.x
        for _ in range(40):
            x = self._dc(S, x)
            for d in self.devs:
                d.accept(S, x)
            changed = [d for d in self.devs if d.discrete(x)]
            if not changed:
                break
            self.version += 1
        self.x = x
        self.dirty = False

    def step(self, h, depth=0):
        S = self.S
        S.dc, S.open, S.scale = False, None, 1.0
        S.h = h
        S.method = "be" if self.force_be else "bdf2"
        S.t = self.t + h
        try:
            x = self._solve(S, self.x)
        except NoConvergence:
            if depth >= 2:
                raise SimError("The simulation stopped at t = %s because the circuit has no steady state the "
                               "simulator can find. This can happen when a logic gate’s output is wired straight "
                               "back to its own input, or when parts are wired in an unusual loop." % fmt_si(self.t, "s"))
            self.force_be = True
            for _ in range(10):
                self.step(h / 10.0, depth + 1)
            self.force_be = True
            return
        self.x = x
        self.t = S.t
        for d in self.devs:
            d.accept(S, x)
        changed = [d for d in self.devs if d.discrete(x)]
        if changed:
            self.version += 1
        self.force_be = bool(changed) or depth > 0
        if self.on_sample is not None and depth == 0:
            self.on_sample(self.t)

    def advance(self, dt, budget=0.025):
        """Move simulated time forward by dt, spending at most `budget` seconds of real time."""
        if self.error:
            return
        try:
            if self.static:
                if self.dirty:
                    self.solve_static()
                self.t += dt
                if self.on_sample is not None:
                    self.on_sample(self.t)
                return
            self.pending += dt
            h = self.h
            end = time.perf_counter() + budget
            self.slow = False
            while self.pending >= 0.5 * h:
                self.step(h)
                self.pending -= h
                if time.perf_counter() > end:
                    if self.pending > h:
                        self.slow = True
                        self.pending = 0.0
                    break
        except SimError as e:
            self.error = str(e)
        except Exception as e:
            log_exception(*sys.exc_info(), context="running the simulation")
            self.error = "The simulator hit an internal problem (%s)." % e

    def bump(self):
        """Something the user controls changed (switch, slider): re-solve."""
        self.version += 1
        self.force_be = True
        self.dirty = True

    # ---------------------------------------------------------------- time scales
    def _jacobian(self, x, open_dev=None):
        S = self.S
        S.dc, S.open = True, open_dev
        A0 = self._base(S)
        S.A = [r[:] for r in A0]
        S.b = [0.0] * self.N
        for d in self.nl:
            d.begin(x)
            d.stamp_nl(S, x)
        S.open = None
        return S.A

    def _thevenin(self, LU, a, b):
        e = [0.0] * self.N
        if a:
            e[a - 1] += 1.0
        if b:
            e[b - 1] -= 1.0
        z = lu_solve(LU, e)
        return (z[a - 1] if a else 0.0) - (z[b - 1] if b else 0.0)

    def _timing(self):
        """Pick the time step, default speed and scope window from the circuit's time constants."""
        P, T = [], []
        for d in self.devs:
            P += d.periods()
        caps = [d for d in self.devs if isinstance(d, Capacitor)]
        inds = [d for d in self.devs if isinstance(d, Inductor)]
        if caps or inds:
            try:
                x = self._dc(self.S, [0.0] * self.N)
                if caps:
                    LU = lu_factor(self._jacobian(x))
                    for c in caps:
                        T.append(self._thevenin(LU, c.n[0], c.n[1]) * c.C)
                for L_ in inds:
                    LU = lu_factor(self._jacobian(x, L_))
                    R = self._thevenin(LU, L_.n[0], L_.n[1])
                    if R > 0:
                        T.append(L_.L / R)
            except Exception:
                pass
            for L_ in inds[:8]:
                for c in caps[:8]:
                    P.append(2 * math.pi * math.sqrt(L_.L * c.C))
        P = [p for p in P if 1e-9 < p < 1e4]
        T = [t for t in T if 1e-9 < t < 1e3]
        Td = min(P) if P else (max(T) if T else None)
        self.T_disp = Td
        self.h = Td / 100.0 if Td else 1e-3
        if P:
            self.h = min(self.h, min(P) / 100.0)
        self.auto_speed = min(1.0, Td / 0.5) if Td else 1.0
        self.auto_window = 5.0 * Td if Td else 10.0
        self._lin_key = None

    # ---------------------------------------------------------------- AC analysis
    def ac_sweep(self, src, out_node, freqs):
        """Small-signal response V(out) / V(source) at each frequency (complex)."""
        S = self.S
        S.t, S.method = 0.0, "be"
        x = self._dc(S, [0.0] * self.N)
        J = self._jacobian(x)
        res = []
        N = self.N
        for f in freqs:
            w = 2 * math.pi * f
            A = [[complex(v) for v in row] for row in J]
            for d in self.reactive:
                d.ac(A, w)
            b = [0j] * N
            b[src.br] = 1.0
            try:
                y = lu_solve(lu_factor(A, 1e-30), b)
                res.append(y[out_node - 1] if out_node else 0j)
            except _Singular:
                res.append(complex("nan"))
        self._lin_key = None
        return res

    # ---------------------------------------------------------------- read-outs
    def nv(self, node):
        return self.x[node - 1] if node else 0.0

    def pin_v(self, key):
        n = self.node_of.get(tuple(key))
        if n is None or (n and n > len(self.x)):
            return None
        return self.nv(n)

    def warnings(self):
        out = []
        if self.error:
            out.append(("Error", None, self.error))
        out += self.notes
        x = self.x
        if not self.error:
            for d in self.devs:
                try:
                    for sev, msg in d.warn(x):
                        out.append((sev, d.cid, msg))
                except Exception:
                    pass
            for i in range(self.nn):
                if abs(x[i]) > 1e5:
                    out.append(("Warning", None, "Net %s has an unrealistic voltage (%s). A part may have nowhere "
                                                 "for its current to go." % (self.node_names[i + 1], fmt_si(x[i], "V"))))
                    break
        return out

    def export(self):
        st = {}
        for d in self.devs:
            s = d.export()
            if s is not None:
                st[d.cid] = s
        st["_pressed"] = list(self.pressed)
        return st


# --------------------------------------------------------------------------
# Example circuits
# --------------------------------------------------------------------------
def build_example(name):
    comps, wires = [], []

    def add(did, x, y, label, value=None, rot=0, flip=False):
        d = next(b for b in BUILTIN_DEFS if b["id"] == did)
        cid = "c%d" % (len(comps) + 1)
        comps.append({"id": cid, "def": did, "x": x, "y": y, "rot": rot, "flip": flip, "label": label,
                      "value": d["value"] if value is None else value, "notes": ""})
        return cid

    def pin_index(cid, pname):
        c = next(c for c in comps if c["id"] == cid)
        rd = RDef(next(b for b in BUILTIN_DEFS if b["id"] == c["def"]))
        return next(i for i, p in enumerate(rd.pins) if p["name"] == pname)

    def wire(a, ap, b, bp, color, bends=()):
        wires.append({"id": "w%d" % (len(wires) + 1), "a": [a, pin_index(a, ap)], "b": [b, pin_index(b, bp)],
                      "bends": [list(p) for p in bends], "color": color})

    red, black, blue, green = "#dc2626", "#1f2933", "#2563eb", "#16a34a"
    orange, purple = "#ea580c", "#7c3aed"
    if name == "led":
        v = add("dc_source", 4, 6, "V1", "9 V")
        r = add("resistor", 9, 2, "R1", "470 Ω")
        d = add("led", 17, 5, "D1", "Red", rot=1)
        g1 = add("ground", 4, 10, "GND1")
        g2 = add("ground", 17, 9, "GND2")
        wire(v, "+", r, "1", red)
        wire(r, "2", d, "A", blue)
        wire(d, "K", g2, "GND", black)
        wire(v, "−", g1, "GND", black)
    elif name == "divider":
        v = add("dc_source", 4, 6, "V1", "10 V")
        r1 = add("resistor", 10, 4, "R1", "10 kΩ", rot=1)
        r2 = add("resistor", 10, 9, "R2", "10 kΩ", rot=1)
        vm = add("voltmeter", 15, 9, "VM1", "", rot=1)
        g1 = add("ground", 4, 10, "GND1")
        g2 = add("ground", 10, 13, "GND2")
        g3 = add("ground", 15, 13, "GND3")
        wire(v, "+", r1, "1", red)
        wire(r1, "2", r2, "1", blue)
        wire(r2, "1", vm, "+", green)
        wire(r2, "2", g2, "GND", black)
        wire(vm, "−", g3, "GND", black)
        wire(v, "−", g1, "GND", black)
    elif name == "rc":
        v = add("ac_source", 4, 6, "V1", "5 V 1 kHz")
        r = add("resistor", 9, 4, "R1", "1 kΩ")
        cap = add("capacitor", 14, 6, "C1", "100 nF", rot=1)
        g1 = add("ground", 4, 10, "GND1")
        g2 = add("ground", 14, 10, "GND2")
        pin_ = add("probe", 7, 1, "Vin")
        pout = add("probe", 14, 1, "Vout")
        wire(v, "1", r, "1", red)
        wire(r, "1", pin_, "V", orange)
        wire(r, "2", cap, "1", blue)
        wire(cap, "1", pout, "V", purple)
        wire(cap, "2", g2, "GND", black)
        wire(v, "2", g1, "GND", black)
    elif name == "transistor":
        p1 = add("vcc", 4, 2, "PWR1", "+5 V")
        sw = add("pushbutton", 4, 6, "SW1", rot=1)
        rb = add("resistor", 8, 8, "R1", "10 kΩ")
        q = add("npn", 13, 8, "Q1")
        p2 = add("vcc", 14, -7, "PWR2", "+5 V")
        rc = add("resistor", 14, -2, "R2", "330 Ω", rot=1)
        d = add("led", 14, 3, "D1", "Green", rot=1)
        g = add("ground", 14, 12, "GND1")
        wire(p1, "V", sw, "1", red)
        wire(sw, "2", rb, "1", blue)
        wire(rb, "2", q, "B", blue)
        wire(p2, "V", rc, "1", red)
        wire(rc, "2", d, "A", orange)
        wire(d, "K", q, "C", green)
        wire(q, "E", g, "GND", black)
    elif name == "blinker":
        u = add("timer555", 14, 9, "U1")
        p1 = add("vcc", 13, 2, "PWR1", "+9 V")
        p2 = add("vcc", 15, 2, "PWR2", "+9 V")
        p3 = add("vcc", 7, 3, "PWR3", "+9 V")
        ra = add("resistor", 7, 8, "R1", "10 kΩ", rot=1)
        rb = add("resistor", 7, 13, "R2", "68 kΩ", rot=1)
        ct = add("capacitor_pol", 7, 18, "C1", "10 µF", rot=1)
        g1 = add("ground", 7, 22, "GND1")
        g2 = add("ground", 14, 15, "GND2")
        r3 = add("resistor", 21, 8, "R3", "470 Ω")
        d = add("led", 25, 10, "D1", "Red", rot=1)
        g3 = add("ground", 25, 14, "GND3")
        wire(p1, "V", u, "VCC", red)
        wire(p2, "V", u, "RESET", red)
        wire(p3, "V", ra, "1", red)
        wire(ra, "2", u, "DISCH", blue)
        wire(ra, "2", rb, "1", blue)
        wire(rb, "2", ct, "+", green)
        wire(ct, "+", u, "THRES", green, bends=[(9, 16)])
        wire(u, "TRIG", u, "THRES", green, bends=[(9, 7)])
        wire(ct, "−", g1, "GND", black)
        wire(u, "GND", g2, "GND", black)
        wire(u, "OUT", r3, "1", orange)
        wire(r3, "2", d, "A", orange)
        wire(d, "K", g3, "GND", black)
    elif name == "counter":
        clk = add("square_source", 2, 8, "V1", "5 V 1 Hz")
        g1 = add("ground", 2, 12, "GND1")
        p1 = add("vcc", 7, 0, "PWR1", "+5 V")
        f1 = add("tff", 10, 4, "FF1")
        p2 = add("vcc", 7, 13, "PWR2", "+5 V")
        f2 = add("tff", 10, 17, "FF2")
        r1 = add("resistor", 18, 3, "R1", "330 Ω")
        d1 = add("led", 22, 6, "D1", "Green", rot=1)
        g2 = add("ground", 22, 10, "GND2")
        r2 = add("resistor", 18, 16, "R2", "330 Ω")
        d2 = add("led", 22, 19, "D2", "Red", rot=1)
        g3 = add("ground", 22, 23, "GND3")
        wire(clk, "+", f1, "CLK", orange)
        wire(clk, "−", g1, "GND", black)
        wire(p1, "V", f1, "T", red)
        wire(p2, "V", f2, "T", red)
        wire(f1, QBAR, f2, "CLK", purple, bends=[(15, 10), (5, 10)])
        wire(f1, "Q", r1, "1", blue)
        wire(r1, "2", d1, "A", blue)
        wire(d1, "K", g2, "GND", black)
        wire(f2, "Q", r2, "1", blue)
        wire(r2, "2", d2, "A", blue)
        wire(d2, "K", g3, "GND", black)
    elif name == "halfadder":
        # ready to become a component: select everything and press Ctrl+G
        pa = add(PORT_DEF, 2, 3, "A", flip=True)
        pb = add(PORT_DEF, 2, 9, "B", flip=True)
        x = add("xor", 10, 3, "U1")
        a = add("and", 10, 9, "U2")
        ps = add(PORT_DEF, 19, 3, "SUM")
        pc = add(PORT_DEF, 19, 9, "CARRY")
        wire(pa, "PIN", x, "A", blue)
        wire(pa, "PIN", a, "A", blue)
        wire(pb, "PIN", x, "B", green)
        wire(pb, "PIN", a, "B", green)
        wire(x, "Y", ps, "PIN", orange)
        wire(a, "Y", pc, "PIN", purple)
    else:  # blink
        u = add("arduino_uno", 6, 10, "U1", "")
        r = add("resistor", 15, 17, "R1", "220 Ω")
        d = add("led", 20, 20, "D1", "Green", rot=1)
        g1 = add("ground", 20, 24, "GND1")
        g2 = add("ground", -1, 10, "GND2")
        wire(u, "D13", r, "1", blue)
        wire(r, "2", d, "A", green)
        wire(d, "K", g1, "GND", black)
        wire(u, "GND", g2, "GND", black)
    return {"format": "circuit-builder", "version": 1, "components": comps, "wires": wires, "definitions": []}


# --------------------------------------------------------------------------
# SVG export
# --------------------------------------------------------------------------
def _esc(s):
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;"))


def canvas_to_svg(cv, skip_tags=("grid", "hint", "overlay", "sim")):
    items = [i for i in cv.find_all() if not set(cv.gettags(i)) & set(skip_tags)]
    if not items:
        return None
    xs0, ys0, xs1, ys1 = [], [], [], []
    for i in items:
        b = cv.bbox(i)
        if b:
            xs0.append(b[0]); ys0.append(b[1]); xs1.append(b[2]); ys1.append(b[3])
    m = 16
    X0, Y0, X1, Y1 = min(xs0) - m, min(ys0) - m, max(xs1) + m, max(ys1) + m
    out = ['<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" '
           'width="%d" height="%d" viewBox="%.1f %.1f %.1f %.1f">'
           % (X1 - X0, Y1 - Y0, X0, Y0, X1 - X0, Y1 - Y0),
           '<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="white"/>' % (X0, Y0, X1 - X0, Y1 - Y0)]
    dpi = cv.winfo_fpixels("1i")
    for i in items:
        t = cv.type(i)
        co = cv.coords(i)
        def col(opt):
            v = cv.itemcget(i, opt)
            return v if v else "none"
        try:
            width = float(cv.itemcget(i, "width") or 1)
        except (tk.TclError, ValueError):
            width = 1.0
        if t == "line":
            pts = " ".join("%.1f,%.1f" % (co[k], co[k + 1]) for k in range(0, len(co), 2))
            dash = cv.itemcget(i, "dash")
            da = ' stroke-dasharray="%s"' % dash.replace(" ", ",") if dash else ""
            out.append('<polyline points="%s" fill="none" stroke="%s" stroke-width="%.2f" stroke-linecap="round" stroke-linejoin="round"%s/>'
                       % (pts, col("fill"), width, da))
        elif t == "polygon":
            pts = " ".join("%.1f,%.1f" % (co[k], co[k + 1]) for k in range(0, len(co), 2))
            out.append('<polygon points="%s" fill="%s" stroke="%s" stroke-width="%.2f" stroke-linejoin="round"/>'
                       % (pts, col("fill"), col("outline"), width))
        elif t == "oval":
            cx, cy, rx, ry = (co[0] + co[2]) / 2, (co[1] + co[3]) / 2, (co[2] - co[0]) / 2, (co[3] - co[1]) / 2
            out.append('<ellipse cx="%.1f" cy="%.1f" rx="%.1f" ry="%.1f" fill="%s" stroke="%s" stroke-width="%.2f"/>'
                       % (cx, cy, rx, ry, col("fill"), col("outline"), width))
        elif t == "rectangle":
            dash = cv.itemcget(i, "dash")
            da = ' stroke-dasharray="%s"' % dash.replace(" ", ",") if dash else ""
            out.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s" stroke="%s" stroke-width="%.2f"%s/>'
                       % (co[0], co[1], co[2] - co[0], co[3] - co[1], col("fill"), col("outline"), width, da))
        elif t == "image":
            name = cv.itemcget(i, "image")
            data = PICTURES.sources.get(name)
            if not data:
                continue
            try:
                iw = int(cv.tk.call("image", "width", name))
                ih = int(cv.tk.call("image", "height", name))
            except (tk.TclError, ValueError):
                continue
            anchor = cv.itemcget(i, "anchor")
            if anchor in ("", "center"):
                anchor = ""
            fx = 0.0 if "w" in anchor else 1.0 if "e" in anchor else 0.5
            fy = 0.0 if "n" in anchor else 1.0 if "s" in anchor else 0.5
            # embed the full-size picture so it stays sharp when the SVG is enlarged
            out.append('<image x="%.1f" y="%.1f" width="%d" height="%d" preserveAspectRatio="none" '
                       'xlink:href="data:image/png;base64,%s"/>' % (co[0] - fx * iw, co[1] - fy * ih, iw, ih, data))
        elif t == "text":
            text = cv.itemcget(i, "text")
            if not text:
                continue
            fnt = cv.itemcget(i, "font")
            try:
                fam = cv.tk.call("font", "actual", fnt, "-family")
                size = int(cv.tk.call("font", "actual", fnt, "-size"))
                weight = cv.tk.call("font", "actual", fnt, "-weight")
            except (tk.TclError, ValueError):
                fam, size, weight = "sans-serif", -11, "normal"
            px = -size if size < 0 else size * dpi / 72.0
            anchor = cv.itemcget(i, "anchor")
            try:
                angle = float(cv.itemcget(i, "angle") or 0)
            except (tk.TclError, ValueError):
                angle = 0.0
            ta = "start" if anchor in ("w", "nw", "sw") else "end" if anchor in ("e", "ne", "se") else "middle"
            lines = text.split("\n")
            lh = px * 1.22
            total = lh * len(lines)
            x, y = co[0], co[1]
            if "n" in anchor:
                top = y
            elif "s" in anchor:
                top = y - total
            else:
                top = y - total / 2
            tr = ' transform="rotate(%.1f %.1f %.1f)"' % (-angle, x, y) if angle else ""
            spans = "".join('<tspan x="%.1f" y="%.1f">%s</tspan>' % (x, top + k * lh + px * 0.92, _esc(ln))
                            for k, ln in enumerate(lines))
            out.append('<text font-family="%s, Segoe UI, Arial, sans-serif" font-size="%.1f" font-weight="%s" fill="%s" text-anchor="%s"%s>%s</text>'
                       % (_esc(fam), px, "bold" if weight == "bold" else "normal", col("fill"), ta, tr, spans))
    out.append("</svg>")
    return "\n".join(out)


def _app_export_svg(self):
    if not self.comps:
        messagebox.showinfo(APP_NAME, "There is nothing to export yet.")
        return
    path = filedialog.asksaveasfilename(title="Export image", defaultextension=".svg",
                                        initialfile=(os.path.splitext(os.path.basename(self.path))[0] if self.path else "circuit") + ".svg",
                                        filetypes=[("SVG image", "*.svg")])
    if not path:
        return
    saved = (self.zoom, self.panx, self.pany, self.sel, self.highlight, self.hover_pin, self.mode)
    self.zoom, self.sel, self.highlight, self.hover_pin, self.mode = 1.0, set(), None, None, "idle"
    self.ghost = None
    was_dark = THEME["dark"]
    set_palette(False)   # lab-report images are always drawn in the light (printable) colors
    try:
        self._redraw()
        svg = canvas_to_svg(self.cv)
    finally:
        set_palette(was_dark)
        self.zoom, self.panx, self.pany, self.sel, self.highlight, self.hover_pin, self.mode = saved
        self._redraw()
    if not svg:
        return
    try:
        with open(path, "w", encoding="utf-8") as f:
            f.write(svg)
    except OSError as e:
        messagebox.showerror(APP_NAME, "Could not export:\n%s" % e)
        return
    self.flash("Image saved to %s (open it in a browser, Word or PowerPoint)." % os.path.basename(path), 6000)


App.export_svg = _app_export_svg


def _app_show_help(self):
    win = tk.Toplevel(self.root)
    win.title("Quick start — " + APP_NAME)
    win.configure(bg=C["panel"])
    win.transient(self.root)
    f = ttk.Frame(win, style="Panel.TFrame", padding=18)
    f.pack(fill="both", expand=True)
    ttk.Label(f, text="Quick start", style="Title.TLabel").pack(anchor="w")
    text = (
        "1.  Find a part in the Components list on the left (use the search box).\n"
        "2.  Drag it onto the grid, or double-click it and then click where it should go.\n"
        "3.  Every part has pins (small circles). Click one pin, then click a pin on another part —\n"
        "     a wire connects them. Click empty space on the way to add corners.\n"
        "4.  Click a part to edit its label (R1, U2 …) and value (1 kΩ, 9 V …) on the right.\n"
        "5.  Tools › Show connections lists every net (pins that share the same voltage).\n"
        "6.  Tools › Check circuit warns about shorts and parts that aren’t connected.\n"
        "7.  Make your own parts from a circuit: build it, add a Component Pin (Building Blocks) for each\n"
        "     connection and label it (A, B, OUT …), select it all and press Ctrl+G (or  + New Component ›\n"
        "     From the selected circuit). The new part works in the simulator just like the circuit inside\n"
        "     it, and is saved in your library. Right-click a copy › Show the circuit inside to change it.\n"
        "     ( + New Component › Draw a part with pins only  is for boards and modules that aren’t simulated.)\n"
        "8.  Give a part a picture (a photo of the real module, say): click the part, then\n"
        "     Add picture… on the right, or use Picture › Choose… in the Component Editor.\n"
        "9.  Press  ▶ Simulate  (F5) to run the circuit. Voltages appear on the wires, LEDs and lamps\n"
        "     light up and meters show readings. Click switches, hold push buttons, hover over a part\n"
        "     for its voltage and current, and right-click a wire or part to plot it on the oscilloscope.\n"
        "     Simulate › Frequency response draws a Bode plot of a filter or amplifier.\n\n"
        "Good to know\n"
        "•  All Ground symbols are connected together, and so are Power Rails with the same value.\n"
        "•  A filled pin is connected; a hollow pin is still free.\n"
        "•  Parts marked as a microcontroller (like the Arduino Uno) can have unused pins: Check circuit\n"
        "    only makes sure their power and ground are wired. Tick the box in a part’s properties, or in\n"
        "    the Component Editor for your own boards.\n"
        "•  Files are saved as .circuit and include any custom parts they use (with their pictures),\n"
        "    so you can share them.\n"
        "•  File › Export image saves an SVG you can put in a lab report.\n"
        "•  Prefer a dark screen? Click  ☾  next to  ▶ Simulate  (or View › Dark mode).")
    ttk.Label(f, text=text, style="Panel.TLabel", justify="left").pack(anchor="w", pady=(8, 12))
    ttk.Label(f, text="Keyboard & mouse", style="Card.TLabel").pack(anchor="w")
    kf = ttk.Frame(f, style="Panel.TFrame")
    kf.pack(anchor="w", pady=(4, 10))
    for i, (k, d) in enumerate(SHORTCUTS):
        ttk.Label(kf, text=k, style="Card.TLabel").grid(row=i, column=0, sticky="w", padx=(0, 16))
        ttk.Label(kf, text=d, style="Muted.TLabel").grid(row=i, column=1, sticky="w")
    ttk.Button(f, text="Close", command=win.destroy).pack(anchor="e")


def _app_show_about(self):
    messagebox.showinfo("About " + APP_NAME,
                        "%s %s\n\nA simple circuit and wiring editor for students, with a built-in "
                        "circuit simulator.\n\n"
                        "Your custom components are stored in:\n%s\n\n"
                        "If something goes wrong, the details are saved in:\n%s"
                        % (APP_NAME, APP_VERSION, self.library.path, error_log_path()))


App.show_help = _app_show_help
App.show_about = _app_show_about


# --------------------------------------------------------------------------
# Simulation user interface
# --------------------------------------------------------------------------
SPEEDS = [("Auto", None), ("10× faster", 10.0), ("Real time", 1.0), ("10× slower", 0.1),
          ("100× slower", 1e-2), ("1 000× slower", 1e-3), ("10 000× slower", 1e-4),
          ("100 000× slower", 1e-5), ("1 000 000× slower", 1e-6)]


def speed_name(ts):
    if abs(ts - 1.0) < 1e-9:
        return "real time"
    if ts > 1.0:
        return "%.3g× faster" % ts
    k = 1.0 / ts
    return ("{:,.0f}".format(k) if k >= 10 else "%.2g" % k).replace(",", " ") + "× slower"


TRACE_COLORS = ["#2563eb", "#dc2626", "#16a34a", "#d97706", "#7c3aed", "#0891b2", "#db2777", "#4b5563"]
CONTROL_MODELS = ("switch", "pushbutton", "potentiometer", "ldr", "tmp36")

SIM_HELP = (
    "Circuit Builder solves your circuit the way SPICE does (nodal analysis), many times a second, "
    "so you see voltages and currents change as the circuit runs.\n\n"
    "Simulated parts\n"
    "Resistors, potentiometers (set the wiper in the part’s panel), LDRs (set the light level), fuses, "
    "capacitors and electrolytic capacitors, inductors, batteries (with a small internal resistance), "
    "DC, AC and square-wave sources, current sources, power rails, voltmeters, ammeters, voltage probes, "
    "switches and push buttons, lamps, motors, buzzers, diodes, Zener diodes, LEDs (the value sets the "
    "color), NPN and PNP transistors, N-MOSFETs, op-amps, logic gates and flip-flops (5 V logic), the 555 timer, the 7805 "
    "regulator, the TMP36 temperature sensor (set the temperature), the relay module, the 74HC logic chips and "
    "any part you give logic equations.\n\n"
    "Your own components\n"
    "A part you made from a circuit (select it, then + New Component › From the selected circuit) simulates "
    "the circuit inside it: gates, "
    "resistors, transistors, LEDs … all work as they did on the canvas. Hover over it for its pin voltages; "
    "an LED inside it makes the whole part glow.\n\n"
    "Not simulated\n"
    "Microcontroller boards (Arduino, Pico), digital modules (LCD, ultrasonic sensor, servo), generic ICs and "
    "parts you draw with + New Component that have no circuit inside. Their pins are left unconnected. A copy of a simulated part (for "
    "example one you gave a picture) still simulates as long as its pin names stay the same.\n\n"
    "Logic chips\n"
    "The 74HC chips (74HC00, 02, 04, 08, 32, 86 and 74) simulate from logic equations, and so can any part you "
    "make: in the Component Editor click Add logic… and write lines such as  Y = A & B,  Q = D on CLK  or  "
    "Q = 0 when RST. While simulating, each logic pin shows a green dot when HIGH and a grey dot when LOW. A chip "
    "with VCC and GND pins only works when they are wired to its power supply.\n\n"
    "Values\n"
    "Each part’s Value box is read: 4.7 kΩ, 100 nF, 10 µF, 1 mH, 9 V, 1 mA, 10 V 60 Hz (peak), "
    "120 V rms 60 Hz, 5 V 1 kHz (square wave), 6 V 1 W (lamp), 6 V 0.2 A (motor), 5.1 V (Zener), "
    "Red / Green / Blue (LED), hFE=200 (transistor gain).\n\n"
    "Models are simplified for learning\n"
    "Transistors use typical values (gain about 150), op-amps have a gain of 200 000 and outputs that stop "
    "about 1.5 V short of their supply rails, logic gates and flip-flops switch at 2.5 V and output 0 V or 5 V, an unconnected logic input "
    "counts as LOW, and flip-flops change on the rising edge of CLK. Real parts "
    "vary, so expect small differences from a lab measurement.\n\n"
    "While it runs\n"
    "Hover over a part for its voltage, current and power; click it for full readings. Click switches, hold "
    "push buttons and drag sliders. You can keep editing: the simulation updates as you change the circuit. "
    "Right-click a wire or part to plot it on the oscilloscope.\n\n"
    "Frequency response\n"
    "Simulate › Frequency response feeds a small sine wave into the chosen source and plots the gain and "
    "phase at the chosen point over a range of frequencies (a Bode plot). It also finds the −3 dB cutoff "
    "of filters.")


def _nice_ticks(lo, hi, n=5):
    if not (hi > lo):
        lo, hi = lo - 1.0, hi + 1.0
    raw = (hi - lo) / float(n)
    mag = 10 ** math.floor(math.log10(raw))
    step = mag
    for m in (1, 2, 2.5, 5, 10):
        step = m * mag
        if step >= raw * 0.999:
            break
    a = math.floor(lo / step + 1e-9) * step
    b = math.ceil(hi / step - 1e-9) * step
    ticks = []
    k = 0
    while k < 60:
        v = a + k * step
        if v > b + step * 1e-6:
            break
        ticks.append(0.0 if abs(v) < step * 1e-9 else v)
        k += 1
    return a, b, ticks


class _SimUI:
    """Simulation methods of App (copied onto App below)."""

    # ---------------------------------------------------------------- tool bar
    def _build_simbar(self):
        bg = C["sim_bg"]
        bar = tk.Frame(self.root, bg=bg)
        self.simbar = bar
        inner = tk.Frame(bar, bg=bg)
        inner.pack(fill="x", padx=10, pady=4)
        self.sim_dot = tk.Label(inner, text="●", bg=bg, fg=C["ok"], font=(self.fam, 11, "bold"))
        self.sim_dot.pack(side="left")
        self.sim_state_var = tk.StringVar(value="Running")
        tk.Label(inner, textvariable=self.sim_state_var, bg=bg, fg=C["text"], font=self.f_bold).pack(side="left", padx=(3, 12))
        self.b_sim_pause = ttk.Button(inner, text="Pause", style="SimBar.TButton", command=self.sim_pause, takefocus=False)
        self.b_sim_pause.pack(side="left")
        b = ttk.Button(inner, text="Restart", style="SimBar.TButton", command=self.sim_restart, takefocus=False)
        b.pack(side="left", padx=4)
        Tooltip(b, "Start again from time zero (capacitors empty, fuses replaced)")
        tk.Frame(inner, width=1, bg=C["sim_border"]).pack(side="left", fill="y", padx=10, pady=2)
        tk.Label(inner, text="Speed", bg=bg, fg=C["muted"]).pack(side="left")
        self.v_speed = tk.StringVar(value=SPEEDS[0][0])
        cb = ttk.Combobox(inner, textvariable=self.v_speed, values=[n for n, _ in SPEEDS], state="readonly",
                          width=15, takefocus=False)
        cb.pack(side="left", padx=(5, 10))
        cb.bind("<<ComboboxSelected>>", lambda e: (self.cv.focus_set(), self._sim_status()))
        Tooltip(cb, "How fast circuit time runs compared with real time.\nAuto picks a speed that suits the circuit.")
        self.sim_time_var = tk.StringVar(value="")
        tk.Label(inner, textvariable=self.sim_time_var, bg=bg, fg=C["text"], width=25, anchor="w").pack(side="left")
        tk.Frame(inner, width=1, bg=C["sim_border"]).pack(side="left", fill="y", padx=10, pady=2)
        b = ttk.Button(inner, text="Oscilloscope", style="SimBar.TButton", command=self.open_scope, takefocus=False)
        b.pack(side="left")
        Tooltip(b, "Plot voltages and currents over time")
        b = ttk.Button(inner, text="Frequency response", style="SimBar.TButton", command=self.open_freq, takefocus=False)
        b.pack(side="left", padx=4)
        Tooltip(b, "Bode plot: gain and phase against frequency")
        self.sim_msg_var = tk.StringVar()
        self.sim_msg = tk.Label(inner, textvariable=self.sim_msg_var, bg=bg, fg=C["muted"], anchor="e", cursor="hand2")
        self.sim_msg.pack(side="right", fill="x", expand=True, padx=(10, 0))
        self.sim_msg.bind("<Button-1>", lambda e: self._show_messages())
        tk.Frame(bar, height=1, bg=C["sim_border"]).pack(side="bottom", fill="x")

    def _show_messages(self):
        self.sel = set()
        self.selection_changed()

    # ---------------------------------------------------------------- start / stop
    def sim_toggle(self):
        if self.sim is None:
            self.sim_start()
        else:
            self.sim_stop()

    def _make_sim(self, carry=None, t=0.0):
        sim = Sim(self, carry=carry, t=t)
        sim.on_sample = self._scope_sample
        return sim

    def sim_start(self):
        self.commit_props()
        if self.mode != "idle":
            self.cancel_mode()
        if not self.comps:
            self.flash("Add some parts first, then press ▶ Simulate.")
            return
        self.sim = self._make_sim()
        self.sim_paused = False
        self.b_sim.configure(text="■  Stop", style="Stop.TButton")
        self.b_sim_pause.configure(text="Pause")
        self.simbar.pack(side="top", fill="x", after=self._tb_line)
        self._sim_last = time.perf_counter()
        self._sim_warn_sig = None
        self._last_sample = -1.0
        for tr in self.scope_traces:
            tr["data"] = []
        if self._sim_job is None:
            self._sim_job = self.root.after(10, self._sim_tick)
        self.request_redraw()
        self.refresh_props()
        self.set_status_hint()
        self._sim_status()

    def sim_stop(self):
        if self.sim is None:
            return
        self.sim = None
        if self._sim_job is not None:
            try:
                self.root.after_cancel(self._sim_job)
            except tk.TclError:
                pass
            self._sim_job = None
        self.simbar.pack_forget()
        self.b_sim.configure(text="▶  Simulate", style="Sim.TButton")
        self.sim_hover = None
        self._sim_pb = None
        self.cv.delete("sim")
        self.request_redraw()
        self.refresh_props()
        self.set_status_hint()
        if self.scope_win is not None:
            self.scope_win.redraw(True)

    def sim_restart(self):
        if self.sim is None:
            self.sim_start()
            return
        self.sim = self._make_sim()
        self._last_sample = -1.0
        for tr in self.scope_traces:
            tr["data"] = []
        self._sim_last = time.perf_counter()
        self._sim_warn_sig = None
        self.request_redraw()
        self.refresh_props()
        self._sim_status()

    def sim_pause(self):
        if self.sim is None:
            return
        self.sim_paused = not self.sim_paused
        txt = "Resume" if self.sim_paused else "Pause"
        self.b_sim_pause.configure(text=txt)
        if self.scope_win is not None:
            self.scope_win.b_pause.configure(text=txt)
        self._sim_last = time.perf_counter()
        self._sim_status()

    def _sim_rebuild(self):
        old = self.sim
        new = self._make_sim(carry=old.export(), t=old.t)
        self.sim = new
        self._sim_warn_sig = None
        self.sim_hover = self.sim_hover if self.sim_hover in self.comps else None

    def sim_timescale(self):
        v = dict(SPEEDS).get(self.v_speed.get())
        if v is None:
            return self.sim.auto_speed if self.sim is not None else 1.0
        return v

    # ---------------------------------------------------------------- the loop
    def _sim_tick(self):
        self._sim_job = None
        sim = self.sim
        if sim is None:
            return
        try:
            now = time.perf_counter()
            dt = min(0.1, max(0.0, now - self._sim_last))
            self._sim_last = now
            if not self.sim_paused:
                sim.advance(dt * self.sim_timescale(), budget=0.025)
            elif sim.static and sim.dirty:
                sim.advance(0.0)
            self._sim_draw()
            if self.sim_hover is not None or self.hover_pin is not None:
                self.draw_overlay()
            self._sim_ui_t += dt
            if self._sim_ui_t >= 0.2:
                self._sim_ui_t = 0.0
                self._sim_status()
                self._sim_update_props()
            if self.scope_win is not None:
                self.scope_win.redraw()
        except Exception:
            # Without this, one error stops the loop for good and the simulation looks frozen.
            # Show it as a simulator problem instead (editing the circuit or Restart starts afresh).
            if self.sim is sim and not sim.error:
                path = log_exception(*sys.exc_info(), context="in the simulation loop")
                sim.error = "The simulator hit an internal problem (details saved to %s)." % path
                try:
                    self._sim_status()
                except Exception:
                    pass
        finally:
            if self.sim is not None and self._sim_job is None:
                self._sim_job = self.root.after(30, self._sim_tick)

    def _sim_status(self):
        sim = self.sim
        if sim is None:
            return
        auto = dict(SPEEDS).get(self.v_speed.get()) is None
        self.sim_time_var.set("t = %s%s" % (fmt_si(sim.t, "s"),
                                            "    (auto: %s)" % speed_name(self.sim_timescale()) if auto else ""))
        if sim.error:
            state, col = "Stopped: problem found", C["danger"]
        elif self.sim_paused:
            state, col = "Paused", C["warn"]
        elif sim.slow:
            state, col = "Running (slower than the chosen speed)", C["warn"]
        else:
            state, col = "Running", C["ok"]
        self.sim_state_var.set(state)
        self.sim_dot.configure(fg=col)
        warns = sim.warnings()
        errs = [w for w in warns if w[0] == "Error"]
        wn = [w for w in warns if w[0] == "Warning"]
        if errs:
            first = re.split(r":|\. ", errs[0][2], 1)[0].rstrip(".")
            msg, mcol = "⚠ %s (click for details)" % first, C["danger"]
        elif wn:
            msg, mcol = "%d warning%s (click to see)" % (len(wn), "" if len(wn) == 1 else "s"), C["warn"]
        elif warns:
            msg, mcol = "%d note%s (click to see)" % (len(warns), "" if len(warns) == 1 else "s"), C["muted"]
        else:
            msg, mcol = "✓ No problems", C["ok"]
        if len(msg) > 110:
            msg = msg[:107].rstrip() + "…"
        self.sim_msg_var.set(msg)
        self.sim_msg.configure(fg=mcol)
        sig = tuple((w[0], w[2]) for w in warns)
        if sig != self._sim_warn_sig:
            self._sim_warn_sig = sig
            if not self.sel and self.mode == "idle":
                self.refresh_props()

    # ---------------------------------------------------------------- drawing
    def _sim_draw(self):
        cv = self.cv
        cv.delete("sim")
        sim = self.sim
        if sim is None or not sim.N or sim.error:
            return
        z = self.zoom
        s = G * z
        x = sim.x
        fpx = max(8, dpx(10, z))
        fontb = (self.fam, -fpx, "bold")
        below = "wire" if cv.find_withtag("wire") else "comp"
        now = time.perf_counter()
        for cid, d in sim.by_cid.items():
            c = self.comps.get(cid)
            if c is None:
                continue
            try:
                v = d.view(x)
            except Exception:
                v = None
            if not v:
                continue
            rd = self.rdef(c)
            bx0, by0, bx1, by1 = rd.body_bbox
            X, Y = self.T(*local_to_world(c, rd, (bx0 + bx1) / 2.0, (by0 + by1) / 2.0))
            glow = v.get("glow")
            if glow and glow[1] > 0.02:
                col, k = glow
                r = s * (0.8 + 0.6 * k)
                own = cv.find_withtag("c:" + cid) if ("c", cid) in self.sel else ()
                rings = [(1.0, 0.2 + 0.35 * k), (0.6, 0.4 + 0.55 * k)]
                for frac, t in (reversed(rings) if own else rings):
                    o = cv.create_oval(X - r * frac, Y - r * frac, X + r * frac, Y + r * frac,
                                       fill=_mix(C["canvas"], col, t), outline="", tags="sim")
                    if own:   # selected: sit just above the selection highlight, under the symbol
                        cv.tag_raise(o, own[0])
                    else:
                        cv.tag_lower(o, below)
            sp = v.get("spin")
            if sp is not None and abs(sp) > 0.02:
                a = (self._spin.get(cid, 0.0) + 40.0 * max(-2.0, min(2.0, sp))) % 360.0
                self._spin[cid] = a
                R = s * 0.95
                cv.create_arc(X - R, Y - R, X + R, Y + R, start=a, extent=100 if sp > 0 else -100, style="arc",
                              outline=C["accent"], width=max(2.0, 2.5 * z), tags="sim")
            cross = ink(v.get("cross"))
            if cross:
                p = [self.T(*local_to_world(c, rd, px, py)) for px, py in ((bx0, by0), (bx1, by1), (bx0, by1), (bx1, by0))]
                cv.create_line(p[0][0], p[0][1], p[1][0], p[1][1], fill=cross, width=max(2.0, 2.5 * z), tags="sim")
                cv.create_line(p[2][0], p[2][1], p[3][0], p[3][1], fill=cross, width=max(2.0, 2.5 * z), tags="sim")
            if v.get("sound") and int(now * 4) % 2 == 0:
                cv.create_text(X + s * 1.1, Y - s * 1.0, text="♪", fill=C["accent"],
                               font=(self.fam, -max(10, dpx(17, z)), "bold"), tags="sim")
            pst = v.get("pinstate")
            if pst:
                rr = max(3.4, 4.4 * z)
                for k, level in pst:
                    if level is None or k >= len(rd.pins):
                        continue
                    pp = rd.pins[k]
                    PX, PY = self.T(*local_to_world(c, rd, pp["x"], pp["y"]))
                    cv.create_oval(PX - rr, PY - rr, PX + rr, PY + rr, fill="#22c55e" if level else "#94a3b8",
                                   outline=C["stroke"], width=max(1.0, 1.1 * z), tags="sim")
            rdg = v.get("reading")
            if rdg:
                bx = self.comp_bbox(c)
                if c.get("rot", 0) % 2 or sim_model_of(self.library, c) == "probe":
                    px, py, anc = bx[2] + 0.3, (bx[1] + bx[3]) / 2.0, "w"
                    if sim_model_of(self.library, c) == "probe":
                        py = bx[1] + 0.8
                else:
                    px, py, anc = (bx[0] + bx[2]) / 2.0, bx[3] + 0.3, "n"
                PX, PY = self.T(px, py)
                t = cv.create_text(PX, PY, text=rdg, anchor=anc, fill=C["meter_fg"], font=fontb, tags="sim")
                b = cv.bbox(t)
                if b:
                    rr = cv.create_rectangle(b[0] - 5, b[1] - 2, b[2] + 5, b[3] + 2, fill=C["meter_bg"],
                                             outline="", tags="sim")
                    cv.tag_lower(rr, t)
        if self.show_volts and z >= 0.45 * self.ui_scale:
            fs = (self.fam, -max(8, dpx(9.5, z)))
            for net in self.compute_nets():
                node = sim.node_of.get(tuple(net["pins"][0]))
                if node is None or node == 0:
                    continue
                volt = sim.nv(node)
                best, blen = None, -1.0
                for wid in net["wires"]:
                    w = self.wires.get(wid)
                    if not w:
                        continue
                    try:
                        pts, _ = self.wire_route(w)
                    except (KeyError, IndexError):
                        continue
                    for i in range(len(pts) - 1):
                        (ax, ay), (bx_, by_) = pts[i], pts[i + 1]
                        ln = abs(bx_ - ax) + abs(by_ - ay)
                        if ln > blen:
                            blen, best = ln, ((ax + bx_) / 2.0, (ay + by_) / 2.0, abs(by_ - ay) < 1e-9)
                if best is None:
                    continue
                PX, PY = self.T(best[0], best[1])
                col = C["volt_pos"] if volt > 0.05 else C["volt_neg"] if volt < -0.05 else C["muted"]
                if best[2]:
                    t = cv.create_text(PX, PY - 5, text=fmt_si(volt, "V"), anchor="s", fill=col, font=fs, tags="sim")
                else:
                    t = cv.create_text(PX + 6, PY, text=fmt_si(volt, "V"), anchor="w", fill=col, font=fs, tags="sim")
                b = cv.bbox(t)
                if b:
                    rr = cv.create_rectangle(b[0] - 3, b[1] - 1, b[2] + 3, b[3] + 1, fill=C["volt_bg"],
                                             outline=_mix(C["volt_bg"], col, 0.35), tags="sim")
                    cv.tag_lower(rr, t)
        cv.tag_raise("overlay")

    def _sim_tip(self, cid):
        cv = self.cv
        sim = self.sim
        c = self.comps[cid]
        rd = self.rdef(c)
        d = sim.by_cid.get(cid)
        lines = ["%s  ·  %s" % (c.get("label") or rd.name, rd.name)]
        if d is None:
            lines.append("Not simulated")
        else:
            try:
                lines += ["%s:  %s" % (a, b) for a, b in d.info(sim.x)]
            except Exception:
                pass
        mx, my = self._mouse
        t = cv.create_text(mx + 16, my + 18, text="\n".join(lines), anchor="nw", fill=C["tip_fg"],
                           font=(self.fam, -int(11 * self.ui_scale)), tags="overlay")
        b = cv.bbox(t)
        if b:
            dx = min(0, cv.winfo_width() - 8 - b[2])
            dy = min(0, cv.winfo_height() - 8 - b[3])
            if dx or dy:
                cv.move(t, dx, dy)
                b = cv.bbox(t)
            r = cv.create_rectangle(b[0] - 8, b[1] - 6, b[2] + 8, b[3] + 6, fill=C["tip_bg"], outline="", tags="overlay")
            cv.tag_lower(r, t)

    # ---------------------------------------------------------------- interaction
    def _sim_press(self, cid):
        if self.sim is None:
            return
        sym = self.rdef(self.comps[cid]).symbol
        if sym == "pushbutton":
            self.sim.pressed.add(cid)
            self.sim.bump()
            self._sim_pb = cid
            self.request_redraw()
        elif sym == "switch":
            self._sim_click = cid

    def toggle_switch(self, cid):
        c = self.comps.get(cid)
        if c is None:
            return
        self.set_switch(cid, not c.get("closed"))
        if self.sel == {("c", cid)}:
            self.refresh_props()

    def set_switch(self, cid, closed):
        c = self.comps.get(cid)
        if c is None:
            return
        c["closed"] = bool(closed)
        self.dirty = True
        self.update_title()
        if self.sim is not None:
            self.sim.bump()
        self.request_redraw()
        self.flash("%s is now %s." % (c.get("label") or "The switch", "closed (on)" if closed else "open (off)"))

    def set_sim_param(self, cid, key, val):
        c = self.comps.get(cid)
        if c is None:
            return
        c[key] = val
        self.dirty = True
        self.update_title()
        if self.sim is not None:
            self.sim.bump()

    # ---------------------------------------------------------------- properties panel
    def _props_sim_readings(self, cid, c, rd, r):
        f = self.props
        wl = self.props_width - 40
        self._head("Live readings", r)
        r += 1
        sim = self.sim
        d = sim.by_cid.get(cid)
        box = tk.Frame(f, bg=C["sim_bg"], highlightthickness=1, highlightbackground=C["sim_border"], padx=8, pady=6)
        box.grid(row=r, column=0, columnspan=2, sticky="ew")
        box.columnconfigure(1, weight=1)
        r += 1
        readings = []
        if d is None:
            tk.Label(box, text="This part isn’t simulated, so its pins are left unconnected."
                     + ("  To make your own part work, build its circuit on the canvas, select it and click "
                        "Make component." if rd.custom else ""),
                     bg=C["sim_bg"], fg=C["muted"], wraplength=wl, justify="left").grid(row=0, column=0, sticky="w")
        else:
            try:
                info = d.info(sim.x)
            except Exception:
                info = []
            for i, (name, txt) in enumerate(info):
                tk.Label(box, text=name, bg=C["sim_bg"], fg=C["muted"]).grid(row=i, column=0, sticky="w", padx=(0, 8))
                v = tk.StringVar(value=txt)
                readings.append(v)
                tk.Label(box, textvariable=v, bg=C["sim_bg"], fg=C["text"], font=self.f_bold).grid(row=i, column=1, sticky="w")
            model = sim_model_of(self.library, c)
            lab = c.get("label") or rd.name
            bf = ttk.Frame(f, style="Panel.TFrame")
            bf.grid(row=r, column=0, columnspan=2, sticky="w", pady=(6, 0))
            r += 1
            if model == "probe" or len(rd.pins) == 1:
                ttk.Button(bf, text="Plot voltage", command=lambda: self.plot_trace(
                    "pin", [cid, 0], lab if model == "probe" else "V(%s)" % lab)).pack(side="left")
            elif len(rd.pins) == 2:
                ttk.Button(bf, text="Plot voltage", command=lambda: self.plot_trace("v", cid, "V(%s)" % lab)).pack(side="left")
                ttk.Button(bf, text="Plot current", command=lambda: self.plot_trace("i", cid, "I(%s)" % lab)).pack(side="left", padx=4)
            else:
                ttk.Label(bf, text="Double-click a pin below to plot its voltage.", style="Hint.TLabel").pack(side="left")
        self.sim_vars = {"cid": cid, "readings": readings, "tree": None}
        return r

    def _slider(self, parent, row, title, cid, key, lo, hi, default, fmt):
        c = self.comps[cid]
        val = float(c.get(key, default))
        lab = tk.StringVar(value=fmt(val))
        ttk.Label(parent, text=title, style="Panel.TLabel").grid(row=row, column=0, sticky="w")
        ttk.Label(parent, textvariable=lab, style="Card.TLabel").grid(row=row, column=1, sticky="e")
        sv = tk.DoubleVar(value=val)

        def moved(_v=None):
            v = sv.get()
            lab.set(fmt(v))
            self.set_sim_param(cid, key, round(v, 4))
        ttk.Scale(parent, from_=lo, to=hi, variable=sv, command=moved, style="Panel.Horizontal.TScale").grid(
            row=row + 1, column=0, columnspan=2, sticky="ew", pady=(2, 0))

    def _props_sim_controls(self, cid, c, rd, r):
        model = sim_model_of(self.library, c)
        if model not in CONTROL_MODELS:
            return r
        f = self.props
        wl = self.props_width - 30
        self._head("Controls", r)
        r += 1
        fr = ttk.Frame(f, style="Panel.TFrame")
        fr.grid(row=r, column=0, columnspan=2, sticky="ew")
        fr.columnconfigure(0, weight=1)
        r += 1
        if model == "switch":
            v = tk.BooleanVar(value=bool(c.get("closed")))
            ttk.Checkbutton(fr, text="Closed (switched on)", variable=v, style="Card.TCheckbutton",
                            command=lambda: self.set_switch(cid, v.get())).grid(row=0, column=0, sticky="w")
            ttk.Label(fr, text="While simulating you can also just click the switch.", style="Hint.TLabel",
                      wraplength=wl).grid(row=1, column=0, sticky="w")
        elif model == "pushbutton":
            ttk.Label(fr, text="While simulating, hold the mouse button down on it to press it.", style="Hint.TLabel",
                      wraplength=wl, justify="left").grid(row=0, column=0, sticky="w")
        elif model == "potentiometer":
            self._slider(fr, 0, "Wiper position", cid, "wiper", 0.0, 1.0, 0.5,
                         lambda v: "%d %% from pin 1" % round(v * 100))
        elif model == "ldr":
            self._slider(fr, 0, "Light level", cid, "light", 0.0, 100.0, 50.0, lambda v: "%d %%" % round(v))
        elif model == "tmp36":
            self._slider(fr, 0, "Temperature", cid, "temp", -40.0, 125.0, 25.0, lambda v: "%d °C" % round(v))
        return r

    def _props_sim_summary(self):
        f = self.props
        wl = self.props_width - 30
        sim = self.sim
        ttk.Label(f, text="Simulation", style="Title.TLabel").grid(row=0, column=0, sticky="w")
        state = "Problem found" if sim.error else ("Paused" if self.sim_paused else "Running")
        kind = "a DC circuit (nothing changes over time)" if sim.static else "changes over time"
        ttk.Label(f, text="%s  ·  %s" % (state, kind), style="Muted.TLabel", wraplength=wl).grid(row=1, column=0, sticky="w")
        warns = sim.warnings()
        self._head("Messages (%d)" % len(warns) if warns else "Messages", 2)
        mf = tk.Frame(f, bg=C["panel"])
        mf.grid(row=3, column=0, sticky="ew")
        colors = {"Error": C["danger"], "Warning": C["warn"], "Info": C["muted"]}
        if not warns:
            tk.Label(mf, text="✓  No problems found.", bg=C["panel"], fg=C["ok"], font=self.f_bold).pack(anchor="w")
        for sev, cid, msg in warns[:7]:
            row = tk.Frame(mf, bg=C["panel"])
            row.pack(fill="x", pady=(0, 7), anchor="w")
            tk.Label(row, text={"Info": "NOTE"}.get(sev, sev.upper()), bg=C["panel"], fg=colors.get(sev, C["muted"]),
                     font=(self.fam, 7, "bold")).pack(anchor="w")
            lbl = tk.Label(row, text=msg, bg=C["panel"], fg=C["text"], wraplength=wl, justify="left", anchor="w")
            lbl.pack(anchor="w", fill="x")
            top = cid.split("/", 1)[0] if cid else None   # a part inside a component: select the component
            if top in self.comps:
                lbl.configure(cursor="hand2")
                lbl.bind("<Button-1>", lambda e, c=top: self._select_comp(c))
        if len(warns) > 7:
            tk.Label(mf, text="+ %d more" % (len(warns) - 7), bg=C["panel"], fg=C["muted"]).pack(anchor="w")
        self._head("While it runs", 4)
        tips = ["Hover over a part to see its voltage, current and power.",
                "Click a switch to flip it; hold a push button down to press it.",
                "Click a part for full readings and controls (sliders for pots, LDRs and sensors).",
                "Right-click a wire or part to plot it on the oscilloscope.",
                "Keep editing: the simulation updates as you change things."]
        tf = tk.Frame(f, bg=C["panel"])
        tf.grid(row=5, column=0, sticky="ew")
        for t in tips:
            tk.Label(tf, text="•  " + t, bg=C["panel"], fg=C["text"], wraplength=wl, justify="left").pack(anchor="w", pady=1)
        ttk.Button(f, text="What gets simulated?", command=self.show_sim_help).grid(row=6, column=0, sticky="w", pady=(12, 0))

    def _select_comp(self, cid):
        if cid in self.comps:
            self.sel = {("c", cid)}
            self.selection_changed()

    def _sim_update_props(self):
        sv = self.sim_vars
        sim = self.sim
        if not sv or sim is None or sv.get("cid") not in self.comps:
            return
        cid = sv["cid"]
        d = sim.by_cid.get(cid)
        x = sim.x
        if d is not None and sv["readings"]:
            try:
                info = d.info(x)
            except Exception:
                info = []
            if len(info) == len(sv["readings"]):
                for var, (_n, txt) in zip(sv["readings"], info):
                    var.set(txt)
        tv = sv.get("tree")
        if tv is None:
            return
        rd = self.rdef(self.comps[cid])
        cur = {}
        if d is not None:
            try:
                cur = dict(zip(d.pidx, d.currents(x)))
            except Exception:
                cur = {}
        for i, p in enumerate(rd.pins):
            v = sim.pin_v((cid, i)) if d is not None or (cid, i) in sim.wired else None
            vtxt = fmt_si(v, "V") if v is not None else "—"
            itxt = fmt_si(cur[i], "A") if i in cur else "—"
            try:
                tv.item(str(i), values=(p["name"], vtxt, itxt))
            except tk.TclError:
                return

    # ---------------------------------------------------------------- oscilloscope traces
    def _plot_menu_items(self, m, cid):
        c = self.comps[cid]
        rd = self.rdef(c)
        lab = c.get("label") or rd.name
        model = sim_model_of(self.library, c)
        if model == "ground" or not rd.pins:
            return
        m.add_separator()
        if model == "probe" or len(rd.pins) == 1:
            m.add_command(label="Plot this voltage (oscilloscope)",
                          command=lambda: self.plot_trace("pin", [cid, 0], lab if model == "probe" else "V(%s)" % lab))
        elif len(rd.pins) == 2:
            m.add_command(label="Plot voltage across (oscilloscope)", command=lambda: self.plot_trace("v", cid, "V(%s)" % lab))
            m.add_command(label="Plot current through (oscilloscope)", command=lambda: self.plot_trace("i", cid, "I(%s)" % lab))
        else:
            sub = tk.Menu(m, tearoff=0)
            for i, p in enumerate(rd.pins):
                sub.add_command(label=p["name"], command=lambda i=i, n=p["name"]: self.plot_trace(
                    "pin", [cid, i], "V(%s.%s)" % (lab, n)))
            m.add_cascade(label="Plot voltage at pin (oscilloscope)", menu=sub)

    def plot_net(self, wid):
        w = self.wires.get(wid)
        if not w:
            return
        net = self.pin_net_map().get(tuple(w["a"]))
        self.plot_trace("pin", list(w["a"]), "V(%s)" % (net["name"] if net else self.pin_name(tuple(w["a"]))))

    def _plot_pin_row(self, cid, tv):
        sel = tv.focus() or (tv.selection() or [None])[0]
        if sel is None or cid not in self.comps:
            return
        c = self.comps[cid]
        rd = self.rdef(c)
        i = int(sel)
        self.plot_trace("pin", [cid, i], "V(%s.%s)" % (c.get("label") or rd.name, rd.pins[i]["name"]))

    def _add_trace(self, kind, key, name):
        for tr in self.scope_traces:
            if tr["kind"] == kind and tr["key"] == key:
                return tr
        used = {tr["color"] for tr in self.scope_traces}
        col = next((cc for cc in TRACE_COLORS if cc not in used), TRACE_COLORS[len(self.scope_traces) % len(TRACE_COLORS)])
        tr = {"kind": kind, "key": key, "name": name, "color": col, "data": []}
        self.scope_traces.append(tr)
        return tr

    def plot_trace(self, kind, key, name):
        self._add_trace(kind, key, name)
        self.open_scope()
        if self.scope_win is not None:
            self.scope_win.build_legend()
            self.scope_win.redraw(True)

    def _default_traces(self):
        for cid, c in self.comps.items():
            model = sim_model_of(self.library, c)
            lab = c.get("label") or "?"
            if model == "probe" and (cid, 0) in self.connected_pins():
                self._add_trace("pin", [cid, 0], lab)
            elif model == "voltmeter":
                self._add_trace("v", cid, "V(%s)" % lab)
            elif model == "ammeter":
                self._add_trace("i", cid, "I(%s)" % lab)
        if not self.scope_traces:
            for net in self.compute_nets():
                if net["name"] != "GND" and len(self.scope_traces) < 3:
                    self._add_trace("pin", list(net["pins"][0]), "V(%s)" % net["name"])

    def open_scope(self):
        if self.sim is None:
            self.sim_start()
        if self.scope_win is not None:
            try:
                self.scope_win.deiconify()
                self.scope_win.lift()
                return
            except tk.TclError:
                self.scope_win = None
        if not self.scope_traces:
            self._default_traces()
        self.scope_win = ScopeWindow(self)

    def open_freq(self):
        if self.freq_win is not None:
            try:
                self.freq_win.deiconify()
                self.freq_win.lift()
                self.freq_win.refresh_lists()
                return
            except tk.TclError:
                self.freq_win = None
        self.freq_win = FreqWindow(self)

    def scope_window_len(self):
        if self.scope_win is not None:
            w = self.scope_win.window_value()
            if w:
                return w
        return self.sim.auto_window if self.sim is not None else 1.0

    def _trace_value(self, tr):
        sim = self.sim
        k = tr["kind"]
        if k == "pin":
            return sim.pin_v(tuple(tr["key"]))
        d = sim.by_cid.get(tr["key"])
        if d is None or not sim.x:
            return None
        try:
            if k == "v":
                return d.vd(sim.x) if len(d.n) >= 2 else d.V(sim.x, 0)
            if k == "i":
                return d.currents(sim.x)[0]
        except Exception:
            return None
        return None

    def _scope_sample(self, t):
        trs = self.scope_traces
        if not trs or self.sim is None:
            return
        if t < self._last_sample:
            for tr in trs:
                tr["data"] = []
            self._last_sample = -1.0
        win = self.scope_window_len()
        if t - self._last_sample < win / 700.0:
            return
        self._last_sample = t
        for tr in trs:
            v = self._trace_value(tr)
            if v is None:
                continue
            data = tr["data"]
            data.append((t, v))
            if len(data) > 6000:
                del data[:2000]
            elif len(data) > 1500 and data[0][0] < t - 3 * win:
                cut = bisect_left(data, (t - 2 * win,))
                del data[:cut]

    def _toggle_volts(self):
        self.show_volts = self.v_volts.get()
        self.settings["show_volts"] = self.show_volts
        self.save_settings()
        self.request_redraw()

    def show_sim_help(self):
        win = tk.Toplevel(self.root)
        win.title("What gets simulated? — " + APP_NAME)
        win.configure(bg=C["panel"])
        win.transient(self.root)
        f = ttk.Frame(win, style="Panel.TFrame", padding=18)
        f.pack(fill="both", expand=True)
        ttk.Label(f, text="What gets simulated?", style="Title.TLabel").pack(anchor="w")
        ttk.Label(f, text=SIM_HELP, style="Panel.TLabel", justify="left",
                  wraplength=int(620 * self.ui_scale)).pack(anchor="w", pady=(8, 12))
        ttk.Button(f, text="Close", command=win.destroy).pack(anchor="e")


for _k, _v in list(_SimUI.__dict__.items()):
    if callable(_v) and not _k.startswith("__"):
        setattr(App, _k, _v)


class ScopeWindow(tk.Toplevel):
    WINDOWS = [("Auto", None), ("100 µs", 1e-4), ("1 ms", 1e-3), ("10 ms", 1e-2), ("100 ms", 0.1),
               ("1 s", 1.0), ("10 s", 10.0), ("1 min", 60.0)]

    def __init__(self, app):
        super().__init__(app.root)
        self.app = app
        s = app.ui_scale
        self.title("Oscilloscope — " + APP_NAME)
        self.configure(bg=C["bg"])
        self.geometry("%dx%d" % (int(800 * s), int(500 * s)))
        self.minsize(int(480 * s), int(320 * s))
        top = ttk.Frame(self, style="Bg.TFrame", padding=(10, 8, 10, 4))
        top.pack(fill="x")
        ttk.Label(top, text="Time shown", style="Status.TLabel").pack(side="left")
        self.v_win = tk.StringVar(value="Auto")
        cb = ttk.Combobox(top, textvariable=self.v_win, values=[n for n, _ in self.WINDOWS], state="readonly", width=8)
        cb.pack(side="left", padx=(6, 12))
        cb.bind("<<ComboboxSelected>>", lambda e: self.redraw(True))
        self.b_pause = ttk.Button(top, text="Resume" if app.sim_paused else "Pause", command=app.sim_pause)
        self.b_pause.pack(side="left")
        ttk.Button(top, text="Clear", command=self._clear).pack(side="left", padx=4)
        mb = ttk.Menubutton(top, text="Add trace ▾")
        self.add_menu = tk.Menu(mb, tearoff=0, postcommand=self._fill_add_menu)
        mb["menu"] = self.add_menu
        mb.pack(side="left", padx=4)
        self._subs = []
        ttk.Button(top, text="Export CSV…", command=self._export).pack(side="right")
        self.cv = tk.Canvas(self, bg=C["plot_bg"], highlightthickness=1, highlightbackground=C["border"])
        self.cv.pack(fill="both", expand=True, padx=10, pady=4)
        self.legend = ttk.Frame(self, style="Bg.TFrame", padding=(10, 2, 10, 10))
        self.legend.pack(fill="x")
        self.cv.bind("<Configure>", lambda e: self.redraw(True))
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.bind("<Escape>", lambda e: self.close())
        self._last = 0.0
        self.val_vars = []
        self.build_legend()

    def close(self):
        self.app.scope_win = None
        self.destroy()

    def on_theme(self):
        self.cv.configure(bg=C["plot_bg"], highlightbackground=C["border"])
        self.build_legend()
        self.redraw(True)

    def window_value(self):
        return dict(self.WINDOWS).get(self.v_win.get())

    def _clear(self):
        for tr in self.app.scope_traces:
            tr["data"] = []
        self.redraw(True)

    def _fill_add_menu(self):
        app = self.app
        m = self.add_menu
        m.delete(0, "end")
        for sub in self._subs:
            sub.destroy()
        self._subs = []
        nets = [n for n in app.compute_nets() if n["name"] != "GND"]
        sub = tk.Menu(m, tearoff=0)
        self._subs.append(sub)
        for n in nets:
            sub.add_command(label="%s   (%s)" % (n["name"], ", ".join(app.pin_name(k) for k in n["pins"][:3])),
                            command=lambda n=n: app.plot_trace("pin", list(n["pins"][0]), "V(%s)" % n["name"]))
        m.add_cascade(label="Voltage of a net", menu=sub)
        twos = [(cid, c) for cid, c in app.comps.items()
                if len(app.rdef(c).pins) == 2 and app.sim is not None and cid in app.sim.by_cid]
        for title, kind, pre in (("Voltage across a part", "v", "V"), ("Current through a part", "i", "I")):
            sub = tk.Menu(m, tearoff=0)
            self._subs.append(sub)
            for cid, c in twos:
                lab = c.get("label") or "?"
                sub.add_command(label="%s  (%s)" % (lab, app.rdef(c).name),
                                command=lambda cid=cid, lab=lab, kind=kind, pre=pre:
                                app.plot_trace(kind, cid, "%s(%s)" % (pre, lab)))
            m.add_cascade(label=title, menu=sub)

    def build_legend(self):
        for w in self.legend.winfo_children():
            w.destroy()
        self.val_vars = []
        trs = self.app.scope_traces
        if not trs:
            ttk.Label(self.legend, text="No traces yet. Right-click a wire or a part on the circuit and choose "
                                        "“Plot…”, or use Add trace.", style="Status.TLabel").pack(anchor="w")
            return
        for i, tr in enumerate(trs):
            row = tk.Frame(self.legend, bg=C["bg"])
            row.grid(row=i // 3, column=i % 3, sticky="w", padx=(0, 18), pady=2)
            tk.Frame(row, width=16, height=4, bg=ink(tr["color"])).pack(side="left", padx=(0, 6))
            tk.Label(row, text=tr["name"], bg=C["bg"], fg=C["text"], font=self.app.f_bold).pack(side="left")
            v = tk.StringVar(value="")
            self.val_vars.append(v)
            tk.Label(row, textvariable=v, bg=C["bg"], fg=C["muted"], width=10, anchor="w").pack(side="left", padx=(6, 2))
            x = tk.Label(row, text="✕", bg=C["bg"], fg=C["muted"], cursor="hand2")
            x.pack(side="left")
            x.bind("<Button-1>", lambda e, t=tr: self._remove(t))
            Tooltip(x, "Remove this trace")

    def _remove(self, tr):
        if tr in self.app.scope_traces:
            self.app.scope_traces.remove(tr)
        self.build_legend()
        self.redraw(True)

    @staticmethod
    def _visible(tr, t0, t1):
        data = tr["data"]
        i = max(0, bisect_left(data, (t0,)) - 1)
        return data[i:]

    def redraw(self, force=False):
        now = time.perf_counter()
        if not force and now - self._last < 0.066:
            return
        self._last = now
        try:
            cv = self.cv
            cv.delete("all")
            W, H = cv.winfo_width(), cv.winfo_height()
        except tk.TclError:
            return
        if W < 60 or H < 60:
            return
        app = self.app
        sim = app.sim
        s = app.ui_scale
        trs = app.scope_traces
        volt = [t for t in trs if t["kind"] != "i"]
        amp = [t for t in trs if t["kind"] == "i"]
        x0, x1 = int(64 * s), W - (int(64 * s) if amp else int(18 * s))
        y0, y1 = int(14 * s), H - int(30 * s)
        if x1 - x0 < 40 or y1 - y0 < 40:
            return
        font = (app.fam, -int(10 * s))
        win = app.scope_window_len()
        if sim is not None:
            tnow = sim.t
        else:
            tnow = max([tr["data"][-1][0] for tr in trs if tr["data"]] or [0.0])
        t1 = max(tnow, win)
        t0 = t1 - win
        vis = {id(tr): self._visible(tr, t0, t1) for tr in trs}

        def rng(group):
            vals = [v for tr in group for _t, v in vis[id(tr)]]
            if not vals:
                return -1.0, 1.0
            lo, hi = min(vals), max(vals)
            if hi - lo < 1e-9:
                pad = max(abs(hi) * 0.1, 1e-3)
            else:
                pad = (hi - lo) * 0.08
            return lo - pad, hi + pad

        vlo, vhi, vt = _nice_ticks(*rng(volt))
        alo, ahi, at = _nice_ticks(*rng(amp))
        grid = C["plot_grid"]

        def Xt(t):
            return x0 + (t - t0) / (t1 - t0) * (x1 - x0)

        _a, _b, xt = _nice_ticks(t0, t1, 6)
        for tt in xt:
            if t0 - 1e-15 <= tt <= t1 + 1e-15:
                X = Xt(tt)
                cv.create_line(X, y0, X, y1, fill=grid)
                cv.create_text(X, y1 + 4, text=fmt_si(tt, "s"), anchor="n", fill=C["muted"], font=font)
        for v in vt:
            Y = y1 - (v - vlo) / (vhi - vlo) * (y1 - y0)
            cv.create_line(x0, Y, x1, Y, fill=C["plot_zero"] if v == 0 else grid)
            if volt:
                cv.create_text(x0 - 6, Y, text=fmt_si(v, "V"), anchor="e", fill=C["muted"], font=font)
        if amp:
            for a in at:
                Y = y1 - (a - alo) / (ahi - alo) * (y1 - y0)
                cv.create_text(x1 + 6, Y, text=fmt_si(a, "A"), anchor="w", fill=C["muted"], font=font)
        cv.create_rectangle(x0, y0, x1, y1, outline=C["border"])
        for group, lo, hi in ((volt, vlo, vhi), (amp, alo, ahi)):
            for tr in group:
                pts = vis[id(tr)]
                if len(pts) < 2:
                    continue
                step = max(1, len(pts) // max(1, 2 * (x1 - x0)))
                coords = []
                for t, v in pts[::step]:
                    X = max(x0, min(x1, Xt(t)))
                    Y = y1 - (v - lo) / (hi - lo) * (y1 - y0)
                    coords += [X, max(y0, min(y1, Y))]
                if len(coords) >= 4:
                    cv.create_line(*coords, fill=ink(tr["color"]), width=max(1.5, 2 * s))
        if not trs:
            cv.create_text((x0 + x1) / 2, (y0 + y1) / 2, fill=C["muted"], font=(app.fam, -int(12 * s)),
                           text="Nothing plotted yet.\nRight-click a wire or a part and choose “Plot…”.", justify="center")
        elif sim is None:
            cv.create_text((x0 + x1) / 2, y0 + 16 * s, fill=C["muted"], font=(app.fam, -int(12 * s)),
                           text="The simulation is stopped. Press ▶ Simulate to see live traces.")
        for var, tr in zip(self.val_vars, trs):
            var.set(fmt_si(tr["data"][-1][1], "A" if tr["kind"] == "i" else "V") if tr["data"] else "—")

    def _export(self):
        trs = self.app.scope_traces
        if not any(tr["data"] for tr in trs):
            messagebox.showinfo(APP_NAME, "There is no data to export yet.", parent=self)
            return
        path = filedialog.asksaveasfilename(parent=self, title="Export oscilloscope data", defaultextension=".csv",
                                            initialfile="oscilloscope.csv", filetypes=[("Spreadsheet (CSV)", "*.csv")])
        if not path:
            return
        cols = [dict(tr["data"]) for tr in trs]
        times = sorted(set(t for col in cols for t in col))
        try:
            with open(path, "w", newline="", encoding="utf-8-sig") as f:
                wr = csv.writer(f)
                wr.writerow(["time (s)"] + ["%s (%s)" % (tr["name"], "A" if tr["kind"] == "i" else "V") for tr in trs])
                for t in times:
                    wr.writerow(["%.9g" % t] + ["" if t not in col else "%.6g" % col[t] for col in cols])
        except OSError as e:
            messagebox.showerror(APP_NAME, "Could not export:\n%s" % e, parent=self)
            return
        self.app.flash("Oscilloscope data saved to %s" % os.path.basename(path))


class FreqWindow(tk.Toplevel):
    def __init__(self, app):
        super().__init__(app.root)
        self.app = app
        s = app.ui_scale
        self.title("Frequency response — " + APP_NAME)
        self.configure(bg=C["bg"])
        self.geometry("%dx%d" % (int(820 * s), int(580 * s)))
        self.minsize(int(560 * s), int(400 * s))
        top = ttk.Frame(self, style="Bg.TFrame", padding=(10, 10, 10, 4))
        top.pack(fill="x")
        ttk.Label(top, text="Input source", style="Status.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(top, text="Output (measured at)", style="Status.TLabel").grid(row=0, column=1, sticky="w", padx=(10, 0))
        ttk.Label(top, text="From", style="Status.TLabel").grid(row=0, column=2, sticky="w", padx=(10, 0))
        ttk.Label(top, text="To", style="Status.TLabel").grid(row=0, column=3, sticky="w", padx=(6, 0))
        self.v_src = tk.StringVar()
        self.v_out = tk.StringVar()
        self.v_f0 = tk.StringVar(value="10 Hz")
        self.v_f1 = tk.StringVar(value="1 MHz")
        self.cb_src = ttk.Combobox(top, textvariable=self.v_src, state="readonly", width=24)
        self.cb_src.grid(row=1, column=0, sticky="w")
        self.cb_out = ttk.Combobox(top, textvariable=self.v_out, state="readonly", width=34)
        self.cb_out.grid(row=1, column=1, sticky="w", padx=(10, 0))
        ttk.Entry(top, textvariable=self.v_f0, width=9).grid(row=1, column=2, sticky="w", padx=(10, 0))
        ttk.Entry(top, textvariable=self.v_f1, width=9).grid(row=1, column=3, sticky="w", padx=(6, 0))
        ttk.Button(top, text="Plot", style="Accent.TButton", command=self.run).grid(row=1, column=4, padx=(10, 0))
        ttk.Button(top, text="Export CSV…", command=self._export).grid(row=1, column=5, padx=(6, 0))
        self.info_var = tk.StringVar(value="Choose the input source and where to measure, then press Plot.")
        tk.Label(self, textvariable=self.info_var, bg=C["bg"], fg=C["text"], font=app.f_bold, anchor="w",
                 justify="left").pack(fill="x", padx=12, pady=(4, 0))
        self.cv = tk.Canvas(self, bg=C["plot_bg"], highlightthickness=1, highlightbackground=C["border"])
        self.cv.pack(fill="both", expand=True, padx=10, pady=(4, 10))
        self.cv.bind("<Configure>", lambda e: self.draw())
        self.cv.bind("<Motion>", self._motion)
        self.cv.bind("<Leave>", lambda e: self._set_hover(None))
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.bind("<Escape>", lambda e: self.close())
        self.data = None
        self.marks = []
        self.hover = None
        self.sources, self.outputs = [], []
        self.refresh_lists()
        if self.sources and self.outputs:
            self.after(60, self.run)

    def close(self):
        self.app.freq_win = None
        self.destroy()

    def on_theme(self):
        self.cv.configure(bg=C["plot_bg"], highlightbackground=C["border"])
        self.draw()

    def refresh_lists(self):
        app = self.app
        src, outs = [], []
        for cid, c in app.comps.items():
            m = sim_model_of(app.library, c)
            if m in ("ac_source", "dc_source", "battery", "square_source"):
                src.append((0 if m == "ac_source" else 1, "%s  (%s)" % (c.get("label") or "?", app.rdef(c).name), cid))
            if m == "probe" and (cid, 0) in app.connected_pins():
                outs.append(("%s  (probe)" % (c.get("label") or "?"), (cid, 0)))
        src.sort(key=lambda t: t[0])
        self.sources = [(n, cid) for _k, n, cid in src]
        for n in app.compute_nets():
            if n["name"] != "GND":
                outs.append(("Net %s  —  %s" % (n["name"], ", ".join(app.pin_name(k) for k in n["pins"][:2])), n["pins"][0]))
        self.outputs = outs
        self.cb_src.configure(values=[n for n, _ in self.sources])
        self.cb_out.configure(values=[n for n, _ in self.outputs])
        if self.v_src.get() not in [n for n, _ in self.sources]:
            self.v_src.set(self.sources[0][0] if self.sources else "")
        if self.v_out.get() not in [n for n, _ in self.outputs]:
            # default: the first measuring point that isn't wired straight to the input source
            pm = app.pin_net_map()
            cid = dict(self.sources).get(self.v_src.get())
            src_nets = set()
            if cid in app.comps:
                src_nets = {pm[(cid, i)]["name"] for i in range(len(app.rdef(app.comps[cid]).pins)) if (cid, i) in pm}
            pick = next((n for n, k in self.outputs if (pm.get(tuple(k)) or {}).get("name") not in src_nets),
                        self.outputs[0][0] if self.outputs else "")
            self.v_out.set(pick)

    def run(self):
        self.refresh_lists()
        if not self.sources:
            messagebox.showinfo(APP_NAME, "Add an AC voltage source (or any voltage source) to feed the circuit, "
                                          "then try again.", parent=self)
            return
        if not self.outputs:
            messagebox.showinfo(APP_NAME, "Wire the circuit up first, then choose where to measure.", parent=self)
            return
        f0, f1 = qty(self.v_f0.get(), "hz"), qty(self.v_f1.get(), "hz")
        if not f0 or not f1 or f0 <= 0 or f1 <= f0:
            messagebox.showwarning(APP_NAME, "Enter a frequency range like 10 Hz to 1 MHz.", parent=self)
            return
        cid = dict(self.sources).get(self.v_src.get())
        key = dict(self.outputs).get(self.v_out.get())
        sim = Sim(self.app)
        if sim.error:
            messagebox.showerror(APP_NAME, sim.error, parent=self)
            return
        src = sim.by_cid.get(cid)
        node = sim.node_of.get(tuple(key)) if key is not None else None
        if src is None or src.br is None or node is None:
            messagebox.showwarning(APP_NAME, "That source or measuring point isn’t part of the simulated circuit.", parent=self)
            return
        n = 241
        freqs = [f0 * (f1 / f0) ** (i / (n - 1.0)) for i in range(n)]
        self.configure(cursor="watch")
        self.update_idletasks()
        try:
            H = sim.ac_sweep(src, node, freqs)
        except SimError as e:
            messagebox.showerror(APP_NAME, str(e), parent=self)
            return
        finally:
            self.configure(cursor="")
        mag, ph = [], []
        prev = None
        for h in H:
            if not (abs(h) == abs(h)) or abs(h) < 1e-15:
                mag.append(float("nan"))
                ph.append(float("nan"))
                continue
            mag.append(20 * math.log10(abs(h)))
            p = math.degrees(math.atan2(h.imag, h.real))
            if prev is not None:
                while p - prev > 180:
                    p -= 360
                while p - prev < -180:
                    p += 360
            prev = p
            ph.append(p)
        self.data = (freqs, mag, ph)
        self._analyse()
        self.draw()

    def _analyse(self):
        f, g, _p = self.data
        good = [i for i in range(len(f)) if math.isfinite(g[i])]
        self.marks = []
        if not good:
            self.info_var.set("No response at this output (it may not be connected to the source).")
            return
        imax = max(good, key=lambda i: g[i])
        gmax = g[imax]
        thr = gmax - 3.0

        def cross(i0, step):
            i = i0
            while 0 <= i + step < len(f):
                j = i + step
                if math.isfinite(g[j]) and g[j] < thr:
                    t = (g[i] - thr) / (g[i] - g[j]) if g[i] != g[j] else 0.0
                    return 10 ** (math.log10(f[i]) + t * (math.log10(f[j]) - math.log10(f[i])))
                i = j
            return None

        flo, fhi = cross(imax, -1), cross(imax, 1)
        if flo and fhi:
            kind = "Band-pass: passes about %s to %s" % (fmt_si(flo, "Hz"), fmt_si(fhi, "Hz"))
        elif fhi:
            kind = "Low-pass: −3 dB cutoff at %s" % fmt_si(fhi, "Hz")
        elif flo:
            kind = "High-pass: −3 dB cutoff at %s" % fmt_si(flo, "Hz")
        else:
            kind = "Flat (within 3 dB) over this range"
        self.marks = [m for m in (flo, fhi) if m]
        gshow = 0.0 if abs(gmax) < 0.05 else gmax
        self.info_var.set("%s     ·     Highest gain %s dB (× %.3g) at %s"
                          % (kind, ("%.1f" % gshow).replace("-", "−"), 10 ** (gmax / 20.0), fmt_si(f[imax], "Hz")))

    def _geom(self):
        W, H = self.cv.winfo_width(), self.cv.winfo_height()
        s = self.app.ui_scale
        x0, x1 = int(64 * s), W - int(18 * s)
        top0, bot1 = int(14 * s), H - int(30 * s)
        gap = int(26 * s)
        h1 = (bot1 - top0 - gap) * 0.58
        return W, H, x0, x1, (top0, top0 + h1), (top0 + h1 + gap, bot1)

    def _x(self, fr, x0, x1):
        f = self.data[0]
        a, b = math.log10(f[0]), math.log10(f[-1])
        return x0 + (math.log10(fr) - a) / (b - a) * (x1 - x0)

    def draw(self):
        cv = self.cv
        cv.delete("all")
        app = self.app
        s = app.ui_scale
        font = (app.fam, -int(10 * s))
        W, H, x0, x1, (a0, a1), (b0, b1) = self._geom()
        if W < 80 or H < 80:
            return
        if not self.data:
            cv.create_text(W / 2, H / 2, text="Choose the input source and where to measure, then press Plot.",
                           fill=C["muted"], font=(app.fam, -int(12 * s)))
            return
        f, g, ph = self.data
        grid, minor = C["bode_grid"], C["bode_minor"]
        for d in range(int(math.floor(math.log10(f[0]))), int(math.ceil(math.log10(f[-1]))) + 1):
            for m in range(1, 10):
                fr = m * 10 ** d
                if f[0] <= fr <= f[-1]:
                    X = self._x(fr, x0, x1)
                    for top, bot in ((a0, a1), (b0, b1)):
                        cv.create_line(X, top, X, bot, fill=grid if m == 1 else minor)
                    if m == 1:
                        cv.create_text(X, b1 + 4, text=fmt_si(fr, "Hz"), anchor="n", fill=C["muted"], font=font)
        for (top, bot), vals, unit, title in (((a0, a1), g, "dB", "Gain (dB)"), ((b0, b1), ph, "°", "Phase (degrees)")):
            fin = [v for v in vals if math.isfinite(v)]
            lo, hi = (min(fin), max(fin)) if fin else (-1.0, 1.0)
            if hi - lo < 1.0:
                lo, hi = lo - 1.0, hi + 1.0
            lo, hi, ticks = _nice_ticks(lo, hi, 5)
            for v in ticks:
                Y = bot - (v - lo) / (hi - lo) * (bot - top)
                cv.create_line(x0, Y, x1, Y, fill=grid)
                cv.create_text(x0 - 6, Y, text=("%g" % round(v, 6)).replace("-", "−"), anchor="e", fill=C["muted"], font=font)
            cv.create_rectangle(x0, top, x1, bot, outline=C["border"])
            cv.create_text(x0 + 6, top + 4, text=title, anchor="nw", fill=C["muted"], font=(app.fam, -int(10 * s), "bold"))
            seg = []
            for fr, v in zip(f, vals):
                if math.isfinite(v):
                    seg += [self._x(fr, x0, x1), bot - (v - lo) / (hi - lo) * (bot - top)]
                else:
                    if len(seg) >= 4:
                        cv.create_line(*seg, fill=C["accent"], width=max(1.5, 2 * s))
                    seg = []
            if len(seg) >= 4:
                cv.create_line(*seg, fill=C["accent"], width=max(1.5, 2 * s))
        for mk in self.marks:
            X = self._x(mk, x0, x1)
            cv.create_line(X, a0, X, b1, fill=C["marker"], dash=(4, 3))
            cv.create_text(X + 4, a1 - 4, text="−3 dB  " + fmt_si(mk, "Hz"), anchor="sw", fill=C["marker"], font=font)
        if self.hover is not None:
            i = self.hover
            X = self._x(f[i], x0, x1)
            cv.create_line(X, a0, X, b1, fill=C["text"], dash=(2, 2))
            txt = "%s   ·   %s dB   ·   %s°" % (fmt_si(f[i], "Hz"),
                                                ("%.2f" % g[i]) if math.isfinite(g[i]) else "—",
                                                ("%.1f" % ph[i]) if math.isfinite(ph[i]) else "—")
            t = cv.create_text(min(X + 8, x1 - 4), a0 + 22 * s, text=txt.replace("-", "−"),
                               anchor="nw" if X + 8 < x1 - 220 * s else "ne", fill=C["tip_fg"], font=font)
            b = cv.bbox(t)
            if b:
                r = cv.create_rectangle(b[0] - 6, b[1] - 3, b[2] + 6, b[3] + 3, fill=C["tip_bg"], outline="")
                cv.tag_lower(r, t)

    def _motion(self, e):
        if not self.data:
            return
        W, H, x0, x1, _a, _b = self._geom()
        if not x0 <= e.x <= x1:
            self._set_hover(None)
            return
        f = self.data[0]
        a, b = math.log10(f[0]), math.log10(f[-1])
        fr = 10 ** (a + (e.x - x0) / float(x1 - x0) * (b - a))
        i = min(range(len(f)), key=lambda k: abs(math.log10(f[k]) - math.log10(fr)))
        self._set_hover(i)

    def _set_hover(self, i):
        if i != self.hover:
            self.hover = i
            self.draw()

    def _export(self):
        if not self.data:
            messagebox.showinfo(APP_NAME, "Press Plot first.", parent=self)
            return
        path = filedialog.asksaveasfilename(parent=self, title="Export frequency response", defaultextension=".csv",
                                            initialfile="frequency_response.csv", filetypes=[("Spreadsheet (CSV)", "*.csv")])
        if not path:
            return
        try:
            with open(path, "w", newline="", encoding="utf-8-sig") as fh:
                wr = csv.writer(fh)
                wr.writerow(["frequency (Hz)", "gain (dB)", "phase (degrees)"])
                for fr, g, p in zip(*self.data):
                    wr.writerow(["%.6g" % fr, "%.4f" % g if math.isfinite(g) else "", "%.3f" % p if math.isfinite(p) else ""])
        except OSError as e:
            messagebox.showerror(APP_NAME, "Could not export:\n%s" % e, parent=self)
            return
        self.app.flash("Frequency response saved to %s" % os.path.basename(path))


# --------------------------------------------------------------------------
def main():
    if os.name == "nt":
        try:
            import ctypes
            try:
                ctypes.windll.shcore.SetProcessDpiAwareness(1)
            except Exception:
                ctypes.windll.user32.SetProcessDPIAware()
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("CircuitBuilder.App.1")
        except Exception:
            pass
    root = tk.Tk()
    try:
        root.tk.call("tk", "scaling", root.winfo_fpixels("1i") / 72.0)
    except tk.TclError:
        pass
    if ICON_PNG_B64:
        try:
            root._icon = tk.PhotoImage(data=ICON_PNG_B64)
            root.iconphoto(True, root._icon)
        except tk.TclError:
            pass
    sc = max(1.0, root.winfo_fpixels("1i") / 96.0)
    sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
    w, h = min(int(1400 * sc), sw - 60), min(int(860 * sc), sh - 100)
    root.geometry("%dx%d+%d+%d" % (w, h, max(0, (sw - w) // 2), max(0, (sh - h) // 3)))
    root.minsize(int(960 * sc), int(600 * sc))
    open_path = sys.argv[1] if len(sys.argv) > 1 and os.path.exists(sys.argv[1]) else None
    try:
        App(root, open_path)
    except Exception:
        # The windowed app has no console, so say what happened instead of just not opening.
        path = log_exception(*sys.exc_info(), context="starting up")
        try:
            messagebox.showerror(APP_NAME, "Circuit Builder couldn’t start.\n\nThe details were saved to:\n%s\n\n"
                                           "Please send that file to your instructor." % path)
        finally:
            root.destroy()
        raise SystemExit(1)
    root.mainloop()


if __name__ == "__main__":
    main()
