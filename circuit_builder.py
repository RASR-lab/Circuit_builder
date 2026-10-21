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
APP_VERSION = "1.3"
FILE_EXT = ".circuit"
LIB_EXT = ".cblib"
G = 24  # pixels per grid unit at 100 % zoom

# --------------------------------------------------------------------------
# Look & feel
# --------------------------------------------------------------------------
C = {
    "bg": "#eef1f5",
    "panel": "#ffffff",
    "border": "#d6dce4",
    "text": "#1f2933",
    "muted": "#6b7785",
    "accent": "#2563eb",
    "accent_dark": "#1d4ed8",
    "accent_light": "#e3ecff",
    "canvas": "#fbfcfd",
    "grid": "#eef1f5",
    "grid_major": "#e0e5ec",
    "stroke": "#26323f",
    "pin_on": "#26323f",
    "pin_off": "#8d99a6",
    "pinlabel": "#3e4a57",
    "danger": "#dc2626",
    "select": "#2563eb",
    "sel_fill": "#eaf1ff",
    "hover": "#f59e0b",
    "highlight": "#fde68a",
    "ok": "#16a34a",
    "ok_dark": "#15803d",
    "warn": "#b45309",
    "sim_bg": "#ecfdf3",
    "sim_border": "#b7e4c7",
    "meter_bg": "#0f172a",
    "meter_fg": "#a7f3d0",
}

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


SYMBOLS = {
    "resistor": sym_resistor, "capacitor": sym_capacitor, "capacitor_pol": sym_capacitor_pol,
    "inductor": sym_inductor, "potentiometer": sym_potentiometer, "ldr": sym_ldr,
    "fuse": sym_fuse, "switch": sym_switch, "pushbutton": sym_pushbutton, "lamp": sym_lamp,
    "motor": sym_motor, "buzzer": sym_buzzer, "voltmeter": sym_voltmeter, "ammeter": sym_ammeter,
    "battery": sym_battery, "dc_source": sym_dc_source, "ac_source": sym_ac_source,
    "square_source": sym_square_source, "probe": sym_probe,
    "current_source": sym_current_source, "ground": sym_ground, "vcc": sym_vcc,
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
                  "Logic Gates", "ICs & Boards", "Modules & Sensors"]


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
    big, small = int(round(11 * z)), int(round(9 * z))
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
            return C["accent_light"] if state == "ghost" else rd.color
        if f == "white":
            return "white"
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
            px = int(round(p.get("size", 11) * z))
            if px < 5:
                continue
            x, y = tp(p["p"])
            cv.create_text(x, y, text=p["s"], fill=stroke, tags=tags,
                           font=(fam, -px, "bold" if p.get("bold") else "normal"))
        elif t == "pintext":
            px = int(round(9 * z))
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
        big, small = int(round(11 * z)), int(round(9 * z))
        if big >= 5:
            top = cv.create_text(cx, cy, text=label or rd.name, anchor="s", fill=stroke,
                                 font=(fam, -big, "bold"), width=wrap, justify="center", tags=tags)
            if label and small >= 5:
                sub = rd.name + (("\n" + value) if value else "")
                cv.create_text(cx, cy + 1, text=sub, anchor="n", fill=C["muted"],
                               font=(fam, -small), width=wrap, justify="center", tags=tags)
            del top
    elif rd.label_pt is not None:
        lines = []
        if rd.label_mode in ("both", "label") and label:
            lines.append(label)
        if rd.label_mode in ("both", "value") and value:
            lines.append(value)
        px = int(round(11 * z))
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
                           fill=C["pin_on"] if on else "white",
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
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def save_json(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    os.replace(tmp, path)


def new_id():
    return uuid.uuid4().hex[:8]


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
        data = load_json(self.path, {})
        for d in data.get("components", []):
            if d.get("id"):
                d["custom"] = True
                self.custom[d["id"]] = d
        self._cache = {}

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

    def save_def(self, d):
        d["custom"] = True
        self.custom[d["id"]] = d
        self._cache.pop(d["id"], None)
        self.persist()

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
        tk.Label(self.tip, text=self.text, bg="#1f2933", fg="white", padx=8, pady=4,
                 font=("Segoe UI", 9)).pack()

    def _leave(self, _e=None):
        if self.job:
            self.widget.after_cancel(self.job)
            self.job = None
        if self.tip:
            self.tip.destroy()
            self.tip = None


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
# Component editor
# --------------------------------------------------------------------------
class ComponentEditor(tk.Toplevel):
    SIDES = ["left", "right", "top", "bottom"]

    def __init__(self, app, d=None, duplicate=False, image=None, use_for=None):
        """image: start with this picture.  use_for: id of a placed part that should switch
        to the saved component (used when adding a picture to a built-in part)."""
        super().__init__(app.root)
        self.app = app
        self.fam = app.fam
        s = app.ui_scale
        self.title("Component Editor — " + APP_NAME)
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
        # a copy of a built-in part keeps that part's simulation model (it is matched by pin names)
        self.sim_model = d.get("sim") or (d.get("id") if (not d.get("custom") and d.get("id") in SIM_MODELS) else None)
        if image is not None:
            d["image"] = image
        if duplicate:
            if image is None:
                d["name"] = d.get("name", "") + " (copy)"
            if not d.get("custom"):
                d["category"] = "My Components"
        self.image = d.get("image") if valid_picture(d.get("image")) else None
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
                rows.append({"kind": "pin", "name": p.get("name", ""), "side": side})
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
        if self.sim_model:
            d["sim"] = self.sim_model
        return d

    # ---- UI ----
    def _build(self, d):
        fam = self.fam
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
                              highlightthickness=1, highlightbackground=C["border"],
                              highlightcolor=C["accent"], padx=6, pady=4)
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
            f = tk.Frame(sw, width=22, height=22, bg=col, highlightthickness=2, cursor="hand2",
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
        self.tree = ttk.Treeview(tf, columns=("n", "name", "side"), show="headings", selectmode="extended")
        self.tree.heading("n", text="#")
        self.tree.heading("name", text="Pin name")
        self.tree.heading("side", text="Side")
        self.tree.column("n", width=40, stretch=False, anchor="center")
        self.tree.column("name", width=160)
        self.tree.column("side", width=80, stretch=False)
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
        if self.sim_model:
            ttk.Label(right, text="Simulates like the built-in part it was copied from, as long as its "
                                  "pin names stay the same.", style="Hint.TLabel",
                      wraplength=int(260 * s), justify="left").pack(anchor="w", pady=(6, 0))

        bar = ttk.Frame(self, style="Bg.TFrame", padding=(12, 0, 12, 12))
        bar.pack(side="bottom", fill="x", before=outer)  # keep the buttons visible on small screens
        ttk.Button(bar, text="Save to library", style="Accent.TButton", command=self._save).pack(side="right")
        ttk.Button(bar, text="Cancel", command=self.destroy).pack(side="right", padx=(0, 8))
        note = None
        if self.edit_id:
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

    def _refresh_rows(self, select=None):
        self.tree.delete(*self.tree.get_children())
        n = 0
        for i, r in enumerate(self.rows):
            if r["kind"] == "pin":
                n += 1
                vals = (n, r["name"], r["side"])
            else:
                vals = ("", "(gap)", r["side"])
            self.tree.insert("", "end", iid=str(i), values=vals, tags=(r["kind"],))
        self.tree.tag_configure("gap", foreground=C["muted"])
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
        d["id"] = self.edit_id or ("custom_" + uuid.uuid4().hex[:10])
        self.app.save_definition(d, use_for=self.use_for)
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
        self.settings = load_json(self.settings_path, {})
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
        self._lib_drag = None
        self._flash_job = None
        self._missing = {}
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

        self._setup_fonts()
        self._setup_style()
        self._build_menu()
        self._build_ui()
        self._bind_keys()
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.update_title()
        self.refresh_props()
        if open_path:
            root.after(100, lambda: self.open_file(open_path))

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
        s.configure(".", background=C["bg"], foreground=C["text"], font=self.f_ui,
                    bordercolor=C["border"], lightcolor=C["panel"], darkcolor=C["border"],
                    troughcolor=C["bg"], focuscolor=C["accent"])
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
        s.configure("TButton", padding=(10, 4), width=0, background="#f6f8fa", bordercolor=C["border"],
                    lightcolor="#f6f8fa", darkcolor="#f6f8fa", relief="flat")
        s.map("TButton", background=[("pressed", C["accent_light"]), ("active", "#edf2fa"), ("disabled", "#f6f8fa")],
              foreground=[("disabled", "#a0a8b2")])
        s.configure("Tool.TButton", padding=(9, 4), width=0, background=C["panel"], lightcolor=C["panel"],
                    darkcolor=C["panel"], bordercolor=C["panel"])
        s.map("Tool.TButton", background=[("pressed", C["accent_light"]), ("active", "#eef2f8")],
              bordercolor=[("active", C["border"])], foreground=[("disabled", "#a7afb9")])
        s.configure("Accent.TButton", background=C["accent"], foreground="white", bordercolor=C["accent"],
                    lightcolor=C["accent"], darkcolor=C["accent"], font=self.f_bold)
        s.map("Accent.TButton", background=[("pressed", C["accent_dark"]), ("active", C["accent_dark"])],
              foreground=[("disabled", "#dfe7f7")])
        s.configure("Sim.TButton", background=C["ok"], foreground="white", bordercolor=C["ok"],
                    lightcolor=C["ok"], darkcolor=C["ok"], font=self.f_bold)
        s.map("Sim.TButton", background=[("pressed", C["ok_dark"]), ("active", C["ok_dark"])])
        s.configure("Stop.TButton", background=C["danger"], foreground="white", bordercolor=C["danger"],
                    lightcolor=C["danger"], darkcolor=C["danger"], font=self.f_bold)
        s.map("Stop.TButton", background=[("pressed", "#b91c1c"), ("active", "#b91c1c")])
        s.configure("SimBar.TButton", padding=(9, 3), width=0, background="white", lightcolor="white",
                    darkcolor="white", bordercolor=C["sim_border"])
        s.map("SimBar.TButton", background=[("pressed", C["accent_light"]), ("active", "#f3faf6")])
        s.configure("Danger.TButton", foreground=C["danger"])
        s.configure("TEntry", fieldbackground="white", padding=4, bordercolor=C["border"],
                    lightcolor="white", darkcolor="white")
        s.map("TEntry", bordercolor=[("focus", C["accent"])], lightcolor=[("focus", C["accent"])])
        s.configure("TCombobox", fieldbackground="white", padding=3, arrowsize=int(12 * sc))
        s.configure("TSpinbox", fieldbackground="white", padding=3, arrowsize=int(10 * sc))
        s.configure("Card.TCheckbutton", background=C["panel"])
        s.map("Card.TCheckbutton", background=[("active", C["panel"])])
        s.configure("Panel.Horizontal.TScale", background=C["panel"], troughcolor="#e6eaf0")
        s.configure("Treeview", background=C["panel"], fieldbackground=C["panel"], borderwidth=0,
                    rowheight=int(22 * sc), font=self.f_ui)
        s.configure("Treeview.Heading", background="#f3f5f8", font=self.f_bold, relief="flat",
                    padding=(6, 3))
        s.map("Treeview", background=[("selected", C["accent_light"])],
              foreground=[("selected", C["text"])])
        s.configure("Lib.Treeview", rowheight=int(24 * sc))
        s.configure("TPanedwindow", background=C["border"])
        s.configure("TSeparator", background=C["border"])
        s.configure("Vertical.TScrollbar", arrowsize=int(12 * sc), background="#e6eaf0",
                    bordercolor=C["bg"], troughcolor=C["bg"], gripcount=0)

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
        m.add_cascade(label="View", menu=vm)

        cm = tk.Menu(m, tearoff=0)
        cm.add_command(label="New component…", command=self.new_component)
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
        nb = ttk.Button(tb, text="+ New Component", style="Accent.TButton", command=self.new_component, takefocus=False)
        nb.pack(side="right")
        Tooltip(nb, "Create your own part with any pins")
        self.b_sim = ttk.Button(tb, text="▶  Simulate", style="Sim.TButton", command=self.sim_toggle, takefocus=False)
        self.b_sim.pack(side="right", padx=(0, 8))
        Tooltip(self.b_sim, "Run the circuit: live voltages and currents (F5)")
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
        self.wire_sw = tk.Frame(tb, width=int(16 * sc), height=int(16 * sc), bg=self.wire_color,
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
                            n = max(n, end[1] + 1)
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
        self.sel = {k for k in self.sel if (k[0] == "c" and k[1] in self.comps) or (k[0] == "w" and k[1] in self.wires)}
        self.changed()

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
            if W <= 1:
                self.request_redraw()
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
                cv.create_line(*cp, fill="#bfd3ff", width=lw * 3.2, capstyle="round", joinstyle="round")
            cv.create_line(*cp, fill=w.get("color", C["accent"]), width=lw, capstyle="round",
                           joinstyle="round", tags=("wire", "w:" + wid))
        for cid, c in self.comps.items():
            render_component(cv, self.rdef(c), c, self.T, z, self.fam,
                             state="selected" if ("c", cid) in self.sel else "normal",
                             connected=connected, cid=cid, show_pin_labels=z >= 0.55,
                             closed=self.is_closed(cid, c))
        for key in hl.get("pins", []):
            if key[0] in self.comps:
                x, y = self.T(*self.pin_world(key))
                r = 7 * z
                cv.create_oval(x - r, y - r, x + r, y + r, outline="#d97706", width=2)
        wsel = [k[1] for k in self.sel if k[0] == "w" and k[1] in self.wires]
        if len(wsel) == 1:
            for b in self.wires[wsel[0]].get("bends", []):
                x, y = self.T(*b)
                r = max(3.5, 4.5 * z)
                cv.create_rectangle(x - r, y - r, x + r, y + r, fill="white", outline=C["select"], width=1.5)
        self._sim_draw()
        self.draw_overlay()
        self.update_counts()

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
                cv.create_line(*cp, fill=self.wire_color, width=max(1.5, 2.4 * z), dash=(6, 4),
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
        t = cv.create_text(x + 14, y - 14, text=txt, anchor="sw", fill="white",
                           font=(self.fam, -int(11 * self.ui_scale)), tags="overlay")
        bx = cv.bbox(t)
        if bx:
            r = cv.create_rectangle(bx[0] - 6, bx[1] - 3, bx[2] + 6, bx[3] + 3, fill="#1f2933",
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

        wired = set()
        for w in self.wires.values():
            a, b = tuple(w["a"]), tuple(w["b"])
            if a[0] in self.comps and b[0] in self.comps:
                union(a, b)
                wired.update((a, b))
        rails = {}
        for cid, c in self.comps.items():
            if c["def"] == "ground" and (cid, 0) in wired:
                rails.setdefault("GND", []).append((cid, 0))
            elif c["def"] == "vcc" and (cid, 0) in wired:
                rails.setdefault("PWR:" + (c.get("value") or "VCC").strip(), []).append((cid, 0))
        for keys in rails.values():
            for k in keys[1:]:
                union(keys[0], k)
        groups = {}
        for k in list(parent):
            groups.setdefault(find(k), []).append(k)
        order = {cid: i for i, cid in enumerate(self.comps)}
        nets = []
        for g in groups.values():
            g.sort(key=lambda k: (order.get(k[0], 0), k[1]))
            nets.append(g)
        nets.sort(key=lambda g: (order.get(g[0][0], 0), g[0][1]))
        out, n, used = [], 1, set()
        for g in nets:
            defs = [self.comps[k[0]]["def"] for k in g]
            name = None
            if "ground" in defs:
                name = "GND"
            else:
                for k in g:
                    c = self.comps[k[0]]
                    if c["def"] == "vcc":
                        name = re.sub(r"\s+", "", c.get("value") or "VCC")
                        break
            if not name:
                name = "N%d" % n
                n += 1
            base, i = name, 2
            while name in used:
                name = "%s_%d" % (base, i)
                i += 1
            used.add(name)
            gs = set(g)
            ws = [wid for wid, w in self.wires.items() if tuple(w["a"]) in gs]
            out.append({"name": name, "pins": g, "wires": ws})
        self._nets_cache = out
        return out

    def pin_net_map(self):
        m = {}
        for net in self.compute_nets():
            for k in net["pins"]:
                m[k] = net
        return m

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
        self.wire_sw.configure(bg=col)
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
            m.add_command(label="New component…", command=self.new_component)
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
                        highlightbackground=C["border"], highlightcolor=C["accent"], padx=6, pady=4)
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
            fr = tk.Frame(sf, width=sz, height=sz, bg=col, cursor="hand2", highlightthickness=2,
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
        if ws:
            self._head("Wire color", 3)
            self._color_swatches(4, ws, None)

    # ------------------------------------------------------------ components (definitions)
    def new_component(self):
        self.commit_props()
        ComponentEditor(self)

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

    def save_definition(self, d, use_for=None):
        """Called by the editor. Adds/updates a custom definition and remaps existing wires.
        use_for: a placed part that should switch to this definition."""
        self.commit_props()
        old = self.library.resolve(d["id"]) if self.library.get(d["id"]) else None
        old_names = [p["name"] for p in old.pins] if old else None
        self.library.save_def(d)
        new = self.library.resolve(d["id"])
        dropped = 0
        users = [cid for cid, c in self.comps.items() if c["def"] == d["id"]]
        if old_names is not None and users:
            self.checkpoint()
            dropped = self._remap_wires(set(users), self._pin_mapping(old_names, new.pins))
            self.changed()
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
        n = 0
        for d in defs or []:
            if not isinstance(d, dict) or not d.get("pins"):
                continue
            d = copy.deepcopy(d)
            if not d.get("id"):
                d["id"] = "custom_" + uuid.uuid4().hex[:10]
            if d["id"] in self.library.builtin:
                continue
            self.library.save_def(d)
            n += 1
        self.populate_library()
        messagebox.showinfo(APP_NAME, "Imported %d component%s." % (n, "" if n == 1 else "s"))

    def export_library(self):
        if not self.library.custom:
            messagebox.showinfo(APP_NAME, "You haven’t created any components yet.\nUse  + New Component  first.")
            return
        path = filedialog.asksaveasfilename(title="Export my components", defaultextension=LIB_EXT,
                                            initialfile="my_components" + LIB_EXT,
                                            filetypes=[("Component library", "*" + LIB_EXT)])
        if not path:
            return
        save_json(path, {"format": "circuit-builder-library", "version": 1,
                         "components": list(self.library.custom.values())})
        self.flash("Exported %d components to %s" % (len(self.library.custom), os.path.basename(path)))

    # ------------------------------------------------------------ files
    def serialize(self):
        used = {c["def"] for c in self.comps.values()}
        defs = [self.library.custom[d] for d in used if d in self.library.custom]
        return {"format": "circuit-builder", "version": 1, "app_version": APP_VERSION,
                "components": list(self.comps.values()), "wires": list(self.wires.values()),
                "definitions": defs,
                "view": {"zoom": self.zoom / self.ui_scale, "panx": self.panx, "pany": self.pany}}

    def load_data(self, data):
        if data.get("format") != "circuit-builder":
            raise ValueError("This is not a Circuit Builder file.")
        self.sim_stop()
        self.scope_traces = []
        if self.scope_win is not None:
            self.scope_win.build_legend()
        added = 0
        for d in data.get("definitions", []):
            if d.get("id") and not self.library.get(d["id"]):
                self.library.save_def(copy.deepcopy(d))
                added += 1
        self.comps = {c["id"]: c for c in data.get("components", [])}
        self.wires = {}
        for w in data.get("wires", []):
            if w["a"][0] in self.comps and w["b"][0] in self.comps:
                w.setdefault("bends", [])
                self.wires[w["id"]] = w
        self._missing = {}
        self.sel = set()
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
        except (ValueError, KeyError, TypeError, IndexError) as e:
            messagebox.showerror(APP_NAME, "Could not open the file:\n%s" % e)
            return
        self.path = path
        self.cancel_mode()
        self.changed()
        self.dirty = False
        self.update_title()
        self.add_recent(path)
        self.root.after(30, self.fit)
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
                "blinker": "Press ▶ Simulate to watch the LED blink about once a second."}
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
            elif n_conn < len(keys):
                free = [rd.pins[i]["name"] for i in range(len(keys)) if (cid, i) not in wired]
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
                                                     "" if len(issues) - warns == 1 else "s"), "#b45309"
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
        tv.tag_configure("Warning", foreground="#b45309")
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
        return [0.0] * (len(self.n) - 1) + [x[self.br]]

    def info(self, x):
        names = ["A", "B"][:len(self.n) - 1]
        ins = ", ".join("%s = %d" % (nm, 1 if self.V(x, i) > 2.5 else 0) for i, nm in enumerate(names))
        vo = self.V(x, len(self.n) - 1)
        return [("Inputs", ins), ("Output Y", "%d  (%s)" % (1 if vo > 2.5 else 0, fmt_si(vo, "V")))]


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
              "reg7805", "tmp36", "relay", "probe", "vcc", "ground"}


def sim_model_of(library, c):
    d = library.get(c["def"])
    if not d:
        return None
    return d.get("sim") or d.get("id")


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
            traceback.print_exc()
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
        nets = app.compute_nets()
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
            for cid, c in app.comps.items():
                pn = {"battery": "−", "dc_source": "−", "ac_source": "2", "square_source": "−",
                      "current_source": "−"}.get(sim_model_of(app.library, c))
                if pn:
                    rd = app.rdef(c)
                    i = next((k for k, p in enumerate(rd.pins) if p["name"] == pn), None)
                    if i is not None and (cid, i) in net_of:
                        ref = net_of[(cid, i)]
                        break
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
        for cid, c in app.comps.items():
            rd = app.rdef(c)
            model = sim_model_of(app.library, c)
            lab = c.get("label") or rd.name
            if model == "ground":
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
                                    "digital modules and parts you made yourself have no simulation model."
                      % ", ".join(unsupported))
        k = self.nn
        for d in self.devs:
            if d.nbr:
                d.br = k
                k += 1
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
            traceback.print_exc()
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

    def add(did, x, y, label, value=None, rot=0):
        d = next(b for b in BUILTIN_DEFS if b["id"] == did)
        cid = "c%d" % (len(comps) + 1)
        comps.append({"id": cid, "def": did, "x": x, "y": y, "rot": rot, "flip": False, "label": label,
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
    self._redraw()
    svg = canvas_to_svg(self.cv)
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
        "7.  Make your own parts with  + New Component : give it a name, list its pins and\n"
        "     choose which side each pin is on. It’s saved in your library for next time.\n"
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
        "•  File › Export image saves an SVG you can put in a lab report.")
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
                        "Your custom components are stored in:\n%s" % (APP_NAME, APP_VERSION, self.library.path))


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
    "color), NPN and PNP transistors, N-MOSFETs, op-amps, logic gates (5 V logic), the 555 timer, the 7805 "
    "regulator, the TMP36 temperature sensor (set the temperature) and the relay module.\n\n"
    "Not simulated\n"
    "Microcontroller boards (Arduino, Pico), digital modules (LCD, ultrasonic sensor, servo), generic ICs and "
    "parts you make yourself. Their pins are left unconnected. A copy of a simulated part (for example one "
    "you gave a picture) still simulates as long as its pin names stay the same.\n\n"
    "Values\n"
    "Each part’s Value box is read: 4.7 kΩ, 100 nF, 10 µF, 1 mH, 9 V, 1 mA, 10 V 60 Hz (peak), "
    "120 V rms 60 Hz, 5 V 1 kHz (square wave), 6 V 1 W (lamp), 6 V 0.2 A (motor), 5.1 V (Zener), "
    "Red / Green / Blue (LED), hFE=200 (transistor gain).\n\n"
    "Models are simplified for learning\n"
    "Transistors use typical values (gain about 150), op-amps have a gain of 200 000 and outputs that stop "
    "about 1.5 V short of their supply rails, logic gates switch at 2.5 V and output 0 V or 5 V. Real parts "
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
        fpx = max(8, int(round(10 * z)))
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
            cross = v.get("cross")
            if cross:
                p = [self.T(*local_to_world(c, rd, px, py)) for px, py in ((bx0, by0), (bx1, by1), (bx0, by1), (bx1, by0))]
                cv.create_line(p[0][0], p[0][1], p[1][0], p[1][1], fill=cross, width=max(2.0, 2.5 * z), tags="sim")
                cv.create_line(p[2][0], p[2][1], p[3][0], p[3][1], fill=cross, width=max(2.0, 2.5 * z), tags="sim")
            if v.get("sound") and int(now * 4) % 2 == 0:
                cv.create_text(X + s * 1.1, Y - s * 1.0, text="♪", fill=C["accent"],
                               font=(self.fam, -max(10, int(17 * z)), "bold"), tags="sim")
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
            fs = (self.fam, -max(8, int(round(9.5 * z))))
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
                col = "#b91c1c" if volt > 0.05 else "#1d4ed8" if volt < -0.05 else C["muted"]
                if best[2]:
                    t = cv.create_text(PX, PY - 5, text=fmt_si(volt, "V"), anchor="s", fill=col, font=fs, tags="sim")
                else:
                    t = cv.create_text(PX + 6, PY, text=fmt_si(volt, "V"), anchor="w", fill=col, font=fs, tags="sim")
                b = cv.bbox(t)
                if b:
                    rr = cv.create_rectangle(b[0] - 3, b[1] - 1, b[2] + 3, b[3] + 1, fill="white",
                                             outline=_mix("#ffffff", col, 0.35), tags="sim")
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
        t = cv.create_text(mx + 16, my + 18, text="\n".join(lines), anchor="nw", fill="white",
                           font=(self.fam, -int(11 * self.ui_scale)), tags="overlay")
        b = cv.bbox(t)
        if b:
            dx = min(0, cv.winfo_width() - 8 - b[2])
            dy = min(0, cv.winfo_height() - 8 - b[3])
            if dx or dy:
                cv.move(t, dx, dy)
                b = cv.bbox(t)
            r = cv.create_rectangle(b[0] - 8, b[1] - 6, b[2] + 8, b[3] + 6, fill="#1f2933", outline="", tags="overlay")
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
            tk.Label(box, text="This part isn’t simulated, so its pins are left unconnected.",
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
            if cid in self.comps:
                lbl.configure(cursor="hand2")
                lbl.bind("<Button-1>", lambda e, c=cid: self._select_comp(c))
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
        self.cv = tk.Canvas(self, bg="white", highlightthickness=1, highlightbackground=C["border"])
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
            tk.Frame(row, width=16, height=4, bg=tr["color"]).pack(side="left", padx=(0, 6))
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
        grid = "#eef1f5"

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
            cv.create_line(x0, Y, x1, Y, fill="#d6dce4" if v == 0 else grid)
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
                    cv.create_line(*coords, fill=tr["color"], width=max(1.5, 2 * s))
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
        self.cv = tk.Canvas(self, bg="white", highlightthickness=1, highlightbackground=C["border"])
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
        grid, minor = "#e6eaf0", "#f3f5f8"
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
            cv.create_line(X, a0, X, b1, fill="#ea580c", dash=(4, 3))
            cv.create_text(X + 4, a1 - 4, text="−3 dB  " + fmt_si(mk, "Hz"), anchor="sw", fill="#ea580c", font=font)
        if self.hover is not None:
            i = self.hover
            X = self._x(f[i], x0, x1)
            cv.create_line(X, a0, X, b1, fill=C["text"], dash=(2, 2))
            txt = "%s   ·   %s dB   ·   %s°" % (fmt_si(f[i], "Hz"),
                                                ("%.2f" % g[i]) if math.isfinite(g[i]) else "—",
                                                ("%.1f" % ph[i]) if math.isfinite(ph[i]) else "—")
            t = cv.create_text(min(X + 8, x1 - 4), a0 + 22 * s, text=txt.replace("-", "−"),
                               anchor="nw" if X + 8 < x1 - 220 * s else "ne", fill="white", font=font)
            b = cv.bbox(t)
            if b:
                r = cv.create_rectangle(b[0] - 6, b[1] - 3, b[2] + 6, b[3] + 3, fill="#1f2933", outline="")
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
    App(root, open_path)
    root.mainloop()


if __name__ == "__main__":
    main()
