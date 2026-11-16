#!/usr/bin/env python3
"""Render the current packaged NetHack Sokoban winning paths as GIF animations.

Standard library only (no Pillow): the script contains a small indexed-colour
canvas, a GIF89a/LZW encoder with an independent decoder used for a
round-trip check, and an indexed PNG writer.

For every map the script

1. reads the board from the pinned ``maps.json`` and cross-checks it against
   the generated ``Maps.lean``;
2. extracts the direction list of the *currently published* witness from the
   Lean sources named in ``WITNESSES`` (it only reads text; Lean is never run);
3. replays that list with a Python transcription of ``Model.lean``
   (eight-direction walking, orthogonal pushing, the two-sided diagonal corner
   rule, rolling-boulder traps, boulders consumed by pits/holes) and requires
   the exact move/push counts, the final state written in the Lean source,
   and the goal ``holes = []``;
4. draws one frame per hero move, extra frames for each cell of a roll and
   for a boulder dropping into a pit/hole, and writes the GIF, QA images and
   ``manifest.json``.

The animation is an illustration.  The proofs are the Lean theorems; a
passing Python replay here is a consistency check, not a proof check.

Usage:  python3 scripts/render_solutions.py [--only soko4-2 ...] [--out DIR]
"""
from __future__ import annotations

import argparse
import glob
import hashlib
import json
import math
import re
import struct
import sys
import zlib
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MAPS_JSON = "lean/validation/sokoban/source/maps.json"
MAPS_LEAN = "lean/NetHack/Sokoban/Maps.lean"
GEN = "lean/NetHack/Sokoban/Generated/"

# The current published witnesses (README "Results" table).  ``anchor`` is a
# (file, literal text) pair that must be present: it is the theorem statement
# tying this path name to these costs.  Historical routes (1-1: 375 and 354
# pushes, 3-2: 147 pushes) are deliberately not listed.
WITNESSES = {
    "soko1-1": dict(
        lower=328, pushes=342, moves=714,
        files=["research/owner1007/Owner1007/Witness11_342.lean"],
        path="path", final="finalState",
        theorem="Owner1007.Witness11_342.solution",
        anchors=[("research/owner1007/Owner1007/Witness11_342.lean",
                  "Trace soko1_1.board soko1_1.initial path finalState 342 714 ∧ Goal finalState"),
                 ("research/owner1007/Owner1007/Interval11_328.lean",
                  "⟨Witness11_342.path,Witness11_342.finalState,714,Witness11_342.solution⟩")]),
    "soko1-2": dict(
        lower=231, pushes=235, moves=578,
        files=[GEN + "Soko12Macro235M578Blocks*.lean", GEN + "Soko12Macro235M578Solution.lean"],
        path="soko1_2Macro235M578Path", final="soko1_2Macro235M578FinalState",
        theorem="NetHack.Sokoban.Generated.soko1_2_macro235_m578_solution",
        anchors=[("lean/Audit/Soko12.lean",
                  "Trace soko1_2.board soko1_2.initial Generated.soko1_2Macro235M578Path Generated.soko1_2Macro235M578FinalState 235 578"),
                 ("research/owner1007/Owner1007/Interval12_231.lean",
                  "⟨Generated.soko1_2Macro235M578Path, Generated.soko1_2Macro235M578FinalState, 578,")]),
    "soko2-1": dict(
        lower=109, pushes=109, moves=475,
        files=[GEN + "Soko21Solution.lean"],
        path="soko2_1CandidatePath", final="soko2_1CandidateFinalState",
        theorem="NetHack.Sokoban.Generated.soko2_1_candidate_trace",
        anchors=[("lean/Audit/Soko21.lean",
                  "Trace soko2_1.board soko2_1.initial Generated.soko2_1CandidatePath Generated.soko2_1CandidateFinalState 109 475")]),
    "soko2-2": dict(
        lower=87, pushes=87, moves=238,
        files=["lean/NetHack/Soko22Witness87/Soko22Macro87M238*.lean"],
        path="soko2_2Macro87M238Path", final="soko2_2Macro87M238FinalState",
        theorem="NetHack.Sokoban.Generated.soko2_2Macro87M238 (Audit.Soko22.witness)",
        anchors=[("lean/Audit/Soko22.lean",
                  "Trace soko2_2.board soko2_2.initial Generated.soko2_2Macro87M238Path Generated.soko2_2Macro87M238FinalState 87 238")]),
    "soko3-1": dict(
        lower=136, pushes=136, moves=270,
        files=["lean/NetHack/Soko31Witness136/Soko31Macro136M270*.lean"],
        path="soko3_1Macro136M270Path", final="soko3_1Macro136M270FinalState",
        theorem="NetHack.Sokoban.Generated.soko3_1Macro136M270 (Audit.Soko31.witness)",
        anchors=[("lean/Audit/Soko31.lean",
                  "Trace soko3_1.board soko3_1.initial Generated.soko3_1Macro136M270Path Generated.soko3_1Macro136M270FinalState 136 270")]),
    "soko3-2": dict(
        lower=141, pushes=141, moves=610,
        files=["research/owner1007/Owner1007/Witness32_141.lean"],
        path="path", final="finalState",
        theorem="Owner1007.Witness32_141.solution",
        anchors=[("research/owner1007/Owner1007/Witness32_141.lean",
                  "Trace soko3_2.board soko3_2.initial path finalState 141 610 ∧ Goal finalState"),
                 ("research/owner1007/Owner1007/Optimal32_141.lean",
                  "⟨Witness32_141.path, Witness32_141.finalState, 610, Witness32_141.solution⟩")]),
    "soko4-1": dict(
        lower=80, pushes=80, moves=299,
        files=[GEN + "Soko41Solution.lean"],
        path="soko4_1CandidatePath", final="soko4_1CandidateFinalState",
        theorem="NetHack.Sokoban.Generated.soko4_1_candidate_trace",
        anchors=[("lean/Audit/Soko41.lean",
                  "Trace soko4_1.board soko4_1.initial Generated.soko4_1CandidatePath Generated.soko4_1CandidateFinalState 80 299")]),
    "soko4-2": dict(
        lower=85, pushes=85, moves=332,
        files=[GEN + "Soko42Solution.lean"],
        path="soko4_2CandidatePath", final="soko4_2CandidateFinalState",
        theorem="NetHack.Sokoban.Generated.soko4_2_candidate_trace",
        anchors=[("lean/Audit/Soko42.lean",
                  "Trace soko4_2.board soko4_2.initial Generated.soko4_2CandidatePath Generated.soko4_2CandidateFinalState 85 332")]),
}


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# --------------------------------------------------------------------------
# Lean source reading (text only)
# --------------------------------------------------------------------------
DIRS = {"north": (0, -1, "N"), "south": (0, 1, "S"), "east": (1, 0, "E"), "west": (-1, 0, "W"),
        "northEast": (1, -1, "NE"), "northWest": (-1, -1, "NW"),
        "southEast": (1, 1, "SE"), "southWest": (-1, 1, "SW")}
DIR_RE = re.compile(r"\.(northEast|northWest|southEast|southWest|north|south|east|west)\b")
DEF_RE = re.compile(
    r"^def\s+(\S+)\s*:\s*(List Dir|State)\s*:=(.*?)(?=^(?:def|theorem|end|namespace|set_option|private|/-)\b|\Z)",
    re.S | re.M)
STATE_RE = re.compile(r"\{\s*player\s*:=\s*(\d+)\s*,\s*boulders\s*:=\s*\[([\d,\s]*)\]\s*,\s*holes\s*:=\s*\[([\d,\s]*)\]\s*\}")


def ints(text: str) -> list[int]:
    return [int(v) for v in re.findall(r"\d+", text)]


def load_witness(cfg: dict):
    """Return (directions, declared final state, [source file records])."""
    paths = []
    for pattern in cfg["files"]:
        found = sorted(glob.glob(str(REPO / pattern)))
        if not found:
            raise SystemExit(f"missing witness source: {pattern}")
        paths += [Path(p) for p in found]
    defs: dict[str, tuple[str, str]] = {}
    for p in paths:
        for name, kind, body in DEF_RE.findall(p.read_text(encoding="utf-8")):
            if name in defs:
                raise SystemExit(f"duplicate definition {name}")
            defs[name] = (kind, body.strip())

    def dirs_of(name: str) -> list[str]:
        kind, body = defs[name]
        assert kind == "List Dir", name
        out: list[str] = []
        for part in body.split("++"):
            part = part.strip()
            if part.startswith("["):
                tokens = DIR_RE.findall(part)
                assert len(tokens) == part.count(".") and part.endswith("]"), name
                out += tokens
            else:
                out += dirs_of(part)
        return out

    def state_of(name: str):
        kind, body = defs[name]
        assert kind == "State", name
        m = STATE_RE.fullmatch(body)
        if not m:
            return state_of(body)
        return int(m.group(1)), ints(m.group(2)), ints(m.group(3))

    records = [{"path": str(p.relative_to(REPO)), "sha256": sha256_file(p)} for p in paths]
    for rel, text in cfg["anchors"]:
        if text not in (REPO / rel).read_text(encoding="utf-8"):
            raise SystemExit(f"anchor statement not found in {rel}: {text}")
        if rel not in [r["path"] for r in records]:
            records.append({"path": rel, "sha256": sha256_file(REPO / rel), "role": "anchor"})
    return dirs_of(cfg["path"]), state_of(cfg["final"]), records


def load_maps():
    source = json.loads((REPO / MAPS_JSON).read_text(encoding="utf-8"))
    lean = (REPO / MAPS_LEAN).read_text(encoding="utf-8")
    maps = {}
    for m in source["maps"]:
        ident = m["id"].replace("-", "_")
        block = re.search(r"^def %s : SourceMap := \{(.*?)(?=^def |\Z)" % ident, lean, re.S | re.M).group(1)

        def field(name, block=block):
            return ints(re.search(name + r" := \[([\d,\s]*)\]", block).group(1))

        board = dict(width=int(re.search(r"width := (\d+)", block).group(1)),
                     height=int(re.search(r"height := (\d+)", block).group(1)),
                     floor=field("floor"), rolling=field("rollingTraps"), doors=field("doors"))
        initial = (int(re.search(r"player := (\d+)", block).group(1)), field("boulders"), field("holes"))
        w = m["width"]
        checks = [
            board["width"] == w, board["height"] == m["height"],
            board["floor"] == m["floorCells"], board["rolling"] == m["rollingCells"],
            sorted(board["doors"]) == sorted(d["x"] + w * d["y"] for d in m["doors"]),
            initial[0] == m["entryCell"], initial[1] == m["boulderCells"],
            sorted(initial[2]) == sorted(m["pitCells"] + m["holeCells"]),
            m["source_sha256"] in block,
            sha256_file(REPO / m["source"]) == m["source_sha256"],
            [r[x] for r in m["rows"] for x in range(w)] is not None and all(len(r) == w for r in m["rows"]),
        ]
        if not all(checks):
            raise SystemExit(f"{m['id']}: maps.json / Maps.lean / dat mismatch {checks}")
        maps[m["id"]] = dict(src=m, board=board, initial=initial)
    return maps


# --------------------------------------------------------------------------
# Python transcription of Model.lean `step` (see lean/NetHack/Sokoban/Model.lean)
# --------------------------------------------------------------------------
class Illegal(Exception):
    pass


class Model:
    def __init__(self, board, initial):
        self.w, self.h = board["width"], board["height"]
        self.floor, self.doors = set(board["floor"]), set(board["doors"])
        self.rolling = set(board["rolling"])
        self.player, self.boulders, self.holes = initial[0], list(initial[1]), list(initial[2])

    def advance(self, cell, d):
        if self.w == 0 or cell >= self.w * self.h:
            return None
        x, y = cell % self.w + DIRS[d][0], cell // self.w + DIRS[d][1]
        return x + self.w * y if 0 <= x < self.w and 0 <= y < self.h else None

    def blocked(self, cell):
        return (cell not in self.floor and cell not in self.doors) or cell in self.boulders

    def side_blocked(self, d):
        cell = self.advance(self.player, d)
        return True if cell is None else self.blocked(cell)

    def corner_blocked(self, d):
        dx, dy, _ = DIRS[d]
        if not (dx and dy):
            return False
        return self.side_blocked("north" if dy < 0 else "south") and self.side_blocked("east" if dx > 0 else "west")

    def step(self, d):
        """Apply one direction.  Returns an event dict; raises Illegal."""
        p = self.player
        if p not in self.floor or p in self.doors or p in self.boulders or p in self.holes:
            raise Illegal("standingAllowed")
        if not self.holes:
            raise Illegal("goal already reached")
        target = self.advance(p, d)
        if target is None or target not in self.floor or target in self.doors or self.corner_blocked(d):
            raise Illegal("target/corner")
        if target not in self.boulders:
            if target in self.holes:
                raise Illegal("walk into open pit/hole")
            self.player = target
            return dict(pushed=False, hero=target)
        # pushBoulder
        dx, dy, _ = DIRS[d]
        if dx and dy:
            raise Illegal("diagonal push")
        opposite = {"north": "south", "south": "north", "east": "west", "west": "east"}[d]
        behind = self.advance(target, opposite)
        if behind is None or behind not in self.floor or behind in self.doors:
            raise Illegal("behind")
        dest = self.advance(target, d)
        if dest is None or dest not in self.floor or dest in self.doors or dest in self.boulders:
            raise Illegal("destination")
        remaining = list(self.boulders)
        remaining.remove(target)
        travel, filled, rolled = [dest], None, False
        if dest in self.holes:
            filled = dest
        elif dest in self.rolling:
            rolled, current, travel = True, target, []
            for _ in range(self.w * self.h + 1):
                nxt = self.advance(current, d)
                if nxt is None or (nxt not in self.doors and nxt not in self.floor):
                    break
                if nxt in self.doors or nxt in remaining:
                    raise Illegal("roll collision")
                travel.append(nxt)
                if nxt in self.holes:
                    filled = nxt
                    break
                current = nxt
            else:
                raise Illegal("fuel")
            if filled is None:
                remaining.insert(0, current)
        else:
            remaining.insert(0, dest)
        if filled is not None:
            self.holes.remove(filled)
        self.boulders, self.player = remaining, target
        return dict(pushed=True, hero=target, source=target, travel=travel, filled=filled, rolled=rolled)


# --------------------------------------------------------------------------
# Palette, font, canvas
# --------------------------------------------------------------------------
PALETTE = [
    ("void", "12141c"), ("floor_a", "2c3142"), ("floor_b", "31374a"), ("floor_line", "262a39"), ("speck", "3a4157"),
    ("wall_top", "6f7896"), ("wall_hi", "949ebd"), ("wall_front", "454c66"), ("wall_dark", "2e3347"),
    ("b_out", "24170d"), ("b_dark", "80603c"), ("b_mid", "ad8751"), ("b_light", "d3ae73"), ("b_spec", "f6e4bb"),
    ("shadow", "1c2030"),
    ("hole_rim", "a278f5"), ("hole_rim2", "5b3aa6"), ("hole_in", "050509"), ("hole_in2", "1a1130"),
    ("pit_rim", "c98f47"), ("pit_rim2", "7b5527"), ("pit_in", "20160d"), ("pit_in2", "0c0805"),
    ("fill_stone", "6f6858"), ("fill_stone2", "514b40"), ("fill_edge", "938a75"),
    ("green", "5fe08f"), ("green_dark", "17643a"),
    ("trap", "ff8a3d"), ("trap_dark", "b4521c"),
    ("stair_1", "dde2f0"), ("stair_2", "aeb5cb"), ("stair_3", "828aa2"), ("stair_4", "5a617a"),
    ("door", "a56c38"), ("door_dark", "6b4320"), ("gold", "ffd34d"),
    ("h_out", "090b12"), ("h_skin", "f8d2a8"), ("h_hat", "ff5a5f"), ("h_tunic", "35c9ff"),
    ("h_tunic2", "1c86c6"), ("h_boot", "eef1fa"),
    ("text", "eef1fa"), ("dim", "9aa2bf"), ("hud_bg", "1b1e2b"), ("bar_bg", "2f3449"), ("accent", "ffd34d"),
]
C = {name: i for i, (name, _) in enumerate(PALETTE)}
TRANSPARENT = 63
PALETTE_BYTES = b"".join(bytes.fromhex(h) for _, h in PALETTE).ljust(64 * 3, b"\0")
NOT_T = re.compile(b"[^\x3f]+")

FONT_SRC = """
A .###. #...# #...# ##### #...# #...# #...#
B ####. #...# #...# ####. #...# #...# ####.
C .###. #...# #.... #.... #.... #...# .###.
D ####. #...# #...# #...# #...# #...# ####.
E ##### #.... #.... ####. #.... #.... #####
F ##### #.... #.... ####. #.... #.... #....
G .###. #...# #.... #.### #...# #...# .###.
H #...# #...# #...# ##### #...# #...# #...#
I .###. ..#.. ..#.. ..#.. ..#.. ..#.. .###.
J ..### ...#. ...#. ...#. ...#. #..#. .##..
K #...# #..#. #.#.. ##... #.#.. #..#. #...#
L #.... #.... #.... #.... #.... #.... #####
M #...# ##.## #.#.# #.#.# #...# #...# #...#
N #...# ##..# #.#.# #..## #...# #...# #...#
O .###. #...# #...# #...# #...# #...# .###.
P ####. #...# #...# ####. #.... #.... #....
Q .###. #...# #...# #...# #.#.# #..#. .##.#
R ####. #...# #...# ####. #.#.. #..#. #...#
S .#### #.... #.... .###. ....# ....# ####.
T ##### ..#.. ..#.. ..#.. ..#.. ..#.. ..#..
U #...# #...# #...# #...# #...# #...# .###.
V #...# #...# #...# #...# #...# .#.#. ..#..
W #...# #...# #...# #.#.# #.#.# ##.## #...#
X #...# #...# .#.#. ..#.. .#.#. #...# #...#
Y #...# #...# .#.#. ..#.. ..#.. ..#.. ..#..
Z ##### ....# ...#. ..#.. .#... #.... #####
0 .###. #...# #..## #.#.# ##..# #...# .###.
1 ..#.. .##.. ..#.. ..#.. ..#.. ..#.. .###.
2 .###. #...# ....# ...#. ..#.. .#... #####
3 ####. ....# ....# .###. ....# ....# ####.
4 ...#. ..##. .#.#. #..#. ##### ...#. ...#.
5 ##### #.... ####. ....# ....# #...# .###.
6 .###. #.... #.... ####. #...# #...# .###.
7 ##### ....# ...#. ..#.. .#... .#... .#...
8 .###. #...# #...# .###. #...# #...# .###.
9 .###. #...# #...# .#### ....# ....# .###.
- ..... ..... ..... ##### ..... ..... .....
/ ....# ....# ...#. ..#.. .#... #.... #....
: ..... ..#.. ..... ..... ..... ..#.. .....
. ..... ..... ..... ..... ..... .##.. .##..
= ..... ..... ##### ..... ##### ..... .....
< ...#. ..#.. .#... #.... .#... ..#.. ...#.
"""
FONT = {line[0]: line[2:].split() for line in FONT_SRC.strip().splitlines()}
FONT[" "] = ["....."] * 7


class Canvas:
    def __init__(self, w, h, fill):
        self.w, self.h = w, h
        self.buf = bytearray([fill]) * (w * h)
        self.dirty: list[tuple[int, int, int, int]] = []

    def rect(self, x, y, w, h, color):
        row = bytes([color]) * w
        for yy in range(y, y + h):
            self.buf[yy * self.w + x: yy * self.w + x + w] = row
        self.dirty.append((x, y, w, h))

    def blit(self, x, y, rows):
        for i, row in enumerate(rows):
            o = (y + i) * self.w + x
            self.buf[o:o + len(row)] = row
        self.dirty.append((x, y, len(rows[0]), len(rows)))

    def text(self, x, y, s, color, scale=2):
        for ch in s:
            for gy, grow in enumerate(FONT[ch]):
                for gx, bit in enumerate(grow):
                    if bit == "#":
                        o = x + gx * scale
                        for yy in range(y + gy * scale, y + (gy + 1) * scale):
                            self.buf[yy * self.w + o: yy * self.w + o + scale] = bytes([color]) * scale
            x += 6 * scale
        self.dirty.append((x - 6 * scale * len(s), y, 6 * scale * len(s), 7 * scale))
        return x

    def snapshot(self):
        return bytes(self.buf)


def text_width(s, scale=2):
    return 6 * scale * len(s) - scale


# --------------------------------------------------------------------------
# Procedural sprites (T x T tiles of palette indices; None = transparent)
# --------------------------------------------------------------------------
T = 24
MID = (T - 1) / 2


def grid(fill=None):
    return [[fill] * T for _ in range(T)]


def over(base, top):
    return [[t if t is not None else b for b, t in zip(br, tr)] for br, tr in zip(base, top)]


def tile_floor(parity):
    g = grid(C["floor_a"] if parity else C["floor_b"])
    for i in range(T):
        g[T - 1][i] = g[i][T - 1] = C["floor_line"]
    for x, y in ((5, 7), (16, 13), (9, 18), (19, 4)):
        g[y][x] = C["speck"]
    return g


def tile_void():
    return grid(C["void"])


def tile_wall(front):
    g = grid(C["wall_top"])
    for i in range(T):
        g[0][i] = g[i][0] = C["wall_hi"]
        g[i][T - 1] = C["wall_dark"]
        g[T - 1][i] = C["wall_dark"]
    if front:
        for y in range(15, T):
            for x in range(T):
                g[y][x] = C["wall_front"]
        for x in range(T):
            g[15][x] = g[19][x] = g[T - 1][x] = C["wall_dark"]
        for y in range(16, 19):
            g[y][6] = g[y][18] = C["wall_dark"]
        for y in range(20, T):
            g[y][12] = g[y][0] = C["wall_dark"]
    return g


def tile_door():
    g = tile_wall(False)
    for y in range(2, T - 1):
        for x in range(4, 20):
            g[y][x] = C["door_dark"] if x in (4, 9, 14, 19) or y == 2 else C["door"]
    for y in range(11, 14):
        for x in range(15, 18):
            g[y][x] = C["gold"]
    return g


def rounded(x, y, inset, r):
    lo, hi = inset + r, T - 1 - inset - r
    cx, cy = min(max(x, lo), hi), min(max(y, lo), hi)
    return math.hypot(x - cx, y - cy) <= r + 0.2


def tile_hole(parity):
    g = tile_floor(parity)
    for y in range(T):
        for x in range(T):
            if rounded(x, y, 5, 3):
                g[y][x] = C["hole_in2"] if y < 9 else C["hole_in"]
            elif rounded(x, y, 4, 3):
                g[y][x] = C["hole_rim2"]
            elif rounded(x, y, 2, 4):
                g[y][x] = C["hole_rim"]
    return g


def tile_pit(parity):
    g = tile_floor(parity)
    for y in range(T):
        for x in range(T):
            d = math.hypot(x - MID, y - MID)
            if d <= 4.6 and math.hypot(x - MID, y - MID - 1.5) <= 4.6:
                g[y][x] = C["pit_in2"]
            elif d <= 7.0:
                g[y][x] = C["pit_in"]
            elif d <= 8.3:
                g[y][x] = C["pit_rim2"]
            elif d <= 10.0:
                g[y][x] = C["pit_rim"]
    return g


def tile_filled(parity, flash):
    g = tile_floor(parity)
    for y in range(T):
        for x in range(T):
            d = math.hypot(x - MID, y - MID)
            if d <= 8.0:
                g[y][x] = C["fill_stone"]
            elif d <= 9.3:
                g[y][x] = C["fill_edge"]
            elif flash and d <= 11.6:
                g[y][x] = C["green"]
    for x, y in ((6, 9), (7, 10), (7, 11), (16, 15), (17, 16), (15, 6), (16, 6), (9, 17), (10, 17)):
        g[y][x] = C["fill_stone2"]
    # check mark
    pts = [(7 + i, 12 + i) for i in range(4)] + [(10 + i, 15 - i) for i in range(8)]
    for x, y in pts:
        for dy in (-1, 0, 1, 2):
            g[y + dy][x] = C["green_dark"] if dy in (-1, 2) else C["green"]
    return g


def tile_trap(parity):
    g = tile_floor(parity)
    for y in range(T):
        for x in range(T):
            d = math.hypot(x - MID, y - MID)
            if 7.0 <= d <= 9.2:
                if abs(x - MID) < 1.6 or abs(y - MID) < 1.6:
                    continue
                g[y][x] = C["trap"] if y < 14 else C["trap_dark"]
            elif d <= 3.0:
                g[y][x] = C["trap"] if d <= 2.0 else C["trap_dark"]
    return g


def tile_stairs(parity, down):
    g = tile_floor(parity)
    shades = [C["stair_1"], C["stair_2"], C["stair_3"], C["stair_4"]]
    if not down:
        shades.reverse()
    for band in range(4):
        for y in range(3 + band * 4 + (1 if band else 0), 3 + band * 4 + 4 + (1 if band == 3 else 0) + 1):
            for x in range(3, 21):
                g[min(y, 20)][x] = shades[band]
    for band in range(1, 4):
        for x in range(3, 21):
            g[3 + band * 4 + 1][x] = C["wall_dark"]
    return g


def sprite_boulder():
    g = grid()
    cx, cy, r = MID, 10.8, 9.4
    for y in range(T):
        for x in range(T):
            d = math.hypot(x - cx, y - cy)
            if d <= r:
                if d > r - 1.25:
                    g[y][x] = C["b_out"]
                else:
                    t = ((x - cx) * -0.62 + (y - cy) * -0.72) / r
                    g[y][x] = C["b_light"] if t > 0.42 else C["b_mid"] if t > -0.18 else C["b_dark"]
                    if math.hypot(x - 8.0, y - 6.8) <= 1.5:
                        g[y][x] = C["b_spec"]
            elif ((x - cx) / 9.5) ** 2 + ((y - 20.3) / 2.6) ** 2 <= 1:
                g[y][x] = C["shadow"]
    for x, y in ((14, 12), (15, 12), (14, 13), (9, 15), (10, 15), (16, 7)):
        g[y][x] = C["b_dark"] if g[y][x] != C["b_dark"] else C["b_out"]
    return g


def sprite_drop():
    g = grid()
    for y in range(T):
        for x in range(T):
            d = math.hypot(x - MID, y - MID - 0.5)
            if d <= 5.6:
                g[y][x] = C["b_out"] if d > 4.5 else C["b_mid"] if (x + y) < 21 else C["b_dark"]
    return g


HERO_ART = """
....HHHH....
...HHHHHH...
..HHHHHHHH..
...SKSSKS...
...SSSSSS...
..TTTTTTTT..
.STTTGGTTTS.
.STTTTTTTTS.
..UTTTTTTU..
...UUUUUU...
...BB..BB...
..BBB..BBB..
"""


def sprite_hero(brackets=True):
    key = {"H": "h_hat", "S": "h_skin", "K": "h_out", "T": "h_tunic", "G": "gold", "U": "h_tunic2", "B": "h_boot"}
    g = grid()
    for y, row in enumerate(HERO_ART.strip().splitlines()):
        for x, ch in enumerate(row):
            if ch != ".":
                for dy in (0, 1):
                    for dx in (0, 1):
                        g[y * 2 + dy][x * 2 + dx] = C[key[ch]]
    out = [row[:] for row in g]
    for y in range(T):
        for x in range(T):
            if g[y][x] is None and any(
                    0 <= y + dy < T and 0 <= x + dx < T and g[y + dy][x + dx] is not None
                    for dy in (-1, 0, 1) for dx in (-1, 0, 1)):
                out[y][x] = C["h_out"]
    if brackets:
        for i in range(6):
            for j in range(2):
                for a, b in ((i, j), (j, i)):
                    for fx in (a, T - 1 - a):
                        for fy in (b, T - 1 - b):
                            if out[fy][fx] is None:
                                out[fy][fx] = C["accent"]
    return out


def to_rows(g):
    return [bytes(row) for row in g]


# --------------------------------------------------------------------------
# GIF / PNG
# --------------------------------------------------------------------------
def lzw_encode(data: bytes, mcs: int = 6) -> bytes:
    """GIF LZW.  Runs of the transparent index advance one code at a time."""
    n, clear, eoi = len(data), 1 << mcs, (1 << mcs) + 1
    out = bytearray()
    size, nxt = mcs + 1, eoi + 1
    acc, nb = clear, size
    table: dict[int, int] = {}
    chain = [TRANSPARENT]            # chain[k] is the code for k+1 transparent pixels

    def emit(code):
        nonlocal acc, nb
        acc |= code << nb
        nb += size
        while nb >= 8:
            out.append(acc & 255)
            acc >>= 8
            nb -= 8

    def add(key, extends_chain):
        nonlocal size, nxt
        if nxt < 4096:
            table[key] = nxt
            if extends_chain:
                chain.append(nxt)
            if nxt == (1 << size):
                size += 1
            nxt += 1
        else:
            emit(clear)
            table.clear()
            del chain[1:]
            size, nxt = mcs + 1, eoi + 1

    cur, i = data[0], 1
    while i < n:
        p = data[i]
        key = (cur << 8) | p
        hit = table.get(key)
        if hit is not None:
            cur = hit
            i += 1
            continue
        emit(cur)
        add(key, p == TRANSPARENT and cur == chain[-1])
        cur = p
        i += 1
        if p != TRANSPARENT:
            continue
        # cur is a single transparent pixel; skip through the rest of its run
        m = NOT_T.search(data, i)
        run = (m.start() if m else n) - i
        while run:
            known = len(chain)
            if run < known:
                cur = chain[run]
                i += run
                break
            cur = chain[-1]
            emit(cur)
            add((cur << 8) | TRANSPARENT, True)
            cur = TRANSPARENT
            i += known
            run -= known
    emit(cur)
    emit(eoi)
    if nb:
        out.append(acc & 255)
    return bytes(out)


def lzw_decode(data: bytes, mcs: int) -> bytes:
    clear, eoi = 1 << mcs, (1 << mcs) + 1
    base = [bytes([i]) for i in range(clear)] + [b"", b""]
    table, size, out, prev = list(base), mcs + 1, bytearray(), None
    acc = nb = 0
    for byte in data:
        acc |= byte << nb
        nb += 8
        while nb >= size:
            code = acc & ((1 << size) - 1)
            acc >>= size
            nb -= size
            if code == clear:
                table, size, prev = list(base), mcs + 1, None
                continue
            if code == eoi:
                return bytes(out)
            if prev is None:
                entry = table[code]
            else:
                entry = table[code] if code < len(table) else prev + prev[:1]
                if len(table) < 4096:
                    table.append(prev + entry[:1])
            out += entry
            prev = entry
            if len(table) == (1 << size) and size < 12:
                size += 1
    raise ValueError("GIF LZW stream without end code")


class GifWriter:
    def __init__(self, canvas: Canvas):
        self.cv = canvas
        self.frames: list[list] = []      # [delay_cs, x, y, w, h, lzw]
        self.hashes: list[bytes] = []

    def frame(self, delay):
        cv = self.cv
        if not self.frames:
            x0, y0, x1, y1 = 0, 0, cv.w, cv.h
            data = bytes(cv.buf)
        else:
            if not cv.dirty:
                self.frames[-1][0] += delay
                return
            x0 = min(r[0] for r in cv.dirty)
            y0 = min(r[1] for r in cv.dirty)
            x1 = max(r[0] + r[2] for r in cv.dirty)
            y1 = max(r[1] + r[3] for r in cv.dirty)
            w = x1 - x0
            sub = bytearray([TRANSPARENT]) * (w * (y1 - y0))
            for rx, ry, rw, rh in cv.dirty:
                for yy in range(ry, ry + rh):
                    o = (yy - y0) * w + rx - x0
                    sub[o:o + rw] = cv.buf[yy * cv.w + rx: yy * cv.w + rx + rw]
            data = bytes(sub)
        cv.dirty = []
        self.frames.append([delay, x0, y0, x1 - x0, y1 - y0, lzw_encode(data)])
        self.hashes.append(hashlib.blake2b(cv.buf, digest_size=8).digest())

    def hold(self, delay):
        self.frames[-1][0] += delay

    def to_bytes(self) -> bytes:
        cv = self.cv
        out = bytearray(b"GIF89a" + struct.pack("<HHBBB", cv.w, cv.h, 0xF5, 0, 0) + PALETTE_BYTES)
        out += b"\x21\xff\x0bNETSCAPE2.0\x03\x01\x00\x00\x00"
        for delay, x, y, w, h, lzw in self.frames:
            out += b"\x21\xf9\x04" + struct.pack("<BHBB", 0x05, delay, TRANSPARENT, 0)
            out += b"\x2c" + struct.pack("<HHHHB", x, y, w, h, 0) + b"\x06"
            for i in range(0, len(lzw), 255):
                chunk = lzw[i:i + 255]
                out += bytes([len(chunk)]) + chunk
            out += b"\x00"
        out += b"\x3b"
        return bytes(out)


def verify_gif(blob: bytes, hashes: list[bytes]) -> tuple[int, int]:
    """Decode a GIF written above with the independent decoder and compare
    every composited frame with the canvas hash recorded while rendering."""
    assert blob[:6] == b"GIF89a"
    w, h, packed = struct.unpack("<HHB", blob[6:11])
    pos = 13 + 3 * (1 << ((packed & 7) + 1))
    screen = bytearray(w * h)
    count = total = 0
    delay, transparent = 0, None
    while True:
        tag = blob[pos]
        if tag == 0x3B:
            break
        if tag == 0x21:
            label = blob[pos + 1]
            pos += 2
            if label == 0xF9:
                flags, delay, tindex = struct.unpack("<BHB", blob[pos + 1:pos + 5])
                transparent = tindex if flags & 1 else None
            while blob[pos]:
                pos += blob[pos] + 1
            pos += 1
            continue
        assert tag == 0x2C
        fx, fy, fw, fh, flags = struct.unpack("<HHHHB", blob[pos + 1:pos + 10])
        assert flags == 0
        mcs = blob[pos + 10]
        pos += 11
        data = bytearray()
        while blob[pos]:
            data += blob[pos + 1:pos + 1 + blob[pos]]
            pos += blob[pos] + 1
        pos += 1
        pixels = lzw_decode(bytes(data), mcs)
        assert len(pixels) == fw * fh, (len(pixels), fw, fh)
        for row in range(fh):
            seg = pixels[row * fw:(row + 1) * fw]
            o = (fy + row) * w + fx
            if transparent is None:
                screen[o:o + fw] = seg
            else:
                for m in NOT_T.finditer(seg):
                    screen[o + m.start():o + m.end()] = m.group()
        if hashlib.blake2b(screen, digest_size=8).digest() != hashes[count]:
            raise SystemExit(f"GIF round-trip mismatch at frame {count}")
        count += 1
        total += delay
    assert count == len(hashes)
    return count, total


def write_png(path: Path, w: int, h: int, pixels: bytes):
    def chunk(kind, body):
        return struct.pack(">I", len(body)) + kind + body + struct.pack(">I", zlib.crc32(kind + body))
    raw = b"".join(b"\0" + pixels[y * w:(y + 1) * w] for y in range(h))
    path.write_bytes(b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 3, 0, 0, 0))
                     + chunk(b"PLTE", PALETTE_BYTES) + chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b""))


def tile_images(images, columns, gap=8):
    """images: list of (w, h, bytes).  Returns one (w, h, bytes) sheet."""
    rows = [images[i:i + columns] for i in range(0, len(images), columns)]
    cw = max(w for w, _, _ in images)
    heights = [max(h for _, h, _ in row) for row in rows]
    W = columns * cw + (columns + 1) * gap
    H = sum(heights) + (len(rows) + 1) * gap
    sheet = bytearray([C["void"]]) * (W * H)
    y = gap
    for row, rh in zip(rows, heights):
        for i, (w, h, px) in enumerate(row):
            x = gap + i * (cw + gap) + (cw - w) // 2
            for yy in range(h):
                o = (y + yy) * W + x
                sheet[o:o + w] = px[yy * w:(yy + 1) * w]
        y += rh + gap
    return W, H, bytes(sheet)


# --------------------------------------------------------------------------
# Scene
# --------------------------------------------------------------------------
MARGIN, TOP, MIN_W = 12, 76, 600
WALK_CS, PUSH_CS, ROLL_CS, DROP_CS, FLASH_CS = 9, 12, 5, 7, 9
START_HOLD_CS, END_HOLD_CS = 150, 500


class Scene:
    def __init__(self, ident, m, cfg):
        self.id, self.src, self.cfg = ident, m["src"], cfg
        src = self.src
        self.cols, self.rows = src["width"], src["height"]
        self.pits = set(src["pitCells"])
        self.kind = "PIT" if self.pits else "HOLE"
        self.stairs = {s["x"] + self.cols * s["y"]: s["direction"] == "down" for s in src["stairs"]}
        self.rolling = set(src["rollingCells"])
        self.doors = {d["x"] + self.cols * d["y"] for d in src["doors"]}
        self.floor = set(src["floorCells"])
        self.total_fill = len(src["pitCells"]) + len(src["holeCells"])
        self.hero, self.boulders = m["initial"][0], set(m["initial"][1])
        self.open, self.filled = set(m["initial"][2]), set()
        self.flash, self.drop = set(), None
        self.moves = self.pushes = 0
        map_w = self.cols * T
        self.W = max(map_w + 2 * MARGIN, MIN_W)
        self.map_x, self.map_y = (self.W - map_w) // 2, TOP
        self.legend_y = self.map_y + self.rows * T + 10
        self.legend = self.legend_items()
        self.H = self.legend_y + self.layout_legend(None) + 8
        self.cv = Canvas(self.W, self.H, C["void"])
        self.cache: dict[tuple, list[bytes]] = {}
        self.sprites = dict(boulder=sprite_boulder(), drop=sprite_drop(), hero=sprite_hero())
        self.draw_static()

    # ---- tiles ----
    def base(self, cell):
        x, y = cell % self.cols, cell // self.cols
        ch = self.src["rows"][y][x]
        par = (x + y) & 1
        if cell in self.doors:
            return ("door",)
        if cell in self.floor:
            if cell in self.open:
                return ("pit" if cell in self.pits else "hole", par)
            if cell in self.filled:
                return ("filled", par, cell in self.flash)
            if cell in self.rolling:
                return ("trap", par)
            if cell in self.stairs:
                return ("stairs", par, self.stairs[cell])
            return ("floor", par)
        if ch in "|-":
            below = self.src["rows"][y + 1][x] if y + 1 < self.rows else " "
            return ("wall", below not in "|-")
        if ch == ".":
            return ("floor", par)
        return ("void",)

    def base_grid(self, key):
        name = key[0]
        return {"door": tile_door, "pit": tile_pit, "hole": tile_hole, "filled": tile_filled, "trap": tile_trap,
                "stairs": tile_stairs, "floor": tile_floor, "wall": tile_wall, "void": tile_void}[name](*key[1:])

    def draw_cell(self, cell):
        key = (self.base(cell), cell == self.drop, cell in self.boulders, cell == self.hero)
        rows = self.cache.get(key)
        if rows is None:
            g = self.base_grid(key[0])
            for flag, name in zip(key[1:], ("drop", "boulder", "hero")):
                if flag:
                    g = over(g, self.sprites[name])
            rows = self.cache[key] = to_rows(g)
        self.cv.blit(self.map_x + (cell % self.cols) * T, self.map_y + (cell // self.cols) * T, rows)

    # ---- HUD ----
    def legend_items(self):
        f = tile_floor(1)
        items = [(over(f, sprite_hero(False)), "HERO"), (over(f, sprite_boulder()), "BOULDER"),
                 (tile_pit(1) if self.pits else tile_hole(1), self.kind), (tile_filled(1, False), "FILLED"),
                 (tile_trap(1), "ROLLING TRAP"), (tile_stairs(1, True), "STAIRS")]
        if self.doors:
            items.append((tile_door(), "DOOR"))
        return items

    def layout_legend(self, draw):
        """Flow layout; returns the height used.  draw(x, y, grid, label)."""
        x, y = MARGIN, 0
        for g, label in self.legend:
            w = T + 6 + text_width(label) + 18
            if x + w - 18 > self.W - MARGIN:
                x, y = MARGIN, y + T + 6
            if draw:
                draw(x, y, g, label)
            x += w
        return y + T

    def draw_static(self):
        cv, cfg = self.cv, self.cfg
        cv.rect(0, 0, self.W, TOP - 8, C["hud_bg"])
        cv.text(MARGIN, 9, self.id.upper().replace("SOKO", "SOKO "), C["accent"], 3)
        if cfg["lower"] == cfg["pushes"]:
            tag, color = f"PROVED MINIMUM: P = {cfg['pushes']}", C["green"]
        else:
            tag, color = f"BEST KNOWN: {cfg['lower']} <= P <= {cfg['pushes']}", C["text"]
        cv.text(self.W - MARGIN - text_width(tag), 13, tag, color, 2)
        # counters: label + value fields
        fields = [("PUSHES", 3, cfg["pushes"]), ("MOVES", 3, cfg["moves"]), (self.kind + "S", 2, self.total_fill)]
        widths = [text_width(f"{lab} {'0' * dig}/{tot}") for lab, dig, tot in fields]
        gap = (self.W - 2 * MARGIN - sum(widths)) // 2
        self.value_pos = []
        x = MARGIN
        for (lab, dig, tot), w in zip(fields, widths):
            vx = cv.text(x, 38, lab + " ", C["dim"], 2)
            self.value_pos.append((vx, dig))
            cv.text(vx + 12 * dig, 38, f"/{tot}", C["dim"], 2)
            x += w + gap
        self.shown = [None, None, None]
        self.bar = (MARGIN, 58, self.W - 2 * MARGIN, 6)
        cv.rect(*self.bar, C["bar_bg"])
        self.bar_px = 0
        cv.rect(0, self.legend_y - 4, self.W, self.H - self.legend_y + 4, C["hud_bg"])

        def draw(x, y, g, label):
            cv.blit(x, self.legend_y + y, to_rows(g))
            cv.text(x + T + 6, self.legend_y + y + 5, label, C["dim"], 2)
        self.layout_legend(draw)
        for cell in range(self.cols * self.rows):
            self.draw_cell(cell)
        self.update_hud()

    def update_hud(self, done=False):
        cv = self.cv
        values = [self.pushes, self.moves, len(self.filled)]
        for i, ((vx, dig), value) in enumerate(zip(self.value_pos, values)):
            if self.shown[i] != (value, done):
                cv.rect(vx, 38, 12 * dig, 14, C["hud_bg"])
                cv.text(vx, 38, f"{value:>{dig}}", C["green"] if done else C["text"], 2)
                self.shown[i] = (value, done)
        x, y, w, h = self.bar
        px = w * self.moves // self.cfg["moves"]
        if done:
            cv.rect(x, y, w, h, C["green"])
        elif px > self.bar_px:
            cv.rect(x + self.bar_px, y, px - self.bar_px, h, C["accent"])
        self.bar_px = px

    def finish(self):
        cv = self.cv
        self.update_hud(done=True)
        cv.rect(0, self.legend_y - 4, self.W, self.H - self.legend_y + 4, C["hud_bg"])
        lines = [f"COMPLETE: ALL {self.total_fill} {self.kind}S FILLED",
                 f"{self.pushes} PUSHES - {self.moves} MOVES"]
        height = self.H - self.legend_y
        if height >= 46:
            ys = [self.legend_y + height // 2 - 19, self.legend_y + height // 2 + 1]
        else:
            lines, ys = [lines[0] + " - " + lines[1].replace(" - ", " / ")], [self.legend_y + height // 2 - 9]
        for line, y in zip(lines, ys):
            scale = 2 if text_width(line) <= self.W - 2 * MARGIN else 1
            cv.text((self.W - text_width(line, scale)) // 2, y, line, C["green"], scale)
        mx, my, mw, mh = self.map_x, self.map_y, self.cols * T, self.rows * T
        for rx, ry, rw, rh in ((mx - 3, my - 3, mw + 6, 3), (mx - 3, my + mh, mw + 6, 3),
                               (mx - 3, my, 3, mh), (mx + mw, my, 3, mh)):
            cv.rect(rx, ry, rw, rh, C["green"])

    def image(self):
        return self.W, self.H, self.cv.snapshot()


def render(ident, m, cfg, outdir: Path, report: Path):
    directions, declared, sources = load_witness(cfg)
    model = Model(m["board"], m["initial"])
    scene = Scene(ident, m, cfg)
    gif = GifWriter(scene.cv)
    gif.frame(START_HOLD_CS)
    shots = {"start": scene.image()}
    pushes = rolls = roll_cells = fills = 0
    for index, d in enumerate(directions):
        try:
            ev = model.step(d)
        except Illegal as exc:
            raise SystemExit(f"{ident}: illegal move {index} ({d}): {exc}")
        dirty = {scene.hero, ev["hero"]} | scene.flash
        scene.flash = set()
        scene.hero = ev["hero"]
        scene.moves += 1
        if not ev["pushed"]:
            for c in dirty:
                scene.draw_cell(c)
            scene.update_hud()
            gif.frame(WALK_CS)
        else:
            pushes += 1
            scene.pushes = pushes
            scene.boulders.discard(ev["source"])
            travel, filled = ev["travel"], ev["filled"]
            rolls += ev["rolled"]
            roll_cells += len(travel) if ev["rolled"] else 0
            previous = None
            for k, cell in enumerate(travel):
                last = k == len(travel) - 1
                if previous is not None:
                    scene.boulders.discard(previous)
                    dirty.add(previous)
                if last and filled is not None:
                    scene.drop = cell
                else:
                    scene.boulders.add(cell)
                dirty.add(cell)
                for c in dirty:
                    scene.draw_cell(c)
                dirty = set()
                scene.update_hud()
                gif.frame(PUSH_CS if k == 0 and not (last and filled is not None and ev["rolled"])
                          else DROP_CS if last and filled is not None else ROLL_CS)
                previous = cell
            if filled is not None:
                fills += 1
                scene.drop = None
                scene.open.discard(filled)
                scene.filled.add(filled)
                scene.flash = {filled}
                scene.draw_cell(filled)
                scene.update_hud()
                gif.frame(FLASH_CS)
        if index + 1 == len(directions) // 2:
            shots["mid"] = scene.image()
    for c in scene.flash:
        scene.flash = set()
        scene.draw_cell(c)
    final = (model.player, model.boulders, model.holes)
    problems = []
    if len(directions) != cfg["moves"]:
        problems.append(f"moves {len(directions)} != {cfg['moves']}")
    if pushes != cfg["pushes"]:
        problems.append(f"pushes {pushes} != {cfg['pushes']}")
    if model.holes:
        problems.append("goal not reached")
    if final != declared:
        problems.append("final state differs from the state declared in the Lean source")
    if scene.boulders != set(model.boulders) or scene.open or scene.hero != model.player:
        problems.append("drawn scene diverged from the model state")
    if problems:
        raise SystemExit(f"{ident}: " + "; ".join(problems))
    scene.finish()
    gif.frame(END_HOLD_CS)
    shots["end"] = scene.image()
    blob = gif.to_bytes()
    frames, duration_cs = verify_gif(blob, gif.hashes)
    path = outdir / f"{ident}.gif"
    path.write_bytes(blob)
    sheet = tile_images([shots["start"], shots["mid"], shots["end"]], 3)
    write_png(report / f"{ident}_start_mid_end.png", *sheet)
    src = scene.src
    entry = {
        "map": ident,
        "result": ("exact minimum" if cfg["lower"] == cfg["pushes"] else "open interval; path is an upper bound only"),
        "proved_lower_bound": cfg["lower"],
        "witness_pushes": pushes, "witness_moves": len(directions),
        "witness_theorem": cfg["theorem"], "witness_path_definition": cfg["path"],
        "witness_sources": sources,
        "map_source": {"path": src["source"], "sha256": src["source_sha256"], "maps_json": MAPS_JSON,
                       "maps_lean": MAPS_LEAN},
        "map_width": src["width"], "map_height": src["height"],
        "boulders": len(src["boulderCells"]), "pits": len(src["pitCells"]), "holes": len(src["holeCells"]),
        "rolling_traps": len(src["rollingCells"]),
        "replay": {"moves": len(directions), "pushes": pushes, "fills": fills, "rolling_pushes": rolls,
                   "rolling_cells_travelled": roll_cells, "final_player": model.player,
                   "final_boulders": model.boulders, "final_holes": model.holes,
                   "final_state_matches_lean_source": True, "final_goal_verified": True},
        "directions": " ".join(DIRS[d][2] for d in directions),
        "gif": {"path": f"{outdir.name}/{ident}.gif" if outdir.name else path.name, "sha256": hashlib.sha256(blob).hexdigest(),
                "bytes": len(blob), "width": scene.W, "height": scene.H, "tile_px": T, "frames": frames,
                "duration_seconds": duration_cs / 100, "loop": "infinite",
                "roundtrip_decoded_frames_match": True},
        "preview": f"report/{ident}_start_mid_end.png",
    }
    return entry, shots


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--out", default=str(REPO / "docs" / "animations"))
    ap.add_argument("--only", nargs="*", help="map ids, e.g. soko4-2")
    args = ap.parse_args()
    outdir = Path(args.out)
    report = outdir / "report"
    report.mkdir(parents=True, exist_ok=True)
    maps = load_maps()
    wanted = args.only or list(WITNESSES)
    entries, starts, ends = [], [], []
    for ident in wanted:
        entry, shots = render(ident, maps[ident], WITNESSES[ident], outdir, report)
        entries.append(entry)
        starts.append(shots["start"])
        ends.append(shots["end"])
        g = entry["gif"]
        print(f"{ident}: {entry['witness_pushes']} pushes / {entry['witness_moves']} moves, goal verified; "
              f"{g['frames']} frames, {g['duration_seconds']:.1f}s, {g['width']}x{g['height']}, {g['bytes']} bytes")
    if not args.only:
        write_png(report / "overview_start.png", *tile_images(starts, 2))
        write_png(report / "overview_end.png", *tile_images(ends, 2))
        manifest = {
            "schema": "nethack-sokoban-animations-v1",
            "generator": {"path": "scripts/render_solutions.py", "sha256": sha256_file(Path(__file__).resolve()),
                          "command": "python3 scripts/render_solutions.py", "dependencies": "Python standard library"},
            "scope": "Illustrations of the packaged winning paths. The Python replay is a consistency check "
                     "against Model.lean semantics, not a proof check; no Lean was run.",
            "maps_json": {"path": MAPS_JSON, "sha256": sha256_file(REPO / MAPS_JSON)},
            "maps_lean": {"path": MAPS_LEAN, "sha256": sha256_file(REPO / MAPS_LEAN)},
            "total_gif_bytes": sum(e["gif"]["bytes"] for e in entries),
            "animations": entries,
        }
        (report / "manifest.json").write_text(json.dumps(manifest, indent=1) + "\n", encoding="utf-8")
        print(f"total GIF bytes: {manifest['total_gif_bytes']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
