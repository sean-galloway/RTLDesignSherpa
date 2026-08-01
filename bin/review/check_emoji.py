#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: check_emoji
# Purpose: The single definition of "emoji" for this repo, plus a scanner.
# Subsystem: tooling
"""Find emoji in documentation. One definition, used everywhere.

Emojis break the LaTeX path in PDF generation and read as unprofessional in a
formal spec, so they are banned in documentation ([[humanization-voice]],
CLAUDE.md, the style guide banlist). Enforcing that needs a definition of
"emoji" that is neither too narrow nor too wide, and this file is it --
`check_tag_survival.py` imports from here rather than carrying its own copy.

**Why one definition.** The first sweep of rtl-common used
`[\\x{1F300}-\\x{1FAFF}\\x{2600}-\\x{27BF}]` and so did the grep that verified
it afterwards. A verification that shares the sweep's blind spot agrees with
itself: that range omits U+2B00-U+2BFF, so a star (U+2B50) removed by the sweep
rules would still have been reported clean, and it omits the U+FE0F variation
selectors, three of which were sitting in rtl/common/CLAUDE.md at the time. The
same scoping error hid a whole file class -- every count was globbed from
`docs/markdown/`, so beside-code CLAUDE.md and README.md were never in the
denominator.

**Why not wider.** Technical documentation is full of non-ASCII that must
survive untouched. Measured across 54 rtl-common files: 713 OVERLINE (waveform
diagrams), 191 RIGHTWARDS ARROW, 178 box-drawing characters, 174 em dashes, 160
middle dots (the doc header separator), plus the usual math and Greek. An
earlier version of the tag-survival check swept U+2190-U+21FF and flagged 15
pages of legitimate state-transition arrows as violations. A checker that cries
wolf on correct documentation is worse than no checker, so arrows, box drawing
and math operators are deliberately OUT.

    python3 bin/review/check_emoji.py docs/markdown/rtl-common rtl/common
    python3 bin/review/check_emoji.py --all          # every tracked .md
    python3 bin/review/check_emoji.py --all --summary

Exit 1 if anything is found, so it can gate.
"""
from __future__ import annotations

import argparse
import collections
import glob
import os
import subprocess
import sys
import unicodedata

# Ranges that ARE emoji.
RANGES = (
    (0x1F000, 0x1FAFF),   # pictographs, transport, mahjong, cards, enclosed
    (0x2600, 0x27BF),     # misc symbols + dingbats: check mark, cross, warning
    (0x2B00, 0x2BFF),     # stars, thick arrows
)
# Stragglers outside those blocks that render as emoji.
SINGLES = frozenset({0x2139, 0x24C2, 0x3030, 0x303D, 0x3297, 0x3299, 0xFE0F})

# Deliberately NOT emoji -- documented so the next person does not "fix" it:
#   U+2190-U+21FF arrows          state transitions, navigation links
#   U+2500-U+257F box drawing     ASCII waveforms and hierarchy diagrams
#   U+2200-U+22FF math operators  >=, !=, element-of, xor
#   U+203E overline               waveform high levels (713 of them in common)
#   superscripts, subscripts, Greek, em/en dash, middle dot, (c)/(r)/(tm)


def is_emoji(ch: str) -> bool:
    o = ord(ch)
    return o in SINGLES or any(lo <= o <= hi for lo, hi in RANGES)


def scan(path: str) -> collections.Counter:
    try:
        text = open(path, encoding="utf-8", errors="replace").read()
    except (OSError, UnicodeError):
        return collections.Counter()
    return collections.Counter(ch for ch in text if is_emoji(ch))


def tracked_markdown() -> list[str]:
    out = subprocess.run(["git", "ls-files", "*.md"], capture_output=True, text=True)
    return [f for f in out.stdout.split("\n") if f and os.path.isfile(f)]


def expand(paths: list[str]) -> list[str]:
    files = []
    for p in paths:
        if os.path.isdir(p):
            files += sorted(glob.glob(os.path.join(p, "**", "*.md"), recursive=True))
        elif os.path.isfile(p):
            files.append(p)
        else:
            files += sorted(glob.glob(p))
    return files


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="*", help="files, dirs (recursed for *.md), or globs")
    ap.add_argument("--all", action="store_true", help="every git-tracked .md in the repo")
    ap.add_argument("--summary", action="store_true", help="totals only, no per-file lines")
    a = ap.parse_args()

    files = tracked_markdown() if a.all else expand(a.paths)
    if not files:
        sys.exit("no files to scan (pass paths or --all)")

    total, dirty, glyphs = 0, 0, collections.Counter()
    for p in sorted(files):
        c = scan(p)
        if not c:
            continue
        dirty += 1
        total += sum(c.values())
        glyphs += c
        if not a.summary:
            print(f"{p:60} {sum(c.values()):>4}  "
                  + " ".join(f"{ch}x{n}" for ch, n in c.most_common(8)))

    print(f"\n{total} emoji in {dirty} of {len(files)} file(s)")
    if glyphs:
        print("by glyph:")
        for ch, n in glyphs.most_common(15):
            print(f"  {ch}  U+{ord(ch):04X}  {n:>4}  {unicodedata.name(ch, '<unnamed>')[:48]}")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())
