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

**Third instance of the same bug, 2026-09-24.** The block U+2300-U+23FF was
absent, so the hourglass, pause, stopwatch and next-track glyphs read as clean:
48 of them sat in tracked .md and this checker reported them as nothing. An
emoji sweep over 235 scripts missed the same block for the same reason and left
18 glyphs behind while reporting success. Only the EMOJI sub-ranges are added
(U+231A-231B, U+23E9-23FA); U+2308-230B stay out because ceiling and floor
brackets are live math in this repo.

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
import json
import pathlib
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
    (0x231A, 0x231B),     # watch, hourglass
    (0x23E9, 0x23FA),     # media controls + clocks: next-track, pause, record,
                          # alarm, stopwatch, timer, HOURGLASS WITH FLOWING SAND
)
# Stragglers outside those blocks that render as emoji.
SINGLES = frozenset({0x2139, 0x24C2, 0x3030, 0x303D, 0x3297, 0x3299, 0xFE0F})

# Deliberately NOT emoji -- documented so the next person does not "fix" it:
#   U+2300-U+2319 technical       diameter, ceiling/floor brackets (U+2308-230B
#                                 appear in real formulas here -- pumice's read
#                                 ring depth is D >= ceil((t_rddata_en+CL)/tCCD))
#   U+2190-U+21FF arrows          state transitions, navigation links
#   U+2500-U+257F box drawing     ASCII waveforms and hierarchy diagrams
#   U+2200-U+22FF math operators  >=, !=, element-of, xor
#   U+203E overline               waveform high levels (713 of them in common)
#   superscripts, subscripts, Greek, em/en dash, middle dot, (c)/(r)/(tm)
#
# Generated .docx/.xlsx deliverables are NOT scanned and must not be swept: they
# are versioned release archives (generate_*_pdf.sh takes --rev), so rewriting
# one falsifies what that release was. Their sources are the .md this tool does
# read. If you ever do scan a container, read the XML INSIDE the zip -- a
# raw-byte scan of the compressed stream both over- and under-counts
# (Bridge_MAS_v1.0 reports 168 raw vs 141 real; APB_Crossbar_MAS_v1.0 107 vs 0).


def is_emoji(ch: str) -> bool:
    o = ord(ch)
    return o in SINGLES or any(lo <= o <= hi for lo, hi in RANGES)


# Beyond .md: the classes a decorative sweep reaches. A sweep over 235 .py/.sh
# on 2026-09-24 removed 2279 glyphs from code and nothing gated them afterwards,
# while this checker looked only at .md -- the same scoping error its docstring
# describes, one file class further out.
ALL_TEXT_GLOBS = ["*.md", "*.py", "*.sh", "*.mk", "Makefile", "*/Makefile",
                  "**/Makefile", "*.sv", "*.svh", "*.v", "*.yaml", "*.yml",
                  "*.toml", "*.cfg", "*.txt", "*.gv", "*.tcl"]

# .docx/.xlsx are ZIP containers: decoding their compressed bytes as UTF-8
# invents codepoints (Bridge_MAS_v1.0 reports 168 raw where 141 are real,
# APB_Crossbar_MAS_v1.0 107 where NONE are). Never scan them as text.
SKIP_SUFFIX = {".docx", ".xlsx", ".pdf", ".png", ".jpg", ".jpeg", ".svg", ".gz",
               ".zip", ".woff", ".woff2", ".ttf", ".eot", ".ico", ".bit", ".vcd"}

BASELINE = "bin/emoji_code_baseline.json"


def _guarded(path: str, text: str) -> str:
    """md_to_docx's EMOJI_MAP keys are input data -- the table that strips emoji
    on the way to DOCX/PDF. Counting them would make this gate demand its own
    removal."""
    if not path.endswith("bin/md_to_docx.py"):
        return text
    lines = text.split("\n")
    try:
        s = next(i for i, l in enumerate(lines) if l.startswith("EMOJI_MAP = {"))
        e = next(i for i, l in enumerate(lines[s:], s) if l.rstrip() == "}")
    except StopIteration:
        return text
    return "\n".join(lines[:s] + lines[e + 1:])


def scan(path: str) -> collections.Counter:
    try:
        text = open(path, encoding="utf-8", errors="replace").read()
    except (OSError, UnicodeError):
        return collections.Counter()
    return collections.Counter(ch for ch in _guarded(path, text) if is_emoji(ch))


def tracked_markdown(code: bool = False) -> list[str]:
    out = subprocess.run(["git", "ls-files"] + (ALL_TEXT_GLOBS if code else ["*.md"]),
                         capture_output=True, text=True)
    return [f for f in out.stdout.split("\n")
            if f and os.path.isfile(f)
            and os.path.splitext(f)[1].lower() not in SKIP_SUFFIX]


def staged_files() -> list[str]:
    out = subprocess.run(["git", "diff", "--cached", "--name-only",
                          "--diff-filter=ACM"], capture_output=True, text=True)
    keep = {".md", ".py", ".sh", ".mk", ".sv", ".svh", ".v", ".yaml", ".yml",
            ".toml", ".cfg", ".txt", ".gv", ".tcl"}
    return [f for f in out.stdout.split("\n")
            if f and os.path.isfile(f)
            and (os.path.splitext(f)[1].lower() in keep
                 or os.path.basename(f) == "Makefile")]


def head_count(path: str) -> int:
    r = subprocess.run(["git", "show", f"HEAD:{path}"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return 0
    return sum(1 for ch in _guarded(path, r.stdout) if is_emoji(ch))


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
    ap.add_argument("--code", action="store_true",
                    help="widen --all beyond .md to .py/.sh/Makefile/.sv/.yaml/.toml/...")
    ap.add_argument("--staged", action="store_true",
                    help="only files staged for commit (for the pre-commit hook)")
    ap.add_argument("--ratchet", action="store_true",
                    help="fail only if a file GREW its count against the baseline")
    ap.add_argument("--update-baseline", action="store_true",
                    help="rewrite the baseline from HEAD (committed blobs, not the worktree)")
    ap.add_argument("--summary", action="store_true", help="totals only, no per-file lines")
    a = ap.parse_args()

    if a.update_baseline:
        # From HEAD, never the worktree: a baseline built from uncommitted state
        # records a level the repo has never been at, and CI only sees blobs.
        base = {f: n for f in tracked_markdown(code=True) if (n := head_count(f))}
        pathlib.Path(BASELINE).write_text(
            json.dumps(base, indent=2, sort_keys=True) + "\n")
        print(f"[emoji] baseline written from HEAD: "
              f"{sum(base.values())} glyph(s) in {len(base)} file(s)")
        return 0

    if a.staged:
        files = staged_files()
        if not files:
            return 0                      # nothing of ours in this commit
    elif a.all:
        files = tracked_markdown(code=a.code)
    else:
        files = expand(a.paths)
    if not files:
        sys.exit("no files to scan (pass paths, --all or --staged)")

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

    if a.ratchet:
        try:
            base = json.loads(pathlib.Path(BASELINE).read_text())
        except OSError:
            base = {}
        grew = [(p, base.get(p, 0), sum(scan(p).values()))
                for p in sorted(files)
                if sum(scan(p).values()) > base.get(p, 0)]
        # SAY WHAT WAS EXAMINED. A gate that passed and a gate that looked at
        # nothing are indistinguishable from outside; that is how the
        # port-consumer check sat broken for a whole area.
        print(f"[emoji] {len(files)} staged file(s) examined, "
              f"{total} glyph(s), {len(grew)} grew", file=sys.stderr)
        if grew:
            print("[emoji] BLOCKED: file(s) gained emoji:", file=sys.stderr)
            for p, was, now in grew:
                print(f"  {p}: {was} -> {now}", file=sys.stderr)
            print("  Emoji break the LaTeX/PDF path and read as unprofessional "
                  "in a spec. Use words.", file=sys.stderr)
            print("  If a glyph is DATA (md_to_docx EMOJI_MAP), it belongs in a "
                  "guarded block, not a bare literal.", file=sys.stderr)
            return 1
        return 0

    print(f"\n{total} emoji in {dirty} of {len(files)} file(s)")
    if glyphs:
        print("by glyph:")
        for ch, n in glyphs.most_common(15):
            print(f"  {ch}  U+{ord(ch):04X}  {n:>4}  {unicodedata.name(ch, '<unnamed>')[:48]}")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())
