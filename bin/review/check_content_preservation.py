#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: check_content_preservation
# Purpose: Prove a humanize round left the TECHNICAL content untouched.
# Subsystem: tooling
"""Prove a humanize round changed prose only.

The voice pass is allowed to rewrite sentences. It is NOT allowed to touch a
code block, rename a signal, or change a number -- and a model told to
"improve" documentation will quietly do all three (see
vault/handbook/authoring/humanization-voice.md).

check_tag_survival.py guards the PIPELINE structure: banners, links, captions,
fences, emoji. It does not look inside a code block, and it cannot tell that
`r_abandoned == 0` became `r_abandoned is zero`. This does.

FATAL (exit 1):
  * a fenced code block whose content changed, or that disappeared
  * a backticked identifier present in the input page and absent from the
    output page -- a renamed or dropped signal, port, parameter or file
WARN (exit 0, printed):
  * a numeric token that vanished from a page's prose ("3" -> "three" is
    legitimate; "1 clock" -> "2 clocks" is not, so read them)
  * table cells that vanished (unification may restyle a table, but a lost
    cell value is usually a lost fact)
  * backticked spans that APPEAR in the output but not the input -- an
    identifier the model invented

    python3 bin/review/check_content_preservation.py --results <round dir>
    python3 bin/review/check_content_preservation.py --input A.md --output B.md
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys
from collections import Counter

BANNER = re.compile(r"^<!-- SOURCE FILE: (\S+) -->\s*$", re.M)
FENCE = re.compile(r"^```[^\n]*\n(.*?)^```\s*$", re.M | re.S)
TICK = re.compile(r"`([^`\n]+)`")
NUM = re.compile(r"(?<![\w.])(?:0x[0-9A-Fa-f_]+|\d+'[bBhHdD][0-9A-Fa-f_xXzZ]+|\d+(?:\.\d+)?)(?![\w.])")


def split_pages(text: str) -> dict[str, str]:
    parts = BANNER.split(text)
    # parts = [preamble, path1, body1, path2, body2, ...]
    return {parts[i]: parts[i + 1] for i in range(1, len(parts) - 1, 2)}


def prose_only(body: str) -> str:
    """The page with fenced blocks removed, so prose checks ignore code."""
    return FENCE.sub("", body)


def table_cells(body: str) -> Counter:
    cells = Counter()
    for line in prose_only(body).splitlines():
        s = line.strip()
        if not s.startswith("|") or re.fullmatch(r"\|[\s:|-]+\|?", s):
            continue
        for c in s.strip("|").split("|"):
            c = c.strip()
            if c:
                cells[c] += 1
    return cells


def compare_page(path: str, before: str, after: str):
    fatal, warn = [], []

    b_code, a_code = FENCE.findall(before), FENCE.findall(after)
    if Counter(b_code) != Counter(a_code):
        lost = list((Counter(b_code) - Counter(a_code)).elements())
        for blk in lost:
            first = next((ln for ln in blk.splitlines() if ln.strip()), "").strip()
            fatal.append(f"code block changed or lost, starting: {first[:70]!r}")
        if not lost:
            fatal.append(f"code block count {len(b_code)} -> {len(a_code)}")

    b_tick = set(TICK.findall(prose_only(before)))
    a_tick = set(TICK.findall(prose_only(after)))
    for t in sorted(b_tick - a_tick):
        fatal.append(f"identifier dropped or renamed: `{t}`")
    invented = sorted(a_tick - b_tick)
    if invented:
        warn.append("identifiers not in the input: " + ", ".join(f"`{t}`" for t in invented[:8]))

    b_num = Counter(NUM.findall(prose_only(before)))
    a_num = Counter(NUM.findall(prose_only(after)))
    gone = sorted((b_num - a_num).keys())
    if gone:
        warn.append("numbers no longer in the prose: " + ", ".join(gone[:12]))

    lost_cells = sorted((table_cells(before) - table_cells(after)).keys())
    if lost_cells:
        warn.append(f"{len(lost_cells)} table cell(s) gone, e.g. "
                    + ", ".join(repr(c[:30]) for c in lost_cells[:5]))
    return fatal, warn


def run(pairs):
    nfatal = 0
    for path, before, after in pairs:
        if after is None:
            print(f"FATAL {path}: page missing from the output")
            nfatal += 1
            continue
        fatal, warn = compare_page(path, before, after)
        for f in fatal:
            print(f"FATAL {path}: {f}")
        for w in warn:
            print(f"warn  {path}: {w}")
        nfatal += len(fatal)
    print(f"\n{len(pairs)} page(s) compared, {nfatal} fatal")
    return 1 if nfatal else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", type=pathlib.Path)
    ap.add_argument("--only", default="")
    ap.add_argument("--input", type=pathlib.Path)
    ap.add_argument("--output", type=pathlib.Path)
    a = ap.parse_args()

    if a.input and a.output:
        b = split_pages(a.input.read_text()) or {"(whole file)": a.input.read_text()}
        o = split_pages(a.output.read_text()) or {"(whole file)": a.output.read_text()}
        return run([(p, b[p], o.get(p)) for p in b])

    if not a.results:
        ap.error("give --results, or --input and --output")
    pairs = []
    for res in sorted(a.results.glob("*.md")):
        unit = res.stem
        if a.only and not unit.startswith(a.only):
            continue
        snap = a.results / "_bundle_snapshot" / unit / "DOCS.md"
        if not snap.exists():
            print(f"FATAL {unit}: no input snapshot at {snap}")
            return 1
        b, o = split_pages(snap.read_text()), split_pages(res.read_text())
        pairs += [(p, b[p], o.get(p)) for p in b]
    if not pairs:
        print("no units found")
        return 1
    return run(pairs)


if __name__ == "__main__":
    sys.exit(main())
