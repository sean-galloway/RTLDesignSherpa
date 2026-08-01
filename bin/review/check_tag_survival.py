#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: check_tag_survival
# Purpose: Gate a humanize round before apply_humanize writes it into the tree.
# Subsystem: tooling
"""Compare a humanize round's output against the inputs it was given.

A voice pass rewrites every page, and the things it is least likely to notice
losing are the ones the downstream pipeline depends on: caption lines that
become LoF/LoT/LoW entries, link targets, HTML anchors, and the
`<!-- SOURCE FILE: ... -->` banners that apply_humanize splits on. Losing a
banner is the worst case and the quietest -- the pages after it are absorbed
into the previous page's body and never written, so the round reports success
and the book silently loses a chapter.

apply_humanize already refuses a page that SHRANK past a floor. That catches a
summarised page; it cannot catch a page that is the right length and no longer
links anywhere, and it never notices a page that stopped existing.

So: run this first, and only apply a round that passes.

    python3 bin/review/check_tag_survival.py --results ~/rtl-doc-review/results/humanize-kimi-k3/round_4
    python3 bin/review/check_tag_survival.py --results ... --only common --verbose

FATAL classes (exit 1): a dropped page, a lost link target, a lost caption
line, unbalanced code fences, or an emoji (they break the LaTeX path in PDF
generation -- see the humanization style guide's banlist).

WARN classes (exit 0, printed): heading-count drift and length ratios outside
0.85-1.20, which are judgement calls -- unification legitimately merges or
retitles sections.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from apply_humanize import split_units  # noqa: E402
from check_emoji import is_emoji  # noqa: E402

LINK = re.compile(r'\]\(([^)\s]+?)(?:\s+"[^"]*")?\)')
ANCHOR = re.compile(r'<a\s+(?:name|id)="([^"]+)"')
CAPTION = re.compile(r'^:\s+\S', re.M)          # LoF/LoT/LoW caption encoding
HEADING = re.compile(r'^#{1,6}\s+\S', re.M)
FENCE = re.compile(r'^```', re.M)
# The emoji class lives in check_emoji.py -- ONE definition, because the first
# version of this check and the grep that verified its sweep carried two
# different ones, and a verification sharing the sweep's blind spot agrees with
# itself. See that module for what is in, what is deliberately out (arrows, box
# drawing, math), and why.
def _emoji(s):
    return [ch for ch in s if is_emoji(ch)]

RATIO_LO, RATIO_HI = 0.85, 1.20


def counts(body: str) -> dict:
    return {
        "links": sorted(LINK.findall(body)),
        "anchors": sorted(ANCHOR.findall(body)),
        "captions": len(CAPTION.findall(body)),
        "headings": len(HEADING.findall(body)),
        "fences": len(FENCE.findall(body)),
        "chars": len(body),
    }


def check_unit(out_path: Path, snap_path: Path, verbose: bool) -> tuple[int, int]:
    """(fatal, warn) counts for one unit."""
    before = {p: b for p, b in split_units(snap_path.read_text(encoding="utf-8"))}
    after = {p: b for p, b in split_units(out_path.read_text(encoding="utf-8"))}
    fatal = warn = 0

    print(f"\n{out_path.name}: {len(before)} page(s) in, {len(after)} out")

    dropped = [p for p in before if p not in after]
    for p in dropped:
        print(f"  FATAL  page DROPPED entirely: {p}")
        print("         its SOURCE FILE banner is missing from the output, so "
              "apply_humanize\n         would fold it into the previous page "
              "and never write it")
        fatal += 1
    for p in after:
        if p not in before:
            print(f"  WARN   page not in the input: {p} (invented banner?)")
            warn += 1

    for p, b in before.items():
        if p not in after:
            continue
        a = after[p]
        cb, ca = counts(b), counts(a)
        msgs = []

        lost = sorted(set(cb["links"]) - set(ca["links"]))
        if lost:
            msgs.append(("FATAL", f"{len(lost)} link target(s) lost: "
                                  f"{', '.join(lost[:4])}{' ...' if len(lost) > 4 else ''}"))
        lost_a = sorted(set(cb["anchors"]) - set(ca["anchors"]))
        if lost_a:
            msgs.append(("FATAL", f"{len(lost_a)} anchor(s) lost: {', '.join(lost_a[:4])}"))
        if ca["captions"] < cb["captions"]:
            msgs.append(("FATAL", f"captions {cb['captions']} -> {ca['captions']} "
                                  "(LoF/LoT/LoW entries)"))
        if ca["fences"] % 2:
            msgs.append(("FATAL", f"unbalanced code fences ({ca['fences']})"))
        emo_a, emo_b = _emoji(a), _emoji(b)
        if len(emo_a) > len(emo_b):
            msgs.append(("FATAL", f"{len(emo_a) - len(emo_b)} emoji INTRODUCED "
                                  f"({''.join(sorted(set(emo_a))[:5])}) -- breaks the LaTeX path"))
        elif emo_a:
            # Not this round's doing, but the voice pass was the chance to
            # remove them and did not. Cleanup finding, not an apply blocker.
            msgs.append(("WARN", f"{len(emo_a)} pre-existing emoji survived the pass "
                                 f"({''.join(sorted(set(emo_a))[:5])})"))

        ratio = ca["chars"] / max(cb["chars"], 1)
        if not RATIO_LO <= ratio <= RATIO_HI:
            msgs.append(("WARN", f"length ratio {ratio:.2f} "
                                 f"({cb['chars']} -> {ca['chars']} chars)"))
        if ca["headings"] != cb["headings"]:
            msgs.append(("WARN", f"headings {cb['headings']} -> {ca['headings']}"))

        for level, m in msgs:
            print(f"  {level}  {os.path.basename(p)}: {m}")
            if level == "FATAL":
                fatal += 1
            else:
                warn += 1
        if verbose and not msgs:
            print(f"  ok     {os.path.basename(p)}: {len(cb['links'])} links, "
                  f"{cb['captions']} captions, ratio {ratio:.2f}")
    return fatal, warn


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--results", required=True, help="humanize round dir")
    ap.add_argument("--only", default="", help="units starting with this prefix")
    ap.add_argument("--verbose", action="store_true", help="also list clean pages")
    a = ap.parse_args()

    rd = Path(a.results)
    if not rd.is_dir():
        sys.exit(f"no such round: {rd}")
    units = sorted(p for p in rd.glob("*.md")
                   if p.name.startswith(a.only) and not p.name.startswith("FINDINGS"))
    if not units:
        sys.exit(f"no units in {rd} matching {a.only!r}")

    fatal = warn = 0
    for u in units:
        snap = rd / "_bundle_snapshot" / u.stem / "DOCS.md"
        if not snap.is_file():
            print(f"\n{u.name}: FATAL no bundle snapshot at {snap} -- "
                  "nothing to compare against")
            fatal += 1
            continue
        f, w = check_unit(u, snap, a.verbose)
        fatal += f
        warn += w

    print(f"\n{len(units)} unit(s): {fatal} fatal, {warn} warn")
    if fatal:
        print("DO NOT apply this round. Fix or re-run the affected units "
              "(run_batch.py --resume N\nfills gaps without touching what "
              "already succeeded).")
    return 1 if fatal else 0


if __name__ == "__main__":
    sys.exit(main())
