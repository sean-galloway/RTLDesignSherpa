#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: apply_humanize
# Purpose: Split a humanize round's output back into the individual doc pages.
# Subsystem: tooling
"""Write a humanize round's rewritten prose back into docs/markdown.

A humanize round returns one blob per UNIT -- ten or twenty pages concatenated,
each introduced by

    <!-- SOURCE FILE: docs/markdown/rtl-common/fifo_sync.md -->

Until this existed there was no way to get that prose back into the tree, so a
finished round left the documentation untouched and looked "partial". Generating
the rewrite is half the job; this is the other half.

    --results DIR   the round directory (…/humanize-<model>/round_N)
    --dry-run       report what would be written, write nothing
    --only PREFIX   restrict to units whose name starts with PREFIX

Refuses to write a page whose rewritten body is dramatically shorter than the
original: that is the signature of a truncated or summarised unit, and silently
replacing a 600-line page with a 40-line precis is the one failure mode here
that nobody would notice until the book was built.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
BANNER = re.compile(r'^<!-- SOURCE FILE: (\S+?) -->\s*$', re.M)

# A rewritten page below this fraction of the original is treated as suspect.
# Voice edits move length by a few percent; a summary loses half or more.
SHRINK_FLOOR = 0.60


def split_units(text: str) -> list[tuple[str, str]]:
    """[(path, body)] for each SOURCE FILE section, banner line removed."""
    hits = list(BANNER.finditer(text))
    out = []
    for i, m in enumerate(hits):
        end = hits[i + 1].start() if i + 1 < len(hits) else len(text)
        body = text[m.end():end]
        # drop the decorative ===== comment lines that bracket the banner
        body = re.sub(r'^<!-- =+ -->\s*$', '', body, flags=re.M)
        out.append((m.group(1), body.strip('\n') + '\n'))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--results', required=True, help='round dir, e.g. .../humanize-kimi-k3/round_1')
    ap.add_argument('--only', default='', help='only units starting with this prefix')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--force', action='store_true',
                    help='write even pages that shrank past the floor (say why in the commit)')
    args = ap.parse_args()

    rd = Path(args.results)
    if not rd.is_dir():
        sys.exit(f'no such round: {rd}')

    units = sorted(p for p in rd.glob('*.md') if p.name.startswith(args.only))
    if not units:
        sys.exit(f'no units in {rd} matching {args.only!r}')

    written = skipped = suspect = 0
    for u in units:
        sections = split_units(u.read_text(encoding='utf-8'))
        if not sections:
            print(f'  {u.name}: no SOURCE FILE banners -- skipped whole unit')
            continue
        print(f'  {u.name}: {len(sections)} page(s)')
        for rel, body in sections:
            target = REPO_ROOT / rel
            if not target.is_file():
                # A page can move between the bundle being built and the round
                # being applied -- a long round leaves plenty of time for it.
                # Follow it by basename rather than discarding its rewrite, but
                # only when the destination is unambiguous.
                cands = sorted((REPO_ROOT / 'docs' / 'markdown').rglob(Path(rel).name))
                if len(cands) == 1:
                    target = cands[0]
                    print(f'      MOVED    {rel} -> {target.relative_to(REPO_ROOT)}')
                else:
                    what = 'not found' if not cands else f'{len(cands)} candidates'
                    print(f'      MISSING  {rel}  ({what})')
                    skipped += 1
                    continue
            before = target.read_text(encoding='utf-8')
            ratio = len(body) / max(len(before), 1)
            if ratio < SHRINK_FLOOR and not args.force:
                print(f'      SUSPECT  {rel}  {len(before)} -> {len(body)} chars ({ratio:.0%}) -- not written')
                suspect += 1
                continue
            if args.dry_run:
                print(f'      would write {rel}  {len(before)} -> {len(body)} chars ({ratio:.0%})')
            else:
                target.write_text(body, encoding='utf-8')
            written += 1

    verb = 'would write' if args.dry_run else 'wrote'
    print(f'\n{verb} {written} page(s); {suspect} suspect, {skipped} missing')
    if suspect:
        print('Suspect pages were NOT written. Read them in the round output before '
              'using --force; a summarised page is the failure this check exists for.')
    return 1 if (suspect or skipped) else 0


if __name__ == '__main__':
    sys.exit(main())
