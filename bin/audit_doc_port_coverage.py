#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DocPortCoverage
# Purpose: Cross-check book pages against the RTL port/parameter lists
#
# Documentation: vault/handbook/authoring/kimi-review-rounds.md
# Subsystem: authoring
#
# Author: sean galloway
# Created: 2026-09-01
"""Report ports and parameters a module declares but its book page never names.

Two consecutive Kimi qc rounds found the same class by hand: round_30 caught
twelve `_cg` pages missing six threaded parameters, round_31 caught a page
dropping nine parameters and another omitting `cfg_freq_sel`. A reviewer finds
one instance and cites one page; the claim is usually on a dozen. This makes
the sweep mechanical.

Match is by NAME ANYWHERE on the page -- a port mentioned in prose, a table, or
a code block counts as documented. The check is deliberately weak: it is a
floor against silent omission, not a claim that the prose is correct.
"""
import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# `module foo #( ... ) ( ... );` - grab the two paren groups separately.
RE_MODULE = re.compile(r'^\s*module\s+(\w+)', re.M)
RE_PARAM = re.compile(r'\bparameter\s+(?:type\s+)?(?:\w+\s+)*?(\w+)\s*(?:=|,|\))')
RE_PORT = re.compile(
    r'^\s*(?:input|output|inout)\s+'      # direction
    r'(?:wire|logic|reg|bit)?\s*'          # optional net type
    r'(?:signed|unsigned)?\s*'             # optional signedness
    r'(?:\[[^\]]*\]\s*)*'                  # optional packed dims
    r'(\w+)', re.M)


def strip_comments(text: str) -> str:
    text = re.sub(r'/\*.*?\*/', '', text, flags=re.S)
    return re.sub(r'//[^\n]*', '', text)


def declared(sv: Path):
    """Return (params, ports) declared by the FIRST module in the file."""
    src = strip_comments(sv.read_text(errors='replace'))
    m = RE_MODULE.search(src)
    if not m:
        return set(), set()
    body = src[m.end():]
    end = body.find(');')
    header = body[:end] if end != -1 else body
    params = {p for p in RE_PARAM.findall(header)}
    ports = {p for p in RE_PORT.findall(header)}
    # A localparam-derived name is not a port; RE_PORT only matches
    # direction-led lines, so ports is already clean.
    return params, ports


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--rtl', default='rtl/amba',
                    help='RTL root to scan (default: rtl/amba)')
    ap.add_argument('--docs', default='docs/markdown/rtl-amba',
                    help='Book root to scan (default: docs/markdown/rtl-amba)')
    ap.add_argument('--ports-only', action='store_true',
                    help='Ignore parameters; report missing ports only')
    ap.add_argument('--params-only', action='store_true',
                    help='Ignore ports; report missing parameters only')
    ap.add_argument('-q', '--quiet', action='store_true',
                    help='Print only the summary line')
    args = ap.parse_args()

    rtl_root = (REPO / args.rtl) if not Path(args.rtl).is_absolute() else Path(args.rtl)
    doc_root = (REPO / args.docs) if not Path(args.docs).is_absolute() else Path(args.docs)

    pages = {p.stem: p for p in doc_root.rglob('*.md')}
    svs = sorted(rtl_root.rglob('*.sv'))
    if not svs:
        print(f'no .sv under {rtl_root}', file=sys.stderr)
        return 2

    total_missing = 0
    offenders = 0
    checked = 0
    for i, sv in enumerate(svs, 1):
        if not args.quiet and i % 50 == 0:
            print(f'  [{i}/{len(svs)}] scanning...', file=sys.stderr)
        page = pages.get(sv.stem)
        if page is None:
            continue
        checked += 1
        params, ports = declared(sv)
        text = page.read_text(errors='replace')
        gaps = []
        if not args.ports_only:
            gaps += [('param', n) for n in sorted(params)
                     if not re.search(rf'\b{re.escape(n)}\b', text)]
        if not args.params_only:
            gaps += [('port', n) for n in sorted(ports)
                     if not re.search(rf'\b{re.escape(n)}\b', text)]
        if gaps:
            offenders += 1
            total_missing += len(gaps)
            if not args.quiet:
                rel = page.relative_to(REPO) if page.is_relative_to(REPO) else page
                print(f'\n{rel}  ({sv.name})')
                for kind, name in gaps:
                    print(f'    undocumented {kind}: {name}')

    print(f'\n{checked} pages cross-checked, {offenders} with gaps, '
          f'{total_missing} undocumented names total')
    return 1 if total_missing else 0


if __name__ == '__main__':
    sys.exit(main())
