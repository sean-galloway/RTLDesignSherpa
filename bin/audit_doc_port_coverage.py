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
import rtl_ast
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# `module foo #( ... ) ( ... );` - grab the two paren groups separately.
RE_MODULE = re.compile(r'^\s*module\s+(\w+)', re.M)
# `parameter [type] [signedness] [packed dims] NAME = ...`
# The packed dimension is why this is not a simple \w+ run: UNIT_ID is declared
# `parameter logic [7:0] UNIT_ID = 8'h01`, and a pattern that cannot skip
# `[7:0]` silently drops every width-typed parameter -- which is exactly how a
# clean 0-gap report coexisted with pages missing UNIT_ID and AGENT_ID.
RE_PARAM = re.compile(
    r'\bparameter\s+'
    r'(?:type\s+)?'
    r'(?:\w+\s*(?:::\s*\w+)?\s+)*?'      # optional type, incl. pkg::type
    r'(?:signed|unsigned\s+)?'
    r'(?:\[[^\]]*\]\s*)*'                 # optional packed dimensions
    r'(\w+)\s*(?:=|,|\))')
RE_PORT_LINE = re.compile(r'^\s*(?:input|output|inout)\b(.*)$', re.M)

# Standard AXI/APB channel signals. A page that says "connect all slave AW/W/B
# signals" or carries a channel table documents these collectively; demanding
# each name individually buries the ports that DO need their own row.
RE_PROTOCOL_PORT = re.compile(
    r'^(?:[smi]_|fub_|int_)?(?:axi|axil|apb|axis)?_?'
    r'(?:aw|ar|w|r|b|p)'
    r'(?:id|addr|len|size|burst|lock|cache|prot|qos|region|user|valid|ready|'
    r'data|strb|last|resp|wakeup|domain|snoop|atop|trace|loop|mpam|mecid|'
    r'nsaid|poison|tag|chunk|idunq|sel|enable|write|slverr|nse|wakeup)$',
    re.I)


def strip_comments(text: str) -> str:
    text = re.sub(r'/\*.*?\*/', '', text, flags=re.S)
    return re.sub(r'//[^\n]*', '', text)


def port_name(tail: str):
    """The port identifier from a direction-led declaration tail.

    Handles qualified types (`monitor_common_pkg::monbus_timestamp_t sig`),
    packed dimensions, and trailing commas/comments -- the name is the LAST
    bare identifier outside any bracket.
    """
    tail = tail.split('//')[0]
    tail = re.sub(r'\w+\s*::\s*\w+', ' ', tail)   # drop pkg::type first
    tail = re.sub(r'\[[^\]]*\]', ' ', tail)        # then packed dimensions
    tail = tail.strip().rstrip(',').strip()
    KW = {'wire', 'logic', 'reg', 'bit', 'signed', 'unsigned', 'var', 'byte',
          'int', 'integer', 'shortint', 'longint', 'real'}
    ids = [i for i in re.findall(r'\b[A-Za-z_]\w*\b', tail) if i not in KW]
    return ids[-1] if ids else None


RE_DELEGATE_LINK = re.compile(r'\[([A-Za-z0-9_]+)\]\(([^)]+\.md)\)')
RE_DELEGATES = re.compile(r'\b(?:same as|identical to)\b', re.I)


def declared(sv: Path):
    """Return (params, ports) for the module the file is named after.

    Verilator's AST, not a regex over the header. A regex cannot see a port
    declared through a macro, and reads `parameter logic [7:0] UNIT_ID` as a
    type rather than a name -- that blind spot once reported "0 gaps" while 24
    parameters were undocumented. Returns None when the file will not
    elaborate, so an unparseable module is reported rather than scored clean.
    """
    f = rtl_ast.facts(str(sv))
    if f is None:
        return None
    return set(f['params']), set(f['ports'])


def with_delegations(page: Path, text: str, depth: int = 1) -> str:
    """Append the text of pages this one EXPLICITLY delegates to.

    A page may say "Same as [apb5_slave](apb5_slave.md)" rather than repeat a
    thirty-row port table, which is better practice than duplicating it -- a
    copy drifts silently. But it left every delegated port reported as
    undocumented (61 of them across the two apb5 CDC pages). Following the link
    makes the delegation checkable instead: if the target ever drops a port,
    these pages start failing.

    Deliberately narrow -- only links on a line that says "same as" or
    "identical to". Following every link would let any cross-reference launder
    a genuine gap.
    """
    if depth <= 0:
        return text
    extra = []
    for line in text.splitlines():
        if not RE_DELEGATES.search(line):
            continue
        for _name, href in RE_DELEGATE_LINK.findall(line):
            tgt = (page.parent / href).resolve()
            if tgt.is_file() and tgt != page.resolve():
                extra.append(with_delegations(
                    tgt, tgt.read_text(errors='replace'), depth - 1))
    return text + '\n' + '\n'.join(extra)


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
    ap.add_argument('--strict', action='store_true',
                    help='Also report standard AXI/APB channel signals, which '
                         'pages normally document collectively')
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
    unparseable = []
    for i, sv in enumerate(svs, 1):
        if not args.quiet and i % 50 == 0:
            print(f'  [{i}/{len(svs)}] scanning...', file=sys.stderr)
        page = pages.get(sv.stem)
        if page is None:
            continue
        if sv.stem.endswith('_pkg'):
            # A package declares types, not ports. It has nothing for this
            # check to measure, and counting it as a failed elaboration
            # buries the modules that genuinely did not parse.
            continue
        checked += 1
        got = declared(sv)
        if got is None:
            unparseable.append(sv.name)
            continue
        params, ports = got
        text = with_delegations(page, page.read_text(errors='replace'))
        gaps = []
        if not args.ports_only:
            gaps += [('param', n) for n in sorted(params)
                     if not re.search(rf'\b{re.escape(n)}\b', text)]
        if not args.params_only:
            gaps += [('port', n) for n in sorted(ports)
                     if not re.search(rf'\b{re.escape(n)}\b', text)
                     and (args.strict or not RE_PROTOCOL_PORT.match(n))]
        if gaps:
            offenders += 1
            total_missing += len(gaps)
            if not args.quiet:
                rel = page.relative_to(REPO) if page.is_relative_to(REPO) else page
                print(f'\n{rel}  ({sv.name})')
                for kind, name in gaps:
                    print(f'    undocumented {kind}: {name}')

    if unparseable:
        print(f'\n{len(unparseable)} module(s) would not elaborate, so were '
              f'NOT checked: {", ".join(sorted(unparseable))}', file=sys.stderr)

    print(f'\n{checked - len(unparseable)} pages cross-checked, {offenders} '
          f'with gaps, {total_missing} undocumented names total')
    return 1 if (total_missing or unparseable) else 0


if __name__ == '__main__':
    sys.exit(main())
