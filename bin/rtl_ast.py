#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RtlAst
# Purpose: Module facts from Verilator's AST, not from regex over source
#
# Documentation: vault/handbook/design/naming-and-style.md
# Subsystem: tooling
"""Extract a module's ports, parameters and sequential-ness from the AST.

Every doc checker in bin/ used to regex the SystemVerilog source, and every one
of them was wrong in a way regex cannot fix:

  - a parameter regex that could not skip a packed dimension made
    `parameter logic [7:0] UNIT_ID` invisible, so 24 undocumented parameters
    were reported as zero gaps;
  - searching for `always_ff` missed this repo's `ALWAYS_FF_RST` macro, which
    92 modules use, and produced 34 pages calling sequential modules "purely
    combinational";
  - splitting instantiations by regex attributed one module's connections to
    another and nearly deleted three pages of correct examples.

Regex sees text. The checks need the elaborated design, so they read Verilator's
AST instead: `--dump-tree-json` at an early stage, where PORT and GPARAM nodes
are still present before parameter substitution.

Cached under .ast-cache/ keyed by source mtime, because a dump per module is
seconds and the checkers run over ~850 modules.
"""
import hashlib
import json
import os
import subprocess
import tempfile

CACHE = '.ast-cache'


def _walk(n, out):
    if isinstance(n, dict):
        out.append(n)
        for v in n.values():
            _walk(v, out)
    elif isinstance(n, list):
        for v in n:
            _walk(v, out)


def facts(sv_path, incdirs=(), verilator='verilator'):
    """-> {'ports': {name: dir}, 'params': [name], 'sequential': bool} or None."""
    stem = os.path.splitext(os.path.basename(sv_path))[0]
    try:
        key = hashlib.sha1(
            f'{sv_path}:{os.path.getmtime(sv_path)}'.encode()).hexdigest()[:16]
    except OSError:
        return None
    os.makedirs(CACHE, exist_ok=True)
    cached = os.path.join(CACHE, f'{key}.json')
    if os.path.exists(cached):
        return json.load(open(cached))

    with tempfile.TemporaryDirectory() as td:
        cmd = [verilator, '--lint-only', '--top-module', stem,
               '--dump-tree-json', '--dumpi-tree-json', '3', '--Mdir', td]
        for i in incdirs:
            cmd += ['-I' + i]
        cmd.append(sv_path)
        subprocess.run(cmd, capture_output=True, timeout=180)
        dumps = sorted(f for f in os.listdir(td) if f.endswith('.tree.json'))
        if not dumps:
            return None
        # earliest stage still holds PORT and GPARAM, before substitution
        tree = json.load(open(os.path.join(td, dumps[0])))
        # Scope to the TOP MODULE's own subtree. Walking the whole dump collects
        # every submodule's parameters too: apb4_master_stub was credited with
        # ALMOST_RD_MARGIN, MEM_STYLE and FLOP_COUNT, which belong to the FIFO
        # and synchroniser it instantiates. That inflated an "undocumented
        # parameter" count from tens to 201.
        allnodes = []
        _walk(tree, allnodes)
        top = next((n for n in allnodes
                    if n.get('type') == 'MODULE' and n.get('name') == stem), None)
        if top is None:
            return None
        nodes = []
        _walk(top, nodes)

    ports, params = {}, []
    for n in nodes:
        if n.get('type') != 'VAR':
            continue
        vt, name = n.get('varType'), n.get('name')
        if vt == 'GPARAM':
            params.append(name)
        elif vt == 'PORT':
            ports[name] = n.get('direction') or 'UNKNOWN'
    # Sequential iff the AST holds a clocked process. Verilator records the
    # source keyword on the ALWAYS node -- 'always_ff', 'always', 'cont_assign'
    # -- so a macro that expands to always_ff is indistinguishable from a
    # literal one, which is precisely what the regex could not do. A SENTREE
    # with an edge is the independent confirmation.
    seq = any(n.get('type') == 'ALWAYS'
              and n.get('keyword') in ('always_ff', 'always_latch', 'always')
              for n in nodes)
    if not seq:
        seq = any(n.get('type') == 'SENITEM'
                  and n.get('edgeType') in ('POS', 'NEG', 'BOTH') for n in nodes)
    out = {'ports': ports, 'params': sorted(set(params)), 'sequential': seq}
    json.dump(out, open(cached, 'w'))
    return out


if __name__ == '__main__':
    import sys
    f = facts(sys.argv[1], incdirs=sys.argv[2:])
    print(json.dumps(f, indent=2) if f else 'no AST')
