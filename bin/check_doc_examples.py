#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DocExampleCheck
# Purpose: An instantiation example must name ports the module actually has
#
# Documentation: vault/handbook/authoring/module-doc-template.md
# Subsystem: authoring
"""Fail when a doc page's instantiation example names a port the RTL lacks.

Twenty-eight pages carried examples with invented ports -- `apb4_slave` shown
with `clk`/`resetn` when it has neither, `axi4_master_rd` with `NUM_MASTERS`
and `NUM_SLAVES`. A reader copying one gets code that does not compile.

These survived every qc and humanize round because no reviewer cross-checks an
example against the port list, and at least two were INTRODUCED by a humanize
round: a voice pass rewrote `bin_to_bcd`'s example into ports the module never
had. A voice pass is free to reword prose; it is not qualified to invent an
interface, and nothing was checking.

Checked by name presence in the module source, which is deliberately weak: it
will not catch a wrong width or a swapped connection, only a name that does not
exist at all. That is the class that actually appeared.
"""
import os
import re
import subprocess
import sys

RE_CONN = re.compile(r'^\s*\.(\w+)\s*\(', re.M)


def module_src(root, stem):
    for base in ('rtl', 'projects'):
        for d, _s, files in os.walk(base):
            if f'{stem}.sv' in files:
                p = os.path.join(d, f'{stem}.sv')
                return re.sub(r'//[^\n]*', '', open(p, errors='ignore').read())
    return None


def main() -> int:
    root = subprocess.check_output(['git', 'rev-parse', '--show-toplevel']).decode().strip()
    os.chdir(root)
    bad = 0
    pages = 0
    # Index every module once, so a page can be checked against whatever module
    # its example actually instantiates rather than one guessed from the page
    # name. This is what lets the check reach projects/components, whose docs
    # are chaptered HAS/MAS books rather than per-module pages -- 109 of those
    # files carry SystemVerilog blocks and none was reachable before.
    index = {}
    for base in ('rtl', 'projects'):
        for d, _s, files in os.walk(base):
            for fn in files:
                if fn.endswith('.sv'):
                    index.setdefault(fn[:-3], os.path.join(d, fn))

    # An instantiation starts either `mod #(` or `mod u_name (`. Matching
    # only the first form meant a parameterless instantiation was not seen
    # as a new one, and its connections were blamed on the module above it
    # -- which is how `sync_pulse`'s ports were reported against
    # `cdc_synchronizer`.
    RE_INST = re.compile(
        r'^\s*([a-z][a-z0-9_]{3,})\s*(?:#\s*\(|u_\w+\s*\()', re.M)
    roots = ['docs'] + [os.path.join(r, 'docs')
                        for r, ds, _f in os.walk('projects') if 'docs' in ds]
    seen = set()
    for root in roots:
      for d, _s, files in os.walk(root):
        for fn in sorted(files):
            if not fn.endswith('.md'):
                continue
            path = os.path.join(d, fn)
            if path in seen:
                continue
            seen.add(path)
            text = open(path, errors='ignore').read()
            for blk in re.findall(r'```systemverilog(.*?)```', text, re.S):
                # Split the block at each instantiation so a connection is
                # attributed to the module it actually belongs to. A block with
                # two instantiations otherwise blames each module for the
                # other's ports -- which flagged correct pages and nearly had me
                # "fix" documentation that was right.
                starts = [(m.start(), m.group(1)) for m in RE_INST.finditer(blk)]
                for k, (pos, mod) in enumerate(starts):
                    if mod not in index:
                        continue
                    end = starts[k + 1][0] if k + 1 < len(starts) else len(blk)
                    seg = blk[pos:end]
                    src = re.sub(r'//[^\n]*', '',
                                 open(index[mod], errors='ignore').read())
                    miss = [c for c in RE_CONN.findall(seg)
                            if not re.search(rf'\b{re.escape(c)}\b', src)]
                    if miss:
                        bad += 1
                        print(f'  {path}: {mod} example names '
                              f'{", ".join(sorted(set(miss))[:5])}')

    for d, _s, files in os.walk('docs/markdown'):
        for fn in sorted(files):
            if not fn.endswith('.md'):
                continue
            path = os.path.join(d, fn)
            src = module_src(root, fn[:-3])
            if src is None:
                continue
            pages += 1
            text = open(path, errors='ignore').read()
            m = re.search(r'## Usage Examples(.*?)(?=\n## |\Z)', text, re.S)
            if not m:
                continue
            missing = [c for c in RE_CONN.findall(m.group(1))
                       if not re.search(rf'\b{re.escape(c)}\b', src)]
            if missing:
                bad += 1
                names = ', '.join(sorted(set(missing))[:6])
                print(f'  {path}: example names ports the module lacks -- {names}')
    print(f'\n{pages} module pages checked, {bad} with a fabricated example')
    # Five known findings in projects/components are tracked as TASK-077 and
    # are being fixed by hand -- a whole-block regeneration drops the other
    # instantiations in the same block. Ratchet: this must not GROW.
    BASELINE = 4
    if bad > BASELINE:
        print(f'  FAIL: {bad} exceeds the baseline of {BASELINE} (TASK-077)')
        return 1
    if bad < BASELINE:
        print(f'  baseline can be lowered to {bad} -- edit BASELINE')
    return 0


if __name__ == '__main__':
    sys.exit(main())
