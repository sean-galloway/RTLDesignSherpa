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
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
