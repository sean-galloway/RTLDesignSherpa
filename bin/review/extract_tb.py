#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: extract_tb
# Purpose: Move an inline TB class out of a test runner into bin/TBClasses/.
# Subsystem: tooling
"""Split a test file into a runner and a TB class.

The rule ([[tb-structure]]): a `val/<area>/test_*.py` is a RUNNER -- a
parameter grid plus a `cocotb_test.run()` call. The testbench belongs in
`bin/TBClasses/<area>/`, where other tests can use it and where the review
bundle collects it as a distinct artifact. 101 tests across the tree still
define their TB inline.

This moves one class and rewrites the import. It works out which module-level
imports the class actually references (by walking the class body for Names and
Attribute roots) rather than copying the runner's whole import block, because a
TB module carrying `cocotb_test.simulator.run` is the same coupling in reverse.

    python3 bin/review/extract_tb.py val/cdc/test_bin2gray.py            # dry run
    python3 bin/review/extract_tb.py val/cdc/test_bin2gray.py --apply

Refuses when the class references a module-level name that is neither an
import nor a class -- a shared constant or helper has to be dealt with
deliberately, not silently duplicated.
"""
from __future__ import annotations

import argparse
import ast
import builtins
import os
import re
import sys

HEADER = """# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: {cls}
# Purpose: Testbench for {mod}
# Subsystem: framework
#
# Extracted from {src} so the runner holds only the parameter grid and the
# cocotb_test.run() call ([[tb-structure]]).

"""


def names_used(node: ast.AST) -> set[str]:
    out = set()
    for n in ast.walk(node):
        if isinstance(n, ast.Name):
            out.add(n.id)
        elif isinstance(n, ast.Attribute):
            root = n
            while isinstance(root, ast.Attribute):
                root = root.value
            if isinstance(root, ast.Name):
                out.add(root.id)
    return out


def bound_names(stmt: ast.stmt) -> set[str]:
    """Names an import statement binds."""
    out = set()
    if isinstance(stmt, ast.Import):
        for a in stmt.names:
            out.add((a.asname or a.name).split('.')[0])
    elif isinstance(stmt, ast.ImportFrom):
        for a in stmt.names:
            out.add(a.asname or a.name)
    return out


def unresolved(mod_src: str) -> list[str]:
    """Names the extracted module loads but never binds.

    The real post-condition. Import selection is a heuristic -- an import used
    only inside a method, a name that arrives from a helper class, a module
    that was imported locally in the original -- so rather than trust it, parse
    the result and check every Load resolves. Cheaper than a simulation, and it
    catches exactly the class of break that a syntax check does not.
    """
    tree = ast.parse(mod_src)
    bound = set(dir(builtins)) | {'self'}
    for n in tree.body:
        if isinstance(n, ast.Import):
            for a in n.names: bound.add((a.asname or a.name).split('.')[0])
        elif isinstance(n, ast.ImportFrom):
            for a in n.names: bound.add(a.asname or a.name)
        elif isinstance(n, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            bound.add(n.name)
        elif isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Name): bound.add(t.id)
    local = set()
    for n in ast.walk(tree):
        # Lambda counts: `lambda p: p & 0x7f` binds p, and omitting it made
        # the check report a clean extraction as broken.
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            local |= {a.arg for a in n.args.args + n.args.kwonlyargs
                      + getattr(n.args, 'posonlyargs', [])}
            if n.args.vararg: local.add(n.args.vararg.arg)
            if n.args.kwarg: local.add(n.args.kwarg.arg)
        if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
            for t in ast.walk(n):
                if isinstance(t, ast.Name) and isinstance(t.ctx, ast.Store): local.add(t.id)
        if isinstance(n, ast.For):
            for t in ast.walk(n.target):
                if isinstance(t, ast.Name): local.add(t.id)
        if isinstance(n, ast.comprehension):
            for t in ast.walk(n.target):
                if isinstance(t, ast.Name): local.add(t.id)
        if isinstance(n, ast.ExceptHandler) and n.name: local.add(n.name)
        if isinstance(n, ast.withitem) and n.optional_vars:
            for t in ast.walk(n.optional_vars):
                if isinstance(t, ast.Name): local.add(t.id)
        if isinstance(n, (ast.Import, ast.ImportFrom)):
            for a in n.names: local.add((a.asname or a.name).split('.')[0])
    used = {n.id for n in ast.walk(tree)
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)}
    return sorted(used - bound - local)


def extract(path: str, apply: bool) -> int:
    src = open(path, encoding='utf-8').read()
    tree = ast.parse(src)
    lines = src.splitlines(keepends=True)

    classes = [n for n in tree.body
               if isinstance(n, ast.ClassDef)
               and any(getattr(b, 'id', '') == 'TBBase' for b in n.bases)]
    if not classes:
        print(f"  {path}: no inline TBBase class"); return 0
    if len(classes) > 1:
        print(f"  {path}: {len(classes)} TB classes -- handle by hand"); return 1

    cls = classes[0]
    used = names_used(cls)

    imports = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom))]
    needed, kept = [], []
    for imp in imports:
        b = bound_names(imp)
        (needed if (b & used) else kept).append(imp)

    # module-level definitions the class leans on that are NOT imports
    module_defs = {t.id for n in tree.body if isinstance(n, ast.Assign)
                   for t in n.targets if isinstance(t, ast.Name)}
    module_defs |= {n.name for n in tree.body
                    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
    # Helper CLASSES count too. Missing this shipped two broken extractions:
    # test_apb_master defines APBGAXIScoreboard in the runner (its import is
    # commented out -- "use the improved version below"), and
    # test_monitor_trans_cam defines TransCamConfig/_TransCamModel. The TB
    # moved, the helper did not, and the failure was a NameError at run time
    # rather than anything a parse would catch.
    module_defs |= {n.name for n in tree.body
                    if isinstance(n, ast.ClassDef) and n is not cls}
    leaked = (used & module_defs)
    if leaked:
        print(f"  {path}: class references module-level {sorted(leaked)} -- "
              f"resolve by hand, not extracting")
        return 1

    area = os.path.basename(os.path.dirname(path))
    stem = re.sub(r'^test_', '', os.path.basename(path))[:-3]
    out_dir = f'bin/TBClasses/{area}'
    out_path = f'{out_dir}/{stem}_tb.py'

    imp_src = ''.join(''.join(lines[i.lineno - 1:i.end_lineno]) for i in needed)
    cls_src = ''.join(lines[cls.lineno - 1:cls.end_lineno])
    new_mod = HEADER.format(cls=cls.name, mod=stem, src=path) + imp_src + '\n\n' + cls_src

    # runner: drop the class, import it instead
    runner = ''.join(lines[:cls.lineno - 1]) + ''.join(lines[cls.end_lineno:])
    imp_line = f'from TBClasses.{area}.{stem}_tb import {cls.name}\n'
    m = re.search(r'^from TBClasses\.[\w.]+ import .*$', runner, re.M)
    if m:
        runner = runner[:m.end() + 1] + imp_line + runner[m.end() + 1:]
    else:
        m2 = re.search(r'^(import|from) .*$', runner, re.M)
        runner = runner[:m2.end() + 1] + imp_line + runner[m2.end() + 1:]

    missing = unresolved(new_mod)
    if missing:
        print(f"  {path}: extracted module would not resolve {missing[:5]} -- "
              f"not extracting")
        return 1

    print(f"  {os.path.basename(path):42} -> {out_path}  ({cls.name}, "
          f"{len(needed)} imports, {cls.end_lineno - cls.lineno + 1} lines)")
    if apply:
        os.makedirs(out_dir, exist_ok=True)
        init = f'{out_dir}/__init__.py'
        if not os.path.exists(init):
            open(init, 'w').write('')
        open(out_path, 'w', encoding='utf-8').write(new_mod)
        open(path, 'w', encoding='utf-8').write(runner)
        ast.parse(new_mod); ast.parse(runner)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('paths', nargs='+')
    ap.add_argument('--apply', action='store_true')
    a = ap.parse_args()
    bad = 0
    for p in a.paths:
        bad += extract(p, a.apply)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
