#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Module: check_test_levels
# Purpose: Enforce the gate/func/full hard requirement across a test area.
# Subsystem: tooling
"""Check that every test offers gate/func/full through BOTH mechanisms.

The requirement ([[test-runner]]): REG_LEVEL must SELECT THE GRID, and
TEST_LEVEL must GATE THE DEPTH. Passing one is not passing the other.

**Why this parses instead of grepping.** Three successive regex versions of
this check each produced a different set of false positives on val/common:
one required a generator named `generate_*params*` and missed
`generate_test_parameters`; the next missed `get_cam_params` because the name
did not start with "generate"; a third used a fixed character window and
missed grids whose REG_LEVEL read sits far from the level literal. Each time
the count moved (24 -> 16 -> 6 -> 4) and each time some of the "findings" were
compliant tests. A scan that cries wolf gets ignored, so this walks the AST:
any function that reads REG_LEVEL and branches on a level literal counts as a
grid, whatever it is called.

TEST_LEVEL is searched across the test file PLUS its resolved TBClasses
imports, because the depth knob usually lives in the TB rather than the
wrapper.

    python3 bin/review/check_test_levels.py val/common
    python3 bin/review/check_test_levels.py val/amba

Exit 1 if anything is missing, so it can gate.
"""
import ast, glob, os, re, sys

def reads_env(node, name):
    """Does this subtree read os.environ for `name`?"""
    for n in ast.walk(node):
        if isinstance(n, ast.Constant) and n.value == name:
            return True
    return False

def has_grid(tree):
    """A grid exists if any function both reads REG_LEVEL and branches on a
    level literal. Covers generate_params, generate_test_parameters,
    get_cam_params, module-level dispatch dicts -- naming is irrelevant."""
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Module)):
            if not reads_env(node, 'REG_LEVEL'):
                continue
            src = ast.dump(node)
            if "'GATE'" in src or "'FULL'" in src or '"GATE"' in src or '"FULL"' in src:
                return True
    return False

def chain_text(p):
    s = open(p, encoding='utf-8', errors='replace').read()
    out = s
    for imp in set(re.findall(r'^\s*(?:from|import)\s+(TBClasses[\w.]*)', s, re.M)):
        rel = imp.replace('.', '/')
        for c in (f'bin/{rel}.py', f'bin/{rel}/__init__.py'):
            if os.path.isfile(c):
                out += open(c, encoding='utf-8', errors='replace').read()
    return s, out

area = sys.argv[1] if len(sys.argv) > 1 else 'val/common'
bad = []
files = sorted(glob.glob(f'{area}/test_*.py'))
for p in files:
    s, chain = chain_text(p)
    try:
        grid = has_grid(ast.parse(s))
    except SyntaxError as e:
        print(f"  PARSE ERROR {p}: {e}"); continue
    depth = 'TEST_LEVEL' in chain
    if not (grid and depth):
        bad.append((os.path.basename(p), '' if grid else 'grid', '' if depth else 'depth'))
print(f"{area}: {len(files)-len(bad)} of {len(files)} compliant")
for n, g, d in bad:
    print(f"  MISSING {n:44} {' + '.join(x for x in (g, d) if x)}")
sys.exit(1 if bad else 0)
