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

**Presence is not wiring (2026-08-05).** The AST rewrite above still checked
the depth half with `'TEST_LEVEL' in <test text + TB text>` -- a substring
search satisfied by the name appearing in a comment. It reported val/common
48 of 48 compliant while THIRTEEN tests had a depth mechanism that could not
move: wrappers that never put TEST_LEVEL in extra_env (the TB then reads the
default forever), grids that pin `test_levels = ['full']` in all three
REG_LEVEL branches, and a TB that never reads the variable its wrapper
exports. An external test review found them one file at a time; this tool had
certified every one. That is worse than no tool, because the green line is
what people quote.

So the depth half is now three checks, all on the AST:

  EXPORTED  the wrapper hands TEST_LEVEL to the simulator (a dict literal key
            or `env['TEST_LEVEL'] = ...`), not merely mentions it
  VARYING   the exported value is not a fixed literal, and any `test_level(s)`
            grid feeding it holds more than one distinct level across its
            branches
  CONSUMED  something in the TB chain actually reads os.environ for it --
            an `os.environ.get('TEST_LEVEL')` or `os.environ['TEST_LEVEL']`,
            not the bare string

    python3 bin/review/check_test_levels.py val/common
    python3 bin/review/check_test_levels.py val/amba

Exit 1 if anything is missing, so it can gate.
"""
import ast, glob, os, re, sys

LEVELS = {'gate', 'func', 'full'}


def _is_environ(node):
    return ((isinstance(node, ast.Attribute) and node.attr == 'environ')
            or (isinstance(node, ast.Name) and node.id == 'environ'))


def reads_environ(tree, name):
    """A real os.environ read of `name` -- not the bare string somewhere."""
    for n in ast.walk(tree):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr == 'get' and _is_environ(n.func.value)
                and n.args and isinstance(n.args[0], ast.Constant)
                and n.args[0].value == name):
            return True
        if isinstance(n, ast.Subscript) and _is_environ(n.value):
            sl = n.slice.value if isinstance(n.slice, ast.Index) else n.slice
            if isinstance(sl, ast.Constant) and sl.value == name:
                return True
    return False


def mentions_name(node, name):
    """Any constant equal to `name` in this subtree (used for REG_LEVEL grids,
    where the read may be indirect)."""
    return any(isinstance(n, ast.Constant) and n.value == name
               for n in ast.walk(node))


def has_grid(tree):
    """A grid exists if any function both reads REG_LEVEL and branches on a
    level literal. Covers generate_params, generate_test_parameters,
    get_cam_params, module-level dispatch dicts -- naming is irrelevant."""
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Module)):
            if not mentions_name(node, 'REG_LEVEL'):
                continue
            src = ast.dump(node)
            if "'GATE'" in src or "'FULL'" in src or '"GATE"' in src or '"FULL"' in src:
                return True
    return False


def exported_values(tree, name):
    """Expressions the wrapper hands to the simulator for `name`."""
    vals = []
    for n in ast.walk(tree):
        if isinstance(n, ast.Dict):
            for k, v in zip(n.keys, n.values):
                if isinstance(k, ast.Constant) and k.value == name:
                    vals.append(v)
        if isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Subscript):
                    sl = t.slice.value if isinstance(t.slice, ast.Index) else t.slice
                    if isinstance(sl, ast.Constant) and sl.value == name:
                        vals.append(n.value)
    return vals


def _levels_in(node):
    return {n.value for n in ast.walk(node)
            if isinstance(n, ast.Constant) and n.value in LEVELS}


def grid_levels(tree):
    """Distinct levels the exported value can actually take.

    Read only assignments to `test_level(s)`, then follow ONE level of
    indirection into any name they reference. Both halves are needed:

    - Whole-module scanning is too loose. Every wrapper mentions some level
      literal somewhere (a default, a map used for the test name), so it
      declared all eight genuinely-pinned tests compliant.
    - Reading the assignment alone is too tight. The level often arrives via a
      lookup table -- `test_level = test_level_map.get(reg_level, 'gate')` --
      where the assignment holds only the default argument, which flagged a
      compliant test_counter_freq_invariant as pinned.

    So `test_levels = ['full']` in all three branches yields {'full'} and is
    reported; the map lookup resolves through test_level_map to all three.
    """
    by_name = {}
    for n in ast.walk(tree):
        if isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Name):
                    by_name.setdefault(t.id, set()).update(_levels_in(n.value))

    seen = set()
    for n in ast.walk(tree):
        if not isinstance(n, ast.Assign):
            continue
        if not any(isinstance(t, ast.Name) and re.fullmatch(r'test_levels?', t.id)
                   for t in n.targets):
            continue
        seen |= _levels_in(n.value)
        for ref in ast.walk(n.value):
            if isinstance(ref, ast.Name) and ref.id in by_name:
                seen |= by_name[ref.id]
    return seen


def tb_chain(p):
    """Resolved TBClasses files this test imports (one level, plus their own)."""
    out, seen = [], set()
    pending = [p]
    while pending:
        cur = pending.pop()
        try:
            s = open(cur, encoding='utf-8', errors='replace').read()
        except OSError:
            continue
        for imp in set(re.findall(r'^\s*(?:from|import)\s+(TBClasses[\w.]*)', s, re.M)):
            rel = imp.replace('.', '/')
            for c in (f'bin/{rel}.py', f'bin/{rel}/__init__.py'):
                if os.path.isfile(c) and c not in seen:
                    seen.add(c)
                    out.append(c)
                    pending.append(c)
    return out


def check(p):
    """Return a list of reasons this test fails the requirement."""
    bad = []
    try:
        tree = ast.parse(open(p, encoding='utf-8', errors='replace').read())
    except SyntaxError as e:
        return [f'PARSE ERROR: {e}']

    if not has_grid(tree):
        bad.append('grid')

    vals = exported_values(tree, 'TEST_LEVEL')
    if not vals:
        bad.append('depth:not-exported')
    else:
        levels = grid_levels(tree)
        literal_only = all(isinstance(v, ast.Constant) for v in vals)
        if literal_only and len({v.value for v in vals if isinstance(v, ast.Constant)}) < 2:
            bad.append('depth:pinned-literal')
        elif levels and len(levels) < 2:
            bad.append(f'depth:pinned-grid({levels.pop()})')

    chain = tb_chain(p)
    consumed = reads_environ(tree, 'TEST_LEVEL')
    for c in chain:
        if consumed:
            break
        try:
            consumed = reads_environ(ast.parse(open(c, encoding='utf-8', errors='replace').read()),
                                     'TEST_LEVEL')
        except SyntaxError:
            continue
    if not consumed:
        bad.append('depth:never-read')
    return bad


def main():
    area = sys.argv[1] if len(sys.argv) > 1 else 'val/common'
    files = sorted(glob.glob(f'{area}/test_*.py'))
    bad = [(os.path.basename(p), r) for p in files if (r := check(p))]
    print(f"{area}: {len(files) - len(bad)} of {len(files)} compliant")
    for n, reasons in bad:
        print(f"  MISSING {n:46} {', '.join(reasons)}")
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
