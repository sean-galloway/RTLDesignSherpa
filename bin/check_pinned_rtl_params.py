#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""PUMICE-028 sweep: RTL parameters that cannot vary per test.

The PUMICE-041 shape: the `parameters=` dict that ELABORATES the RTL is fed a
value fixed at import, while the per-test value of that same quantity reaches
only the testbench. The arguments are right and the DUT is still built wrong,
so comparing a test's arguments against its intent cannot find it -- only the
provenance of the elaborated value can.

A parameter is PINNED when its value expression is reachable from no function
argument and no local assignment -- a bare literal, or a module-level constant.
Pinned is not automatically wrong: most parameters are legitimately fixed. It
is wrong when the same quantity is ALSO parametrized in that file, which is
reported as a twin.
"""
import ast, sys, pathlib, re

ENVISH = re.compile(r'^(LOG_PATH|SEED|DUT|COCOTB|TEST_|VERILATOR|COVERAGE)')

def norm(n): return re.sub(r'[^a-z0-9]', '', n.lower())

def analyse(path):
    src = pathlib.Path(path).read_text()
    tree = ast.parse(src)
    consts = {}
    for node in tree.body:
        if isinstance(node, ast.Assign):
            for t in node.targets:
                if isinstance(t, ast.Name) and t.id.isupper():
                    try: consts[t.id] = ast.literal_eval(node.value)
                    except Exception: consts[t.id] = '<expr>'

    rows, examined = [], 0
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        args   = {a.arg for a in fn.args.args}
        locals_ = set()
        for n in ast.walk(fn):
            if isinstance(n, ast.Assign):
                for t in n.targets:
                    if isinstance(t, ast.Name): locals_.add(t.id)
            elif isinstance(n, (ast.For, ast.comprehension)):
                tgt = getattr(n, 'target', None)
                for x in ast.walk(tgt) if tgt else []:
                    if isinstance(x, ast.Name): locals_.add(x.id)
        varying = args | locals_

        # find the dict passed as parameters=
        for call in [n for n in ast.walk(fn) if isinstance(n, ast.Call)]:
            for kw in call.keywords:
                if kw.arg != 'parameters': continue
                d = kw.value
                if isinstance(d, ast.Name):           # resolve one level
                    want = d.id
                    for n in ast.walk(fn):
                        if (isinstance(n, ast.Assign) and isinstance(n.value, ast.Dict)
                            and any(isinstance(t, ast.Name) and t.id == want
                                    for t in n.targets)):
                            d = n.value
                            break
                if not isinstance(d, ast.Dict): continue
                # names that already supply SOME parameter in this dict are not
                # orphaned -- APB_DATA_WIDTH pinned to 32 beside a DATA_WIDTH fed
                # by `data_width` is two quantities, not one pinned by accident.
                supplying = set()
                for _k, _v in zip(d.keys, d.values):
                    for _x in ast.walk(_v):
                        if isinstance(_x, ast.Name) and _x.id in varying:
                            supplying.add(_x.id)
                for k, v in zip(d.keys, d.values):
                    if not (isinstance(k, ast.Constant) and isinstance(k.value, str)): continue
                    key = k.value
                    if ENVISH.match(key): continue
                    examined += 1
                    names = {x.id for x in ast.walk(v) if isinstance(x, ast.Name)}
                    if names & varying: continue          # genuinely per-test
                    kk = norm(key)
                    twins = sorted(a for a in varying
                                   if len(norm(a)) >= 2 and norm(a) in kk
                                   and a not in supplying)
                    src_desc = (f"module const {sorted(names & set(consts))}"
                                if names & set(consts) else
                                f"literal {ast.unparse(v)}")
                    rows.append((fn.name, key, src_desc, twins))
    return rows, examined

SELF_TEST = """
DRAM_BL = 8
def _run(bl, dfi_rate):
    run(parameters={"DRAM_BL": str(DRAM_BL), "DFI_RATE": str(dfi_rate)})
"""

def _self_test():
    """The checker must fail on the defect it was written for.

    This is the PUMICE-041 shape reduced to six lines: a per-test `bl` that
    reaches the testbench while the elaborated DRAM_BL comes from the
    module-level constant. A checker that cannot fail here reports "0
    violations" over a suite it is not actually inspecting, which is the
    failure mode this file exists to prevent -- so the self-test is not
    optional decoration, it is the warrant for the count below it.
    """
    import tempfile, os
    with tempfile.NamedTemporaryFile('w', suffix='.py', delete=False) as fh:
        fh.write(SELF_TEST); tmp = fh.name
    try:
        rows, _ = analyse(tmp)
        bad = [r for r in rows if r[3]]
        if len(bad) != 1 or bad[0][1] != 'DRAM_BL':
            print(f"SELF-TEST FAILED: expected 1 hit on DRAM_BL, got {bad}")
            return False
        print("self-test ok: the PUMICE-041 shape is detected")
        return True
    finally:
        os.unlink(tmp)


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('files', nargs='*', help='test_*.py files to inspect')
    ap.add_argument('--self-test', action='store_true',
                    help='prove the checker fails on the defect it targets, then exit')
    ns = ap.parse_args(argv)

    if ns.self_test:
        return 0 if _self_test() else 1
    if not ns.files:
        ap.error('no files given (pass test_*.py paths, or --self-test)')
    if not _self_test():
        return 1

    tot_ex = tot_pin = tot_bad = 0
    for p in ns.files:
        try:
            rows, ex = analyse(p)
        except SyntaxError as e:
            print(f"?? {p}: unparseable ({e})")
            continue
        tot_ex += ex; tot_pin += len(rows)
        bad = [r for r in rows if r[3]]
        tot_bad += len(bad)
        if bad:
            print(f"\n### {p}")
            for fn, key, sd, twins in bad:
                print(f"  !! {fn}(): {key} <- {sd}   ||  parametrized twin in scope: {twins}")
    print(f"\n== {tot_ex} RTL parameters examined, {tot_pin} pinned, "
          f"{tot_bad} pinned WITH a parametrized twin ==")
    return 1 if tot_bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
