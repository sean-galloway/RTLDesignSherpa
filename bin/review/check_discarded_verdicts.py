#!/usr/bin/env python3
"""Find scenario verdicts that are computed and then thrown away.

A TB scenario that returns False on failure is only a test if somebody
reads the answer. Written as a bare statement --

    await tb.test_burst_tracking(num_bursts=15)     # verdict discarded

-- the scenario reports its failure into the void and the suite stays
green. Found in the converters (CONV-002): two entire test files whose
every scenario was failing while 22 configurations reported pass.

Reports only what is actually dangerous:

  * the call must be a bare expression statement inside a @cocotb.test
    (an assignment like `ok = await tb.foo()` is someone taking the
    verdict somewhere, and TB-internal calls often handle it another way);
  * the callee must be able to `return False`;
  * and it must NOT assert internally -- a scenario that asserts cannot
    fail silently no matter what the caller does with its return value.

The callee is resolved through the TB class the file constructs, not by
name: `run_basic_test` exists in a dozen unrelated classes, and matching
on the name alone reports both "safe" and "silent fail" for the same
line.

Usage: check_discarded_verdicts.py [root]
Exit 1 if any dangerous discard is found.
"""
import ast
import pathlib
import re
import sys

SKIP = ("venv", "__pycache__", "local_sim_build", ".git", "obj_dir",
        # Worktrees are OTHER sessions' checkouts of this same repo. Scanning
        # them double-counts every finding and attributes it to a path nobody
        # can fix from here: the one scenario-level discard this tool reported
        # on 2026-09-14 was a stale copy of a file the main tree had already
        # fixed. Never report on a tree you are not in.
        ".claude", "worktrees")


def _returns_false(fn):
    return any(isinstance(n, ast.Return) and isinstance(n.value, ast.Constant)
               and n.value.value is False for n in ast.walk(fn))


def _asserts(fn):
    return any(isinstance(n, ast.Assert) for n in ast.walk(fn))


def _is_cocotb_test(fn):
    return any("cocotb.test" in ast.unparse(d) for d in fn.decorator_list)


def index_classes(root):
    """class name -> [(path, {method: (returns_false, asserts)})]"""
    out = {}
    for p in root.rglob("*.py"):
        if any(x in p.parts for x in SKIP):
            continue
        try:
            tree = ast.parse(p.read_text(errors="replace"))
        except (SyntaxError, ValueError):
            continue
        for n in ast.walk(tree):
            if not isinstance(n, ast.ClassDef):
                continue
            meths = {m.name: (_returns_false(m), _asserts(m))
                     for m in n.body
                     if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))}
            out.setdefault(n.name, []).append((str(p), meths))
    return out


def scan(root):
    classes = index_classes(root)
    findings = []
    for p in root.rglob("*.py"):
        if any(x in p.parts for x in SKIP):
            continue
        src = p.read_text(errors="replace")
        try:
            tree = ast.parse(src)
        except (SyntaxError, ValueError):
            continue

        local = {n.name: n for n in ast.walk(tree)
                 if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
        constructed = re.findall(r"^\s*(?:tb|self\.tb)\s*=\s*(\w+)\s*\(", src, re.M)

        for fn in ast.walk(tree):
            if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            if not _is_cocotb_test(fn):
                continue
            for node in ast.walk(fn):
                if not isinstance(node, ast.Expr):
                    continue
                call = node.value
                if isinstance(call, ast.Await):
                    call = call.value
                if not isinstance(call, ast.Call):
                    continue
                f = call.func
                name = (f.attr if isinstance(f, ast.Attribute)
                        else f.id if isinstance(f, ast.Name) else None)
                if not name:
                    continue

                info = None
                if isinstance(f, ast.Name) and name in local:
                    m = local[name]
                    info = (_returns_false(m), _asserts(m), "(local)")
                elif constructed:
                    for path, meths in classes.get(constructed[0], []):
                        if name in meths:
                            info = (*meths[name], constructed[0])
                            break
                if info and info[0] and not info[1]:
                    findings.append((str(p), node.lineno, fn.name, name, info[2]))
    return findings


# Ratchet baseline, in the shape filelist_registry.py already uses: a count
# per file that may shrink but never grow. A hard gate is not an option here --
# there are 100 pre-existing discards in helpers (generate_test_report,
# wait_for_channel_idle, _set), and CONV-002's own lesson is that turning on
# a wall of red "diagnoses nothing and blocks everyone".
BASELINE = pathlib.Path(__file__).resolve().parents[2] / "bin" / "review" / \
    "discarded_verdicts_baseline.json"


def _ratchet(findings) -> int:
    import collections, json
    cur = collections.Counter()
    for path, _l, _t, _m, _o in findings:
        cur[_rel(path)] += 1
    if not BASELINE.exists():
        BASELINE.write_text(json.dumps(dict(sorted(cur.items())), indent=2) + "\n")
        print(f"wrote baseline: {sum(cur.values())} discard(s) in {len(cur)} file(s)")
        return 0
    base = json.loads(BASELINE.read_text())
    grew = {f: (base.get(f, 0), n) for f, n in cur.items() if n > base.get(f, 0)}
    if grew:
        print("Discarded verdicts GREW -- a False in these is invisible:\n")
        for f, (was, now) in sorted(grew.items()):
            print(f"  {f}: {was} -> {now}")
        print("\nAssign and assert the result, or make the scenario assert "
              "internally.\nIf a file legitimately shrank elsewhere, re-baseline "
              "with --baseline.")
        return 1
    shrank = sum(base.get(f, 0) - cur.get(f, 0) for f in base)
    print(f"PASS (ratchet): no file grew. {sum(cur.values())} discard(s) "
          f"outstanding" + (f", {shrank} fewer than baseline" if shrank > 0 else "")
          + ". See CONV-002.")
    return 0


def _rel(path):
    try:
        return str(pathlib.Path(path).resolve().relative_to(
            pathlib.Path(__file__).resolve().parents[2]))
    except ValueError:
        return str(path)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    flags = {a for a in sys.argv[1:] if a.startswith("-")}
    root = pathlib.Path(args[0] if args else ".")
    findings = scan(root)
    if "--baseline" in flags:
        BASELINE.unlink(missing_ok=True)
        return _ratchet(findings)
    if "--ratchet" in flags:
        return _ratchet(findings)
    if not findings:
        print("No discarded scenario verdicts.")
        return 0
    print(f"{len(findings)} discarded verdict(s) -- a False here is invisible:\n")
    cur = None
    for path, line, test, meth, owner in sorted(findings):
        rel = path.replace(str(root) + "/", "")
        if rel != cur:
            print(rel)
            cur = rel
        print(f"    {line:>5}  {test}() -> {meth}()   [{owner}]")
    print("\nAssign and assert the result, or make the scenario assert internally.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
