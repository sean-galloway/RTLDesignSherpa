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

SKIP = ("venv", "__pycache__", "local_sim_build", ".git", "obj_dir")


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


def main():
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    findings = scan(root)
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
