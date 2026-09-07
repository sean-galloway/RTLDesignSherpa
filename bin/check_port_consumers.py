#!/usr/bin/env python3
"""Adding a port to a module breaks every consumer that does not connect it.

On 2026-09-07 `ow_mant_interp` was added to `math_bf16_fast_reciprocal`.
Two of its three consumers were updated. The third,
`math_bf16_newton_raphson_recip`, was not, and Verilator's PINMISSING is an
ERROR under the flags cocotb passes -- so all five of that module's tests
failed to BUILD. They did not fail an assertion; they never simulated.

The FUNC subset never elaborated that module, so a raw `pytest math` run was
green. Only the FULL matrix built it. The gap between "the suite is green" and
"the design compiles" was fifteen minutes of wall clock and one changed port.

Verilator finds this in under a second, from a filelist that already exists.
So a script owns it, not a reviewer and not a full regression.

Scope is deliberately narrow, to keep it free of false positives:

  * only .sv files whose module PORT SET changed against HEAD are considered
    (a body-only edit triggers nothing);
  * only the flattened lint filelists that actually list the changed file are
    linted -- these are that module's real consumers;
  * only PINMISSING / PINNOTFOUND / PINCONNECTEMPTY are reported. Areas carry
    pre-existing warnings, and a gate that fails on those gets bypassed, which
    is the same as not having one.

Usage:
    check_port_consumers.py            # staged .sv (pre-commit)
    check_port_consumers.py <file>...  # explicit files
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

PIN_ERRORS = ("PINMISSING", "PINNOTFOUND", "PINCONNECTEMPTY")

# `module foo #(...) ( ... );` -- we only need the port NAME set, so match the
# direction keyword and take the last identifier before , or ) or a comment.
PORT_RE = re.compile(
    r"^\s*(?:input|output|inout)\b[^;]*?([A-Za-z_]\w*)\s*(?:,|\)|$)", re.M
)
MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z_]\w*)", re.M)


def repo_root() -> Path:
    return Path(subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True, check=True).stdout.strip())


def port_set(text: str) -> set[str]:
    """Port names in the module header (everything before the first
    `endmodule`; good enough, since we compare a file against ITSELF)."""
    head = text.split("endmodule", 1)[0]
    return set(PORT_RE.findall(head))


def head_blob(root: Path, rel: str) -> str | None:
    r = subprocess.run(["git", "show", f"HEAD:{rel}"],
                       cwd=root, capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def staged_sv(root: Path) -> list[str]:
    r = subprocess.run(["git", "diff", "--cached", "--name-only",
                        "--diff-filter=ACM"],
                       cwd=root, capture_output=True, text=True, check=True)
    return [f for f in r.stdout.splitlines() if f.endswith(".sv")]


def consumers_of(root: Path, rel: str) -> list[Path]:
    """Flattened lint filelists that list this source AND are not its own."""
    hits = []
    name = Path(rel).name
    for f in root.glob("rtl/*/lint_reports/verilator/*.f"):
        if f.stem == Path(rel).stem:
            continue                      # the module's own filelist
        body = f.read_text(errors="ignore")
        if any(line.strip().endswith("/" + name) for line in body.splitlines()):
            hits.append(f)
    return sorted(hits)


def lint(root: Path, filelist: Path) -> list[str]:
    r = subprocess.run(
        ["verilator", "--lint-only", "-sv", "-f", str(filelist)],
        cwd=root, capture_output=True, text=True)
    return [ln for ln in (r.stdout + r.stderr).splitlines()
            if any(e in ln for e in PIN_ERRORS)]


def main(argv: list[str]) -> int:
    root = repo_root()
    files = argv[1:] or staged_sv(root)
    if not files:
        return 0

    changed: list[str] = []
    for rel in files:
        path = root / rel
        if not path.is_file():
            continue
        old = head_blob(root, rel)
        if old is None:
            continue                      # new file: no consumers can be stale
        if port_set(old) != port_set(path.read_text(errors="ignore")):
            changed.append(rel)

    if not changed:
        return 0

    failures: dict[str, list[str]] = {}
    unchecked: list[str] = []
    for rel in changed:
        cons = consumers_of(root, rel)
        if not cons:
            unchecked.append(rel)
            continue
        for fl in cons:
            bad = lint(root, fl)
            if bad:
                failures.setdefault(fl.stem, []).extend(bad)

    for rel in unchecked:
        mods = MODULE_RE.findall((root / rel).read_text(errors="ignore"))
        print(f"[port-consumers] note: {rel} changed its port list "
              f"({', '.join(mods) or 'module'}) but no OTHER lint filelist "
              f"lists it, so no consumer was checked.", file=sys.stderr)

    if failures:
        print("[port-consumers] a changed port list broke its consumers:",
              file=sys.stderr)
        for stem, lines in failures.items():
            print(f"\n  consumer: {stem}", file=sys.stderr)
            for ln in lines[:6]:
                print(f"    {ln.strip()}", file=sys.stderr)
        print("\n  Connect the port at every instantiation (an explicit empty"
              "\n  connection, `.port()`, is fine when the consumer does not"
              "\n  want it -- it says so on purpose). PINMISSING is an ERROR"
              "\n  under the flags cocotb passes, so these do not fail a test:"
              "\n  they fail the BUILD, and the test never runs.", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
