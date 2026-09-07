#!/usr/bin/env python3
"""A staged .sv must PARSE. Nothing cheaper is worth this much.

Commit 1d25191f converted every remaining flop to `ALWAYS_FF_RST` and left
SIXTEEN files that Verilator cannot parse. The converter had picked the wrong
`end` to replace with the macro's closing paren -- misled by sources whose
closing `end` was misindented to line up with the inner one -- and emitted

    `ALWAYS_FF_RST(clk, rst,
        if (`RST_ASSERTED(rst)) begin
            ...
    ) else begin                <-- the `end` is gone, the `)` is early
            ...
        end
        end                     <-- and the real close is still an `end`

Ten test failures surfaced a week later in one file, from one area's FULL run.
The other fifteen were invisible because nothing in dv/ references them: the
timing_characterization `asic_only` tree and a Yosys formal copy have no tests
at all. A file that does not parse is not a subtle defect. It is the cheapest
possible thing to detect, and it survived because nothing looked.

Reports ONLY genuine syntax errors -- not missing modules, not width warnings,
not lint opinions. A file is judged on whether it can be read, nothing more,
so this stays free of the pre-existing-warning noise that makes a gate
ignorable (silent-fallbacks rule 10).

Usage:
    check_sv_parses.py            # staged .sv (pre-commit)
    check_sv_parses.py <file>...  # explicit files
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

INCLUDE_RE = re.compile(r'^\s*`include\s+"([^"]+)"', re.M)


def repo_root() -> Path:
    return Path(subprocess.run(["git", "rev-parse", "--show-toplevel"],
                               capture_output=True, text=True,
                               check=True).stdout.strip())


def staged_sv(root: Path) -> list[str]:
    out = subprocess.run(["git", "diff", "--cached", "--name-only",
                          "--diff-filter=ACM"],
                         cwd=root, capture_output=True, text=True, check=True)
    return [f for f in out.stdout.splitlines() if f.endswith((".sv", ".svh"))]


def include_dirs(root: Path, path: Path) -> list[str]:
    """-I for the file's own directory plus wherever its `include targets live."""
    dirs = {str(path.parent)}
    try:
        text = path.read_text(errors="ignore")
    except OSError:
        return sorted(dirs)
    for name in INCLUDE_RE.findall(text):
        base = Path(name).name
        for hit in root.rglob(base):
            if ".git" not in hit.parts:
                dirs.add(str(hit.parent))
                break
    return sorted(dirs)


def parse_errors(root: Path, rel: str) -> list[str]:
    path = root / rel
    cmd = ["verilator", "--lint-only", "-sv", "--Wno-fatal"]
    for d in include_dirs(root, path):
        cmd.append(f"-I{d}")
    cmd.append(str(path))
    r = subprocess.run(cmd, cwd=root, capture_output=True, text=True)
    return [ln for ln in (r.stdout + r.stderr).splitlines()
            if "syntax error" in ln]


def main(argv: list[str]) -> int:
    root = repo_root()
    files = argv[1:] or staged_sv(root)
    files = [f for f in files if (root / f).is_file()]
    if not files:
        return 0

    broken: dict[str, list[str]] = {}
    for rel in files:
        errs = parse_errors(root, rel)
        if errs:
            broken[rel] = errs

    if broken:
        print("[sv-parse] staged file(s) do not parse:", file=sys.stderr)
        for rel, errs in broken.items():
            print(f"\n  {rel}", file=sys.stderr)
            for e in errs[:4]:
                print(f"    {e.strip()}", file=sys.stderr)
            if len(errs) > 4:
                print(f"    ... and {len(errs) - 4} more", file=sys.stderr)
        print("\n  These cannot simulate, lint, or synthesise. If the file is a\n"
              "  deliberately macro-free fork (the timing_characterization\n"
              "  asic_only tree, a Yosys formal copy), it must NOT be converted\n"
              "  to `ALWAYS_FF_RST at all -- revert it rather than repair it.",
              file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
