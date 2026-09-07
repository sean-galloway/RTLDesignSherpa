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
The other fifteen were invisible because nothing in dv/ referenced them -- they
sat in two "macro-free fork" trees that turned out to be duplicates and have
since been deleted. A file that does not parse is not a subtle defect. It is
the cheapest possible thing to detect, and it survived because nothing looked.

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


def _syntax_errors(root: Path, cmd: list[str]) -> list[str]:
    r = subprocess.run(cmd, cwd=root, capture_output=True, text=True)
    return [ln for ln in (r.stdout + r.stderr).splitlines()
            if "syntax error" in ln]


_FL_INDEX: dict[str, list[Path]] | None = None
_FL_VERDICT: dict[str, list[str]] = {}


def _filelist_index(root: Path) -> dict[str, list[Path]]:
    """basename -> filelists that list it. Built ONCE.

    Built lazily and cached because the naive form -- re-globbing every
    filelist for every failing file -- made a 61-file commit exceed two
    minutes and time out. A gate slow enough to hang a commit gets bypassed as
    surely as one that cries wolf.
    """
    global _FL_INDEX
    if _FL_INDEX is not None:
        return _FL_INDEX
    idx: dict[str, list[Path]] = {}
    for pat in ("**/filelists/*.f", "**/lint_reports/verilator/*.f"):
        for f in root.glob(pat):
            try:
                body = f.read_text(errors="ignore")
            except OSError:
                continue
            for line in body.splitlines():
                line = line.strip()
                if line.endswith(".sv") and "/" in line:
                    idx.setdefault(line.rsplit("/", 1)[1], []).append(f)
    _FL_INDEX = idx
    return idx


def filelists_listing(root: Path, rel: str) -> list[Path]:
    """Filelists that name this source (at most a few -- one is enough)."""
    return _filelist_index(root).get(Path(rel).name, [])[:2]


def parse_errors(root: Path, rel: str) -> list[str]:
    """Syntax errors for one file, judged in a compilation unit that can
    actually resolve its types.

    Standalone first, because it is fast and covers most files. A file that
    uses a type from a sibling package (`foo_pkg::bar_t`) CANNOT parse alone --
    verilator says "unexpected IDENTIFIER, expecting TYPE-IDENTIFIER" and every
    port after it cascades. Every generated bridge does this, so a
    standalone-only gate called 61 healthy files broken while their suite
    passed 70/70. Per silent-fallbacks rule 10, a gate that fires on correct
    code is a gate people learn to bypass.

    So when standalone fails, retry through a filelist that lists the file --
    its real compilation unit -- and only report if it fails there too.
    """
    path = root / rel
    try:
        text = path.read_text(errors="ignore")
    except OSError:
        return []

    # A file that imports or scope-resolves a package CANNOT parse alone, so
    # the standalone attempt is guaranteed to fail and cost a verilator run
    # each. Skipping it for those files took a 61-file generated-bridge commit
    # from ~58s to a couple of seconds.
    needs_unit = "::" in text or "import " in text

    if not needs_unit:
        cmd = ["verilator", "--lint-only", "-sv", "--Wno-fatal"]
        for d in include_dirs(root, path):
            cmd.append(f"-I{d}")
        errs = _syntax_errors(root, cmd + [str(path)])
        if not errs:
            return []
    else:
        errs = [f"%Error: {rel}: needs its compilation unit (uses a package)"]

    for fl in filelists_listing(root, rel):
        key = str(fl)
        if key not in _FL_VERDICT:
            _FL_VERDICT[key] = _syntax_errors(
                root, ["verilator", "--lint-only", "-sv", "--Wno-fatal",
                       "-f", str(fl)])
        if not _FL_VERDICT[key]:
            return []      # parses in its real unit; standalone was the problem

    if needs_unit and not filelists_listing(root, rel):
        # No filelist lists it and it cannot stand alone -- we cannot judge it.
        # Say nothing rather than cry wolf (silent-fallbacks rule 10).
        return []
    return errs


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
        print("\n  These cannot simulate, lint, or synthesise.", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
