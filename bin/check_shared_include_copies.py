#!/usr/bin/env python3
"""A shared include may be copied, but a copy may not DIVERGE.

`rtl/amba/includes/reset_defs.svh` decides whether every flop in the repo
resets asynchronously. On 2026-09-07 it was made unconditionally async --
and eight tracked copies of it, one of them live in the
timing_characterization build, kept the old conditional. That component's
flops would have elaborated with SYNCHRONOUS reset while the rest of the
tree was async, and nothing in the repo compared the two files, so the
split was invisible: both trees compiled, both passed, and they disagreed
about what the hardware was.

Seven of those copies turned out to be dead artifacts. Deleting them is
not a fix on its own, because the reason they rotted -- nobody diffs a
copy -- survives the deletion. This does the diff.

Copies are allowed. A component may vendor a shared include to keep its
filelist self-contained. What is not allowed is a copy whose CONTENT has
drifted from the canonical file.

Exit 0 if every copy matches, 1 otherwise.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

# basename -> canonical path, relative to the repo root.
CANONICAL = {
    "reset_defs.svh": "rtl/amba/includes/reset_defs.svh",
}


def tracked_files(root: Path) -> list[str]:
    out = subprocess.run(
        ["git", "ls-files"], cwd=root, capture_output=True, text=True, check=True
    )
    return out.stdout.splitlines()


def main() -> int:
    root = Path(
        subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    )

    files = tracked_files(root)
    failures: list[tuple[str, str]] = []

    for basename, canon_rel in CANONICAL.items():
        canon = root / canon_rel
        if not canon.is_file():
            print(f"[shared-includes] canonical file missing: {canon_rel}", file=sys.stderr)
            return 1
        want = canon.read_bytes()

        for rel in files:
            if Path(rel).name != basename or rel == canon_rel:
                continue
            path = root / rel
            if not path.is_file():
                continue  # staged deletion
            if path.read_bytes() != want:
                failures.append((rel, canon_rel))

    if failures:
        print("[shared-includes] copies have DIVERGED from the canonical file:", file=sys.stderr)
        for rel, canon_rel in failures:
            print(f"  {rel}", file=sys.stderr)
            print(f"      differs from {canon_rel}", file=sys.stderr)
        print("", file=sys.stderr)
        print("  A copy that disagrees with the canonical file makes two trees", file=sys.stderr)
        print("  build different hardware while both report success.", file=sys.stderr)
        print("  Re-sync it:", file=sys.stderr)
        for rel, canon_rel in failures:
            print(f"      cp {canon_rel} {rel}", file=sys.stderr)
        print("  or delete the copy if nothing reads it.", file=sys.stderr)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
