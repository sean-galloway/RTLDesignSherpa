#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Remove Verilator build trees, skipping any a live run is building in.

`make clean-build` used to be:

    rm -rf local_sim_build/ sim_build/
    find . -type d -name 'local_sim_build' -exec rm -rf {} +

which is a recursive find-and-destroy across the whole subtree. In a shared
worktree with concurrent sessions that deletes other people's in-flight
builds, and the failure it produces is not obviously a deletion: the run dies
somewhere inside Verilator or cocotb with a missing file, or -- worse --
finishes with a corrupted model. `vault/Tasks/amba/open.md` records three
occurrences before the cause was found, one of them traced to a DIFFERENT
session cleaning the same root.

`sim_build_path()` already marks each build directory with the pid building
in it. This consults those markers, so the safety lives in the tool every
caller runs rather than in a discipline every caller has to remember.

Liveness is the test, not session identity -- see sim_build_is_busy(). A
marker naming a dead pid, or one older than the age limit, is reclaimable.

Usage:
    clean_sim_builds.py [DIR ...]        # default: cwd
    clean_sim_builds.py --dry-run DIR    # report, delete nothing
"""

from __future__ import annotations

import argparse
import os
import shutil
import sys

_REPO_BIN = os.path.dirname(os.path.abspath(__file__))
if _REPO_BIN not in sys.path:
    sys.path.insert(0, _REPO_BIN)

from TBClasses.shared.utilities import sim_build_is_busy  # noqa: E402

# Container directory names that hold per-test build trees.
CONTAINERS = ('local_sim_build', 'sim_build')


def find_containers(roots):
    """Every build-tree container under the given roots."""
    found = []
    for root in roots:
        for dirpath, dirnames, _ in os.walk(root):
            for name in list(dirnames):
                if name in CONTAINERS:
                    found.append(os.path.join(dirpath, name))
                    dirnames.remove(name)      # do not descend into it
    return found


def clean_container(container, dry_run=False):
    """Remove the free build dirs inside one container.

    Returns (removed, skipped) where skipped entries carry the owner marker,
    so the caller can say WHO is still building rather than just refusing.
    """
    removed, skipped = [], []
    try:
        entries = sorted(os.listdir(container))
    except OSError:
        return removed, skipped

    for entry in entries:
        path = os.path.join(container, entry)
        if not os.path.isdir(path):
            continue
        owner = sim_build_is_busy(path)
        if owner:
            skipped.append((path, owner))
            continue
        if not dry_run:
            shutil.rmtree(path, ignore_errors=True)
        removed.append(path)

    # Drop the container itself only when nothing was left behind, so a
    # skipped build keeps the directory that holds it.
    if not skipped and not dry_run:
        shutil.rmtree(container, ignore_errors=True)
    return removed, skipped


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('dirs', nargs='*', default=None,
                    help='roots to clean (default: cwd)')
    ap.add_argument('--dry-run', action='store_true',
                    help='report what would happen, delete nothing')
    args = ap.parse_args()

    roots = args.dirs or [os.getcwd()]
    total_removed, all_skipped = 0, []

    for container in find_containers(roots):
        removed, skipped = clean_container(container, args.dry_run)
        total_removed += len(removed)
        all_skipped += skipped

    verb = 'would remove' if args.dry_run else 'cleaned'
    print(f"{verb}: {total_removed} sim build dir(s)")

    if all_skipped:
        # Loud, not silent. A skipped directory means this clean did NOT do
        # what the caller asked, and a caller who believes the tree is clean
        # when it is not will mis-read whatever happens next.
        print(f"SKIPPED {len(all_skipped)} dir(s) -- a live run is building "
              f"in them:")
        for path, owner in all_skipped:
            print(f"  {os.path.relpath(path)}  "
                  f"(pid={owner.get('pid')} session={owner.get('session')})")
        print("Nothing was deleted from those. Wait for the run, or clean "
              "them by name once it ends.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
