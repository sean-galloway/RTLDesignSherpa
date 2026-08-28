#!/usr/bin/env python3
"""Delete simulation build directories without stepping on another session.

Replaces the reflex `rm -rf val/<area>/local_sim_build/*`, which is how
VAL-XDIST-INTERMITTENT happened: in a shared worktree, that glob deletes
in-flight builds belonging to whatever else is running, and the victim
fails with "FileNotFoundError: RTL source not found" and reads as flaky.

This honours the advisory `.sim_busy` marker each build directory carries
(session, pid, start time). A directory is skipped when it belongs to a
DIFFERENT session whose owning process is still alive and whose marker is
recent. Your own directories, dead owners and stale markers are all fair
game, so the normal "clean before a fresh run" workflow still works.

    bin/sim_build_clean.py val/amba                 # this area
    bin/sim_build_clean.py val/amba --pattern monbus
    bin/sim_build_clean.py val/amba --dry-run
    bin/sim_build_clean.py --all                    # every val/ area

Exit status is 0 even when directories were skipped -- skipping is the
correct outcome, not an error. It is reported so it is never silent.
"""
import argparse
import os
import shutil
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'TBClasses'))

from shared.utilities import (  # noqa: E402
    sim_build_root, sim_build_is_busy, sim_session_id,
)


def clean_area(tests_dir: str, pattern: str, dry_run: bool) -> tuple:
    root = sim_build_root(tests_dir)
    if not os.path.isdir(root):
        return 0, 0
    removed = skipped = 0
    for name in sorted(os.listdir(root)):
        if pattern and pattern not in name:
            continue
        path = os.path.join(root, name)
        if not os.path.isdir(path):
            continue
        busy = sim_build_is_busy(path)
        if busy:
            skipped += 1
            print(f"  SKIP  {name}  (in use by session "
                  f"{busy.get('session')}, pid {busy.get('pid')})")
            continue
        if dry_run:
            print(f"  would remove  {name}")
        else:
            shutil.rmtree(path, ignore_errors=True)
        removed += 1
    return removed, skipped


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('areas', nargs='*', help='test directories, e.g. val/amba')
    ap.add_argument('--pattern', default='', help='only names containing this substring')
    ap.add_argument('--all', action='store_true', help='every val/* area')
    ap.add_argument('--dry-run', action='store_true')
    args = ap.parse_args()

    areas = list(args.areas)
    if args.all:
        for d in sorted(os.listdir('val')):
            p = os.path.join('val', d)
            if os.path.isdir(p):
                areas.append(p)
    if not areas:
        ap.error('give at least one area, or --all')

    print(f"session: {sim_session_id()}"
          f"{'  (DRY RUN)' if args.dry_run else ''}")
    total_r = total_s = 0
    for area in areas:
        r, s = clean_area(area, args.pattern, args.dry_run)
        if r or s:
            print(f"{area}: {r} removed, {s} skipped")
        total_r += r
        total_s += s

    print(f"\ntotal: {total_r} removed, {total_s} skipped")
    if total_s:
        print("Skipped directories belong to another live session -- that is "
              "the protection working, not a failure.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
