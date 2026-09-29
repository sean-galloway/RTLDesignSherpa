# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Teeth for bin/check_task_ids.py (tooling TASK-015).

The checker runs in the pre-commit hook and, from 2026-09-29, in CI. A gate
that merely runs proves nothing; this pins that it FAILS on each invariant it
claims: a count table that disagrees with the directory, an INDEX that does
not list an item on disk, a stale Next ID, and a filename/H1 mismatch -- and
that a consistent lane passes. Each case is a scratch git repo holding one
lane, mutated one way.
"""
from __future__ import annotations

import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "bin" / "check_task_ids.py"

INDEX = textwrap.dedent("""\
    <!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

    # scratch — tasks

    **Next ID: TASK-003** — never recycle a number, even when its item closed.

    | State | Count | What |
    |---|---|---|
    | [open/](open/) | {open} | accepted, not started |
    | [active/](active/) | 0 | in progress right now |
    | [closed/](closed/) | {closed} | done (kept for history) |
    | [dropped/](dropped/) | 0 | ended without completing |
    | [deferred/](deferred/) | 0 | parked pending a named condition |

    ## Open

    {open_list}
    ## Closed

    {closed_list}
    """)


def _lane(tmp_path: Path, *, open_count=1, closed_count=1,
          list_open=("TASK-001",), list_closed=("TASK-002",), h1_002="TASK-002") -> Path:
    repo = tmp_path / "repo"
    lane = repo / "vault" / "Tasks" / "scratch" / "task"
    for st in ("open", "active", "closed", "dropped", "deferred"):
        (lane / st).mkdir(parents=True)
    (lane / "open" / "TASK-000.md").write_text("# TASK-000: TEMPLATE — copy this file\n\n**Status:** open\n")
    (lane / "open" / "TASK-001.md").write_text("# TASK-001: an open item\n\n**Status:** open\n")
    (lane / "closed" / "TASK-002.md").write_text(f"# {h1_002}: a closed item\n\n**Status:** closed\n")
    (lane / "INDEX.md").write_text(INDEX.format(
        open=open_count, closed=closed_count,
        open_list="".join(f"- **{t}** — item\n" for t in list_open),
        closed_list="".join(f"- **{t}** — item\n" for t in list_closed)))
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    return repo


def _run(repo: Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(CHECKER)], cwd=repo, capture_output=True, text=True)


def test_consistent_lane_passes(tmp_path):
    r = _run(_lane(tmp_path))
    assert r.returncode == 0, r.stderr + r.stdout


def test_wrong_count_fails(tmp_path):
    r = _run(_lane(tmp_path, closed_count=15))
    assert r.returncode == 1 and "closed: 15" in r.stderr and "holds 1" in r.stderr


def test_unlisted_item_fails(tmp_path):
    r = _run(_lane(tmp_path, list_closed=()))
    assert r.returncode == 1 and "TASK-002 exists on disk" in r.stderr


def test_stale_next_id_fails(tmp_path):
    repo = _lane(tmp_path)
    idx = repo / "vault/Tasks/scratch/task/INDEX.md"
    idx.write_text(idx.read_text().replace("Next ID: TASK-003", "Next ID: TASK-002"))
    r = _run(repo)
    assert r.returncode == 1 and "Next ID" in r.stderr


def test_filename_h1_mismatch_fails(tmp_path):
    r = _run(_lane(tmp_path, h1_002="TASK-009"))
    assert r.returncode == 1 and "filename and heading must match" in r.stderr
