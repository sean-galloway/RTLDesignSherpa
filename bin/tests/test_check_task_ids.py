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


# ---------------------------------------------------------------------------
# Hook context: the checker must validate the tree being COMMITTED (tooling
# BUG-014).
#
# `git commit -- <paths>` builds a temporary index of HEAD plus only the listed
# paths. Name one half of a `git mv` and the commit takes the addition and leaves
# the staged deletion behind -- the item lands in two states at once. On disk the
# old copy is already gone, so a checker that globs directories sees a consistent
# tree and prints PASS over an inconsistent commit.
#
# This is end to end on purpose: it installs a real pre-commit hook and runs a
# real pathspec commit, because the defect lives in the difference between the
# worktree and the hook's temporary index. Nothing short of a real commit
# produces that difference.
# ---------------------------------------------------------------------------

HOOK = textwrap.dedent("""\
    #!/bin/sh
    exec "{py}" "{checker}"
    """)


def _repo_with_hook(tmp_path, **kw) -> Path:
    repo = _lane(tmp_path, **kw)
    subprocess.run(["git", "config", "user.email", "t@example.com"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "t"], cwd=repo, check=True)
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
    subprocess.run(["git", "commit", "-qm", "base", "--no-verify"], cwd=repo, check=True)
    hook = repo / ".git" / "hooks" / "pre-commit"
    hook.write_text(HOOK.format(py=sys.executable, checker=CHECKER))
    hook.chmod(0o755)
    return repo


def _lane_dir(repo: Path) -> Path:
    return repo / "vault" / "Tasks" / "scratch" / "task"


def test_hook_rejects_a_half_committed_move(tmp_path):
    """The pathspec names only the NEW path, so the deletion is left behind.

    Before BUG-014 this commit SUCCEEDED: the hook globbed the worktree, where
    open/TASK-001.md was already gone, and reported a consistent lane.
    """
    repo = _repo_with_hook(tmp_path)
    lane = _lane_dir(repo)
    subprocess.run(["git", "mv", "open/TASK-001.md", "closed/TASK-001.md"],
                   cwd=lane, check=True)
    # Keep the INDEX honest about the move, so the ONLY defect under test is the
    # dropped deletion -- otherwise a stale count could be what fails.
    (lane / "INDEX.md").write_text(INDEX.format(
        open=0, closed=2,
        open_list="", closed_list="- **TASK-001** — item\n- **TASK-002** — item\n"))
    r = subprocess.run(["git", "commit", "-qm", "move", "--",
                        "vault/Tasks/scratch/task/closed/TASK-001.md",
                        "vault/Tasks/scratch/task/INDEX.md"],
                       cwd=repo, capture_output=True, text=True)
    assert r.returncode != 0, (
        "the hook approved a commit placing TASK-001 in both open/ and closed/\n"
        f"stdout:\n{r.stdout}\nstderr:\n{r.stderr}")
    assert "DUPLICATE ID TASK-001" in (r.stdout + r.stderr), \
        f"rejected, but not for the duplicate:\n{r.stdout}\n{r.stderr}"


def test_hook_accepts_a_move_that_names_both_halves(tmp_path):
    """The control. Without this, the test above is satisfied by a checker that
    rejects every move -- which would block all tracker work."""
    repo = _repo_with_hook(tmp_path)
    lane = _lane_dir(repo)
    subprocess.run(["git", "mv", "open/TASK-001.md", "closed/TASK-001.md"],
                   cwd=lane, check=True)
    (lane / "INDEX.md").write_text(INDEX.format(
        open=0, closed=2,
        open_list="", closed_list="- **TASK-001** — item\n- **TASK-002** — item\n"))
    r = subprocess.run(["git", "commit", "-qm", "move", "--",
                        "vault/Tasks/scratch/task/closed/TASK-001.md",
                        "vault/Tasks/scratch/task/open/TASK-001.md",
                        "vault/Tasks/scratch/task/INDEX.md"],
                       cwd=repo, capture_output=True, text=True)
    assert r.returncode == 0, f"a correct move was rejected:\n{r.stdout}\n{r.stderr}"


def test_hook_still_sees_a_count_lie_in_the_committed_tree(tmp_path):
    """The count check must also read the index, not just the duplicate check.

    A move that updates the directories but NOT the INDEX counts is the other
    half of what 0804d45d3 did, and it has to fail from hook context too.
    """
    repo = _repo_with_hook(tmp_path)
    lane = _lane_dir(repo)
    subprocess.run(["git", "mv", "open/TASK-001.md", "closed/TASK-001.md"],
                   cwd=lane, check=True)
    r = subprocess.run(["git", "commit", "-qm", "move", "--",
                        "vault/Tasks/scratch/task/closed/TASK-001.md",
                        "vault/Tasks/scratch/task/open/TASK-001.md"],
                       cwd=repo, capture_output=True, text=True)
    assert r.returncode != 0, (
        "the hook approved a commit whose INDEX counts contradict its "
        f"directories:\n{r.stdout}\n{r.stderr}")


def test_area_labels_survive_hook_context(tmp_path):
    """The label is `<area>/<lane>`, and it must not degrade to a bare lane name.

    18 directories are called `task`, so "task: DUPLICATE ID ..." names nothing.
    Reading from a materialised index tree is exactly where a path-relative label
    silently falls back to `.name`, so pin it from hook context.
    """
    repo = _repo_with_hook(tmp_path)
    lane = _lane_dir(repo)
    subprocess.run(["git", "mv", "open/TASK-001.md", "closed/TASK-001.md"],
                   cwd=lane, check=True)
    r = subprocess.run(["git", "commit", "-qm", "move", "--",
                        "vault/Tasks/scratch/task/closed/TASK-001.md"],
                       cwd=repo, capture_output=True, text=True)
    out = r.stdout + r.stderr
    assert r.returncode != 0, out
    # Specifically the DUPLICATE line, which only exists once the index is being
    # read. Asserting any `scratch/task:` would pass pre-fix on the unrelated
    # count error the worktree already shows.
    assert "scratch/task: DUPLICATE ID TASK-001" in out, \
        f"label degraded to a bare lane name, or the duplicate was not seen:\n{out}"


def test_tasks_root_checks_the_tree_you_point_at(tmp_path):
    """--tasks-root is how you ask what a COMMIT contains, not the worktree.

    Pin that it reads the given tree and not the cwd's: the defect is planted
    ONLY in the pointed-at tree, and the repo the checker runs from is clean.
    """
    good = _lane(tmp_path / "good")
    bad = _lane(tmp_path / "bad", open_count=1, closed_count=1)
    # Plant the half-committed move in `bad` only: the ID in two states at once.
    badlane = bad / "vault" / "Tasks" / "scratch" / "task"
    (badlane / "closed" / "TASK-001.md").write_text(
        "# TASK-001: an open item\n\n**Status:** closed\n")

    r = subprocess.run([sys.executable, str(CHECKER), "--tasks-root",
                        str(bad / "vault" / "Tasks")],
                       cwd=good, capture_output=True, text=True)
    out = r.stdout + r.stderr
    assert r.returncode != 0, f"the planted duplicate was not seen:\n{out}"
    assert "DUPLICATE ID TASK-001" in out, out
    # And the clean tree it was run FROM still passes, so the flag really did
    # redirect the read rather than merely adding a second one.
    assert _run(good).returncode == 0


def test_tasks_root_rejects_a_bad_path(tmp_path):
    repo = _lane(tmp_path)
    r = subprocess.run([sys.executable, str(CHECKER), "--tasks-root",
                        str(tmp_path / "nope")], cwd=repo,
                       capture_output=True, text=True)
    assert r.returncode != 0
    assert "not a directory" in (r.stdout + r.stderr)
