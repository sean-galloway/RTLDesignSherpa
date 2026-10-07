# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""The two board-lock implementations must agree, and nothing else enforced it.

tooling TASK-022 put a board-keyed lock on the make targets
(`projects/fpga-systems/bin/board_lock.sh`), and the scoria host driver then took
the same lock from Python
(`projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/host/board_lock.py`) so a directly-invoked
runner is guarded too.

WHY THIS TEST EXISTS. Two implementations of one lock key, with nothing pinning
them together, is not merely untested -- it is a worse failure than having no lock
at all. If the derivations drift, BOTH sides acquire happily and each believes it
owns the board, which is exactly the silent-wrong-data outcome the lock was built
to prevent. It would also look fine: no error, no timeout, two green runs.

This repo has already been bitten by the same shape. `protocol_types.py` validates
a protocol name while `signal_mapping_helper.PROTOCOL_SIGNAL_CONFIGS` resolves it,
and adding a name to one and not the other was a silent gap until the two
registries were pinned against each other. Same fix here: assert agreement rather
than document it.

The agreement was verified by hand in both directions when the Python side landed.
A hand-run check catches nobody, so it is asserted here instead.

SAFETY: every test redirects RDS_BOARD_LOCK_DIR at a pytest tmp_path, so nothing
here can ever take the real `/tmp/rds-board-<serial>.lock` and block a live board
run. That matters -- a test that can stall a 20-minute characterization would be
worse than the bug.
"""

from __future__ import annotations

import importlib.util
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
SHELL_LOCK = REPO_ROOT / "projects/fpga-systems/bin/board_lock.sh"
PY_LOCK = REPO_ROOT / "projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/host/board_lock.py"

# Boards the registry knows, plus the cases the derivation has to handle
# identically on both sides: a name with no registry entry (falls back to the
# name), a name carrying characters that cannot go in a filename, and a name
# made of characters that are ALLOWED and must survive untouched.
#
# That last case earns its place. A mutation of the shell's sanitisation class
# from [A-Za-z0-9._-] to [A-Za-z0-9._] -- dropping the hyphen -- passed this test
# until `has-dash.and-dot` was added, because both real serials are alphanumeric
# and the other two fallbacks sanitise to underscores, so nothing exercised the
# boundary. A guard that cannot fail is decoration; this is the case that gives
# it teeth on the character class rather than only on the filename shape.
BOARDS = [
    "genesys2",
    "nexys_a7_100t",
    "no_such_board",
    "weird/name:v2",
    "has-dash.and-dot",
]

pytestmark = pytest.mark.skipif(
    shutil.which("flock") is None, reason="flock(1) not available"
)


def _load_py_lock():
    """Import the Python side, failing loudly if it moved.

    A skip would be wrong here. The whole point is that these two stay pinned, so
    if the Python implementation is renamed or relocated this test must FAIL and
    say so -- that is the signal to re-pin it, not a reason to stop checking.
    """
    assert PY_LOCK.is_file(), (
        f"{PY_LOCK} is missing. The Python board lock moved or was deleted; "
        "re-point this test at it. Do NOT delete this test -- it is what keeps "
        "the two lock implementations agreeing (tooling TASK-022)."
    )
    spec = importlib.util.spec_from_file_location("_board_lock_py", PY_LOCK)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _shell_lock_path(board: str, lock_dir: Path) -> str:
    """Ask board_lock.sh, via a payload that prints the path it is holding."""
    env = {**os.environ, "RDS_BOARD_LOCK_DIR": str(lock_dir)}
    # The payload lists the lock dir; the shell has already created the file.
    subprocess.run(
        [str(SHELL_LOCK), "--board", board, "--", "true"],
        env=env, check=True, capture_output=True, text=True,
    )
    created = sorted(p.name for p in lock_dir.iterdir())
    assert len(created) == 1, f"expected one lock file, got {created}"
    return str(lock_dir / created[0])


@pytest.mark.parametrize("board", BOARDS)
def test_lock_path_derivations_agree(board, tmp_path):
    """THE load-bearing assertion: one board, one lock file, both languages."""
    py = _load_py_lock()
    shell_dir = tmp_path / "shell"
    shell_dir.mkdir()
    os.environ["RDS_BOARD_LOCK_DIR"] = str(shell_dir)
    try:
        py_path = Path(py.lock_path(board)).name
    finally:
        os.environ.pop("RDS_BOARD_LOCK_DIR", None)
    shell_path = Path(_shell_lock_path(board, shell_dir)).name
    assert py_path == shell_path, (
        f"board {board!r}: board_lock.py derives {py_path!r} but board_lock.sh "
        f"derives {shell_path!r}. DIVERGED DERIVATIONS ARE WORSE THAN NO LOCK -- "
        "both sides would acquire and each would believe it owns the board."
    )


def test_default_lock_dir_agrees():
    """The DEFAULT directory must match, and no other test here exercises it.

    Every other test sets RDS_BOARD_LOCK_DIR explicitly so it cannot touch the
    real board lock -- which means a mutation of either side's DEFAULT passes them
    all. That is the most dangerous divergence of the lot: in production nobody
    sets the variable, so mismatched defaults put the two implementations on
    different files while both report success.

    Pinned without acquiring anything: lock_path() is pure, and the shell's
    default is a literal. Deliberately does NOT run board_lock.sh, because doing
    so with the env var unset would take the real lock and could refuse a live
    board run for the duration.
    """
    py = _load_py_lock()
    saved = os.environ.pop("RDS_BOARD_LOCK_DIR", None)
    try:
        py_default = os.path.dirname(py.lock_path("genesys2"))
    finally:
        if saved is not None:
            os.environ["RDS_BOARD_LOCK_DIR"] = saved
    assert py_default == "/tmp", f"board_lock.py defaults to {py_default!r}"
    assert 'RDS_BOARD_LOCK_DIR:-/tmp' in SHELL_LOCK.read_text(), (
        "board_lock.sh's default lock dir changed; board_lock.py still uses "
        f"{py_default!r}. Mismatched DEFAULTS are invisible in every other test "
        "here, and catastrophic in production where the env var is unset."
    )


def test_busy_exit_codes_agree():
    """A wrapper seeing 98 from either side means the same thing."""
    py = _load_py_lock()
    src = SHELL_LOCK.read_text()
    assert "EXIT_BUSY=98" in src, "board_lock.sh's busy exit code changed"
    assert py.LOCK_BUSY_EXIT == 98, (
        f"board_lock.py LOCK_BUSY_EXIT is {py.LOCK_BUSY_EXIT}, shell uses 98"
    )


def test_shell_holding_blocks_python(tmp_path):
    py = _load_py_lock()
    env = {**os.environ, "RDS_BOARD_LOCK_DIR": str(tmp_path)}
    sentinel = tmp_path / "held"
    holder = subprocess.Popen(
        [str(SHELL_LOCK), "--board", "genesys2", "--",
         "sh", "-c", f"touch {sentinel}; sleep 10"],
        env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    try:
        deadline = time.time() + 15
        while not sentinel.exists() and time.time() < deadline:
            time.sleep(0.05)
        assert sentinel.exists(), "shell holder never started"
        os.environ["RDS_BOARD_LOCK_DIR"] = str(tmp_path)
        try:
            with pytest.raises(py.BoardBusy):
                with py.BoardLock("genesys2"):
                    pass
        finally:
            os.environ.pop("RDS_BOARD_LOCK_DIR", None)
    finally:
        holder.kill()
        holder.wait()


def test_python_holding_blocks_shell(tmp_path):
    py = _load_py_lock()
    os.environ["RDS_BOARD_LOCK_DIR"] = str(tmp_path)
    env = {**os.environ, "RDS_BOARD_LOCK_DIR": str(tmp_path)}
    try:
        with py.BoardLock("genesys2"):
            done = subprocess.run(
                [str(SHELL_LOCK), "--board", "genesys2", "--", "true"],
                env=env, capture_output=True, text=True,
            )
        assert done.returncode == 98, (
            f"shell got rc={done.returncode} while Python held the lock; "
            "expected 98. The two sides are not seeing the same lock file."
        )
        assert "IN USE" in done.stdout, "the busy hint did not print"
    finally:
        os.environ.pop("RDS_BOARD_LOCK_DIR", None)


def test_lock_is_released_for_both_after_use(tmp_path):
    """Neither side leaves a lock behind -- the flock dies with its holder."""
    py = _load_py_lock()
    env = {**os.environ, "RDS_BOARD_LOCK_DIR": str(tmp_path)}
    subprocess.run([str(SHELL_LOCK), "--board", "genesys2", "--", "true"],
                   env=env, check=True, capture_output=True)
    os.environ["RDS_BOARD_LOCK_DIR"] = str(tmp_path)
    try:
        with py.BoardLock("genesys2"):
            pass
        with py.BoardLock("genesys2"):
            pass
    finally:
        os.environ.pop("RDS_BOARD_LOCK_DIR", None)
    again = subprocess.run([str(SHELL_LOCK), "--board", "genesys2", "--", "true"],
                           env=env, capture_output=True, text=True)
    assert again.returncode == 0, "lock not released after the holders exited"


def test_different_boards_do_not_block_each_other(tmp_path):
    """Per-BOARD, not per-machine: two boards share one JTAG chain here."""
    env = {**os.environ, "RDS_BOARD_LOCK_DIR": str(tmp_path)}
    sentinel = tmp_path / "held2"
    holder = subprocess.Popen(
        [str(SHELL_LOCK), "--board", "genesys2", "--",
         "sh", "-c", f"touch {sentinel}; sleep 10"],
        env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    try:
        deadline = time.time() + 15
        while not sentinel.exists() and time.time() < deadline:
            time.sleep(0.05)
        other = subprocess.run(
            [str(SHELL_LOCK), "--board", "nexys_a7_100t", "--", "true"],
            env=env, capture_output=True, text=True,
        )
        assert other.returncode == 0, (
            "a different board was refused; the lock is not per-board"
        )
    finally:
        holder.kill()
        holder.wait()

# ---------------------------------------------------------------------------
# Nested acquisition: a runner launched THROUGH the shell lock
# ---------------------------------------------------------------------------
def test_nested_python_under_shell_lock_does_not_deadlock(tmp_path):
    """A runner under `make run-*` must not be refused by its OWN holder.

    board_lock.sh execs its payload with fd 9 still holding the flock, so a
    Python runner it launches inherits that descriptor. Opening the same file
    and taking a SECOND flock on a NEW descriptor is refused by the kernel, so
    the runner deadlocked against the make-level lock it was running under --
    exit 98 against itself.

    This case did not exist when the interop test was first written, which is
    why the suite passed while the defect shipped. A lock that refuses its own
    holder gets "fixed" by someone deleting the lock.
    """
    lock_dir = tmp_path / "nested"
    lock_dir.mkdir()
    inner = tmp_path / "inner.py"
    inner.write_text(
        "import sys\n"
        f"sys.path.insert(0, {str(PY_LOCK.parent)!r})\n"
        "from board_lock import BoardLock, BoardBusy\n"
        "try:\n"
        "    with BoardLock('genesys2') as bl:\n"
        "        print('ADOPTED' if bl.adopted else 'TOOK_OWN')\n"
        "except BoardBusy:\n"
        "    print('DEADLOCK')\n"
    )
    env = {**os.environ, "RDS_BOARD_LOCK_DIR": str(lock_dir)}
    r = subprocess.run(
        [str(SHELL_LOCK), "--board", "genesys2", "--",
         sys.executable, str(inner)],
        env=env, capture_output=True, text=True, timeout=120,
    )
    out = r.stdout.strip().splitlines()
    assert "DEADLOCK" not in out, (
        "the Python lock was refused by the shell lock it was running under. "
        "BoardLock must adopt an inherited descriptor -- see _inherited_fd."
    )
    assert "ADOPTED" in out, (
        f"expected the nested lock to ADOPT the ancestor's descriptor, got "
        f"{out!r}. TOOK_OWN would mean it opened a second lock, which is the "
        f"bug in a different disguise."
    )


def test_adopted_lock_does_not_release_the_ancestors(tmp_path):
    """Exiting an adopted scope must NOT drop the lock for the whole tree.

    The inherited descriptor belongs to the ancestor. Closing it -- the obvious
    thing for a context manager to do -- would release the board while the
    outer holder still believes it owns it, which is worse than the deadlock it
    replaced: silent instead of loud.
    """
    lock_dir = tmp_path / "adopt"
    lock_dir.mkdir()
    inner = tmp_path / "inner2.py"
    inner.write_text(
        "import sys, subprocess\n"
        f"sys.path.insert(0, {str(PY_LOCK.parent)!r})\n"
        "from board_lock import BoardLock\n"
        "with BoardLock('genesys2') as bl:\n"
        "    pass\n"
        f"rc = subprocess.run([{str(SHELL_LOCK)!r}, '--board', 'genesys2',\n"
        "                     '--', 'true'], capture_output=True).returncode\n"
        "print(f'OUTSIDER_RC={rc}')\n"
    )
    env = {**os.environ, "RDS_BOARD_LOCK_DIR": str(lock_dir)}
    r = subprocess.run(
        [str(SHELL_LOCK), "--board", "genesys2", "--",
         sys.executable, str(inner)],
        env=env, capture_output=True, text=True, timeout=120,
    )
    assert "OUTSIDER_RC=98" in r.stdout, (
        f"after an adopted scope exited, an outsider acquired the board. The "
        f"ancestor's lock was dropped. stdout={r.stdout!r}"
    )

