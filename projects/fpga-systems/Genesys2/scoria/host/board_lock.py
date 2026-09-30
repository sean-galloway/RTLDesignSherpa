# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""Take the shared board lock from Python, interoperably with board_lock.sh.

tooling TASK-022 put a board-keyed lock on the MAKE targets (program, tcl-*,
run-*, seq-*, run). That leaves a real hole, and it is the exact shape of the
2026-09-30 near miss: `run_characterization.py --port /dev/ttyUSB0` invoked
DIRECTLY takes no lock and is invisible to anyone else's check. The durable fix
named in the task is runners taking the lock themselves; this is that, for the
scoria host driver.

INTEROPERABILITY IS THE WHOLE REQUIREMENT. A second lock with a different key
is worse than no lock: both sides would acquire happily and each would believe
it held the board. So the key derivation here mirrors
projects/fpga-systems/bin/board_lock.sh exactly --

    dir   $RDS_BOARD_LOCK_DIR, default /tmp
    key   the registry's JTAG serial, falling back to the BOARD name
    sanitise  every char outside [A-Za-z0-9._-] -> '_'
    file  <dir>/rds-board-<key>.lock

-- and is tested against the shell script rather than assumed compatible.

flock on an open file description, like the shell version: the lock lives with
the fd, dies with the process, and needs no PID file and no staleness check.
"""
from __future__ import annotations

import errno
import fcntl
import os
import re
import subprocess
import sys
from typing import Optional

#: Same exit code board_lock.sh uses, so a wrapper sees one convention.
LOCK_BUSY_EXIT = 98


class BoardBusy(RuntimeError):
    """Another process holds this board."""


def lock_path(board: str) -> str:
    """The lock file for `board`. Must agree with board_lock.sh byte for byte."""
    lock_dir = os.environ.get("RDS_BOARD_LOCK_DIR", "/tmp")
    key = ""
    repo = os.environ.get("REPO_ROOT") or subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True, text=True).stdout.strip()
    cli = os.path.join(repo, "projects/fpga-systems/bin/fpga_board.py")
    if os.path.isfile(cli):
        try:
            key = subprocess.run([sys.executable, cli, "--board", board, "serial"],
                                 capture_output=True, text=True,
                                 timeout=30).stdout.strip()
        except Exception:
            key = ""
    if not key:
        key = board
    key = re.sub(r"[^A-Za-z0-9._-]", "_", key)
    return os.path.join(lock_dir, f"rds-board-{key}.lock")


class BoardLock:
    """Context manager holding one board's exclusive lock.

        with BoardLock("genesys2"):
            ...drive the board...

    Non-blocking by design. Waiting silently is how two runs end up serialised
    by luck and nobody learns the board was contended; raising names the holder
    so the operator can decide.
    """

    def __init__(self, board: str, *, required: bool = True):
        self.board = board
        self.required = required
        self.path = lock_path(board)
        self._fd: Optional[int] = None

    def __enter__(self) -> "BoardLock":
        self._fd = os.open(self.path, os.O_WRONLY | os.O_CREAT, 0o666)
        try:
            fcntl.flock(self._fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as e:
            os.close(self._fd); self._fd = None
            if e.errno not in (errno.EACCES, errno.EAGAIN):
                raise
            holder = ""
            try:
                holder = subprocess.run(["fuser", "-v", self.path],
                                        capture_output=True, text=True,
                                        timeout=10).stderr.strip()
            except Exception:
                pass
            msg = (f"board {self.board!r} is LOCKED by another process.\n"
                   f"  lock: {self.path}\n"
                   f"  {holder or 'run: fuser -v ' + self.path}\n"
                   f"Reprogramming or driving a board mid-run leaves the other "
                   f"side's results looking valid while measuring the wrong "
                   f"design -- see tooling TASK-022.")
            if self.required:
                raise BoardBusy(msg) from None
            print(f"WARNING: {msg}", file=sys.stderr)
        return self

    def __exit__(self, *exc) -> None:
        if self._fd is not None:
            # flock releases on close; be explicit so the window is not
            # "whenever the GC gets there".
            try:
                fcntl.flock(self._fd, fcntl.LOCK_UN)
            finally:
                os.close(self._fd)
                self._fd = None

    @property
    def held(self) -> bool:
        return self._fd is not None
