# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: board_guard
# Purpose: What a rapids runner does before it touches the real board: take the
#          shared board lock (tooling TASK-022) and read the JTAG device
#          identity at start and end. Used ONLY where the real serial port is
#          opened; the UART sim campaign injects its transport and never gets here.
#
# Documentation: projects/fpga-systems/Genesys2/rapids/flows-rapids/
# Subsystem: rapids_byte_harness

"""The lock itself is the scoria module's (Genesys2/scoria/host/board_lock.py),
imported from its home rather than copied, so there is one key derivation and
one exit code (98). Two cases it does not cover, handled here:

* A runner started through `make run-*` inherits the lock on an open file
  descriptor (board_lock.sh execs the payload with fd 9 held). A second flock
  from the same tree would see the board busy -- held by itself -- so an
  inherited descriptor on the lock file counts as holding it.
* The identity readback. `fpga_board.py` has no JTAG readback, so this runs
  jtag_readback.tcl through vivado and compares the target serial to the board
  registry's, at start and again at end. A board swapped or re-enumerated
  mid-run changes the readback, and then the numbers in the results file were
  not measured on the board the run started on."""

import fcntl
import json
import os
import subprocess
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_GENESYS2 = os.path.normpath(os.path.join(_HERE, os.pardir, os.pardir, os.pardir))
_SCORIA_HOST = os.path.join(_GENESYS2, 'scoria', 'host')
_FPGA_BIN = os.path.normpath(os.path.join(_GENESYS2, os.pardir, 'bin'))
TCL = os.path.join(_HERE, 'jtag_readback.tcl')
BOARD = 'genesys2'

if _SCORIA_HOST not in sys.path:
    sys.path.insert(0, _SCORIA_HOST)
from board_lock import BoardBusy, BoardLock, LOCK_BUSY_EXIT, lock_path  # noqa: E402,F401

IDENTITY_EXIT = 3


class IdentityError(RuntimeError):
    """The JTAG readback is not the expected board, or changed during the run."""


def expected_serial(board=BOARD) -> str:
    """The registry's JTAG serial for `board` (never a literal in a runner)."""
    out = subprocess.run([sys.executable, os.path.join(_FPGA_BIN, 'fpga_board.py'),
                          '--board', board, 'serial'],
                         capture_output=True, text=True, timeout=30).stdout.strip()
    if not out:
        raise IdentityError(f"fpga_board.py has no JTAG serial for board {board!r}")
    return out


def parse_readback(text: str) -> dict:
    """Targets and devices from jtag_readback.tcl output."""
    targets, devices = [], []
    for ln in text.splitlines():
        parts = ln.split()
        if ln.startswith('JTAG_TARGET ') and len(parts) == 2:
            targets.append({'target': parts[1], 'serial': parts[1].rsplit('/', 1)[-1]})
        elif ln.startswith('JTAG_DEVICE ') and len(parts) >= 5:
            devices.append({'target': parts[1], 'device': parts[2], 'part': parts[3],
                            'idcode': parts[4]})
    return {'targets': targets, 'devices': devices}


def jtag_readback(vivado=None, tcl=TCL, timeout=240) -> dict:
    """Run the readback through vivado; returns parse_readback()'s dict."""
    vivado = vivado or os.environ.get('VIVADO', 'vivado')
    res = subprocess.run([vivado, '-mode', 'batch', '-notrace', '-source', tcl],
                         capture_output=True, text=True, timeout=timeout)
    rb = parse_readback(res.stdout)
    if res.returncode != 0 or not rb['targets']:
        raise IdentityError(f"JTAG readback failed (rc={res.returncode}): "
                            f"{(res.stderr or res.stdout).strip()[-300:]}")
    return rb


def check_expected(rb: dict, serial: str) -> None:
    """The board under test must be on the chain, with a device behind it."""
    mine = [t['target'] for t in rb['targets'] if serial in t['serial']]
    devs = [d for d in rb['devices'] if d['target'] in mine]
    if not mine or not devs:
        raise IdentityError(f"expected board {serial} not on the JTAG chain with a device "
                            f"(targets: {[t['serial'] for t in rb['targets']]})")


def _inherited_fd(path: str):
    """A descriptor on the lock file that really HOLDS the lock: make's exec'd
    payload has one. Re-locking it succeeds only if this process tree owns the
    lock; a descriptor merely open on the file does not count."""
    for fd in os.listdir('/proc/self/fd'):
        try:
            if os.readlink(f'/proc/self/fd/{fd}') != path:
                continue
            fcntl.flock(int(fd), fcntl.LOCK_EX | fcntl.LOCK_NB)
            return int(fd)
        except OSError:
            continue
    return None


class HardwareRun:
    """with HardwareRun() as hw: ... ; ok = hw.finish(result_paths)

    Raises BoardBusy (exit 98 at the caller) if another process holds the board
    and IdentityError if the JTAG readback is not the expected board."""

    def __init__(self, board=BOARD, readback=True, read_fn=None):
        self.board, self.readback = board, readback
        self._read = read_fn or jtag_readback
        self.identity = {}
        self._lock = None

    def __enter__(self):
        path = lock_path(self.board)
        inherited = _inherited_fd(path) is not None
        if not inherited:
            self._lock = BoardLock(self.board).__enter__()
        self.identity['board_lock'] = {'path': path, 'inherited': inherited}
        if self.readback:
            self._serial = expected_serial(self.board)
            start = self._read()
            check_expected(start, self._serial)
            self.identity['jtag'] = {'expected_serial': self._serial, 'start': start}
        return self

    def __exit__(self, *exc):
        if self._lock is not None:
            self._lock.__exit__(*exc)

    def finish(self, paths) -> bool:
        """End readback; stamp start+end into each results JSON. False (and a
        message) if the board changed or is not the expected one."""
        if not self.readback:
            return True
        try:
            end = self._read()
            check_expected(end, self._serial)
            stable = end == self.identity['jtag']['start']
            why = '' if stable else 'JTAG readback at end differs from the start'
        except IdentityError as exc:
            end, stable, why = {'error': str(exc)}, False, str(exc)
        self.identity['jtag'].update({'end': end, 'stable': stable})
        for p in paths:
            if os.path.isfile(p):
                with open(p) as fh:
                    doc = json.load(fh)
                doc.update(self.identity)
                with open(p, 'w') as fh:
                    json.dump(doc, fh, indent=2)
        if not stable:
            print(f"FAIL: {why}: the results are not from one board", flush=True)
        return stable
