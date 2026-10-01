# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_rapids_board_guard
# Purpose: The rapids runners' board lock and JTAG-identity bracket (tooling
#          TASK-022). No board and no simulator: a held lock must stop the
#          HARDWARE path before it opens a port, the sim path must never take
#          the lock, and the readback check must fail a moved or wrong board.
#
# Documentation: projects/fpga-systems/Genesys2/rapids/flows-rapids/
# Subsystem: rapids_byte_harness

import contextlib
import json
import os
import stat
import subprocess
import sys

import pytest

_HOST = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir, 'host')
sys.path.insert(0, os.path.abspath(_HOST))

import board_guard  # noqa: E402
import run_characterization as rc  # noqa: E402


@pytest.fixture
def lockdir(tmp_path, monkeypatch):
    monkeypatch.setenv('RDS_BOARD_LOCK_DIR', str(tmp_path))
    return tmp_path


@contextlib.contextmanager
def held_elsewhere():
    """Another PROCESS holds the board lock (a same-process holder would look
    like an inherited descriptor, which is the make path)."""
    code = ("import sys; sys.path.insert(0, %r); from board_lock import BoardLock\n"
            "with BoardLock(%r):\n    print('held', flush=True); sys.stdin.readline()\n"
            % (board_guard._SCORIA_HOST, board_guard.BOARD))
    p = subprocess.Popen([sys.executable, '-c', code], stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, text=True)
    try:
        assert p.stdout.readline().strip() == 'held'
        yield
    finally:
        p.stdin.write('\n'); p.stdin.close(); p.wait(timeout=30)


class _NoPort(Exception):
    pass


@pytest.fixture
def portguard(monkeypatch):
    """Any attempt to scan or open a serial port fails the test."""
    def boom(*a, **k):
        raise _NoPort("the hardware path touched a serial port")
    monkeypatch.setattr(rc.rio, 'autodetect_port', boom)
    monkeypatch.setattr(rc, 'RapidsByteIO', boom)


def test_held_lock_stops_hardware_path_before_the_port(lockdir, portguard, capsys):
    with held_elsewhere():
        rc_ = rc.main(['--smoke'])
    out = capsys.readouterr().out
    assert rc_ == board_guard.LOCK_BUSY_EXIT == 98
    assert 'LOCKED by another process' in out and 'rds-board-' in out


def test_raises_boardbusy_directly(lockdir):
    with held_elsewhere():
        with pytest.raises(board_guard.BoardBusy):
            with board_guard.HardwareRun(readback=False):
                pytest.fail("entered the hardware section with the board held")


def test_sim_path_takes_no_lock(lockdir, portguard):
    """An injected transport never reaches HardwareRun: a held lock is ignored."""
    class DeadIO:
        def ping(self):
            return False

    with held_elsewhere():
        rc_ = rc.main(['--smoke', '--results', str(lockdir / 'r.json')], io=DeadIO())
    assert rc_ == 2            # the ping failed -- NOT 98 (busy), and no port was opened
    assert not rc.IDENTITY


def test_released_lock_is_retaken(lockdir):
    with board_guard.HardwareRun(readback=False):
        pass
    with board_guard.HardwareRun(readback=False):
        pass


def test_inherited_descriptor_counts_as_holding(lockdir):
    """make's board_lock.sh execs the payload with the lock on an inherited fd."""
    path = board_guard.lock_path(board_guard.BOARD)
    holder = board_guard.BoardLock(board_guard.BOARD).__enter__()
    try:
        dup = os.dup(holder._fd)
        try:
            with board_guard.HardwareRun(readback=False) as hw:
                assert hw.identity['board_lock'] == {'path': path, 'inherited': True}
        finally:
            os.close(dup)
    finally:
        holder.__exit__(None, None, None)


# ---- JTAG identity -------------------------------------------------------

READBACK = (
    "JTAG_TARGET localhost:3121/xilinx_tcf/Digilent/{s}A\n"
    "JTAG_TARGET localhost:3121/xilinx_tcf/Digilent/{s}B\n"
    "JTAG_DEVICE localhost:3121/xilinx_tcf/Digilent/{s}B xc7k325t_0 xc7k325t 0011\n")


def _rb(serial, idcode='0011'):
    return board_guard.parse_readback(READBACK.format(s=serial).replace('0011', idcode))


def test_parse_readback():
    rb = _rb('SER1')
    assert [t['serial'] for t in rb['targets']] == ['SER1A', 'SER1B']
    assert rb['devices'][0]['part'] == 'xc7k325t'


def test_check_expected_needs_the_board_with_a_device():
    board_guard.check_expected(_rb('SER1'), 'SER1')
    with pytest.raises(board_guard.IdentityError):
        board_guard.check_expected(_rb('OTHER'), 'SER1')


def _run_with(monkeypatch, lockdir, reads, tmp_path):
    monkeypatch.setattr(board_guard, 'expected_serial', lambda board=board_guard.BOARD: 'SER1')
    it = iter(reads)
    res = tmp_path / 'res.json'
    res.write_text(json.dumps({'passed': 1}))
    with board_guard.HardwareRun(read_fn=lambda: next(it)) as hw:
        ok = hw.finish([str(res)])
    return ok, json.loads(res.read_text())


def test_identity_stable_is_stamped(monkeypatch, lockdir, tmp_path, capsys):
    ok, doc = _run_with(monkeypatch, lockdir, [_rb('SER1'), _rb('SER1')], tmp_path)
    assert ok and doc['jtag']['stable'] is True
    assert doc['jtag']['start'] == doc['jtag']['end'] and doc['jtag']['expected_serial'] == 'SER1'
    assert doc['board_lock']['inherited'] is False and doc['passed'] == 1


def test_identity_changed_fails_the_run(monkeypatch, lockdir, tmp_path, capsys):
    ok, doc = _run_with(monkeypatch, lockdir, [_rb('SER1'), _rb('SER1', idcode='0022')], tmp_path)
    assert not ok and doc['jtag']['stable'] is False
    assert 'differs from the start' in capsys.readouterr().out


def test_wrong_board_at_start_refuses_to_run(monkeypatch, lockdir):
    monkeypatch.setattr(board_guard, 'expected_serial', lambda board=board_guard.BOARD: 'SER1')
    with pytest.raises(board_guard.IdentityError):
        with board_guard.HardwareRun(read_fn=lambda: _rb('OTHER')):
            pytest.fail("ran on the wrong board")


def test_readback_through_a_vivado_stand_in(tmp_path):
    """jtag_readback() runs `vivado -mode batch ... -source <tcl>` and parses stdout."""
    fake = tmp_path / 'vivado'
    fake.write_text("#!/bin/sh\ncat <<'EOF'\n" + READBACK.format(s='SER1') + "EOF\n")
    fake.chmod(fake.stat().st_mode | stat.S_IEXEC)
    rb = board_guard.jtag_readback(vivado=str(fake))
    board_guard.check_expected(rb, 'SER1')
    empty = tmp_path / 'vivado_bad'
    empty.write_text("#!/bin/sh\necho nothing\nexit 1\n")
    empty.chmod(empty.stat().st_mode | stat.S_IEXEC)
    with pytest.raises(board_guard.IdentityError):
        board_guard.jtag_readback(vivado=str(empty))


def test_identity_check_rereads_once_on_the_enumeration_race(monkeypatch):
    """The Genesys 2 chain transiently lists the board with no device behind it
    (a bare `...A0` target whose failed open makes the real `...A0B` report
    "already opened"). read_and_check must RE-READ and accept the clean second
    reading -- otherwise a good campaign is marked "not from one board".
    Observed 2026-10-01 against a 28/28 perf run."""
    monkeypatch.setattr(board_guard.time, 'sleep', lambda _s: None)
    calls = {'n': 0}

    def flaky():
        calls['n'] += 1
        if calls['n'] == 1:
            return {'targets': [{'target': 'T/SER1', 'serial': 'SER1'}], 'devices': []}
        return _rb('SER1')

    rb = board_guard.read_and_check(flaky, 'SER1')
    assert calls['n'] == 2, "must re-read exactly once, not accept the bad reading"
    assert rb['devices'], "must return the reading that actually had a device"


def test_identity_check_still_fails_when_the_board_is_really_absent(monkeypatch):
    """The re-read must not become a way to pass without the board: every
    attempt faces the same check, so a persistently absent board still fails."""
    monkeypatch.setattr(board_guard.time, 'sleep', lambda _s: None)
    calls = {'n': 0}

    def never():
        calls['n'] += 1
        return _rb('OTHER')

    with pytest.raises(board_guard.IdentityError):
        board_guard.read_and_check(never, 'SER1')
    assert calls['n'] == 2, "should have tried twice before giving up"
