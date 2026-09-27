# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""RegisterMap.walk() against a fake bus -- the walk had no test anywhere
(tooling BUG-003): its only callers were two board host programs, so the
TypeError on an ERROR response shipped and took every endpoint's verdict with
it. This pins the three contracts the board walk relies on:

  1. an ERROR response (read -> None) is ONE failure and the walk continues;
  2. the no-reply sentinel is a distinct failure;
  3. `names=` restricts the walk, which is how a guarded window is skipped.
"""
import logging
import os
import sys
import tempfile

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(_HERE, "..", "..", "..")))
from TBClasses.apb.register_map import RegisterMap  # noqa: E402

_REGMAP = """top_block = {
 'CTRL':    {'EN': {'default': '0x1', 'offset': '0', 'sw': 'rw', 'type': 'field'},
             'MODE': {'default': '0x2', 'offset': '3:1', 'sw': 'rw', 'type': 'field'},
             'address': '0x000', 'default': '0x00000005', 'name': 'CTRL', 'offset': '0x000',
             'size': 4, 'sw': 'rw', 'type': 'reg'},
 'STATUS':  {'V': {'default': '0x0', 'offset': '31:0', 'sw': 'r', 'type': 'field'},
             'address': '0x004', 'default': '0x00000000', 'name': 'STATUS', 'offset': '0x004',
             'size': 4, 'sw': 'r', 'type': 'reg'},
 'MON_CFG': {'X': {'default': '0x0', 'offset': '15:0', 'sw': 'rw', 'type': 'field'},
             'address': '0x1000', 'default': '0x00000000', 'name': 'MON_CFG', 'offset': '0x1000',
             'size': 4, 'sw': 'rw', 'type': 'reg'},
}
"""


class FakeBus:
    """A register file that answers like the board: dict-backed, with an
    optional set of addresses that return ERROR (None) and one that never
    replies (the walker's sentinel)."""

    def __init__(self, rm, error_at=(), silent_at=()):
        self.mem, self.latch, self.dflt = {}, {}, {}
        self.error_at = set(error_at)
        self.silent_at = set(silent_at)
        self.sentinel = rm.WALK_NO_RESPONSE
        for name, reg in rm.registers.items():
            a = rm.reg_address(reg, rm.start_address)
            self.dflt[a] = rm.reg_default(reg)
            # hardware latches only the writable, non-pulse bits; the rest read
            # their default -- the same model walk() asserts against
            self.latch[a] = (rm.sw_writable_mask(reg) & ~rm.nonlatching_mask(reg)) & 0xFFFF_FFFF
            self.mem[a] = self.dflt[a]

    def read(self, addr):
        if addr in self.error_at:
            return None
        if addr in self.silent_at:
            return self.sentinel
        return self.mem.get(addr, 0)

    def write(self, addr, value):
        if addr in self.error_at or addr in self.silent_at or addr not in self.mem:
            return
        self.mem[addr] = (value & self.latch[addr]) | (self.dflt[addr] & ~self.latch[addr] & 0xFFFF_FFFF)


@pytest.fixture
def rm(tmp_path):
    p = tmp_path / "fake_regmap.py"
    p.write_text(_REGMAP)
    import contextlib, io
    with contextlib.redirect_stdout(io.StringIO()):
        return RegisterMap(str(p), 32, 32, 0x0010_0000, logging.getLogger("t"))


def test_clean_walk_passes(rm):
    bus = FakeBus(rm)
    assert rm.walk(read=bus.read, write=bus.write) == []


def test_error_response_is_one_failure_and_the_walk_continues(rm):
    mon = rm.reg_address(rm.registers["MON_CFG"], rm.start_address)
    bus = FakeBus(rm, error_at={mon})
    fails = rm.walk(read=bus.read, write=bus.write)
    assert len(fails) == 1, fails
    assert "MON_CFG" in fails[0] and "ERROR RESPONSE" in fails[0]
    # the registers after the guarded one were still walked (CTRL was written
    # with the patterns and restored to its default)
    ctrl = rm.reg_address(rm.registers["CTRL"], rm.start_address)
    assert bus.mem[ctrl] == rm.reg_default(rm.registers["CTRL"])


def test_no_response_is_a_distinct_failure(rm):
    st = rm.reg_address(rm.registers["STATUS"], rm.start_address)
    bus = FakeBus(rm, silent_at={st})
    fails = rm.walk(read=bus.read, write=bus.write)
    assert len(fails) == 1 and "NO RESPONSE" in fails[0], fails


def test_names_skips_the_guarded_window(rm):
    mon = rm.reg_address(rm.registers["MON_CFG"], rm.start_address)
    bus = FakeBus(rm, error_at={mon})
    names = [n for n, r in rm.registers.items() if rm.reg_address(r) < 0x1000]
    assert rm.walk(read=bus.read, write=bus.write, names=names) == []


def test_no_write_checks_reset_but_never_pokes(rm):
    bus = FakeBus(rm)
    writes = []
    def write(addr, value):
        writes.append(addr); bus.write(addr, value)
    ctrl = rm.reg_address(rm.registers["CTRL"], rm.start_address)
    fails = rm.walk(read=bus.read, write=write, no_write=("CTRL",))
    assert fails == [] and ctrl not in writes
