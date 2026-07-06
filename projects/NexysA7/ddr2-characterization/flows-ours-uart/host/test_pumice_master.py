#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less unit tests for pumice_master.py.

Injects a mock UART bridge that models the harness register space plus a tiny
DDR2/a7ddrphy calibration device (a "good" write phase + a read-tap eye window;
CRC passes only when both are satisfied). This exercises the leveling data-eye
search, the simple write-then-read pass, and the full-characterization sweep
WITHOUT a board -- so the host orchestration logic is CI-checkable.

    pytest test_pumice_master.py -q
"""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(__file__))
import ddr2_char as dc
from ddr2_char import DDR2CharDriver, HARNESS_CSR_BASE
import pumice_master as pm


# --------------------------------------------------------------------------
# Mock device + bridge
# --------------------------------------------------------------------------
class MockDevice:
    """Models a7ddrphy calibration: read CRC passes iff the write phase equals
    GOOD_WR_PHASE and the read IDELAY tap sits inside [EYE_LO, EYE_HI]."""

    def __init__(self, good_wr_phase=1, eye=(8, 22), has_eye=True):
        self.good_wr_phase = good_wr_phase
        self.eye_lo, self.eye_hi = eye
        self.has_eye = has_eye
        self.rdly_tap = 0
        self.wrphase = 0
        self.phy_addr = 0
        self.phy_wdata = 0

    def apply_phy(self, knob, val):
        if knob == dc.PHY_RDLY_DQ_RST:
            self.rdly_tap = 0
        elif knob == dc.PHY_RDLY_DQ_INC:
            self.rdly_tap += 1
        elif knob == dc.PHY_WRPHASE:
            self.wrphase = val
        # rst / bitslips / phase / lane-select are no-ops for this model

    def read_ok(self):
        if not self.has_eye:
            return False
        return (self.wrphase == self.good_wr_phase
                and self.eye_lo <= self.rdly_tap <= self.eye_hi)


class MockBridge:
    """read(addr)->int / write(addr,val)->bool over an in-memory reg model."""

    # plausible non-zero readbacks for the perf/timer windows
    _DEFAULTS = None

    def __init__(self, dev: MockDevice):
        self.dev = dev
        self.regs = {}

    def _off(self, addr):
        return addr - HARNESS_CSR_BASE

    def write(self, addr, val):
        off = self._off(addr)
        self.regs[off] = val
        if off == dc.PHY_CSR_ADDR:
            self.dev.phy_addr = val
        elif off == dc.PHY_CSR_WDATA:
            self.dev.phy_wdata = val
        elif off == dc.PHY_CSR_CTRL and (val & 1):
            self.dev.apply_phy(self.dev.phy_addr, self.dev.phy_wdata)
        elif off == dc.CTRL:
            if val & (1 << 0):                       # start_wr
                self.regs[dc.STATUS] = self.regs.get(dc.STATUS, 0) | (1 << 0)
            if val & (1 << 1):                       # start_rd
                self.regs[dc.STATUS] = self.regs.get(dc.STATUS, 0) | (1 << 1)
                ok = self.dev.read_ok()
                self.regs[dc.CRC_MATCH]    = 0b111 if ok else 0b110  # valid; match=ok
                self.regs[dc.CRC_EXPECTED] = 0xABCD
                self.regs[dc.CRC_ACTUAL]   = 0xABCD if ok else 0xDEAD
                self.regs[dc.BEATS_MISM]   = 0 if ok else 4
            if val & (1 << 2):                       # clear_stats
                self.regs[dc.STATUS] = 0
            if val & (1 << 4):                       # soft_reset
                self.regs[dc.STATUS] = 0
        return True

    def read(self, addr):
        off = self._off(addr)
        if off == dc.BUILD_ID:
            return 0x4444_5232
        if off == dc.PHY_CSR_RDATA:
            return 0
        # timer window
        if off == dc.TIMER_STATUS:
            return 0b101                 # done + pass
        if off in (dc.TIMER_CYC_LO,):
            return 5000
        if off in (dc.TIMER_R_FIRST_LO, dc.TIMER_W_FIRST_LO):
            return 10
        if off in (dc.TIMER_R_LAST_LO, dc.TIMER_W_LAST_LO):
            return 5010
        # perf bus meters (util ~= 800/1000 = 80%)
        if off in (dc.OBS_RD_PROD, dc.OBS_WR_PROD):
            return 800
        if off in (dc.OBS_RD_BP, dc.OBS_WR_BP):
            return 100
        if off in (dc.OBS_RD_STARV, dc.OBS_WR_STARV,
                   dc.OBS_RD_IDLE, dc.OBS_WR_IDLE):
            return 50
        if off == dc.OBS_HIST_COUNT:
            return 7
        if off == dc.OBS_HIST_TOTAL:
            return 100
        return self.regs.get(off, 0)


def _mk_driver(dev: MockDevice) -> DDR2CharDriver:
    """Build a DDR2CharDriver with the mock bridge (no serial port opened).

    Uses the real constructor via bridge injection, so this exercises the
    same by-name UartRegisterMap path as the silicon/sim flows.
    """
    return DDR2CharDriver(bridge=MockBridge(dev))


# --------------------------------------------------------------------------
# Tests
# --------------------------------------------------------------------------
def test_build_id_reads_back():
    drv = _mk_driver(MockDevice())
    assert drv.build_id() == 0x4444_5232


def test_leveling_finds_eye():
    dev = MockDevice(good_wr_phase=2, eye=(9, 21))
    drv = _mk_driver(dev)
    res = pm.A7Leveling(drv, base_addr=0x0, txn_count=4, verbose=False).run()
    assert res.ok, res.notes
    assert res.wr_phase == 2
    lo, hi = res.rd_window
    assert (lo, hi) == (9, 21)
    assert res.rd_tap == (9 + 21) // 2          # centred
    assert lo <= res.rd_tap <= hi


def test_leveling_fails_without_eye():
    dev = MockDevice(has_eye=False)
    drv = _mk_driver(dev)
    res = pm.A7Leveling(drv, base_addr=0x0, txn_count=4, verbose=False).run()
    assert not res.ok
    assert res.notes


def test_simple_passes_after_leveling():
    dev = MockDevice(good_wr_phase=1, eye=(8, 22))
    drv = _mk_driver(dev)
    st = pm.SimpleTest(drv, base_addr=0x0)
    st.init(do_leveling=True)
    assert st.level is not None and st.level.ok
    r = st.run(burst_len=8, txn_count=16)
    assert r.ok
    assert r.mismatched == 0


def test_simple_fails_when_uncalibrated():
    # skip leveling on a device whose default (phase 0, tap 0) is outside the eye
    dev = MockDevice(good_wr_phase=1, eye=(8, 22))
    drv = _mk_driver(dev)
    st = pm.SimpleTest(drv, base_addr=0x0)
    st.init(do_leveling=False)
    r = st.run()
    assert not r.ok                              # uncalibrated -> CRC mismatch


def test_full_characterization_sweep():
    dev = MockDevice(good_wr_phase=1, eye=(8, 22))
    drv = _mk_driver(dev)
    fc = pm.FullCharacterization(drv, base_addr=0x0, txn_count=8)
    fc.init(do_leveling=True)
    pts = fc.run()
    assert len(pts) == len(fc.DEFAULT_GRID)
    assert all(p.ok for p in pts)                # calibrated -> every point passes
    assert all(p.cycles > 0 for p in pts)
    assert all(0.0 <= p.rd_util <= 1.0 for p in pts)
    assert all(len(p.rd_hist) == 16 for p in pts)


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
