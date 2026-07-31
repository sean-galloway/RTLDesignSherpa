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
from ddr2_char import DDR2CharDriver, HARNESS_CSR_BASE, HARNESS_REGMAP
from TBClasses.harness.uart_register_map import UartRegisterMap
import pumice_master as pm


# --------------------------------------------------------------------------
# Mock device + bridge
# --------------------------------------------------------------------------
class MockDevice:
    """Models a7ddrphy READ calibration (A7 = read-leveling only): a read
    passes iff the read bitslip equals GOOD_BITSLIP and the read IDELAY tap
    sits inside [EYE_LO, EYE_HI]. Mirrors the corrected A7Leveling sweep
    (bitslip x IDELAY tap, dly_sel-bracketed strobes, no PHY_RST/wrphase)."""

    def __init__(self, good_bitslip=2, eye=(8, 22), has_eye=True):
        self.good_bitslip = good_bitslip
        self.eye_lo, self.eye_hi = eye
        self.has_eye = has_eye
        self.rdly_tap = 0
        self.bitslip = 0
        self.phy_addr = 0
        self.phy_wdata = 0

    def apply_phy(self, knob, val):
        if knob == dc.PHY_RDLY_DQ_RST:
            self.rdly_tap = 0
        elif knob == dc.PHY_RDLY_DQ_INC:
            self.rdly_tap += 1
        elif knob == dc.PHY_RDLY_DQ_BITSLIP_RST:
            self.bitslip = 0
        elif knob == dc.PHY_RDLY_DQ_BITSLIP:
            self.bitslip = (self.bitslip + 1) % 8
        # dly_sel / wrphase / rst / wdly bitslips are no-ops for this model

    def read_ok(self):
        if not self.has_eye:
            return False
        return (self.bitslip == self.good_bitslip
                and self.eye_lo <= self.rdly_tap <= self.eye_hi)


class MockBridge:
    """read(addr)->int / write(addr,val)->bool over an in-memory reg model,
    addressed entirely BY NAME via the same PeakRDL harness regmap the driver
    uses -- no hardcoded offsets. (self is the bridge; UartRegisterMap.addr()
    does no I/O, so it is safe to build during construction just to resolve
    absolute address -> register name.)"""

    def __init__(self, dev: MockDevice):
        self.dev = dev
        self.regs = {}                       # keyed by register NAME
        self._rm = UartRegisterMap(self, HARNESS_CSR_BASE,
                                   regmap_file=HARNESS_REGMAP)
        self._name = {self._rm.addr(rn): rn for rn in self._rm.registers}

    def _reg(self, addr):
        return self._name.get(addr)

    def write(self, addr, val):
        name = self._reg(addr)
        if name is not None:
            self.regs[name] = val
        if name == "PHY_CSR_ADDR":
            self.dev.phy_addr = val
        elif name == "PHY_CSR_WDATA":
            self.dev.phy_wdata = val
        elif name == "PHY_CSR_CTRL" and (val & 1):
            self.dev.apply_phy(self.dev.phy_addr, self.dev.phy_wdata)
        elif name == "CTRL":
            if val & (1 << 0):                       # start_wr
                self.regs["STATUS"] = self.regs.get("STATUS", 0) | (1 << 0)
            if val & (1 << 1):                       # start_rd
                self.regs["STATUS"] = self.regs.get("STATUS", 0) | (1 << 1)
                ok = self.dev.read_ok()
                self.regs["CRC_MATCH"]    = 0b111 if ok else 0b110  # valid; match=ok
                self.regs["CRC_EXPECTED"] = 0xABCD
                self.regs["CRC_ACTUAL"]   = 0xABCD if ok else 0xDEAD
                self.regs["BEATS_MISM"]   = 0 if ok else 4
            if val & (1 << 2):                       # clear_stats
                self.regs["STATUS"] = 0
            if val & (1 << 4):                       # soft_reset
                self.regs["STATUS"] = 0
        return True

    def read(self, addr):
        name = self._reg(addr)
        if name == "BUILD_ID":
            return 0x4444_5232
        if name == "PHY_CSR_RDATA":
            return 0
        # timer window
        if name == "TIMER_STATUS":
            return 0b101                 # done + pass
        if name == "TIMER_CYCLES_LO":
            return 5000
        if name in ("TIMER_R_FIRST_LO", "TIMER_W_FIRST_LO"):
            return 10
        if name in ("TIMER_R_LAST_LO", "TIMER_W_LAST_LO"):
            return 5010
        # perf bus meters (util ~= 800/1000 = 80%)
        if name in ("OBS_RD_PROD", "OBS_WR_PROD"):
            return 800
        if name in ("OBS_RD_BP", "OBS_WR_BP"):
            return 100
        if name in ("OBS_RD_STARV", "OBS_WR_STARV",
                    "OBS_RD_IDLE", "OBS_WR_IDLE"):
            return 50
        if name == "OBS_HIST_COUNT":
            return 7
        if name == "OBS_HIST_TOTAL":
            return 100
        return self.regs.get(name, 0)


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
    dev = MockDevice(good_bitslip=2, eye=(9, 21))
    drv = _mk_driver(dev)
    res = pm.A7Leveling(drv, base_addr=0x0, txn_count=2, verbose=False).run()
    assert res.ok, res.notes
    assert res.bitslip == 2
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
    dev = MockDevice(good_bitslip=1, eye=(8, 22))
    drv = _mk_driver(dev)
    st = pm.SimpleTest(drv, base_addr=0x0)
    st.init(do_leveling=True)
    assert st.level is not None and st.level.ok
    r = st.run(burst_len=8, txn_count=16)
    assert r.ok
    assert r.mismatched == 0


def test_simple_fails_when_uncalibrated():
    # skip leveling on a device whose default (phase 0, tap 0) is outside the eye
    dev = MockDevice(good_bitslip=1, eye=(8, 22))
    drv = _mk_driver(dev)
    st = pm.SimpleTest(drv, base_addr=0x0)
    st.init(do_leveling=False)
    r = st.run()
    assert not r.ok                              # uncalibrated -> CRC mismatch


def test_full_characterization_sweep():
    dev = MockDevice(good_bitslip=1, eye=(8, 22))
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
