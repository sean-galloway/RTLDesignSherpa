#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Board-less proof: the pumice char flow composes each regmap as its own Device.

`build_ddr2_bus()` loads the generated pumice controller regmap and the harness
regmap as SEPARATE named devices over one (mock) bridge -- by name, field sugar,
no hand-merge, no hardcoded offsets.

    source env_python && pytest test_pumice_device.py -q
"""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

if not os.environ.get("REPO_ROOT"):
    pytest.skip("REPO_ROOT not set (source env_python)", allow_module_level=True)

import pumice_device as pd  # noqa: E402


class _MockBridge:
    def __init__(self):
        self.mem = {}

    def write(self, addr, val):
        self.mem[addr] = val & 0xFFFF_FFFF
        return True

    def read(self, addr):
        return self.mem.get(addr, 0)


def test_bus_composes_pumice_and_harness_by_name():
    bus = pd.build_ddr2_bus(_MockBridge())
    assert set(bus.names()) == {"pumice", "harness"}
    # each regmap at its own window
    assert bus["pumice"].addr("DFI_PHASE") == pd.DDR2_APB_BASE + 0x60
    assert bus["harness"].addr("STATUS") == pd.HARNESS_CSR_BASE + 0x04
    assert isinstance(bus["pumice"], pd.Pumice)


def test_pumice_device_field_ops():
    b = _MockBridge()
    bus = pd.build_ddr2_bus(b)
    p = bus["pumice"]
    p.set_dfi_phase(rd_phase=1, wr_phase=0)
    assert p.field("DFI_PHASE", "rd_phase") == 1
    p.set_page_policy(2)                       # CLOSE, via read-modify-write
    assert p.field("REFRESH_TUNING", "page_policy_or") == 2
    p.set_sched_policy(order_mode=1)
    assert p.field("SCHED_POLICY", "order_mode") == 1
    p.set_refresh(postpone=4, pullin=2)
    assert p.field("REF_CTRL", "postpone_limit") == 4
    assert p.field("REF_CTRL", "pullin_limit") == 2
    # attribute sugar reaches the same word
    b.mem[p.addr("STATUS")] = 1 << 0           # init_done (pumice STATUS bit 0)
    assert p.init_done() is True


def test_ddr2_part_trrd_is_the_2kb_page_value():
    """memory-controllers BUG-003: JESD79-2F Tables 42 / 43 give tRRD by page
    size, 7.5 ns for 1 KB-page products and 10 ns for 2 KB-page products. The
    board's x16 with 1K columns is a 2 KB page, so the table carries 10 ns; the
    three rows below are the bug's effect table (same count at both board
    clocks under the 2 CK floor, one MC cycle more at the DDR2-800 span config)."""
    assert pd.DDR2_MT47H64M16_NS["tRRD"] == 10.0
    assert pd.DDR2_MT47H64M16_NS["tFAW"] == 45.0          # the 2 KB-page tFAW, already right
    rows = {  # (mc_clk_hz, cl): tRRD in MC cycles
        (75e6, 3): 2,      # board_ddr2_300 (CK 150): 2 CK floor either way
        (100e6, 3): 2,     # ddr2_400_cl3_bl4 (CK 200): 2 CK floor either way
        (200e6, 6): 3,     # ddr2_800_cl6_bl4 span config (CK 400): was 2 with tRRD 7.5
    }
    for (hz, cl), want in rows.items():
        assert pd.ddr2_timings_mc_cycles(hz, cl=cl)["tRRD"] == want, (hz, cl)


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))


def test_auto_precharge_trp_fields_follow_the_derivation():
    """memory-controllers MC-020 decision 2: tRP_AP_RD / tRP_AP_WR are the shared tRP under the margin and the
    exact hop from the self-close's fire cycle to an ACT on row_phase under phase_exact -- 1 / 2 at 100 MHz on
    the SKU's phases (0 / 0 / 1), where the RTL's shared tRP of 2 put ACT -> RDA -> ACT at 7 MC against tRC 6."""
    m = pd.ddr2_timings_mc_cycles(100e6, cl=3, rd_phase=0, wr_phase=0, row_phase=1)
    assert (m["tRP_AP_RD"], m["tRP_AP_WR"]) == (m["tRP"], m["tRP"])
    x = pd.ddr2_timings_mc_cycles(100e6, cl=3, rd_phase=0, wr_phase=0, row_phase=1, phase_exact=True)
    assert (x["tRP_AP_RD"], x["tRP_AP_WR"]) == (1, 2)
    # the chain through the self-close is at least tRC, each path (tRAS 5 + 1 = 6 = tRC)
    assert x["tRAS"] + x["tRP_AP_RD"] >= x["tRC"] and x["tRAS"] + x["tRP_AP_WR"] >= x["tRC"]
    # legal at the CK: fire slot's close CK + nRP <= the ACT's CK on row_phase 1 (RD: 2 + 3 <= 2 * 2 + 1)
    assert 2 * (x["tRTP"] + x["tRP_AP_RD"]) + 1 >= 2 + 3 and 2 * (x["tWR"] + x["tRP_AP_WR"]) + 1 >= 7 + 3
    # row commands on phase 0 (the lane off): the read path pays the full hop, the write path's close is late in its cycle
    x0 = pd.ddr2_timings_mc_cycles(100e6, cl=3, rd_phase=0, wr_phase=0, row_phase=0, phase_exact=True)
    assert (x0["tRP_AP_RD"], x0["tRP_AP_WR"]) == (2, 1)


def test_set_jedec_timings_skips_the_ap_fields_on_a_regmap_without_the_register():
    """The host serves pumice too; its regmap has no TIMINGS_RP_AP, so the group is skipped and the applied dict
    does not claim the fields were programmed."""
    bus = pd.build_ddr2_bus(_MockBridge())
    p = bus["pumice"]
    applied = p.set_jedec_timings(dict(tRP=2, tRP_AP_RD=1, tRP_AP_WR=2))
    assert applied == {"tRP": 2}

