"""DDR2 device-timing checks against JESD79-2F (memory-controllers MC-012).

Each test pins one constraint of python/ramulator/dram/ddr2.py to the clause
or table it comes from, through the probe / issue harness: the gate must open
exactly at the JEDEC cycle, not a cycle early and not a cycle late.
"""
import pytest

import ramulator
import tests.device_timings.harness as device_timings
from tests.utils import extract_dram_layout


pytestmark = pytest.mark.device_timings


def make_dut(timing_preset="DDR2_800E", org_preset="DDR2_1Gb_x16", cls=None, **overrides):
    dram_cls = cls or ramulator.dram.DDR2
    dram = dram_cls(org_preset=org_preset, timing_preset=timing_preset, **overrides)
    return device_timings.DeviceUnderTest(dram)


def bank(dut, b, row=0, col=0):
    return dut.addr_vec(Rank=0, Bank=b, Row=row, Column=col)


# ---- presets: the JEDEC numbers themselves -----------------------------------

def test_800e_bin_resolves_the_table_43_values_for_a_2kb_page():
    t = make_dut("DDR2_800E").timings
    # Table 41: 6-6-6, tRAS 45 ns, tRC 60 ns at tCK 2.5 ns
    assert (t["nCL"], t["nRCD"], t["nRP"], t["nRAS"], t["nRC"]) == (6, 6, 6, 18, 24)
    # Table 43, 2 KB page: tRRD 10 ns -> 4, tFAW 45 ns -> 18; tWTR 7.5 -> 3; tCCD 2
    assert (t["nRRD"], t["nFAW"], t["nWTR"], t["nCCD"]) == (4, 18, 3, 2)
    # WL = CL - 1 (clause 3.9), tRFC(1 Gb) 127.5 ns -> 51, tREFI 7.8 us -> 3120
    assert (t["nCWL"], t["nRFC"], t["nREFI"]) == (5, 51, 3120)


def test_1kb_page_takes_the_1kb_trrd_tfaw_column():
    t = make_dut("DDR2_800E", org_preset="DDR2_1Gb_x8").timings
    # x8 with 1K columns = 1 KB page: tRRD 7.5 ns -> 3, tFAW 35 ns -> 14 at DDR2-800
    assert (t["nRRD"], t["nFAW"]) == (3, 14)


def test_400b_bin_has_the_slower_twtr_and_the_50ns_tfaw():
    t = make_dut("DDR2_400B").timings
    # Table 41 DDR2-400B: 3-3-3, tRAS 40, tRC 55 at 5 ns; Table 42: tWTR 10 ns, tFAW(2 KB) 50 ns
    assert (t["nCL"], t["nRCD"], t["nRP"], t["nRAS"], t["nRC"]) == (3, 3, 3, 8, 11)
    assert (t["nWTR"], t["nRRD"], t["nFAW"]) == (2, 2, 10)


def test_board_part_presets_match_the_rtl_derivation_in_ck():
    # pumice_device.ddr2_timings_mc_cycles at 75 / 100 MHz, in CK (2 CK per MC cycle):
    # tRCD/tRP 15 ns -> 3 CK at both; tRAS 45 -> 7 / 9; tRC 60 -> 9 / 12; tFAW 45 -> 7 / 9
    t300 = make_dut("DDR2_MT47H64M16_300_CL3").timings
    t400 = make_dut("DDR2_MT47H64M16_400_CL3").timings
    assert (t300["nRCD"], t300["nRP"], t300["nRAS"], t300["nRC"], t300["nFAW"]) == (3, 3, 7, 9, 7)
    assert (t400["nRCD"], t400["nRP"], t400["nRAS"], t400["nRC"], t400["nFAW"]) == (3, 3, 9, 12, 9)
    # the part's tRRD is 10 ns (2 KB page); 7.5 ns or 10 ns both round to 2 CK at CK 150 / 200 MHz
    assert t300["nRRD"] == 2 and t400["nRRD"] == 2
    assert t300["nRFC"] == 20 and t400["nRFC"] == 26
    assert t300["nREFI"] == 1169 and t400["nREFI"] == 1560


def test_bl4_and_bl8_classes_differ_only_in_prefetch_and_nbl():
    bl4 = ramulator.dram.DDR2(org_preset="DDR2_1Gb_x16", timing_preset="DDR2_800E")
    bl8 = ramulator.dram.DDR2_BL8(org_preset="DDR2_1Gb_x16", timing_preset="DDR2_800E")
    assert ramulator.dram.DDR2.internal_prefetch_size == 4
    assert ramulator.dram.DDR2_BL8.internal_prefetch_size == 8
    _, t4 = bl4.resolve()
    _, t8 = bl8.resolve()
    assert t4["nBL"] == 2 and t8["nBL"] == 4
    assert {k: v for k, v in t4.items() if k != "nBL"} == {k: v for k, v in t8.items() if k != "nBL"}
    # 1K columns of x16: 256 BL4 bursts per page, 128 BL8 bursts
    assert extract_dram_layout(bl4)["num_cls"] == 256
    assert extract_dram_layout(bl8)["num_cls"] == 128


# ---- command gates ------------------------------------------------------------

def test_rd_on_closed_bank_requires_act():
    dut = make_dut()
    probe = dut.probe("RD", bank(dut, 0, row=12), clk=0)
    assert probe.preq == "ACT"
    assert probe.ready is False
    assert probe.row_open is False


def test_act_to_rd_is_trcd():
    dut = make_dut()
    a = bank(dut, 0, row=12)
    dut.issue("ACT", a, clk=0)
    dut.assert_earliest_ready_at("RD", a, dut.timings["nRCD"])


def test_rd_to_prepb_is_bl_half_plus_trtp_minus_two():
    # clause 3.9.1: RD -> PRE = AL + BL/2 + max(tRTP, 2) - 2, under tRAS from the ACT
    dut = make_dut()
    a = bank(dut, 0, row=12)
    t = dut.timings
    dut.issue("ACT", a, clk=0)
    dut.issue("RD", a, clk=t["nRCD"])
    expect = max(t["nRCD"] + t["nBL"] + t["nRTP"] - 2, t["nRAS"])
    dut.assert_earliest_ready_at("PREpb", a, expect)


def test_prepb_to_act_is_trp_and_preab_to_act_is_trp_plus_one():
    # Table 41 note 1: tRPall = tRP + 1 tCK on an 8-bank device
    t = make_dut().timings
    dut = make_dut()
    a = bank(dut, 0, row=12)
    dut.issue("ACT", a, clk=0)
    dut.issue("PREpb", a, clk=t["nRAS"])
    dut.assert_earliest_ready_at("ACT", a, t["nRAS"] + t["nRP"])

    dut = make_dut()
    all_banks = dut.addr_vec(Rank=0, Bank=dut.ALL, Row=dut.ALL, Column=dut.ALL)
    dut.issue("ACT", a, clk=0)
    dut.issue("PREab", all_banks, clk=t["nRAS"])
    dut.assert_earliest_ready_at("ACT", a, t["nRAS"] + t["nRP"] + 1)


def test_wr_to_prepb_is_wl_plus_bl_half_plus_twr():
    dut = make_dut()
    a = bank(dut, 0, row=12)
    t = dut.timings
    dut.issue("ACT", a, clk=0)
    dut.issue("WR", a, clk=t["nRCD"])
    expect = max(t["nRCD"] + t["nCWL"] + t["nBL"] + t["nWR"], t["nRAS"])
    dut.assert_earliest_ready_at("PREpb", a, expect)


def test_write_to_read_turnaround_is_wl_plus_bl_half_plus_twtr():
    dut = make_dut()
    a = bank(dut, 0, row=12)
    t = dut.timings
    dut.issue("ACT", a, clk=0)
    dut.issue("WR", a, clk=t["nRCD"])
    dut.assert_earliest_ready_at("RD", a, t["nRCD"] + t["nCWL"] + t["nBL"] + t["nWTR"])


def test_read_to_write_turnaround_is_rl_plus_bl_half_plus_two_minus_wl():
    dut = make_dut()
    a = bank(dut, 0, row=12)
    t = dut.timings
    dut.issue("ACT", a, clk=0)
    dut.issue("RD", a, clk=t["nRCD"])
    # with WL = CL - 1 this is BL/2 + 3
    dut.assert_earliest_ready_at("WR", a, t["nRCD"] + t["nCL"] + t["nBL"] + 2 - t["nCWL"])


def test_fifth_activate_waits_for_tfaw():
    # DDR2-800E 2 KB: nRRD 4, nFAW 18 -- four ACTs at 0/4/8/12, the fifth at 18 not 16
    dut = make_dut("DDR2_800E")
    t = dut.timings
    assert 4 * t["nRRD"] < t["nFAW"], "preset must make tFAW, not tRRD, the binding gate"
    for i in range(4):
        dut.assert_earliest_ready_at("ACT", bank(dut, i, row=i), i * t["nRRD"])
        dut.issue("ACT", bank(dut, i, row=i), clk=i * t["nRRD"])
    dut.assert_earliest_ready_at("ACT", bank(dut, 4, row=4), t["nFAW"])


def test_refab_needs_closed_banks_and_act_after_refab_waits_trfc():
    dut = make_dut()
    t = dut.timings
    a = bank(dut, 0, row=12)
    ref = dut.addr_vec(Rank=0, Bank=dut.ALL, Row=dut.ALL, Column=dut.ALL)
    dut.issue("ACT", a, clk=0)
    probe = dut.probe("REFab", ref, clk=1)
    assert probe.preq == "PREab"
    dut.issue("PREab", ref, clk=t["nRAS"])
    dut.assert_earliest_ready_at("REFab", ref, t["nRAS"] + t["nRP"] + 1)
    dut.issue("REFab", ref, clk=t["nRAS"] + t["nRP"] + 1)
    dut.assert_earliest_ready_at("ACT", a, t["nRAS"] + t["nRP"] + 1 + t["nRFC"])
