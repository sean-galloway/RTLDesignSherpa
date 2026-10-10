# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `andesite_odt_ctrl` -- DDR4 per-rank ODT pin policy.

New block (no carry). The MAS 08 fence is the spec: per-rank policy states
(PARK / RD-other -> RTT_NOM / RD-self -> ODT off / WR-self -> RTT_WR),
the scheduler grant tap, ODTL-family latency enforcement on the pin, and
the init seam (init_sequencer owns the pin until init_done, then the block
samples init_odt_i as its starting value).

LPDDR4 scope note per the MAS page: MR-programmed termination is init-side
there, so this block is DDR4-scoped; the suite never claims LPDDR4 pins.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

NUM_RANKS = 2
OP_RD = 0x02
OP_WR = 0x04
OP_ACT = 0x01


class OdtTB(TBBase):
    async def setup(self, *, odtlon=3, odtloff=2, odt_turn=4, tadc=1):
        await self.start_clock('mc_clk', 10, 'ns')
        d = self.dut
        d.init_done_i.value = 0
        d.init_odt_i.value = 0
        d.grant_valid_i.value = 0
        d.grant_op_i.value = 0
        d.grant_rank_i.value = 0
        d.odtlon_i.value = odtlon
        d.odtloff_i.value = odtloff
        d.odt_turn_i.value = odt_turn
        d.tadc_i.value = tadc
        d.rtt_nom_img_i.value = 1
        d.rtt_wr_img_i.value = 2
        d.rtt_park_img_i.value = 3
        await self.assert_reset()
        await self.wait_clocks('mc_clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('mc_clk', 3)

    async def assert_reset(self):
        self.dut.mc_rst_n.value = 0

    async def deassert_reset(self):
        self.dut.mc_rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    async def tap(self, op, rank):
        """One-cycle grant tap."""
        self.dut.grant_valid_i.value = 1
        self.dut.grant_op_i.value = op
        self.dut.grant_rank_i.value = rank
        await RisingEdge(self.dut.mc_clk)
        self.dut.grant_valid_i.value = 0
        await Timer(1, 'ns')

    async def wait_park(self, mask=0x3, limit=20):
        """After the init seam, the park policy asserts both pins within
        tADC cycles; grant taps must not start before that settles."""
        for _ in range(limit):
            await RisingEdge(self.dut.mc_clk)
            await Timer(1, 'ns')
            if (self.pin() & mask) == mask:
                return
        raise AssertionError("park policy never asserted after handoff")

    def pin(self):
        return int(self.dut.odt_pin_o.value)

    def hist(self, rank):
        return (int(self.dut.hist_state_o.value) >> (rank * 2)) & 0x3

    def trans(self, rank):
        return (int(self.dut.trans_count_o.value) >> (rank * 8)) & 0xFF


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_andesite_odt_ctrl(dut):
    tt = os.environ.get("TEST_TYPE", "smoke")
    tb = OdtTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "smoke":
        await tb.setup()
        # init seam: before init_done the pin tracks init_odt_i
        dut.init_odt_i.value = 0x1
        await Timer(1, 'ns')
        chk(tb.pin() == 0x1, f"pin {tb.pin()} != init_odt 0x1 before init_done")
        # ownership transfers at init_done: the block samples init_odt as
        # its starting value (0x1 -- distinguishable from park's 0b11)
        dut.init_done_i.value = 1
        await RisingEdge(dut.mc_clk)
        await Timer(1, 'ns')
        chk(tb.pin() == 0x1, "init_odt not sampled as the starting pin value")

    elif tt == "wr_self_asserts_after_odtlon":
        await tb.setup(odtlon=3)
        dut.init_done_i.value = 1
        dut.init_odt_i.value = 0x0
        await RisingEdge(dut.mc_clk)
        await tb.tap(OP_WR, 1)
        # rank 1: WR state; pin asserts after ODTLon countdown
        for i in range(12):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ns')
            if tb.pin() & 0x2:
                break
        chk((tb.pin() & 0x2) != 0, "rank1 ODT never asserted after WR grant")
        chk(3 <= i <= 5, f"pin asserted at countdown {i}, expected ODTLon=3 ±")
        chk(tb.hist(1) == 3, f"rank1 state {tb.hist(1)} != WR(3)")

    elif tt == "rd_self_turns_odt_off":
        await tb.setup(odtloff=2)
        dut.init_done_i.value = 1
        await tb.wait_park()
        await tb.tap(OP_RD, 0)
        # rank 0 reads: its ODT goes off after ODTLoff; rank 1 presents NOM
        for i in range(12):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ns')
            if not (tb.pin() & 0x1):
                break
        chk(not (tb.pin() & 0x1), "rank0 ODT never released after RD self")
        chk(2 <= i <= 4, f"rank0 release at {i}, expected ODTLoff=2 ±")
        chk(tb.hist(0) == 2, f"rank0 state {tb.hist(0)} != RD_SELF(2)")
        chk((tb.pin() & 0x2) != 0, "rank1 did not present NOM during the read")
        chk(tb.hist(1) == 1, f"rank1 state {tb.hist(1)} != RD_NOM(1)")

    elif tt == "wr_to_rd_uses_turnaround":
        await tb.setup(odt_turn=4, odtloff=1)
        dut.init_done_i.value = 1
        await tb.wait_park()
        await tb.tap(OP_WR, 1)
        for i in range(12):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ns')
            if tb.pin() & 0x2:
                break
        # now a read to the same rank: WR -> RD_SELF releases via the
        # write-to-read turnaround, not ODTLoff
        await tb.tap(OP_RD, 1)
        for j in range(12):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ns')
            if not (tb.pin() & 0x2):
                break
        chk(not (tb.pin() & 0x2), "rank1 ODT never released on WR->RD")
        chk(4 <= j <= 6, f"release at {j}, expected ODT_TURN=4 (not ODTLoff=1)")

    elif tt == "non_rw_grants_hold_state":
        await tb.setup()
        dut.init_done_i.value = 1
        await tb.wait_park()
        await tb.tap(OP_ACT, 0)
        p0 = tb.pin()
        for _ in range(6):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ns')
        chk(tb.pin() == p0, "ACT grant moved the pin")
        chk(tb.trans(0) == 0 and tb.trans(1) == 0,
            f"ACT grant counted transitions: {tb.trans(0)}/{tb.trans(1)}")

    elif tt == "transitions_counted_per_rank":
        await tb.setup()
        dut.init_done_i.value = 1
        await RisingEdge(dut.mc_clk)
        t0 = tb.trans(0)
        await tb.tap(OP_RD, 1)   # rank0: PARK -> RD_NOM
        for _ in range(10):
            await RisingEdge(dut.mc_clk)
        chk(tb.trans(0) == t0 + 1,
            f"rank0 transitions {tb.trans(0)} != {t0 + 1}")
        chk(tb.trans(1) == 1, f"rank1 transitions {tb.trans(1)} != 1")

    elif tt == "single_rank_degenerates":
        # The 1-rank design point exercises PARK and WR only; the coupling
        # structure must degenerate, not special-case.
        await tb.setup()
        dut.init_done_i.value = 1
        await tb.wait_park()
        await tb.tap(OP_WR, 0)
        for i in range(12):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ns')
            if tb.pin() & 0x1:
                break
        chk((tb.pin() & 0x1) != 0, "single-rank WR never asserted ODT")
        await tb.tap(OP_RD, 0)
        for j in range(12):
            await RisingEdge(dut.mc_clk)
            await Timer(1, 'ns')
            if not (tb.pin() & 0x1):
                break
        chk(not (tb.pin() & 0x1), "single-rank RD-self never released ODT")

    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('mc_clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["smoke", "wr_self_asserts_after_odtlon", "rd_self_turns_odt_off"]
_FUNC = _GATE + ["wr_to_rd_uses_turnaround", "non_rw_grants_hold_state",
                 "transitions_counted_per_rank", "single_rank_degenerates"]
_FULL = _FUNC
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FULL}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_andesite_odt_ctrl(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "andesite_odt_ctrl"
    test_name = f"test_andesite_odt_ctrl_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/"
                       "rtl/filelists/fub/andesite_odt_ctrl.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_andesite_odt_ctrl",
        sim_build=sim_build, simulator="verilator",
        parameters={"NUM_RANKS": str(NUM_RANKS)},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
