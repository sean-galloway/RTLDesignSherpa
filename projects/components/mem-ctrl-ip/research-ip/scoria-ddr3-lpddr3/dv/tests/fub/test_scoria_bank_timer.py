# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""Unit test for `scoria_bank_timer` -- the per-bank JEDEC window leaf.

No pumice test targets this module directly (pumice tests bank_timerS, the
array). It is worth testing alone because every window here is a JEDEC
requirement whose violation corrupts data rather than degrading throughput, and
because the SPACING CONVENTION is easy to get wrong by one in the unsafe
direction.

The convention, from scoria_csr.rdl: every timing field is a count of cycles to
BLOCK, so a window programmed to N is enforced as N+1 cycles of command
spacing -- the counter is loaded with N on the event and the gate opens the
cycle after it would reach zero. Program the JEDEC value from the datasheet; do
NOT subtract one to compensate.

That convention is the thing this file pins down. A test asserting "at least N"
passes a design that opens one cycle early, which is the direction that
violates the part. So the measurement here is exact: the gap is counted and
compared, not bounded.

Lookahead (the _la_o outputs) is a SEPARATE claim: it reports what will be safe
LA cycles from now, so the arbiter's multi-stage pick can commit early. A
lookahead that is merely equal to the live signal is useless; one that is too
optimistic issues a command into a closed window.
"""

import os
import random

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, sim_build_path

# bank_state_e, scoria_pkg
BANK_IDLE, BANK_ACTIVATING, BANK_ACTIVE = 0, 1, 2


class BtTB(TBBase):
    async def setup(self, *, rcd=4, rp=4, ras=10, rc=14, wr=6, rtp=3):
        await self.start_clock('clk', 10, 'ns')
        d = self.dut
        d.t_rcd_i.value = rcd
        d.t_rp_i.value = rp
        d.t_ras_i.value = ras
        d.t_rc_i.value = rc
        d.t_wr_i.value = wr
        d.t_rtp_i.value = rtp
        for s in ('set_act_i', 'set_rd_i', 'set_wr_i', 'set_pre_i', 'set_ap_i'):
            getattr(d, s).value = 0
        d.row_i.value = 0
        await self.assert_reset()
        await self.wait_clocks('clk', 5)
        await self.deassert_reset()
        await self.wait_clocks('clk', 3)

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1

    async def setup_clocks_and_reset(self):
        await self.setup()

    async def pulse(self, name, *, ap=0, row=0):
        d = self.dut
        if name == 'set_act_i':
            d.row_i.value = row
        d.set_ap_i.value = ap
        getattr(d, name).value = 1
        await RisingEdge(d.clk)
        getattr(d, name).value = 0
        d.set_ap_i.value = 0

    async def gap_until(self, sig, limit=200):
        """Cycles from NOW until `sig` reads high. 0 = already high.

        Counted from immediately after the event pulse, so the returned number
        is the enforced spacing in cycles.
        """
        for i in range(limit):
            if int(getattr(self.dut, sig).value):
                return i
            await RisingEdge(self.dut.clk)
        return None


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_scoria_bank_timer(dut):
    tt = os.environ.get("TEST_TYPE", "trcd_exact")
    tb = BtTB(dut)
    fails = []

    def chk(c, m):
        if not c:
            fails.append(m); tb.log.error(m)

    if tt == "trcd_exact":
        # ACT -> RD spacing must be EXACTLY t_rcd + 1 (the N+1 convention).
        for n in (2, 4, 7):
            await tb.setup(rcd=n)
            await tb.pulse('set_act_i', row=0x21)
            g = await tb.gap_until('safe_rd_o')
            chk(g == n + 1,
                f"t_rcd={n}: ACT->RD gap {g}, expected {n + 1}. The convention "
                f"is N+1 cycles of spacing for a window programmed to N "
                f"(scoria_csr.rdl); asserting N here is off by one in the "
                f"UNSAFE direction and would pass a design that opens early.")

    elif tt == "trcd_never_early":
        # The direction that matters. Opening one cycle early violates the part
        # and a >= assertion would not see it.
        for n in (3, 6):
            await tb.setup(rcd=n)
            await tb.pulse('set_act_i', row=1)
            for i in range(n + 1):
                chk(int(dut.safe_rd_o.value) == 0,
                    f"t_rcd={n}: safe_rd_o high {i} cycles after ACT -- the "
                    f"window is still open, this issues a column command "
                    f"inside tRCD")
                await RisingEdge(dut.clk)
            chk(int(dut.safe_rd_o.value) == 1,
                f"t_rcd={n}: safe_rd_o still low after {n + 1} cycles")

    elif tt == "row_tracking":
        await tb.setup()
        chk(int(dut.row_valid_o.value) == 0, "row_valid set before any ACT")
        await tb.pulse('set_act_i', row=0x1234)
        await tb.wait_clocks('clk', 1)
        chk(int(dut.row_valid_o.value) == 1, "row_valid clear after ACT")
        chk(int(dut.open_row_o.value) == 0x1234,
            f"open_row 0x{int(dut.open_row_o.value):X} != 0x1234")
        await tb.gap_until('safe_pre_o')
        await tb.pulse('set_pre_i')
        await tb.wait_clocks('clk', 1)
        chk(int(dut.row_valid_o.value) == 0, "row_valid still set after PRE")

    elif tt == "state_reflects_window":
        await tb.setup(rcd=5)
        chk(int(dut.state_o.value) == BANK_IDLE,
            f"state {int(dut.state_o.value)} != IDLE at rest")
        await tb.pulse('set_act_i', row=7)
        await tb.wait_clocks('clk', 1)
        chk(int(dut.state_o.value) == BANK_ACTIVATING,
            f"state {int(dut.state_o.value)} != ACTIVATING inside tRCD")
        await tb.gap_until('safe_rd_o')
        chk(int(dut.state_o.value) == BANK_ACTIVE,
            f"state {int(dut.state_o.value)} != ACTIVE after tRCD")

    elif tt == "tras_blocks_precharge":
        # ACT -> PRE must wait tRAS. Precharging early truncates the row.
        for n in (6, 11):
            await tb.setup(ras=n, rcd=2)
            await tb.pulse('set_act_i', row=3)
            g = await tb.gap_until('safe_pre_o')
            chk(g == n + 1, f"t_ras={n}: ACT->PRE gap {g}, expected {n + 1}")

    elif tt == "trp_blocks_activate":
        # PRE -> ACT must wait tRP.
        for n in (3, 5):
            await tb.setup(rp=n, ras=1, rcd=1, rc=1)
            await tb.pulse('set_act_i', row=3)
            await tb.gap_until('safe_pre_o')
            await tb.pulse('set_pre_i')
            g = await tb.gap_until('safe_act_o')
            chk(g == n + 1, f"t_rp={n}: PRE->ACT gap {g}, expected {n + 1}")

    elif tt == "auto_precharge_blocks_columns":
        # An AP-qualified column leaves the bank closing; further columns must
        # be refused until it settles, or they land on a precharging row.
        await tb.setup(rcd=2, wr=5)
        await tb.pulse('set_act_i', row=9)
        await tb.gap_until('safe_rd_o')
        await tb.pulse('set_rd_i', ap=1)
        await tb.wait_clocks('clk', 1)
        chk(int(dut.obs_ap_pending_o.value) == 1,
            "obs_ap_pending clear after an AP-qualified read")
        chk(int(dut.safe_rd_o.value) == 0,
            "safe_rd_o still high with an auto-precharge pending -- a further "
            "column would land on a row that is closing")

    elif tt == "lookahead_is_earlier_not_equal":
        # REQUIRES LA != 0. The module defaults LA=0 and says so: "LA=0
        # collapses every term to its safe_*_o twin". At the default this case
        # asserts something false by construction -- which it did, reporting
        # "lookahead went high at 8, live at 8" against correct RTL. The array
        # instantiates with BANK_LA=4, so the test runs at 4.
        #
        # The lookahead must LEAD the live signal, or the arbiter's early
        # commit buys nothing; and it must not lead by more than LA, or it
        # commits into a window that is still closed.
        await tb.setup(rcd=7)
        await tb.pulse('set_act_i', row=2)
        la = await tb.gap_until('safe_rdwr_la_o')
        await tb.setup(rcd=7)
        await tb.pulse('set_act_i', row=2)
        live = await tb.gap_until('safe_rd_o')
        chk(la is not None and live is not None, "a signal never went high")
        if la is not None and live is not None:
            chk(la < live,
                f"lookahead went high at {la}, live at {live} -- the lookahead "
                f"must LEAD or the arbiter's early commit is pointless")
            chk(live - la <= 4,
                f"lookahead leads by {live - la} cycles; LA is the pick "
                f"pipeline depth (4) and leading by more issues into a window "
                f"that is still closed")

    elif tt == "random_soak":
        rng = random.Random(int(os.environ.get('SEED', '13')))
        lvl = os.environ.get("TEST_LEVEL", "FUNC").upper()
        n = {"GATE": 100, "FUNC": 400, "FULL": 1500}.get(lvl, 400)
        await tb.setup(rcd=3, rp=3, ras=7, rc=10, wr=4, rtp=2)
        for _ in range(n):
            # Only ever issue what the timer says is safe -- the point is that
            # following its advice can never produce an illegal state.
            if int(dut.safe_act_o.value) and rng.random() < 0.4:
                await tb.pulse('set_act_i', row=rng.randrange(1 << 14))
            elif int(dut.safe_rd_o.value) and rng.random() < 0.4:
                await tb.pulse('set_rd_i', ap=rng.randint(0, 1))
            elif int(dut.safe_pre_o.value) and rng.random() < 0.3:
                await tb.pulse('set_pre_i')
            else:
                await RisingEdge(dut.clk)
            chk(int(dut.state_o.value) <= BANK_ACTIVE
                or int(dut.state_o.value) < 8,
                f"illegal bank state {int(dut.state_o.value)}")
            chk(not (int(dut.safe_act_o.value) and int(dut.row_valid_o.value)),
                "safe_act_o high with a row still open -- an ACT on an open "
                "bank loses the row without a precharge")
    else:
        raise ValueError(f"Unknown TEST_TYPE: {tt}")

    await tb.wait_clocks('clk', 3)
    assert not fails, f"{len(fails)} check(s) failed:\n  " + "\n  ".join(fails)


_GATE = ["trcd_exact", "trcd_never_early", "row_tracking"]
_FUNC = _GATE + ["state_reflects_window", "tras_blocks_precharge",
                 "trp_blocks_activate", "auto_precharge_blocks_columns",
                 "lookahead_is_earlier_not_equal", "random_soak"]
_TEST_LEVEL = (os.environ.get("REG_LEVEL") or os.environ.get("TEST_LEVEL")
               or "FUNC").upper()
_PARAMS = {"GATE": _GATE, "FUNC": _FUNC, "FULL": _FUNC}.get(_TEST_LEVEL, _FUNC)


@pytest.mark.parametrize("test_type", _PARAMS)
def test_scoria_bank_timer(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "scoria_bank_timer"
    test_name = f"test_scoria_bank_timer_{test_type}"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=("projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/"
                       "rtl/filelists/fub/scoria_bank_timers.f"))
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    run(python_search=[tests_dir], verilog_sources=verilog_sources,
        includes=includes, toplevel=dut_name, module=module,
        testcase="cocotb_test_scoria_bank_timer",
        sim_build=sim_build, simulator="verilator",
        parameters={"LA": "4"} if test_type == "lookahead_is_earlier_not_equal"
                   else {},
        extra_env={"DUT": dut_name, "TEST_TYPE": test_type,
                   "TEST_LEVEL": _TEST_LEVEL, "COCOTB_LOG_LEVEL": "INFO",
                   "SEED": os.environ.get('SEED', str(random.randint(0, 99999))),
                   "COCOTB_RESULTS_FILE":
                       os.path.join(log_dir, f"results_{test_name}.xml")},
        compile_args=["+define+USE_ASYNC_RESET"],
        keep_files=True, timescale="1ns/1ps")
