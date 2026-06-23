# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Smoke test for command_scheduler_macro.

command_scheduler_macro = scheduler + page_predictor + xbank_timers +
global_timers + refresh_ctrl + powerdown_ctrl + mode_register +
init_sequencer. The FUB-level unit tests cover each in detail; this
macro-level test verifies the wiring between them:

  init_walks_through : after reset, dfi_init_start_o asserts, then
                       dfi_init_complete_i + zqcl mock are exercised,
                       init_busy_o eventually deasserts.
  smoke_wr_cmd       : with init done, drive a wr CAM match + bank
                       readys → scheduler issues CMD_ACT followed by
                       CMD_WRA (closed-page default).

This is a skeleton. Full integration tests (refresh, MR programming,
multi-bank arbitration) come later.
"""

import os
import sys
import random
import logging
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

_NBA_SETTLE_PS = 1

OP_NOP = 0x0
OP_ACT = 0x1
OP_RDA = 0x3
OP_WRA = 0x5
OP_MRS = 0xA


class CommandSchedulerMacroTB(TBBase):
    CLK = 10

    def __init__(self, dut):
        super().__init__(dut)
        self.SEED = int(os.environ.get('SEED', '12345'))
        random.seed(self.SEED)
        self.NUM_RANKS = int(os.environ.get('NUM_RANKS', '1'))
        self.NUM_BANKS = int(os.environ.get('NUM_BANKS', '8'))
        self.WR_CAM_DEPTH = int(os.environ.get('WR_CAM_DEPTH', '16'))
        self.RD_CAM_DEPTH = int(os.environ.get('RD_CAM_DEPTH', '16'))

    async def setup(self):
        self.dut.memtype_i.value         = 0   # MEMTYPE_DDR2
        self.dut.t_refi_i.value          = 1000
        self.dut.t_rcd_i.value           = 4
        self.dut.t_rp_i.value            = 4
        self.dut.t_ras_i.value           = 8
        self.dut.t_rc_i.value            = 12
        self.dut.t_wr_i.value            = 3
        self.dut.t_wtr_i.value           = 2
        self.dut.t_rtp_i.value           = 2
        self.dut.t_faw_i.value           = 16
        self.dut.t_rrd_i.value           = 4
        self.dut.idle_threshold_i.value  = 1000
        self.dut.enable_pde_i.value      = 0
        self.dut.enable_sref_i.value     = 0

        self.dut.mr_we_i.value           = 0
        self.dut.mr_index_i.value        = 0
        self.dut.mr_data_i.value         = 0
        self.dut.mr_rank_i.value         = 0

        self.dut.wr_match_pending_i.value = 0
        self.dut.wr_match_rowhit_i.value  = 0
        self.dut.rd_match_pending_i.value = 0
        self.dut.rd_match_rowhit_i.value  = 0

        self.dut.wr_snap_rank_i.value = 0
        self.dut.wr_snap_bank_i.value = 0
        self.dut.wr_snap_row_i.value  = 0
        self.dut.wr_snap_col_i.value  = 0
        self.dut.wr_snap_len_i.value  = 0
        self.dut.rd_snap_rank_i.value = 0
        self.dut.rd_snap_bank_i.value = 0
        self.dut.rd_snap_row_i.value  = 0
        self.dut.rd_snap_col_i.value  = 0
        self.dut.rd_snap_len_i.value  = 0

        self.dut.cmd_ready_i.value         = 1
        self.dut.dfi_init_complete_i.value = 0

        await self.start_clock('mc_clk', freq=self.CLK, units='ns')
        self.dut.mc_rst_n.value = 0
        await self.wait_clocks('mc_clk', 5)
        self.dut.mc_rst_n.value = 1
        await self.wait_clocks('mc_clk', 5)

    async def wait_init_done(self, timeout_cycles=200):
        """Walk through the init handshake: dfi_init_start → complete →
        MR writes → ZQCL grant → init_busy_o deasserts."""
        # Phase 1: wait for dfi_init_start_o.
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if int(self.dut.dfi_init_start_o.value):
                break
        # Phase 2: pulse dfi_init_complete_i.
        self.dut.dfi_init_complete_i.value = 1
        # Phase 3: let the MR sequencer run, then init_busy_o drops.
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if int(self.dut.controller_idle_o.value):
                # init complete → scheduler idle
                return True
        return False


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_command_scheduler_macro(dut):
    test_type = os.environ.get("TEST_TYPE", "init_walks_through")
    tb = CommandSchedulerMacroTB(dut)

    if test_type == "init_walks_through":
        await tb.setup()
        init_done = await tb.wait_init_done()
        assert init_done, "init_busy_o never deasserted within timeout"

    elif test_type == "smoke_wr_cmd":
        await tb.setup()
        ok = await tb.wait_init_done()
        assert ok, "init didn't complete"

        # Drive a wr CAM match in slot 3, row 0x100, col 0x40, len 4.
        slot = 3
        WSL = max(1, (tb.WR_CAM_DEPTH - 1).bit_length())
        BKW = (tb.NUM_BANKS - 1).bit_length() or 1
        COL_WIDTH = 10
        BLW = 8
        ROW_WIDTH = 14

        # match_pending bit for slot 3
        tb.dut.wr_match_pending_i.value = (1 << slot)
        # Snapshot for that slot: rank 0, bank 2, row 0x100, col 0x40, len 4
        tb.dut.wr_snap_bank_i.value = (2 << (slot * BKW))
        tb.dut.wr_snap_row_i.value  = (0x100 << (slot * ROW_WIDTH))
        tb.dut.wr_snap_col_i.value  = (0x40 << (slot * COL_WIDTH))
        tb.dut.wr_snap_len_i.value  = (4   << (slot * BLW))

        # Observe scheduler output for CMD_ACT then CMD_WRA.
        saw_act = False
        saw_wra = False
        for _ in range(200):
            await RisingEdge(tb.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if int(tb.dut.cmd_valid_o.value):
                op = int(tb.dut.cmd_op_o.value)
                if op == OP_ACT:
                    saw_act = True
                if op == OP_WRA and saw_act:
                    saw_wra = True
                    break
        assert saw_act,  "scheduler never issued OP_ACT"
        assert saw_wra,  "scheduler never followed up with OP_WRA"

    elif test_type == "no_double_issue_race":
        # REGRESSION test for the scheduler S_DONE re-issue bug
        # (commit 66f32c7f). The scheduler used to fire wr_issued_we_o
        # from S_DONE while transitioning to S_IDLE the same cycle.
        # Because the strobe is strict-flopped, the consuming CAM saw
        # it ONE cycle after the FSM was back in S_IDLE. If the test
        # holds wr_match_pending_i high for ONE EXTRA cycle (modeling
        # the CAM's r_issued register lag), the buggy scheduler
        # re-picks the slot and fires wr_issued_we_o a second time.
        #
        # This test simulates that exact CAM-lag pattern: drop
        # wr_match_pending one mc_clk AFTER observing wr_issued_we_o,
        # and count pulses. Exactly 1 → fix is in place; 2+ → race
        # regressed.
        await tb.setup()
        ok = await tb.wait_init_done()
        assert ok, "init didn't complete"

        slot = 1
        BKW = (tb.NUM_BANKS - 1).bit_length() or 1
        COL_WIDTH = 10
        BLW = 8
        ROW_WIDTH = 14

        # Drive a pending wr slot. snap values for bank 1 row 0 col 0 len 1.
        match_bits = (1 << slot)
        tb.dut.wr_match_pending_i.value = match_bits
        tb.dut.wr_snap_bank_i.value = (1 << (slot * BKW))
        tb.dut.wr_snap_row_i.value  = (0 << (slot * ROW_WIDTH))
        tb.dut.wr_snap_col_i.value  = (0 << (slot * COL_WIDTH))
        tb.dut.wr_snap_len_i.value  = (1 << (slot * BLW))

        # Walk the FSM through ACT+WR and watch issued_we. Once we see
        # wr_issued_we_o = 1, wait ONE mc_clk before dropping
        # wr_match_pending — this models the CAM's r_issued register lag.
        pulses = 0
        cleared = False
        for _ in range(400):
            await RisingEdge(tb.dut.mc_clk)
            await Timer(_NBA_SETTLE_PS, units='ps')
            if int(tb.dut.wr_issued_we_o.value):
                pulses += 1
                if not cleared:
                    # ONE cycle of CAM lag, then drop pending.
                    await RisingEdge(tb.dut.mc_clk)
                    tb.dut.wr_match_pending_i.value = 0
                    cleared = True
        assert pulses == 1, (
            f"wr_issued_we_o pulsed {pulses} times with 1-cycle CAM lag; "
            "expected exactly 1 (S_DONE re-issue race regressed). "
            "See scheduler.sv comment on S_NEED_RDWR / S_DONE issued_we "
            "placement."
        )

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    await tb.wait_clocks('mc_clk', 5)


_SCENARIOS = ["init_walks_through", "smoke_wr_cmd", "no_double_issue_race"]


@pytest.mark.parametrize("test_type", _SCENARIOS, ids=_SCENARIOS)
def test_command_scheduler_macro(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "command_scheduler_macro"
    test_name = f"test_command_scheduler_macro_{test_type}"

    filelist_path = ("projects/components/memory-controllers/ddr2-lpddr2/"
                     "rtl/filelists/macro/command_scheduler_macro.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = os.path.join(tests_dir, "local_sim_build", test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "NUM_RANKS":   "1",
        "NUM_BANKS":   "8",
        "WR_CAM_DEPTH": "16",
        "RD_CAM_DEPTH": "16",
        "SEED":         str(random.randint(0, 100000)),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }

    compile_args = ["+define+USE_ASYNC_RESET"]
    sim_args = []
    plus_args = []
    enable_waves = bool(int(os.environ.get("WAVES", "0")))
    if enable_waves:
        compile_args += ["--trace-fst", "--trace-structs", "--trace-depth", "99"]
        sim_args     += ["--trace", "--trace-structs", "--trace-depth", "99"]
        plus_args    += ["--trace"]

    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module=module,
        testcase="cocotb_test_command_scheduler_macro",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, sim_args=sim_args, plus_args=plus_args,
        waves=enable_waves, keep_files=True, timescale="1ns/1ps")
