# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Directed unit test for the Axis-2 paging PREDICTORS behind pumice_page_policy
(PUMICE-006 modes 5/6/7). It proves each predictor mode produces a DISTINCT
per-bank auto-precharge verdict versus the default policy:

  * mode 0 (build_default): ap_mode_en_o stays 0 -- no auto-precharge, whatever
    the command stream (this is the RED baseline the predictors must beat).
  * mode 6 (rbl_static): hammering ACTs at ONE row drives the miss counter past
    the threshold -> u_rbl.low_locality_o -> ap_close_o asserts (GREEN).
  * mode 5 (adapt_access): a row that sees <=1 column per activation is voted
    closed after a few ACT/PRE cycles -> u_row_pred.close_pred_o -> ap_close_o
    asserts (GREEN).

The verdict flops are latched at ACT time (rbl is pipelined +1 cycle, PUMICE-017)
and held while the row is open, so the checks settle a few cycles after the ACT.
Assertions use only the top ports, so no --public access is required.
"""

import os
import sys
import pytest

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.tbbase import TBBase

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

OP_NOP, OP_ACT, OP_RD, OP_WR, OP_PRE = 0x0, 0x1, 0x2, 0x4, 0x6


class PredTB(TBBase):
    CLK = 10

    async def setup(self, mode):
        d = self.dut
        # config: park the timeout path, neutral shapes ("0 = build default")
        d.policy_mode_i.value   = mode
        d.policy_scope_i.value  = 0
        d.ctr_thresh_i.value    = 2      # mode 5: close when counter >= 2
        d.ctr_init_i.value      = 1      # weak-open init
        d.tr_init_i.value       = 0xFF   # long idle timer -> timeout never fires
        d.tr_min_i.value        = 0xFF
        d.tr_max_i.value        = 0xFF
        d.tr_step_i.value       = 0
        d.mc_high_thr_i.value   = 0
        d.mc_low_thr_i.value    = 0
        d.mc_init_i.value       = 0
        d.check_interval_i.value = 0xFFFF
        d.rbl_miss_thresh_i.value = 2    # mode 6: low-locality when cnt > 2
        d.rbl_ways_i.value      = 0
        d.rbl_sets_i.value      = 0
        d.rbl_reset_ivl_i.value = 0      # no epoch -> counters never auto-clear
        d.cmd_valid_i.value     = 0
        d.cmd_op_i.value        = OP_NOP
        d.cmd_bank_i.value      = 0
        d.cmd_row_i.value       = 0
        d.bank_row_active_i.value = 0
        d.bank_open_row_i.value   = 0
        await self.start_clock('aclk', freq=self.CLK, units='ns')
        d.aresetn.value = 0
        await self.wait_clocks('aclk', 5)
        d.aresetn.value = 1
        await self.wait_clocks('aclk', 5)

    async def cmd(self, op, bank=0, row=0, active_mask=None, open_row=None):
        """Drive one command for a single cycle; optionally set bank state."""
        d = self.dut
        if active_mask is not None:
            d.bank_row_active_i.value = active_mask
        if open_row is not None:
            d.bank_open_row_i.value = open_row
        d.cmd_valid_i.value = 1
        d.cmd_op_i.value    = op
        d.cmd_bank_i.value  = bank
        d.cmd_row_i.value   = row
        await RisingEdge(d.aclk)
        await Timer(1, units='ps')
        d.cmd_valid_i.value = 0
        d.cmd_op_i.value    = OP_NOP

    def ap_active(self) -> int:
        """Effective per-bank auto-precharge mask (0 when the mode is off)."""
        if int(self.dut.ap_mode_en_o.value) == 0:
            return 0
        return int(self.dut.ap_close_o.value)


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_page_predictor(dut):
    tb = PredTB(dut)
    ROW = 0x1234
    BANK = 3

    # ---- mode 0: default -> NEVER auto-precharge (RED baseline) -------------
    await tb.setup(mode=0)
    for _ in range(8):
        await tb.cmd(OP_ACT, bank=BANK, row=ROW, active_mask=(1 << BANK),
                     open_row=(ROW << (BANK * 14)))
        await tb.wait_clocks('aclk', 2)
    assert int(dut.ap_mode_en_o.value) == 0, \
        "mode 0 asserted ap_mode_en_o -- default must not auto-precharge"
    assert tb.ap_active() == 0, "mode 0 produced an auto-precharge verdict"
    dut._log.info("mode 0: ap_mode_en=0, ap_close=0 (RED baseline confirmed)")

    # ---- mode 6: rbl_static -> hammer one row past the miss threshold ------
    await tb.setup(mode=6)
    assert int(dut.ap_mode_en_o.value) == 1, "mode 6 must enable ap_mode_en_o"
    for _ in range(6):
        await tb.cmd(OP_ACT, bank=BANK, row=ROW, active_mask=(1 << BANK),
                     open_row=(ROW << (BANK * 14)))
        await tb.wait_clocks('aclk', 2)
    await tb.wait_clocks('aclk', 4)
    ap6 = tb.ap_active()
    assert (ap6 >> BANK) & 1, (
        f"mode 6 (rbl_static) did not auto-precharge the hammered bank: "
        f"ap_close=0b{ap6:08b} (expected bit {BANK} set)")
    dut._log.info(f"mode 6: ap_close=0b{ap6:08b} bit {BANK} SET (GREEN)")

    # ---- mode 5: adapt_access -> a single-access row is voted closed -------
    await tb.setup(mode=5)
    assert int(dut.ap_mode_en_o.value) == 1, "mode 5 must enable ap_mode_en_o"
    open_vec = (ROW << (BANK * 14))
    for _ in range(4):
        # ACT the row, serve ZERO columns, then explicit PRE -> close-friendly
        await tb.cmd(OP_ACT, bank=BANK, row=ROW, active_mask=(1 << BANK),
                     open_row=open_vec)
        await tb.wait_clocks('aclk', 1)
        await tb.cmd(OP_PRE, bank=BANK, row=ROW, active_mask=0, open_row=open_vec)
        await tb.wait_clocks('aclk', 2)
    # final ACT: verdict latches from the learned (close-voting) counter
    await tb.cmd(OP_ACT, bank=BANK, row=ROW, active_mask=(1 << BANK),
                 open_row=open_vec)
    await tb.wait_clocks('aclk', 3)
    ap5 = tb.ap_active()
    assert (ap5 >> BANK) & 1, (
        f"mode 5 (adapt_access) did not auto-precharge the single-access row: "
        f"ap_close=0b{ap5:08b} (expected bit {BANK} set)")
    dut._log.info(f"mode 5: ap_close=0b{ap5:08b} bit {BANK} SET (GREEN)")
    dut._log.info("PASS: predictors produce DISTINCT per-bank auto-precharge "
                  "(mode 0 none; modes 5 and 6 close the target bank)")


@pytest.mark.parametrize("test_type", ["directed"])
def test_page_predictor(request, test_type):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_page_policy"
    test_name = f"test_page_predictor_{test_type}"

    filelist_path = ("projects/components/memory-controllers/pumice-ddr2-lpddr2/"
                     "rtl/filelists/fub/pumice_page_policy.f")
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist_path)

    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    extra_env = {
        "DUT": dut_name,
        "TEST_TYPE": test_type,
        "SEED": os.environ.get('SEED', "1"),
        "COCOTB_LOG_LEVEL": "INFO",
        "COCOTB_RESULTS_FILE":
            os.path.join(log_dir, f"results_{test_name}.xml"),
    }

    compile_args = ["+define+USE_ASYNC_RESET"]
    run(python_search=[tests_dir],
        verilog_sources=verilog_sources, includes=includes,
        toplevel=dut_name, module="test_page_predictor",
        testcase="cocotb_test_page_predictor",
        sim_build=sim_build, simulator="verilator",
        extra_env=extra_env,
        compile_args=compile_args, waves=False, keep_files=True,
        timescale="1ns/1ps")
