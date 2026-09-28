# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway

"""
Directed unit test for pumice_page_policy's auto-precharge decision.

WHAT THIS USED TO BE. It tested the Axis-2 paging PREDICTORS (modes 5/6/7),
proving mode 5 (adapt_access) voted a single-access row closed via
u_row_pred.close_pred_o -> ap_close_o. Modes 6/7 were retired 2026-09-26 and
modes 4/5 on 2026-09-27, taking pumice_row_pred_table.sv with them, so there is
no predictor left in this block to test.

WHAT IT IS NOW, and why it was not simply deleted. A retired mode encoding is
still WRITABLE -- policy_mode is a 3-bit field and software can put 4..7 in it.
The contract is that those encodings fall through to the BUILD DEFAULT, which
means ap_mode_en_o stays 0 and no bank is auto-precharged. That contract is the
only thing standing between a stale host writing mode 5 and the controller
doing something undefined, and nothing else checks it at this level. So the
mode-0 baseline is kept and the retired encodings are asserted to behave
identically to it.

The live auto-precharge path (mode 2, static_close) is covered here too, so the
test still distinguishes "no AP" from "AP" rather than only asserting absence --
a test that only ever expects 0 cannot tell a correct block from a dead one.
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
from TBClasses.shared.test_levels import level_env, reg_level_grid

_DV_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "../.."))
if _DV_DIR not in sys.path:
    sys.path.insert(0, _DV_DIR)

from tbclasses.pumice_levels import depth as _profile_depth  # noqa: E402

OP_NOP, OP_ACT, OP_RD, OP_WR, OP_PRE = 0x0, 0x1, 0x2, 0x4, 0x6


class PredTB(TBBase):
    CLK = 10

    async def setup(self, mode):
        d = self.dut
        # config: park the timeout path, neutral shapes ("0 = build default")
        d.policy_mode_i.value   = mode
        d.tr_init_i.value       = 0xFF   # long idle timer -> timeout never fires
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
    open_vec = (ROW << (BANK * 14))
    # ACTs per mode before the verdict is read: pure repetition, so it scales
    # with the level. Mode 2 keeps its own literal (2) -- static_close's AP
    # verdict is checked after exactly two, that is the scenario.
    n_acts = _profile_depth('page_policy_acts')
    # The wrapper reads TEST_LEVEL itself, beside its knob: bin/review/check_test_levels.py
    # follows only TBClasses/projects imports, and this area imports tbclasses.* (a
    # hyphenated component path cannot be a package import), so a read hidden inside
    # pumice_levels.depth() would be invisible to the gate. Forced, not chosen (BUG-004).
    dut._log.info("depth: TEST_LEVEL=%s page_policy_acts=%d",
                  os.environ.get("TEST_LEVEL", "gate"), n_acts)

    async def drive_acts(n=n_acts):
        for _ in range(n):
            await tb.cmd(OP_ACT, bank=BANK, row=ROW, active_mask=(1 << BANK),
                         open_row=open_vec)
            await tb.wait_clocks('aclk', 2)

    # ---- mode 0: build default -> NEVER auto-precharge (the baseline) -------
    await tb.setup(mode=0)
    await drive_acts()
    assert int(dut.ap_mode_en_o.value) == 0, \
        "mode 0 asserted ap_mode_en_o -- the build default must not auto-precharge"
    assert tb.ap_active() == 0, "mode 0 produced an auto-precharge verdict"
    dut._log.info("mode 0 (build default): ap_mode_en=0, ap_close=0")

    # ---- mode 2: static_close -> the LIVE auto-precharge path ---------------
    # Present so this test can still tell "no AP" from "AP". Asserting only
    # absence would pass just as happily against a block that had stopped
    # driving ap_close_o at all.
    await tb.setup(mode=2)
    await drive_acts(2)
    assert int(dut.ap_mode_en_o.value) == 1, "mode 2 must enable ap_mode_en_o"
    ap2 = tb.ap_active()
    assert (ap2 >> BANK) & 1, (
        f"mode 2 (static_close) did not auto-precharge: ap_close=0b{ap2:08b}")
    dut._log.info("mode 2 (static_close): ap_close=0b%08b -- AP path is live", ap2)

    # ---- modes 4..7: RETIRED, must fall through to the build default -------
    # 4 adapt_time / 5 adapt_access retired 2026-09-27 (TASK-014); 6 rbl_static
    # / 7 rbl_dyn retired 2026-09-26 (TASK-011). Software can still write these
    # encodings, so the fallthrough is a real contract, not a formality.
    for mode in (4, 5, 6, 7):
        await tb.setup(mode=mode)
        await drive_acts()
        assert int(dut.ap_mode_en_o.value) == 0, (
            f"RETIRED mode {mode} asserted ap_mode_en_o -- it must fall through "
            f"to the build default, which never auto-precharges")
        ap = tb.ap_active()
        assert ap == 0, (
            f"RETIRED mode {mode} produced an auto-precharge verdict "
            f"ap_close=0b{ap:08b} -- it must behave exactly as mode 0")
    dut._log.info("modes 4,5,6,7 (RETIRED): all fall through to the build "
                  "default -- ap_mode_en=0, ap_close=0")
    dut._log.info("PASS: build default and retired encodings never auto-precharge; "
                  "static_close does")


@pytest.mark.parametrize("test_type", ["directed"])
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_page_predictor(request, test_type, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dut_name = "pumice_page_policy"
    test_name = f"test_page_predictor_{test_type}_{test_level}"

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
        **level_env(test_level),
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
