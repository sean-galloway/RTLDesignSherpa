# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gatling_rv32ui
# Purpose: The riscv-tests rv32ui-p-* battery on all four gatling contexts at
#          once: four different images side by side each round, rotated until
#          every context has run every image; spike + golden lockstep per
#          context at func level.
#
# Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32itetrad
#
# Created: 2026-10-21

"""gatling rv32ui battery (PRD 6: "rv32ui battery is the gate").

gate: the simple/add/addi smoke images, each on every context.  func: all
42 images x 4 contexts with kestrel's golden interpreter full-field diff and
the spike (pc, insn) lockstep on every (context, image).  full: all 42 x 4
without lockstep.  Every level also checks the barrel: each context retires
exactly once per four-cycle window.
"""

import os
from pathlib import Path

import cocotb
import pytest

import gatling_sim
from TBClasses.shared.test_levels import reg_level_grid

from gatling.gatling_battery import GatlingBattery          # noqa: E402
from tbclasses.kestrel.rv32ui_battery import LINK_BASE      # noqa: E402


@cocotb.test(timeout_time=60_000, timeout_unit="ms")
async def cocotb_test_gatling_rv32ui_battery(dut):
    """All rv32ui-p images on all four contexts, four different at a time."""
    level = os.environ.get("TEST_LEVEL", "func")
    log_dir = os.path.dirname(os.environ.get("LOG_PATH", "."))
    battery = GatlingBattery(dut, repo_root=os.environ["REPO_ROOT"], level=level,
                             work_dir=os.path.join(log_dir, "gatling_rv32ui_battery"))
    await battery.run()


@pytest.mark.parametrize("test_level, description",
                         [(lvl, f"gatling_rv32ui {lvl}") for lvl in reg_level_grid()])
def test_gatling_rv32ui(request, test_level, description):
    gatling_sim.run_cell(
        module="test_gatling_rv32ui", testcase="cocotb_test_gatling_rv32ui_battery",
        toplevel="gatling_tb_top", filelist=gatling_sim.TB_FILELIST,
        cell=f"test_gatling_rv32ui_{test_level}", test_level=test_level,
        parameters={"RESET_ADDR": str(LINK_BASE)})
