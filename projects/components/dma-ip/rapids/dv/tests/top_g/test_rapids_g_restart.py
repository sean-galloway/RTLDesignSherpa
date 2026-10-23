# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_rapids_g_restart
# Purpose: rapids-g (rapids TASK-034): a seq_restart pulse puts both gatlings
#          at the same phase whatever the clocks since reset.
#
# Author: sean galloway
# Created: 2026-10-22

"""seq_restart on rapids_g_top: the harts' timing after a restart is fixed.

Free running, the firmware's poll loop is wherever the clocks since reset put
it, so the same descriptors land at a different phase in simulation and on the
board (the UART sets how long the host takes to reach GO) and a small transfer
can take a different time. The board harness pulses seq_restart on GO to remove
that.

The test pulses seq_restart twice, at two moments whose distance is not a
multiple of the barrel's rotation, and records every cycle after each pulse:
both gatlings' rotation (sel_q) and every hart's PC. The two traces must be
identical, and the harts must be running the firmware (several PCs, not held
at reset). Without the restart the rotation alone would differ.
"""

import os
import sys
from pathlib import Path

import cocotb
import pytest

from TBClasses.shared.test_levels import reg_level_grid

from rapids_g_rehost import make_runner

REPO = os.environ.get('REPO_ROOT', str(Path(__file__).resolve().parents[7]))
sys.path.insert(0, REPO)

from projects.components.dma_ip.rapids.dv.tbclasses.rapids_top_tb import RapidsTopTB  # noqa: E402

FIRST_GAP = 1000        # clocks from reset to the first pulse
SECOND_GAP = 1002       # clocks from the end of the first trace to the second pulse
TRACE = 300             # clocks recorded after each pulse
ROTATIONS = (4, 8)      # the barrel's rotation at either hart count


def _gatling(dut, half):
    return getattr(dut.u_base.u_core, f"u_{half}").u_scheduler_group_array.g_shared.u_seq.u_gatling


async def _pulse_and_trace(tb, dut):
    dut.seq_restart.value = 1
    await tb.wait_clocks(tb.clk_name, 1)
    dut.seq_restart.value = 0
    trace = []
    for _ in range(TRACE):
        await tb.wait_clocks(tb.clk_name, 1)
        trace.append(tuple((int(_gatling(dut, h).sel_q.value), int(_gatling(dut, h).pc_q.value))
                           for h in ('src', 'snk')))
    return trace


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def cocotb_test_restart(dut):
    # the two pulses must sit at different rotation phases, or the test
    # could not tell a restart from none
    assert all((1 + TRACE + SECOND_GAP) % r for r in ROTATIONS), "pick SECOND_GAP so the pulses differ in phase"
    tb = RapidsTopTB(dut)
    dut.seq_restart.value = 0
    await tb.start_clock(tb.clk_name, freq=tb.CLK_PERIOD, units='ns')
    await tb.assert_reset()
    await tb.wait_clocks(tb.clk_name, 10)
    await tb.deassert_reset()

    await tb.wait_clocks(tb.clk_name, FIRST_GAP)
    first = await _pulse_and_trace(tb, dut)
    await tb.wait_clocks(tb.clk_name, SECOND_GAP)
    second = await _pulse_and_trace(tb, dut)

    pcs = {pc for cyc in first for _, pc in cyc}
    tb.log.info(f"{len(pcs)} distinct PC vectors in {TRACE} clocks after a restart")
    assert len(pcs) > 4, "the harts did not run after the restart"
    diff = [i for i, (a, b) in enumerate(zip(first, second)) if a != b]
    if diff:
        i = diff[0]
        tb.log.error(f"{len(diff)}/{TRACE} cycles differ; first at +{i}: {first[i]} vs {second[i]}")
    assert not diff, "the gatlings' timing after a restart depends on when it came"


_run_top = make_runner('test_rapids_g_restart', {
    'DATA_WIDTH': 512, 'ADDR_WIDTH': 64, 'AXI_ID_WIDTH': 8, 'SRAM_DEPTH': 512,
    'APB_ADDR_WIDTH': 13, 'APB_DATA_WIDTH': 32,
})


@pytest.mark.top
@pytest.mark.rapids_g
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_rapids_g_restart(request, test_level):
    """A seq_restart pulse gives both gatlings the same timing whenever it comes."""
    _run_top("cocotb_test_restart", "test_rapids_restart", test_level=test_level, dut='rapids_top')
