# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_cxs_slave_cg
# Purpose: cxs_slave_cg: the cxs_slave phases with the clock gate enabled,
#          plus the gating claim itself
#
# Documentation: docs/markdown/rtl-amba/cxs/cxs_slave_cg.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-15
"""With link control the receiver MUST gate in STOP and a rising
CXSACTIVEREQ must wake it (IHI 0079D 5.5) -- the 'wake' phase after the idle
window proves it, every flit checked. With no link control it must NEVER
gate: a flit can arrive on any cycle."""
import os

import pytest
import cocotb

from TBClasses.cxs.cxs_slave_tb import CXSSlaveTB
from cxs_test_common import COUNTS, configs_for_level, current_test_level, run_cxs


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cxs_slave_cg_test(dut):
    tb = CXSSlaveTB(dut, cg=True, rx_fifo_depth=int(os.environ['RX_FIFO_DEPTH']))
    n = COUNTS[current_test_level()]
    await tb.setup_clocks_and_reset()
    ok = await tb.run_phase('stream', n)
    ok = ok and await tb.run_phase('backpressure', n, fub_profile='slow_producer')
    ok = ok and await tb.run_idle_deactivate()
    before = tb.gated_cycles
    await tb.wait_clocks('aclk', 60)
    idle_gated = tb.gated_cycles - before
    ok = ok and await tb.run_phase('wake', n, tx_profile='gappy')
    await tb.wait_clocks('aclk', 50)
    passed = tb.check() and ok
    if tb.cfg.link_control and idle_gated == 0:
        tb.errors.append("never gated in STOP")
    if not tb.cfg.link_control and tb.gated_cycles:
        tb.errors.append(f"gated {tb.gated_cycles} cycles with no link control (flits can be lost)")
    tb.log.info(f"gated cycles: {tb.gated_cycles} (idle window {idle_gated})")
    passed = tb.report() and passed
    assert passed, f"{len(tb.errors)} error(s); first: {tb.errors[:1]}"


@pytest.mark.parametrize("cfg, level", configs_for_level(), ids=lambda v: getattr(v, 'short_name', lambda: v)())
def test_cxs_slave_cg(request, cfg, level):
    """cxs_slave_cg (rtl/amba/cxs/cxs_slave_cg.sv)."""
    run_cxs(request, "cxs_slave_cg", cfg, level, {'RX_FIFO_DEPTH': cfg.max_credit})
