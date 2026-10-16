# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_cxs_master_cg
# Purpose: cxs_master_cg: the cxs_master phases with the clock gate enabled,
#          plus the gating claim itself
#
# Documentation: docs/markdown/rtl-amba/cxs/cxs_master_cg.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-15
"""Same traffic as test_cxs_master, every flit still checked, with
cfg_cg_enable=1. The gating claim: with link control the block MUST gate
while the link sits in STOP (idle phase), and with no link control it must
NEVER gate -- a credit can arrive any cycle, and one lost while the clock is
stopped is lost for good."""
import pytest
import cocotb

from TBClasses.cxs.cxs_master_tb import CXSMasterTB
from cxs_test_common import COUNTS, configs_for_level, current_test_level, run_cxs


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cxs_master_cg_test(dut):
    tb = CXSMasterTB(dut, cg=True)
    n = COUNTS[current_test_level()]
    await tb.setup_clocks_and_reset()
    ok = await tb.run_phase('fast', n, 'fast')
    ok = ok and await tb.run_phase('starve', n, 'starve', buffer_depth=min(3, tb.cfg.max_credit))
    tb.rx.buffer_depth = tb.cfg.max_credit
    ok = ok and await tb.run_pool_fill()      # deactivation then has credits to return
    ok = ok and await tb.run_idle_deactivate()
    before = tb.gated_cycles
    await tb.wait_clocks('aclk', 60)          # idle in STOP (or holding credits)
    idle_gated = tb.gated_cycles - before
    ok = ok and await tb.run_phase('wake', n, 'gappy')
    await tb.wait_clocks('aclk', 50)
    passed = tb.check() and ok
    if tb.cfg.link_control and idle_gated == 0:
        tb.errors.append("never gated in STOP")
    if not tb.cfg.link_control and tb.gated_cycles:
        tb.errors.append(f"gated {tb.gated_cycles} cycles with no link control (credits can be lost)")
    tb.log.info(f"gated cycles: {tb.gated_cycles} (idle window {idle_gated})")
    passed = tb.report() and passed
    assert passed, f"{len(tb.errors)} error(s); first: {tb.errors[:1]}"


@pytest.mark.parametrize("cfg, level", configs_for_level(), ids=lambda v: getattr(v, 'short_name', lambda: v)())
def test_cxs_master_cg(request, cfg, level):
    """cxs_master_cg (rtl/amba/cxs/cxs_master_cg.sv)."""
    run_cxs(request, "cxs_master_cg", cfg, level)
