# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_cxs_master
# Purpose: cxs_master (CXS transmitter, IHI 0079 Issues A-D) against the
#          framework CXSReceiver, with a CXSMonitor on the link
#
# Documentation: docs/markdown/rtl-amba/cxs/cxs_master.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-15
"""REG_LEVEL picks the configuration grid (cxs_test_common); TEST_LEVEL the
packets per phase. Phases and their claims: bin/TBClasses/cxs/cxs_master_tb.py."""
import pytest
import cocotb

from TBClasses.cxs.cxs_master_tb import CXSMasterTB
from cxs_test_common import COUNTS, configs_for_level, current_test_level, run_cxs


async def run_master_phases(tb):
    n = COUNTS[current_test_level()]
    cfg = tb.cfg
    await tb.setup_clocks_and_reset()
    ok = await tb.run_phase('fast', n, 'fast')
    ok = ok and await tb.run_phase('starve', n, 'starve', buffer_depth=min(3, cfg.max_credit))
    ok = ok and await tb.run_phase('gappy', n, 'gappy', fub_profile='fast')
    ok = ok and await tb.run_phase('b2b', n, 'fast', fub_profile='backtoback')
    tb.rx.buffer_depth = cfg.max_credit
    ok = ok and await tb.run_pool_fill()
    ok = ok and await tb.run_idle_deactivate()
    ok = ok and await tb.run_phase('reactivate', n // 2 + 1, 'gappy')
    ok = ok and await tb.run_hint_deactivate()
    ok = ok and await tb.run_phase('after-hint', n // 2 + 1, 'fast')
    ok = ok and await tb.run_midpacket_idle(n // 2 + 1)
    await tb.wait_clocks('aclk', 50)
    passed = tb.check()
    # parity last: it sets the sticky flag on purpose
    passed = await tb.run_parity_injection() and passed and ok
    tb.report()
    return passed


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cxs_master_test(dut):
    tb = CXSMasterTB(dut)
    assert await run_master_phases(tb), f"{len(tb.errors)} error(s); first: {tb.errors[:1]}"


@pytest.mark.parametrize("cfg, level", configs_for_level(), ids=lambda v: getattr(v, 'short_name', lambda: v)())
def test_cxs_master(request, cfg, level):
    """cxs_master (rtl/amba/cxs/cxs_master.sv)."""
    run_cxs(request, "cxs_master", cfg, level)
