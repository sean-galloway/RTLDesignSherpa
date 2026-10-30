# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_chi_hnf_port
# Purpose: chi_hnf_port (CHI HN-F link layer, IHI 0050 Issue H) against the
#          framework CHI requester BFM, with a CHIMonitor on the link
#
# Documentation: docs/markdown/rtl-amba/chi/chi_hnf_port.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-29
"""REG_LEVEL picks the configuration grid (chi_test_common); TEST_LEVEL the
operations per phase. Phases and their claims: bin/TBClasses/chi/chi_hnf_port_tb.py."""
import pytest
import cocotb

from TBClasses.chi.chi_hnf_port_tb import CHIHnfPortTB
from chi_test_common import COUNTS, points_for_level, current_test_level, run_chi


async def run_hnf_phases(tb):
    n = COUNTS[current_test_level()]
    await tb.setup_clocks_and_reset()
    ok = await tb.run_phase('fast', n)
    ok = ok and await tb.run_starve(n)
    ok = ok and await tb.run_phase('gappy', n, link='gappy', fub='fast', snoops=3)
    ok = ok and await tb.run_phase('b2b', n, fub='backtoback', fub_rx='backtoback')
    ok = ok and await tb.run_pool_fill()
    if tb.link_ctrl:
        ok = ok and await tb.run_hold()
        ok = ok and await tb.run_idle_deactivate()
        ok = ok and await tb.run_snoop_wake(2)
        ok = ok and await tb.run_remote_activation()
        ok = ok and await tb.run_phase('reactivate', n // 2 + 1, link='gappy')
        ok = ok and await tb.run_churn(n // 2 + 1)
    else:
        ok = ok and await tb.run_snoops(2)
    await tb.wait_clocks('aclk', 50)
    passed = tb.check_end() and ok
    return tb.verdict('chi_hnf_port', tb.required_counts()) and passed


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def chi_hnf_port_test(dut):
    tb = CHIHnfPortTB(dut)
    assert await run_hnf_phases(tb), f"{len(tb.errors)} error(s); first: {tb.errors[:1]}"


@pytest.mark.parametrize("point, level", points_for_level(), ids=lambda v: getattr(v, 'short_name', lambda: v)())
def test_chi_hnf_port(request, point, level):
    """chi_hnf_port (rtl/amba/chi/chi_hnf_port.sv)."""
    run_chi(request, "chi_hnf_port", point, level)
