# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_cxs_slave_monlite
# Purpose: cxs_slave_monlite -- the CXS slave endpoint with cxs_monitor_lite
#          tapping it (amba TASK-044)
#
# Documentation: docs/markdown/rtl-amba/monitor/cxs_monitor_lite.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-15
"""The cxs_slave endpoint traffic and scoreboard, plus a MonbusSlave on the
ocelus bus judging every packet class (bin/TBClasses/cxs/cxs_monlite_tb.py).
REG_LEVEL picks the configuration grid shared with the endpoint tests
(val/amba/cxs_test_common.py); TEST_LEVEL the traffic per phase."""
import os
import sys

import pytest
import cocotb

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # val/amba
from cxs_test_common import configs_for_level, run_cxs  # noqa: E402
from TBClasses.cxs.cxs_monlite_tb import CXSSlaveMonliteTB  # noqa: E402


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cxs_slave_monlite_test(dut):
    tb = CXSSlaveMonliteTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_monlite_suite()
    errs = tb.errors + tb.mon_errors
    assert ok, f"{len(errs)} error(s); first: {errs[:2]}"


@pytest.mark.parametrize("cfg, level", configs_for_level(),
                         ids=lambda v: getattr(v, 'short_name', lambda: v)())
def test_cxs_slave_monlite(request, cfg, level):
    """cxs_slave_monlite (rtl/amba/cxs/cxs_slave_monlite.sv)."""
    run_cxs(request, "cxs_slave_monlite", cfg, level, {'ACLK_MHZ': 100})
