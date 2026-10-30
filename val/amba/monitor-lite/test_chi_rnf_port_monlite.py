# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_chi_rnf_port_monlite
# Purpose: chi_rnf_port_monlite -- the CHI RNF port with chi_monitor_lite tapping it
#
# Documentation: docs/markdown/rtl-amba/monitor/chi_monitor_lite.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-30
"""The rnf port traffic of val/amba/test_chi_rnf_port.py, plus a MonbusSlave judging
every packet class against the spec-level model (bin/TBClasses/chi/chi_monlite_tb.py).
REG_LEVEL picks the configuration grid (chi_test_common.MONLITE_EXTRAS adds the
table sizes); TEST_LEVEL the operations per phase."""
import os
import sys

import cocotb
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # val/amba
from chi_test_common import monlite_points_for_level, run_chi
from TBClasses.chi.chi_monlite_tb import CHIRnfMonliteTB


@cocotb.test(timeout_time=400, timeout_unit="ms")
async def chi_rnf_port_monlite_test(dut):
    tb = CHIRnfMonliteTB(dut)
    await tb.setup_clocks_and_reset()
    ok = await tb.run_monlite_suite()
    errs = tb.errors + tb.mon_errors
    assert ok, f"{len(errs)} error(s); first: {errs[:2]}"


@pytest.mark.parametrize("point, level, extra, tag", monlite_points_for_level(),
                         ids=lambda v: v.short_name() if hasattr(v, 'short_name') else (v if isinstance(v, str) and v.startswith('_n') else None))
def test_chi_rnf_port_monlite(request, point, level, extra, tag):
    """chi_rnf_port_monlite (rtl/amba/chi/chi_rnf_port_monlite.sv)."""
    run_chi(request, "chi_rnf_port_monlite", point, level, extra, tag)
