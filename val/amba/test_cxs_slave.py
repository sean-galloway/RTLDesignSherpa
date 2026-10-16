# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_cxs_slave
# Purpose: cxs_slave (CXS receiver, IHI 0079 Issues A-D) against the
#          framework CXSTransmitter, with a CXSMonitor on the link
#
# Documentation: docs/markdown/rtl-amba/cxs/cxs_slave.md
# Subsystem: amba
# Author: sean galloway
# Created: 2026-10-15
"""REG_LEVEL picks the configuration grid (cxs_test_common), each also run
with a receive FIFO smaller than CXS_MAX_CREDIT (the FIFO, not the property,
then bounds the credit pool); TEST_LEVEL the packets per phase. Phases and
their claims: bin/TBClasses/cxs/cxs_slave_tb.py."""
import os

import pytest
import cocotb

from TBClasses.cxs.cxs_slave_tb import CXSSlaveTB
from cxs_test_common import COUNTS, configs_for_level, current_test_level, run_cxs


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cxs_slave_test(dut):
    tb = CXSSlaveTB(dut, rx_fifo_depth=int(os.environ['RX_FIFO_DEPTH']))
    n = COUNTS[current_test_level()]
    await tb.setup_clocks_and_reset()
    ok = await tb.run_phase('stream', n)
    ok = ok and await tb.run_phase('backpressure', n, fub_profile='slow_producer')
    ok = ok and await tb.run_phase('gappy', n, tx_profile='gappy', fub_profile='constrained')
    ok = ok and await tb.run_pool_fill()
    ok = ok and await tb.run_idle_deactivate()
    ok = ok and await tb.run_phase('reactivate', n // 2 + 1)
    ok = ok and await tb.run_hint_deactivate()
    ok = ok and await tb.run_phase('after-hint', n // 2 + 1, fub_profile='fast')
    await tb.wait_clocks('aclk', 50)
    passed = tb.check() and ok
    passed = await tb.run_parity_injection() and passed
    passed = tb.report() and passed
    assert passed, f"{len(tb.errors)} error(s); first: {tb.errors[:1]}"


def _params():
    out = []
    for cfg, level in configs_for_level():
        out.append((cfg, level, cfg.max_credit))
        if cfg.max_credit > 3:
            out.append((cfg, level, 3))         # FIFO smaller than the credit property
    return out


@pytest.mark.parametrize("cfg, level, depth", _params(),
                         ids=lambda v: getattr(v, 'short_name', lambda: str(v))())
def test_cxs_slave(request, cfg, level, depth):
    """cxs_slave (rtl/amba/cxs/cxs_slave.sv)."""
    run_cxs(request, "cxs_slave", cfg, level, {'RX_FIFO_DEPTH': depth}, tag_extra=f"_fd{depth}")
