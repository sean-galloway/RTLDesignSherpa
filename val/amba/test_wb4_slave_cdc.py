# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""wb4_slave_cdc: the wb4_slave phases (traffic, abort, post-abort) with the
Wishbone BFMs on wb_clk and the queue BFMs on aclk, at several clock ratios
in both directions."""
import os
import random
from itertools import product

import pytest
import cocotb
from TBClasses.amba.wb4_slave_tb import WB4SlaveTB
from wb4_test_common import SLAVE_PHASES as PHASES, COUNTS, run_wb4


@cocotb.test(timeout_time=60, timeout_unit="ms")
async def wb4_slave_cdc_test(dut):
    tb = WB4SlaveTB(dut)
    rng = random.Random(int(os.environ.get('SEED', '0')))
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    level = level if level in COUNTS else 'gate'
    tb.log.info(f"wb_clk {tb.wb_period} ns, aclk {tb.fub_period} ns")
    await tb.setup_clocks_and_reset()
    phases = PHASES if level != 'gate' else PHASES[:3]
    peak = 0
    for prof in phases:
        tb.set_profiles(*prof)
        tb.mon.max_inflight = 0
        ok = await tb.run_traffic(COUNTS[level], rng, mix=0.2, timeout_clocks=80000)
        peak = max(peak, tb.mon.max_inflight)
        tb.log.info(f"phase {prof}: {'ok' if ok else 'FAILED'} max_inflight={tb.mon.max_inflight}")
        if not ok:
            break
    if not tb.errors:
        tb.set_profiles('fixed', 'fixed', 'fixed')
        await tb.run_abort(rng, outstanding=4)
        if not tb.errors:
            ok = await tb.run_traffic(COUNTS[level] // 2, rng, mix=0.2, timeout_clocks=80000)
            tb.log.info(f"post-abort traffic: {'ok' if ok else 'FAILED'}")
    await tb.wait_clocks(tb.wb_clk_name, 40)
    tb.done = True
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    if tb.classic:
        assert peak == 1, f"max_inflight={peak}: classic mode must hold one request at a time"
    else:
        assert peak > 1, f"max_inflight={peak}: never pipelined"
    assert tb.mon.aborts >= 1, "the abort phase never dropped CYC with requests outstanding"
    s = tb.stats
    assert s['ack'] and s['err'] and s['rty'], f"not every status exercised: {s}"


def generate_test_params():
    """(addr_width, data_width, max_outstanding, classic, wb_period, fub_period, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        return [(32, 32, 16, 0, 10, 3, 'gate'), (32, 32, 16, 0, 3, 10, 'gate')]
    if reg == 'FUNC':
        return [(32, 32, 16, 0, 10, 3, 'func'), (32, 32, 16, 0, 3, 10, 'func'), (32, 32, 16, 0, 10, 10, 'func'),
                (32, 64, 4, 1, 7, 10, 'func'), (32, 32, 4, 0, 10, 7, 'func')]
    return [(32, dw, mo, c, wp, fp, 'full') for dw in (32, 64) for mo in (4, 16) for c in (0, 1)
            for (wp, fp) in ((10, 3), (3, 10), (10, 10), (7, 10), (10, 7))]


@pytest.mark.parametrize("addr_width, data_width, max_outstanding, classic, wb_period, fub_period, test_level",
                         generate_test_params())
def test_wb4_slave_cdc(request, addr_width, data_width, max_outstanding, classic, wb_period, fub_period, test_level):
    """wb4_slave_cdc (rtl/amba/wb4/wb4_slave_cdc.sv)."""
    tag = (f"aw{addr_width:03d}_dw{data_width:03d}_mo{max_outstanding}_{'classic' if classic else 'pipe'}"
           f"_wb{wb_period}_a{fub_period}_{test_level}")
    run_wb4(request, 'wb4_slave_cdc', 'rtl/amba/filelists/wb4_slave_cdc.f', tag,
            {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
             'MAX_OUTSTANDING': str(max_outstanding), 'CLASSIC': str(classic)},
            {'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
             'MAX_OUTSTANDING': str(max_outstanding), 'CLASSIC': str(classic),
             'WB_CLK': 'wb_clk', 'FUB_CLK': 'aclk',
             'WB_CLK_PERIOD': str(wb_period), 'FUB_CLK_PERIOD': str(fub_period)})
