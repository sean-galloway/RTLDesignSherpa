# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""wb4_master_cg: the wb4_master phases under clock gating.

Every clock: never gated while a cycle is open or a command/response is
pending. After every phase: the clock gates within the idle count (enable
high) or never gates (CG_ENABLE=0 configuration).
"""
import os
import random

import pytest
import cocotb
from TBClasses.amba.wb4_cg_tb import WB4MasterCGTB
from wb4_test_common import MASTER_PHASES as PHASES, COUNTS, run_wb4


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def wb4_master_cg_test(dut):
    tb = WB4MasterCGTB(dut)
    rng = random.Random(int(os.environ.get('SEED', '0')))
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    level = level if level in COUNTS else 'gate'
    await tb.setup_clocks_and_reset()
    phases = PHASES if level != 'gate' else PHASES[:3]
    peak = 0
    for prof in phases:
        tb.set_profiles(*prof)
        tb.mon.max_inflight = 0
        ok = await tb.run_traffic(COUNTS[level], rng, mix=0.2)
        peak = max(peak, tb.mon.max_inflight)
        tb.log.info(f"phase {prof}: {'ok' if ok else 'FAILED'} max_inflight={tb.mon.max_inflight}")
        if not ok:
            break
        await tb.wait_clocks('clk', 4)
        await tb.expect_gated()
    tb.done = True
    tb.cg_report()
    assert tb.report(), f"{len(tb.errors)} error(s); first: {tb.errors[0] if tb.errors else ''}"
    if tb.cg_enable:
        assert tb.cg_stats['gate_edges'] >= len(phases), "the clock never gated between phases"
    else:
        assert tb.cg_stats['gated_clocks'] == 0
    if tb.classic:
        assert peak == 1, f"max_inflight={peak}: classic mode must hold one request at a time"
    else:
        assert peak > 1, f"max_inflight={peak}: never pipelined"


def generate_test_params():
    """(addr_width, data_width, classic, cg_enable, idle_count, test_level)"""
    reg = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg == 'GATE':
        return [(32, 32, 0, 1, 4, 'gate'), (32, 32, 0, 0, 4, 'gate')]
    if reg == 'FUNC':
        return [(32, 32, 0, 1, 4, 'func'), (32, 32, 1, 1, 2, 'func'), (32, 64, 0, 1, 8, 'func'),
                (32, 32, 0, 0, 4, 'func')]
    return [(32, dw, c, e, ic, 'full') for dw in (32, 64) for c in (0, 1) for e in (1, 0) for ic in (1, 4, 12)]


@pytest.mark.parametrize("addr_width, data_width, classic, cg_enable, idle_count, test_level",
                         generate_test_params())
def test_wb4_master_cg(request, addr_width, data_width, classic, cg_enable, idle_count, test_level):
    """wb4_master_cg (rtl/amba/wb4/wb4_master_cg.sv)."""
    tag = (f"aw{addr_width:03d}_dw{data_width:03d}_{'classic' if classic else 'pipe'}"
           f"_cg{cg_enable}_ic{idle_count}_{test_level}")
    run_wb4(request, 'wb4_master_cg', 'rtl/amba/filelists/wb4_master_cg.f', tag,
            {'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width), 'CLASSIC': str(classic)},
            {'TEST_LEVEL': test_level, 'ADDR_WIDTH': str(addr_width), 'DATA_WIDTH': str(data_width),
             'CLASSIC': str(classic), 'CG_ENABLE': str(cg_enable), 'CG_IDLE_COUNT': str(idle_count)})
