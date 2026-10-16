#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): several targets in flight on a port with
# read-return atomics and trace echo, bridge_1x2_rw_axi5a -- the fix for the
# one-target limitation those ports kept after L1 (bridge GitHub #119 L1b).
#
# cpu is AXI5 with trace + atomic; ddr implements trace, sram does not (the
# port echoes the request's trace itself, bridge BUG-010). ddr is made slow,
# so anything that completes before it shows the port no longer waits on it.
#
#   trace_overlap   -- read ddr (ID 1, trace 0), then read sram (ID 2,
#                      trace 1): sram's R arrives first, and EACH R carries
#                      its own request's trace -- sram's included, which sram
#                      cannot produce, so the echo is the port's per-ID table.
#   atomic_overlap  -- a read of ddr (ID 4) held by the slow slave, then an
#                      AtomicLoad ADD to sram (ID 3): the atomic finishes
#                      first and returns the word's original value on R.
#   same_id_trace   -- two reads of ddr with ONE ID and different traces
#                      (1, then 0). Same target, so the target rule allows
#                      both; the trace rule must hold the second, or the
#                      table's one trace bit per ID would be overwritten and
#                      the first R would echo 0.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge1x2_rw_axi5a_tb import Bridge1x2RwAxi5aTB

DDR, SRAM = 0, 1
DDR_BASE, SRAM_BASE = 0x0000_0000, 0x8000_0000
SLOW = 80
ATOP_LOAD_ADD = 0b100000   # AtomicLoad, little-endian, ADD


async def _timed(tb, coro, order, tag):
    out = await coro
    order.append((tag, tb.cyc))
    return out


async def _count(tb):
    tb.cyc = 0
    while True:
        await ClockCycles(tb.clock, 1)
        tb.cyc += 1


async def _setup(dut):
    tb = Bridge1x2RwAxi5aTB(dut)
    await tb.setup_clocks_and_reset()
    cocotb.start_soon(_count(tb))
    return tb


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rw_axi5a_trace_overlap(dut):
    tb = await _setup(dut)
    rd = tb.master_rd[0]
    a_ddr, a_sram = DDR_BASE + 0x300, SRAM_BASE + 0x300
    want_ddr = tb.slave_mem_read(DDR, a_ddr, master_idx=0)
    want_sram = tb.slave_mem_read(SRAM, a_sram, master_idx=0)
    tb.set_slave_response_delay(DDR, SLOW)
    tb.cyc = 0
    order = []
    t1 = cocotb.start_soon(_timed(tb, rd.read_transaction(a_ddr, burst_len=1, id=1, trace=0), order, 'ddr'))
    await ClockCycles(tb.clock, 4)
    t2 = cocotb.start_soon(_timed(tb, rd.read_transaction(a_sram, burst_len=1, id=2, trace=1), order, 'sram'))
    r1, r2 = (await t1)[0], (await t2)[0]
    tb.log.info(f"trace_overlap order {order}; ddr {r1['data']:#x}/trace {r1['trace']}, "
                f"sram {r2['data']:#x}/trace {r2['trace']}")
    assert [t for t, _ in order] == ['sram', 'ddr'] and order[0][1] < SLOW, (
        f"the sram read waited on the slow ddr read: {order} (one-target limit)")
    assert r1['data'] == want_ddr and r2['data'] == want_sram, "read data swapped"
    assert r1['trace'] == 0 and r2['trace'] == 1, (
        f"RTRACE must echo each request's ARTRACE: ddr got {r1['trace']} (want 0), "
        f"sram got {r2['trace']} (want 1)")
    tb.assert_compliance()


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rw_axi5a_atomic_overlap(dut):
    tb = await _setup(dut)
    wr, rd = tb.master_wr[0], tb.master_rd[0]
    a_ddr, a_sram = DDR_BASE + 0x340, SRAM_BASE + 0x340
    r = await wr.write_transaction(a_sram, 0x0000_0040, size=2, id=1)
    assert r.get('response') == 0
    want_ddr = tb.slave_mem_read(DDR, a_ddr, master_idx=0)
    # The SLOW slave holds a READ; the atomic goes to the fast one. (A slow
    # atomic does not work as the discriminator: the slave BFM delays its B
    # but returns the read-return R promptly, so the old FIFO drained and
    # the old RTL passed too.) The old gate held the atomic AW until the ddr
    # read returned, because it would have been a second target.
    tb.set_slave_response_delay(DDR, SLOW)
    tb.cyc = 0
    order = []
    tr = cocotb.start_soon(_timed(tb, rd.read_transaction(a_ddr, burst_len=1, id=4), order, 'read'))
    for _ in range(200):
        await RisingEdge(tb.clock)
        if int(dut.ddr_axi_arvalid.value):
            break
    else:
        raise AssertionError("the read never reached ddr")
    await ClockCycles(tb.clock, 2)
    ta = cocotb.start_soon(_timed(tb, wr.atomic_operation(a_sram, 2, ATOP_LOAD_ADD, read_channel=rd,
                                                          size=2, id=3), order, 'atomic'))
    ra, rr = await ta, (await tr)[0]
    tb.log.info(f"atomic_overlap order {order}; atomic {ra}; read {rr['data']:#x}")
    assert [t for t, _ in order] == ['atomic', 'read'], (
        f"the atomic at sram waited on the ddr read: {order} (one-target limit)")
    assert ra.get('response') == 0 and ra.get('read_resp') == 0 and ra.get('read_data') == 0x40, (
        f"AtomicLoad ADD must return the original 0x40: {ra}")
    assert tb.slave_mem_read(SRAM, a_sram, master_idx=0) == 0x42
    assert rr['data'] == want_ddr
    tb.assert_compliance()


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_1x2_rw_axi5a_same_id_trace(dut):
    tb = await _setup(dut)
    rd = tb.master_rd[0]
    a0, a1 = DDR_BASE + 0x380, DDR_BASE + 0x384
    w0 = tb.slave_mem_read(DDR, a0, master_idx=0)
    w1 = tb.slave_mem_read(DDR, a1, master_idx=0)
    tb.set_slave_response_delay(DDR, SLOW)
    t0 = cocotb.start_soon(rd.read_transaction(a0, burst_len=1, id=6, trace=1))
    await ClockCycles(tb.clock, 4)
    t1 = cocotb.start_soon(rd.read_transaction(a1, burst_len=1, id=6, trace=0))
    r0, r1 = (await t0)[0], (await t1)[0]
    tb.log.info(f"same_id_trace: first {r0['data']:#x}/trace {r0['trace']}, "
                f"second {r1['data']:#x}/trace {r1['trace']}")
    assert (r0['data'], r1['data']) == (w0, w1), "same-ID reads returned out of order"
    assert (r0['trace'], r1['trace']) == (1, 0), (
        f"traces {r0['trace']}, {r1['trace']} (want 1, 0): a same-ID request with a "
        f"different trace overwrote the in-flight entry instead of waiting")
    tb.assert_compliance()


def _run(testcase, test_level):
    module, repo_root_, tests_dir, log_dir, _ = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_1x2_rw_axi5a"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root_,
        filelist_path='projects/components/fabric-gen-ip/bridge/rtl/filelists/bridge_1x2_rw_axi5a.f')
    worker = os.environ.get('PYTEST_XDIST_WORKER', '')
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    short = testcase.replace("cocotb_test_bridge_1x2_rw_axi5a_", "")
    name = f"test_{dut_name}_mt_{short}_{test_level}_{reg_level}" + (f"_{worker}" if worker else "")
    sim_build = sim_build_path(tests_dir, name)
    os.makedirs(log_dir, exist_ok=True)
    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase=testcase,
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert', '--coverage'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': os.path.join(log_dir, f'{name}.log'),
            'COCOTB_RESULTS_FILE': os.path.join(log_dir, f'results_{name}.xml'),
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_rw_axi5a_trace_overlap(request, test_level):
    """Pytest wrapper: a trace-echo port has two targets in flight"""
    _run("cocotb_test_bridge_1x2_rw_axi5a_trace_overlap", test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_rw_axi5a_atomic_overlap(request, test_level):
    """Pytest wrapper: a read overtakes a read-return atomic at another slave"""
    _run("cocotb_test_bridge_1x2_rw_axi5a_atomic_overlap", test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_1x2_rw_axi5a_same_id_trace(request, test_level):
    """Pytest wrapper: one ID, two traces -- the second request waits"""
    _run("cocotb_test_bridge_1x2_rw_axi5a_same_id_trace", test_level)


if __name__ == "__main__":
    pytest.main([__file__, '-v', '-s'])
