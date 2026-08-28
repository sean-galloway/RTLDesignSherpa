#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# axi5_atomic_filter (BRIDGE-002 A5-3a): store-class atomics and plain
# writes pass through; read-return atomics (AWATOP[5]==1) are swallowed
# — AW not forwarded, W burst discarded, local DECERR B with the AW ID.

import os

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path

ATOP_NONE = 0b000000
ATOP_STORE = 0b010000   # AtomicStore: B-only response, forwards
ATOP_LOAD = 0b100000    # AtomicLoad: read-return, swallowed
ATOP_SWAP = 0b110000    # AtomicSwap: read-return, swallowed


async def _downstream_model(dut, fwd_aw, bresp_queue):
    """Always-ready downstream: log forwarded AWs, and after each
    forwarded burst's WLAST return a B (id popped from fwd_aw order)."""
    dut.m_awready.value = 1
    dut.m_wready.value = 1
    dut.m_bvalid.value = 0
    pending_b = []
    inflight = []
    while True:
        await RisingEdge(dut.aclk)
        if int(dut.m_awvalid.value) and int(dut.m_awready.value):
            aw_id = int(dut.s_awid.value)  # payload routes around the DUT
            fwd_aw.append(aw_id)
            inflight.append(aw_id)
        if int(dut.m_wvalid.value) and int(dut.m_wready.value) \
                and int(dut.s_wlast.value):
            pending_b.append(inflight.pop(0))
        if int(dut.m_bvalid.value) and int(dut.m_bready.value):
            dut.m_bvalid.value = 0
        if pending_b and not int(dut.m_bvalid.value):
            bid = pending_b.pop(0)
            dut.m_bid.value = bid
            dut.m_bresp.value = 0  # OKAY
            dut.m_bvalid.value = 1
            bresp_queue.append(bid)


async def _send_write(dut, awid, atop, beats):
    """Drive one AW then its W burst through the upstream side."""
    dut.s_awid.value = awid
    dut.s_awatop.value = atop
    dut.s_awvalid.value = 1
    while True:
        await RisingEdge(dut.aclk)
        if int(dut.s_awready.value):
            break
    dut.s_awvalid.value = 0
    for i in range(beats):
        dut.s_wlast.value = 1 if i == beats - 1 else 0
        dut.s_wvalid.value = 1
        while True:
            await RisingEdge(dut.aclk)
            if int(dut.s_wready.value):
                break
    dut.s_wvalid.value = 0
    dut.s_wlast.value = 0


async def _collect_b(dut, out, count):
    while len(out) < count:
        await RisingEdge(dut.aclk)
        if int(dut.s_bvalid.value) and int(dut.s_bready.value):
            out.append((int(dut.s_bid.value), int(dut.s_bresp.value)))


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def atomic_filter_test(dut):
    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    for sig in ('s_awvalid', 's_wvalid', 's_wlast', 's_bready',
                'm_awready', 'm_wready', 'm_bvalid', 'm_bid', 'm_bresp',
                's_awid', 's_awatop'):
        getattr(dut, sig).value = 0
    dut.aresetn.value = 0
    await ClockCycles(dut.aclk, 5)
    dut.aresetn.value = 1
    await ClockCycles(dut.aclk, 2)

    fwd_aw, ds_bresp = [], []
    cocotb.start_soon(_downstream_model(dut, fwd_aw, ds_bresp))
    dut.s_bready.value = 1

    b_seen = []
    cocotb.start_soon(_collect_b(dut, b_seen, 6))

    # 1. plain write (passes), 2. store-class atomic (passes),
    # 3. load-class atomic (swallowed), 4. swap (swallowed),
    # 5. plain write after the swallows (passes),
    # 6. multi-beat load-class (swallowed, 4 W beats discarded).
    await _send_write(dut, 0x1, ATOP_NONE, 1)
    await _send_write(dut, 0x2, ATOP_STORE, 2)
    await _send_write(dut, 0x3, ATOP_LOAD, 1)
    await _send_write(dut, 0x4, ATOP_SWAP, 1)
    await _send_write(dut, 0x5, ATOP_NONE, 1)
    await _send_write(dut, 0x6, ATOP_LOAD, 4)

    await ClockCycles(dut.aclk, 50)

    assert fwd_aw == [0x1, 0x2, 0x5], (
        f"forwarded AW set wrong: {[hex(x) for x in fwd_aw]}")
    assert len(b_seen) == 6, f"expected 6 B responses, saw {b_seen}"

    by_id = dict(b_seen)
    assert len(by_id) == 6, f"duplicate B ids: {b_seen}"
    for bid in (0x1, 0x2, 0x5):
        assert by_id[bid] == 0, f"forwarded id {bid:#x} not OKAY: {by_id[bid]}"
    for bid in (0x3, 0x4, 0x6):
        assert by_id[bid] == 3, f"swallowed id {bid:#x} not DECERR: {by_id[bid]}"

    # Same-ID B ordering within each class is preserved (queue order).
    local_order = [bid for bid, r in b_seen if r == 3]
    assert local_order == [0x3, 0x4, 0x6], f"local DECERR order: {local_order}"

    dut._log.info("axi5_atomic_filter: 3 forwarded / 3 swallowed, "
                  "DECERRs and W routing all correct")


def test_axi5_atomic_filter(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi5': 'rtl/amba/axi5',
    })

    dut_name = "axi5_atomic_filter"
    # Sources come from the DUT's filelist rather than a private copy of its
    # dependency list -- a hand-list is invisible to filelist_registry --check.
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'rtl/amba/filelists/{dut_name}.f')

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{dut_name}{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="atomic_filter_test",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **waves['extra_env'],
        },
    )
