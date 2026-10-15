#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# HAND-WRITTEN (not generated): several targets in flight per master on
# bridge_2x2_rw -- the fix for the one-target-per-master limitation
# (bridge GitHub #119 L1).
#
# A master adapter used to accept a new AW/AR only while every outstanding one
# went to the SAME slave. It now tracks per ID: a request waits only when its
# ID is already in flight to a DIFFERENT slave (AXI same-ID ordering), and a
# new AW also waits while W is owed to a different slave (W carries no ID).
#
#   overlap      -- a fast slave answers while a slow slave still holds an
#                   earlier request from the same master, on R and on B. The
#                   old gate held the second request until the first returned,
#                   so the completion ORDER tells the two designs apart.
#   same_id      -- the same two requests with ONE ID: the bridge must hold
#                   the second, and each read returns its own slave's data.
#   mixed_stress -- both masters, random IDs, slaves and response delays,
#                   all in flight at once; every write lands and every read
#                   returns the right word. Exercises the crossbar's response
#                   arbiter and the crossed-W hold under load.

import os
import sys
import pytest

from TBClasses.shared.utilities import get_repo_root, sim_build_path

repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import cocotb
from cocotb.triggers import ClockCycles
from cocotb_test.simulator import run
from TBClasses.shared.utilities import get_paths, get_wave_config
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid

from bridge2x2_rw_tb import Bridge2x2RwTB

DDR, SRAM = 0, 1
DDR_ADDR = 0x00000100
SRAM_ADDR = 0x80000100
SLOW = 80          # cycles the slow slave holds its response

# Concurrent operations per master in mixed_stress, by TEST_LEVEL.
STRESS_OPS = {'gate': 12, 'func': 48, 'full': 160}


async def _timed(tb, coro, order, tag):
    """Run `coro`, then record (tag, cycle) in completion order."""
    result = await coro
    order.append((tag, tb.cycle))
    return result


async def _cycle_counter(tb):
    tb.cycle = 0
    while True:
        await ClockCycles(tb.clock, 1)
        tb.cycle += 1


async def _wait_all(tb, tasks, cycles):
    for _ in range(cycles // 10):
        if all(t.done() for t in tasks):
            return
        await ClockCycles(tb.clock, 10)
    pending = sum(not t.done() for t in tasks)
    raise AssertionError(f"{pending}/{len(tasks)} operations never completed "
                         f"in {cycles} cycles -- a response was lost or the "
                         f"bridge deadlocked")


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_multitarget_overlap(dut):
    """Same master, different IDs, slow slave first: the fast slave's
    response must come back FIRST, on both R and B."""
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    cocotb.start_soon(_cycle_counter(tb))
    tb.set_slave_response_delay(DDR, SLOW)

    want_ddr = tb.expected_pattern(DDR, DDR_ADDR)
    want_sram = tb.expected_pattern(SRAM, SRAM_ADDR)
    size = tb._natural_arsize(0)
    rd = tb.master_rd[0]

    order = []
    t_ddr = cocotb.start_soon(_timed(tb, rd.single_read(DDR_ADDR, id=1, size=size), order, 'ddr'))
    await ClockCycles(tb.clock, 4)          # the ddr AR is accepted first
    t_sram = cocotb.start_soon(_timed(tb, rd.single_read(SRAM_ADDR, id=2, size=size), order, 'sram'))
    await _wait_all(tb, [t_ddr, t_sram], 20 * SLOW)

    tb.log.info(f"read completion order: {order}")
    assert [tag for tag, _ in order] == ['sram', 'ddr'], (
        f"the sram read (ID 2) finished after the ddr read (ID 1): {order}. "
        f"The adapter is still holding a request to a second slave until the "
        f"first slave answers (the one-outstanding-target gate).")
    assert order[0][1] < SLOW, (
        f"the sram read took {order[0][1]} cycles, longer than the slow "
        f"slave's {SLOW}-cycle hold: it waited on the ddr read")
    assert t_ddr.result() == want_ddr, f"ddr read 0x{t_ddr.result():x}, want 0x{want_ddr:x}"
    assert t_sram.result() == want_sram, f"sram read 0x{t_sram.result():x}, want 0x{want_sram:x}"

    # Writes: same shape on AW/W/B.
    order.clear()
    tb.cycle = 0
    t_ddr = cocotb.start_soon(_timed(tb, tb.master_write(0, DDR_ADDR + 0x40, 0xD0D0_0001, txn_id=3), order, 'ddr'))
    await ClockCycles(tb.clock, 4)
    t_sram = cocotb.start_soon(_timed(tb, tb.master_write(0, SRAM_ADDR + 0x40, 0x5A5A_0002, txn_id=4), order, 'sram'))
    await _wait_all(tb, [t_ddr, t_sram], 20 * SLOW)

    tb.log.info(f"write completion order: {order}")
    assert [tag for tag, _ in order] == ['sram', 'ddr'], (
        f"the sram write (ID 4) finished after the ddr write (ID 3): {order}")
    assert tb.slave_mem_read(DDR, DDR_ADDR + 0x40) == 0xD0D0_0001
    assert tb.slave_mem_read(SRAM, SRAM_ADDR + 0x40) == 0x5A5A_0002


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_multitarget_same_id(dut):
    """Same master, SAME ID, slow slave first: AXI requires the responses in
    issue order, so the bridge must hold the second request. A read that
    overtook would hand the first read the second slave's data (the master
    pairs same-ID beats by order)."""
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    cocotb.start_soon(_cycle_counter(tb))
    tb.set_slave_response_delay(DDR, SLOW)

    want_ddr = tb.expected_pattern(DDR, DDR_ADDR)
    want_sram = tb.expected_pattern(SRAM, SRAM_ADDR)
    assert want_ddr != want_sram, "seed patterns must differ for this test to see a swap"
    size = tb._natural_arsize(0)
    rd = tb.master_rd[0]

    order = []
    t_ddr = cocotb.start_soon(_timed(tb, rd.single_read(DDR_ADDR, id=5, size=size), order, 'ddr'))
    await ClockCycles(tb.clock, 4)
    t_sram = cocotb.start_soon(_timed(tb, rd.single_read(SRAM_ADDR, id=5, size=size), order, 'sram'))
    await _wait_all(tb, [t_ddr, t_sram], 20 * SLOW)

    tb.log.info(f"same-ID read completion order: {order}")
    assert t_ddr.result() == want_ddr, (
        f"the first ID-5 read returned 0x{t_ddr.result():x}, want ddr's "
        f"0x{want_ddr:x}: a same-ID response overtook (AXI ordering broken)")
    assert t_sram.result() == want_sram, (
        f"the second ID-5 read returned 0x{t_sram.result():x}, want sram's 0x{want_sram:x}")

    # Writes: the second B must not be delivered first. With one ID the BFM
    # pairs B by order, so the observable is completion order.
    order.clear()
    t_ddr = cocotb.start_soon(_timed(tb, tb.master_write(0, DDR_ADDR + 0x80, 0x1D00_0005, txn_id=5), order, 'ddr'))
    await ClockCycles(tb.clock, 4)
    t_sram = cocotb.start_soon(_timed(tb, tb.master_write(0, SRAM_ADDR + 0x80, 0x1D00_0006, txn_id=5), order, 'sram'))
    await _wait_all(tb, [t_ddr, t_sram], 20 * SLOW)
    tb.log.info(f"same-ID write completion order: {order}")
    assert tb.slave_mem_read(SRAM, SRAM_ADDR + 0x80) == 0x1D00_0006
    assert tb.slave_mem_read(DDR, DDR_ADDR + 0x80) == 0x1D00_0005
    sram_aw_after = order[0][0] == 'ddr'
    assert sram_aw_after, (
        f"an ID-5 B for sram was delivered before the earlier ID-5 write to "
        f"ddr completed: {order}")


@cocotb.test(timeout_time=2000, timeout_unit="ms")
async def cocotb_test_bridge_2x2_rw_multitarget_mixed_stress(dut):
    """Both masters, random IDs and slaves, random per-slave response delays,
    every operation launched at once. Each master owns a disjoint address
    region per slave, so every write is checked in memory afterwards and
    every read is checked against the seed or the write that preceded it."""
    tb = Bridge2x2RwTB(dut)
    await tb.setup_clocks_and_reset()
    level = str(tb.level).lower()
    n_ops = STRESS_OPS.get(level, STRESS_OPS['func'])
    rng = tb.rng

    # Phase 1: writes, then phase 2: reads of the same words mixed with
    # seed reads. Delays re-drawn between phases.
    plan = []
    for m in (0, 1):
        for i in range(n_ops):
            s = rng.choice((DDR, SRAM))
            base = DDR_ADDR if s == DDR else SRAM_ADDR
            addr = base + 0x400 + (m * 0x200) + (i * 4) % 0x200
            plan.append((m, s, addr, rng.randrange(4), 0xC0DE_0000 | (m << 12) | i))
    # Last write to each address wins; a later read must see it.
    final = {}
    for (m, s, addr, _id, data) in plan:
        final[(m, addr)] = (s, data)

    for phase in ('write', 'read'):
        for s in (DDR, SRAM):
            tb.set_slave_response_delay(s, rng.choice((0, 3, 17, 40)))
        tasks = []
        for (m, s, addr, txn_id, data) in plan:
            if phase == 'write':
                # Same ID + same address from one master stays ordered by
                # AXI, so overlapping writes resolve to the plan's last.
                tasks.append(cocotb.start_soon(tb.master_write(m, addr, data, txn_id=(m << 3) | txn_id)))
            else:
                size = tb._natural_arsize(m)
                tasks.append(cocotb.start_soon(
                    tb.master_rd[m].single_read(addr, id=(m << 3) | txn_id, size=size)))
        await _wait_all(tb, tasks, 400 * n_ops)
        if phase == 'read':
            bad = []
            for (m, s, addr, _id, _d), t in zip(plan, tasks):
                want = final[(m, addr)][1]
                if t.result() != want:
                    bad.append((m, s, hex(addr), hex(t.result()), hex(want)))
            assert not bad, f"{len(bad)} reads returned the wrong word; first: {bad[:4]}"
        tb.log.info(f"mixed_stress {phase}: {len(tasks)} operations completed")

    for (m, addr), (s, data) in final.items():
        got = tb.slave_mem_read(s, addr, master_idx=m)
        assert got == data, f"slave {s} @0x{addr:08x} holds 0x{got:08x}, want 0x{data:08x}"


# ============================================================================
# Pytest wrappers
# ============================================================================

def _run(testcase, test_level):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_bridge': '../../../../rtl/bridge',
        'rtl_common': '../../../../rtl/common',
        'rtl_amba': '../../../../rtl/amba'
    })
    dut_name = "bridge_2x2_rw"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/fabric-gen-ip/bridge/rtl/filelists/bridge_2x2_rw.f'
    )
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    short = testcase.replace("cocotb_test_bridge_2x2_rw_", "")
    sim_build_name = f"test_{dut_name}_{short}_{test_level}_{reg_level}{worker_suffix}"
    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
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
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_multitarget_overlap(request, test_level):
    """Pytest wrapper: a second slave answers while the first still holds"""
    _run("cocotb_test_bridge_2x2_rw_multitarget_overlap", test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_multitarget_same_id(request, test_level):
    """Pytest wrapper: same-ID requests to two slaves stay in order"""
    _run("cocotb_test_bridge_2x2_rw_multitarget_same_id", test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_bridge_2x2_rw_multitarget_mixed_stress(request, test_level):
    """Pytest wrapper: both masters, random IDs/slaves/delays, all in flight"""
    _run("cocotb_test_bridge_2x2_rw_multitarget_mixed_stress", test_level)


if __name__ == "__main__":
    pytest.main([__file__, '-v', '-s'])
