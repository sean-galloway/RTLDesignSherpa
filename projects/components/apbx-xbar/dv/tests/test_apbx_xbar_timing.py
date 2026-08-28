#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# Locks down the APB crossbar's published timing numbers so they cannot drift
# or be re-litigated from memory. Every figure in ch05_performance/02_latency
# is asserted here, measured passively at the ports.
#
# MEASUREMENT CONVENTION -- all counts are rising pclk edges, and every
# quantity names the two edges it spans. This matters: the fabric latency and
# the back-to-back period differ by exactly one cycle, and conflating them is
# what produced the wrong published cadence.
#
#   ACCESS -> PREADY   8   first ACCESS edge to the edge where PREADY is high
#   PSEL   -> PREADY   9   the same, counted from the SETUP edge (= 1 + 8)
#   PREADY -> PREADY  10   steady-state period at the earliest LEGAL turnaround
#
# Why the period is 10 and not 9: after PREADY at cycle N the bus is still in
# ACCESS for that cycle, so the next transfer's mandatory SETUP cycle cannot
# start before N+1, putting its ACCESS at N+2 and its PREADY at N+2+8 = N+10.
# A period of 9 would require SETUP to share a cycle with the previous
# transfer's ACCESS, which is not a legal APB waveform. The earliest legal
# turnaround is therefore PSEL held high with PENABLE low for exactly one
# cycle -- which is what this test drives.
#
# Also asserts the TASK-071 fix end to end: the DOWNSTREAM port must see a
# one-cycle setup phase. Before the fix it saw two.

import os

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, NextTimeStep
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

BASE = 0x1000_0000

FABRIC_ACCESS_TO_PREADY = 8
SETUP_TO_PREADY = 9
BACK_TO_BACK_PERIOD = 10


async def _sampler(dut, rec):
    cyc = 0
    prev_psel = prev_access = 0
    dn_run = 0
    while True:
        await RisingEdge(dut.pclk)
        cyc += 1
        psel = int(dut.m0_apb_PSEL.value)
        penable = int(dut.m0_apb_PENABLE.value)
        pready = int(dut.m0_apb_PREADY.value)
        access = psel and penable

        if psel and not prev_psel:
            rec['psel_rise'].append(cyc)
        if access and not prev_access:
            rec['access_rise'].append(cyc)
        if access and pready:
            rec['ready'].append(cyc)
        prev_psel, prev_access = psel, access

        # Downstream setup-phase run length (TASK-071).
        if int(dut.s0_apb_PSEL.value) and not int(dut.s0_apb_PENABLE.value):
            dn_run += 1
        else:
            if dn_run:
                rec['dn_setup'].append(dn_run)
            dn_run = 0


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def apbx_xbar_timing_test(dut):
    cocotb.start_soon(Clock(dut.pclk, 10, units="ns").start())

    dut.s0_apb_PREADY.value = 1
    dut.s0_apb_PRDATA.value = 0xC0DE_0000
    dut.s0_apb_PSLVERR.value = 0

    for sig, val in (("PSEL", 0), ("PENABLE", 0), ("PWRITE", 0), ("PADDR", 0),
                     ("PWDATA", 0), ("PSTRB", 0), ("PPROT", 0)):
        getattr(dut, f"m0_apb_{sig}").value = val

    dut.presetn.value = 0
    await ClockCycles(dut.pclk, 5)
    dut.presetn.value = 1
    await ClockCycles(dut.pclk, 5)

    rec = {'psel_rise': [], 'access_rise': [], 'ready': [], 'dn_setup': []}
    cocotb.start_soon(_sampler(dut, rec))

    n_xfers = 5
    for i in range(n_xfers):
        dut.m0_apb_PADDR.value = BASE + (i * 4)
        dut.m0_apb_PWRITE.value = 0
        dut.m0_apb_PSEL.value = 1
        dut.m0_apb_PENABLE.value = 0
        await RisingEdge(dut.pclk)
        await NextTimeStep()
        dut.m0_apb_PENABLE.value = 1

        while True:
            await RisingEdge(dut.pclk)
            if int(dut.m0_apb_PREADY.value):
                break
        # Earliest LEGAL turnaround: PSEL stays high, PENABLE drops for exactly
        # one cycle, and that cycle is the next transfer's SETUP phase.
        await NextTimeStep()
        dut.m0_apb_PENABLE.value = 0

    await ClockCycles(dut.pclk, 10)

    access_to_ready = [r - a for a, r in zip(rec['access_rise'], rec['ready'])]
    setup_to_ready = [r - p for p, r in zip(rec['psel_rise'], rec['ready'])]
    period = [b - a for a, b in zip(rec['ready'], rec['ready'][1:])]

    dut._log.info(f"ACCESS->PREADY  = {access_to_ready}")
    dut._log.info(f"SETUP->PREADY   = {setup_to_ready}")
    dut._log.info(f"PREADY->PREADY  = {period}")
    dut._log.info(f"downstream setup runs = {rec['dn_setup']}")

    assert len(rec['ready']) == n_xfers, \
        f"expected {n_xfers} completions, saw {len(rec['ready'])}: {rec['ready']}"

    assert all(v == FABRIC_ACCESS_TO_PREADY for v in access_to_ready), (
        f"fabric latency changed: ACCESS->PREADY = {access_to_ready}, "
        f"documented {FABRIC_ACCESS_TO_PREADY} "
        f"(ch05_performance/02_latency). Update the docs WITH the measurement, "
        f"or find what regressed.")

    assert setup_to_ready[0] == SETUP_TO_PREADY, (
        f"single-transfer latency changed: SETUP->PREADY = {setup_to_ready[0]}, "
        f"documented {SETUP_TO_PREADY}")

    assert all(v == BACK_TO_BACK_PERIOD for v in period), (
        f"back-to-back period changed: PREADY->PREADY = {period}, documented "
        f"{BACK_TO_BACK_PERIOD}. Note this is deliberately ONE MORE than the "
        f"{SETUP_TO_PREADY}-cycle single-transfer latency -- the mandatory "
        f"SETUP cycle cannot overlap the previous transfer's ACCESS. A "
        f"measurement of {SETUP_TO_PREADY} here means the turnaround being "
        f"driven is not legal APB.")

    assert rec['dn_setup'] and all(v == 1 for v in rec['dn_setup']), (
        f"downstream setup phase must be exactly one cycle, saw "
        f"{rec['dn_setup']} -- TASK-071 regressed in apb4_master.")

    dut._log.info("all published timing numbers hold")


def test_apbx_xbar_timing(request):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_xbar': 'projects/components/apbx-xbar/rtl'})

    dut_name = "apbx_xbar_1to1"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/apbx-xbar/rtl/filelists/core/apbx_xbar_1to1.f')

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_apbx_xbar_timing{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="apbx_xbar_timing_test",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
        },
    )
