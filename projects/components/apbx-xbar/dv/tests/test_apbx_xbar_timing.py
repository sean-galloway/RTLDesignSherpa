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
from TBClasses.shared.filelist_utils import get_sources_from_filelist

BASE = 0x1000_0000

# Indexed by whether the variant has an arbiter. The generator emits
# arbiter_round_robin ONLY when M > 1, and its grant is a flop
# (`grant <= w_next_grant`), which costs exactly one cycle on every figure.
# Publishing the M=1 numbers unconditionally -- measured on apbx_xbar_1to1,
# the one variant with no arbiter -- made every arbitrated variant's
# published latency one cycle optimistic, including the 2x4 the PRD calls
# the typical SoC case. Both classes are asserted here now.
TIMING = {
    #            ACCESS->PREADY, SETUP->PREADY, PREADY->PREADY
    'arbitrated':      (9, 10, 11),
    'single_master':   (8,  9, 10),
}
# The latency-breakdown tables in ch05_performance/02_latency must SUM to the
# SETUP->PREADY total, and they did not until 2026-08-29: forward read 4 (4 + 3
# could not reach 9), then read 5 unconditionally while carrying a 1-cycle
# arbitration row -- impossible, since the 5 was measured on the one variant
# with no arbiter. A total that is right while its parts are wrong is how both
# survived, so the decomposition is asserted per class too.
#
# The forward path differs by that arbitration cycle; the response path does
# not, because arbitration is on the command side only. Both measured.
FORWARD_PATH = {'single_master': 5, 'arbitrated': 6}
RESPONSE_PATH = 3     # downstream PREADY edge -> master PREADY edge


async def _sampler(dut, rec):
    cyc = 0
    prev_psel = prev_access = prev_s_psel = 0
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

        # Forward path: downstream PSEL rise. Response path: measured from the
        # downstream PREADY edge, which for a zero-wait slave is its ACCESS edge.
        s_psel = int(dut.s0_apb_PSEL.value)
        if s_psel and not prev_s_psel:
            rec['s_psel_rise'].append(cyc)
        prev_s_psel = s_psel
        if s_psel and int(dut.s0_apb_PENABLE.value) and int(dut.s0_apb_PREADY.value):
            rec['s_ready'].append(cyc)

        # Downstream setup-phase run length (TASK-071).
        if int(dut.s0_apb_PSEL.value) and not int(dut.s0_apb_PENABLE.value):
            dn_run += 1
        else:
            if dn_run:
                rec['dn_setup'].append(dn_run)
            dn_run = 0


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def apbx_xbar_timing_test(dut):
    klass = os.environ.get('TIMING_CLASS', 'single_master')
    fabric, setup_to_pready, period = TIMING[klass]
    dut._log.info(f"variant class = {klass}: expecting "
                  f"ACCESS->PREADY {fabric}, SETUP->PREADY {setup_to_pready}, "
                  f"PREADY->PREADY {period}")

    cocotb.start_soon(Clock(dut.pclk, 10, units="ns").start())

    dut.s0_apb_PREADY.value = 1
    dut.s0_apb_PRDATA.value = 0xC0DE_0000
    dut.s0_apb_PSLVERR.value = 0

    for sig, val in (("PSEL", 0), ("PENABLE", 0), ("PWRITE", 0), ("PADDR", 0),
                     ("PWDATA", 0), ("PSTRB", 0), ("PPROT", 0)):
        getattr(dut, f"m0_apb_{sig}").value = val
        if hasattr(dut, f"m1_apb_{sig}"):
            getattr(dut, f"m1_apb_{sig}").value = val

    dut.presetn.value = 0
    await ClockCycles(dut.pclk, 5)
    dut.presetn.value = 1
    await ClockCycles(dut.pclk, 5)

    rec = {'psel_rise': [], 'access_rise': [], 'ready': [], 'dn_setup': [],
           's_psel_rise': [], 's_ready': []}
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
    period_expected = period
    period = [b - a for a, b in zip(rec['ready'], rec['ready'][1:])]

    dut._log.info(f"ACCESS->PREADY  = {access_to_ready}")
    dut._log.info(f"SETUP->PREADY   = {setup_to_ready}")
    dut._log.info(f"PREADY->PREADY  = {period}")
    dut._log.info(f"downstream setup runs = {rec['dn_setup']}")

    assert len(rec['ready']) == n_xfers, \
        f"expected {n_xfers} completions, saw {len(rec['ready'])}: {rec['ready']}"

    assert all(v == fabric for v in access_to_ready), (
        f"fabric latency changed: ACCESS->PREADY = {access_to_ready}, "
        f"documented {fabric} for a {klass} variant "
        f"(ch05_performance/02_latency). Update the docs WITH the measurement, "
        f"or find what regressed.")

    assert setup_to_ready[0] == setup_to_pready, (
        f"single-transfer latency changed: SETUP->PREADY = {setup_to_ready[0]}, "
        f"documented {setup_to_pready} for a {klass} variant")

    assert all(v == period_expected for v in period), (
        f"back-to-back period changed: PREADY->PREADY = {period}, documented "
        f"{period_expected}. Note this is deliberately ONE MORE than the "
        f"{setup_to_pready}-cycle single-transfer latency -- the mandatory "
        f"SETUP cycle cannot overlap the previous transfer's ACCESS. A "
        f"measurement of {setup_to_pready} here means the turnaround being "
        f"driven is not legal APB.")

    fwd = rec['s_psel_rise'][0] - rec['psel_rise'][0]
    rsp = rec['ready'][0] - rec['s_ready'][0]
    dut._log.info(f"forward path = {fwd}, response path = {rsp}")

    assert fwd == FORWARD_PATH[klass], (
        f"forward path changed: master SETUP -> downstream PSEL = {fwd}, "
        f"documented {FORWARD_PATH[klass]} for a {klass} variant "
        f"(ch05_performance/02_latency)")
    assert rsp == RESPONSE_PATH, (
        f"response path changed: downstream PREADY -> master PREADY = {rsp}, "
        f"documented {RESPONSE_PATH}")
    assert FORWARD_PATH[klass] + 1 + RESPONSE_PATH == setup_to_pready, (
        f"the documented breakdown no longer sums for {klass}: "
        f"{FORWARD_PATH[klass]} + 1 + {RESPONSE_PATH} != {setup_to_pready}")

    assert rec['dn_setup'] and all(v == 1 for v in rec['dn_setup']), (
        f"downstream setup phase must be exactly one cycle, saw "
        f"{rec['dn_setup']} -- TASK-071 regressed in apb4_master.")

    dut._log.info("all published timing numbers hold")


import pytest


@pytest.mark.parametrize("dut_name,klass", [
    ("apbx_xbar_1to1", "single_master"),
    ("apbx_xbar_2to1", "arbitrated"),
])
def test_apbx_xbar_timing(request, dut_name, klass):
    """Both variant classes. Testing only the single-master one is how the
    published numbers came to be a cycle optimistic for every arbitrated
    variant -- apbx_xbar_1to1 is the only variant with no arbiter at all."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_xbar': 'projects/components/apbx-xbar/rtl'})

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'projects/components/apbx-xbar/rtl/filelists/core/{dut_name}.f')

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{dut_name}_timing{worker_suffix}"

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
            'TIMING_CLASS': klass,
        },
    )
