#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# TASK-071: apb4_master / apb5_master must present exactly ONE setup cycle.
#
# AMBA APB defines the SETUP phase as exactly one cycle -- PSEL asserted with
# PENABLE low -- followed by ACCESS (PSEL and PENABLE both high). These FSMs
# asserted PSEL in BOTH the IDLE launch cycle and the SETUP state, so every
# transfer launched from idle showed TWO setup cycles. Back-to-back transfers
# taking the ACCESS -> SETUP shortcut were already compliant, so this only
# ever appeared on a launch from idle.
#
# The check is a passive monitor: sample PSEL/PENABLE every rising edge and
# measure the run length of each (PSEL && !PENABLE) region. Every run must be
# exactly 1. A run of 2 is the bug; a run of 0 would mean PENABLE asserted
# with no setup phase at all, which is the opposite violation and equally bad.

import os

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths
from TBClasses.shared.filelist_utils import get_sources_from_filelist


async def _setup_phase_monitor(dut, runs):
    """Record the length of every (PSEL && !PENABLE) run on the APB port."""
    current = 0
    while True:
        await RisingEdge(dut.pclk)
        psel = int(dut.m_apb_PSEL.value)
        penable = int(dut.m_apb_PENABLE.value)
        if psel and not penable:
            current += 1
        else:
            if current:
                runs.append(current)
            current = 0


async def _always_ready_completer(dut, prdata=0xC0DE_0000):
    dut.m_apb_PREADY.value = 1
    dut.m_apb_PRDATA.value = prdata
    dut.m_apb_PSLVERR.value = 0


async def _issue(dut, addr, write, wdata=0, timeout=100):
    """Drive one cmd through the master and wait for its response."""
    dut.cmd_paddr.value = addr
    dut.cmd_pwrite.value = int(write)
    dut.cmd_pwdata.value = wdata
    dut.cmd_pstrb.value = 0xF
    dut.cmd_pprot.value = 0
    dut.cmd_valid.value = 1

    for _ in range(timeout):
        await RisingEdge(dut.pclk)
        if int(dut.cmd_ready.value):
            break
    else:
        assert False, f"cmd at 0x{addr:08X} was never accepted"
    dut.cmd_valid.value = 0

    for _ in range(timeout):
        await RisingEdge(dut.pclk)
        if int(dut.rsp_valid.value):
            return
    assert False, f"cmd at 0x{addr:08X} never produced a response"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def apb_master_setup_phase_test(dut):
    cocotb.start_soon(Clock(dut.pclk, 10, units="ns").start())

    dut.cmd_valid.value = 0
    dut.rsp_ready.value = 1
    await _always_ready_completer(dut)

    dut.presetn.value = 0
    await ClockCycles(dut.pclk, 5)
    dut.presetn.value = 1
    await ClockCycles(dut.pclk, 5)

    runs = []
    cocotb.start_soon(_setup_phase_monitor(dut, runs))

    # Four transfers, each separated by idle so every one launches from IDLE.
    # The back-to-back ACCESS -> SETUP shortcut was always compliant; the
    # launch-from-idle path is the one under test.
    for i in range(4):
        await _issue(dut, 0x1000_0000 + (i * 4), write=(i % 2 == 0), wdata=0xA5A5_0000 + i)
        await ClockCycles(dut.pclk, 4)

    await ClockCycles(dut.pclk, 4)

    dut._log.info(f"setup-phase run lengths = {runs}")

    assert len(runs) >= 4, (
        f"expected at least 4 setup phases for 4 transfers, saw {len(runs)}: {runs}")

    bad = [(i, n) for i, n in enumerate(runs) if n != 1]
    assert not bad, (
        f"APB setup phase must be exactly ONE cycle (PSEL high, PENABLE low). "
        f"Offending runs (index, length): {bad}. Full record: {runs}. "
        f"A length of 2 means PSEL is asserted in the IDLE launch cycle AND "
        f"again in SETUP -- TASK-071.")

    dut._log.info(f"all {len(runs)} setup phases were exactly 1 cycle")


def _run_one(request, dut_name, filelist):
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_amba': 'rtl/amba'})

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=filelist)

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{dut_name}_setup_phase{worker_suffix}"

    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="apb_master_setup_phase_test",
        sim_build=sim_build,
        waves=False,
        extra_args=['--assert'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
        },
    )


def test_apb4_master_setup_phase(request):
    _run_one(request, "apb4_master", 'rtl/amba/filelists/apb4_master.f')


def test_apb5_master_setup_phase(request):
    _run_one(request, "apb5_master", 'rtl/amba/filelists/apb5_master.f')
