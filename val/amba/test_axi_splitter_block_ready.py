# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: test_axi_splitter_block_ready
# Purpose: block_ready must BLOCK a splitter, not duplicate through it.
#
# Documentation: docs/markdown/rtl-amba/shared/axi_master_rd_splitter.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-08-16

"""block_ready contract for axi_master_{rd,wr}_splitter (TASK-061).

THE INVARIANT: while block_ready is asserted, no command reaches the slave.

Both splitters gated the upstream ready and the FSM capture on block_ready but
NOT the downstream valid:

    IDLE: m_axi_arvalid = fub_arvalid;             // ungated
    fub_arready = m_axi_arready && !block_ready;   // gated
    if (fub_arvalid && m_axi_arready && !block_ready)  // capture: gated

With block_ready=1, fub_arvalid=1 and m_axi_arready=1 the slave accepts the
command, the upstream handshake never completes, and the FSM never captures --
so the master holds the same command on the bus and the slave accepts it AGAIN,
every cycle. The result is DUPLICATED downstream transactions, not blocked
ones.

Why no existing test caught it: the whole splitter suite leaves block_ready
tied low, so the gate was never asserted. Nothing in rtl/ instantiates either
splitter today either, which is the "who would notice if this library module
were wrong?" shape from the escape-analysis note. This file asserts the signal
and counts what crosses the boundary.
"""

import os

import cocotb
import pytest
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

IS_WRITE = os.environ.get("SPLITTER_IS_WRITE", "0") == "1"


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def cocotb_test_block_ready_blocks(dut):
    """Hold block_ready and prove nothing reaches the slave."""
    is_write = os.environ.get("SPLITTER_IS_WRITE", "0") == "1"
    ch = "aw" if is_write else "ar"

    fub_valid = getattr(dut, f"fub_{ch}valid")
    fub_ready = getattr(dut, f"fub_{ch}ready")
    m_valid = getattr(dut, f"m_axi_{ch}valid")
    m_ready = getattr(dut, f"m_axi_{ch}ready")

    # Reset
    dut.aresetn.value = 0
    dut.block_ready.value = 0
    fub_valid.value = 0
    m_ready.value = 1
    for sig, val in ((f"fub_{ch}id", 3), (f"fub_{ch}addr", 0x1000),
                     (f"fub_{ch}len", 3), (f"fub_{ch}size", 2),
                     (f"fub_{ch}burst", 1)):
        s = getattr(dut, sig, None)
        if s is not None:
            s.value = val
    cocotb.start_soon(_clock(dut))
    for _ in range(10):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    for _ in range(5):
        await RisingEdge(dut.aclk)

    # ---- Phase 1: BLOCKED. Present a command for many cycles. ----------
    dut.block_ready.value = 1
    fub_valid.value = 1
    accepted_while_blocked = 0
    upstream_while_blocked = 0
    for _ in range(60):
        await RisingEdge(dut.aclk)
        if int(m_valid.value) and int(m_ready.value):
            accepted_while_blocked += 1
        if int(fub_valid.value) and int(fub_ready.value):
            upstream_while_blocked += 1

    dut._log.info(f"blocked window: downstream accepts={accepted_while_blocked} "
                  f"upstream handshakes={upstream_while_blocked}")

    failures = []
    if accepted_while_blocked:
        failures.append(
            f"{accepted_while_blocked} command(s) reached the slave while "
            f"block_ready was asserted. The downstream valid is not gated, so "
            f"the same command is re-accepted every cycle -- duplication, not "
            f"blocking.")
    if upstream_while_blocked:
        failures.append(
            f"{upstream_while_blocked} upstream handshake(s) completed while "
            f"blocked; the upstream ready gate is broken too.")

    # ---- Phase 2: RELEASED. The command must now go through exactly once.
    dut.block_ready.value = 0
    accepted_after = 0
    for _ in range(40):
        await RisingEdge(dut.aclk)
        if int(m_valid.value) and int(m_ready.value):
            accepted_after += 1
        if int(fub_valid.value) and int(fub_ready.value):
            fub_valid.value = 0          # one command only
    dut._log.info(f"released window: downstream accepts={accepted_after}")

    if accepted_after == 0:
        failures.append(
            "no command reached the slave after block_ready was released -- "
            "the gate does not recover, which is a deadlock rather than "
            "backpressure.")

    if failures:
        for f in failures:
            dut._log.error(f)
        raise AssertionError("; ".join(failures))
    dut._log.info("PASS: blocked = nothing through; released = command flows")


async def _clock(dut):
    dut.aclk.value = 0
    while True:
        await cocotb.triggers.Timer(5, units="ns")
        dut.aclk.value = 1
        await cocotb.triggers.Timer(5, units="ns")
        dut.aclk.value = 0


@pytest.mark.parametrize("is_write", [False, True])
def test_axi_splitter_block_ready(is_write):
    """block_ready must block, on both splitters."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':         'rtl/common',
        'rtl_gaxi':        'rtl/amba/gaxi',
        'rtl_axi4':        'rtl/amba/axi4/',
        'rtl_amba_shared': 'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "axi_master_wr_splitter" if is_write else "axi_master_rd_splitter"
    test_name = f"test_{worker_id}_{dut_name}_block_ready"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f"rtl/amba/filelists/{dut_name}.f")

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes + [rtl_dict['rtl_cmn'], sim_build],
        toplevel=dut_name,
        module="test_axi_splitter_block_ready",
        parameters={
            'AXI_ID_WIDTH': '8', 'AXI_ADDR_WIDTH': '32',
            'AXI_DATA_WIDTH': '32', 'AXI_USER_WIDTH': '1',
        },
        sim_build=sim_build,
        extra_env={'DUT': dut_name, 'LOG_PATH': log_path,
                   'COCOTB_LOG_LEVEL': 'INFO',
                   'SPLITTER_IS_WRITE': '1' if is_write else '0'},
        testcase="cocotb_test_block_ready_blocks",
        keep_files=True,
        compile_args=["-Wall", "-Wno-DECLFILENAME", "-Wno-UNUSED",
                      "-Wno-PINMISSING", "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND",
                      "-Wno-WIDTHTRUNC", "-Wno-SELRANGE", "-Wno-TIMESCALEMOD",
                      "-Wno-SYNCASYNCNET", "-Wno-CASEINCOMPLETE"],
    )
