# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axil_perf_byte_count
# Purpose: perf_byte_count must scale with AXIL_DATA_WIDTH
#
# Documentation: docs/markdown/rtl-amba/axil5/axil5_master_rd_mon.md
# Subsystem: amba
#
# Author: sean galloway
# Created: 2026-09-02
"""`perf_byte_count` must count the bytes the bus actually moved.

The AXI4-Lite and AXI5-Lite monitors hardwired `cmd_size` to `3'b010` (4 bytes)
when instantiating `axi_monitor_base`, which computes

    perf_byte_count += (1 << cmd_size)   per productive beat

so on a 64-bit Lite bus every beat moved 8 bytes and was counted as 4. Byte
counts read exactly half, and nothing failed -- the number was plausible.

The whole axil4 + axil5 suite passed with the bug present and passed unchanged
with it fixed, because no test anywhere read `perf_byte_count`. That is the
gap this file closes: it asserts the count against a KNOWN number of
transactions at both legal Lite data widths, so the 32-bit case pins the
behaviour that must not change and the 64-bit case is the one that was wrong.
"""
import os
import random

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist


async def _reset(dut):
    dut.aresetn.value = 0
    for _ in range(8):
        await RisingEdge(dut.aclk)
    dut.aresetn.value = 1
    await RisingEdge(dut.aclk)


def _drive_idle(dut):
    """Everything inert; the test drives only what it needs."""
    for name, val in (
        ('cfg_monitor_enable', 1), ('cfg_error_enable', 0),
        ('cfg_compl_enable', 0), ('cfg_timeout_enable', 0),
        ('cfg_threshold_enable', 0), ('cfg_debug_enable', 0),
        ('cfg_perf_enable', 1),
        ('cfg_start_event_sel', 0),   # 3'b000 = software trigger
        ('cfg_end_event_sel', 0),
        ('cfg_start_trigger', 0), ('cfg_end_trigger', 0),
        ('cfg_window_force_close', 0),
        ('monbus_ready', 1),
        ('m_axil_arready', 1),
        ('fub_axil_arvalid', 0), ('fub_axil_rready', 1),
        ('m_axil_rvalid', 0),
    ):
        if hasattr(dut, name):
            getattr(dut, name).value = val


async def _pulse(dut, name):
    getattr(dut, name).value = 1
    await RisingEdge(dut.aclk)
    getattr(dut, name).value = 0
    await RisingEdge(dut.aclk)


@cocotb.test(timeout_time=5, timeout_unit="ms")
async def perf_byte_count_scales_with_width(dut):
    """N single-beat reads inside one window must count N * (DW/8) bytes."""
    dw = int(os.environ.get('TEST_DATA_WIDTH', '32'))
    beats = int(os.environ.get('TEST_BEATS', '8'))
    expect = beats * (dw // 8)

    cocotb.start_soon(Clock(dut.aclk, 10, units="ns").start())
    _drive_idle(dut)
    await _reset(dut)

    await _pulse(dut, 'cfg_start_trigger')
    assert int(dut.window_active.value) == 1, "window did not open on the trigger"

    # An AR handshake FIRST. `axi_monitor_base` latches cmd_size on the command
    # handshake (`r_axsize_latched <= cmd_size` when `w_cmd_handshake`), and it
    # defaults to 3'h0 = 1 byte per beat before any AR. Skip this and every beat
    # counts as one byte, which looks like the bug under test but is the
    # stimulus being wrong -- worth stating, because that is exactly how this
    # test failed on its first run.
    dut.fub_axil_arvalid.value = 1
    if hasattr(dut, 'fub_axil_araddr'):
        dut.fub_axil_araddr.value = 0
    await RisingEdge(dut.aclk)
    while int(dut.fub_axil_arready.value) == 0:
        await RisingEdge(dut.aclk)
    dut.fub_axil_arvalid.value = 0
    await RisingEdge(dut.aclk)

    # One productive R beat per iteration. The monitor counts beats on the data
    # channel, so driving the R handshake is what moves perf_byte_count.
    for _ in range(beats):
        dut.m_axil_rvalid.value = 1
        await RisingEdge(dut.aclk)
        while int(dut.fub_axil_rready.value) == 0:
            await RisingEdge(dut.aclk)
        dut.m_axil_rvalid.value = 0
        await RisingEdge(dut.aclk)

    await _pulse(dut, 'cfg_end_trigger')
    for _ in range(4):
        await RisingEdge(dut.aclk)

    got = int(dut.perf_byte_count.value)
    dut._log.info(f"DW={dw}: {beats} beats, perf_byte_count={got}, expected {expect}")
    assert got == expect, (
        f"perf_byte_count wrong at AXIL_DATA_WIDTH={dw}: got {got}, expected "
        f"{expect} ({beats} beats x {dw // 8} bytes). A hardwired cmd_size "
        f"counts every beat as 4 bytes regardless of the bus width."
    )


@pytest.mark.parametrize("dut_name, data_width", [
    ("axil4_master_rd_mon", 32),
    ("axil4_master_rd_mon", 64),
    ("axil5_master_rd_mon", 32),
    ("axil5_master_rd_mon", 64),
])
def test_axil_perf_byte_count(request, dut_name, data_width):
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')
    family = 'axil4' if dut_name.startswith('axil4') else 'axil5'

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        f'rtl_{family}': f'rtl/amba/{family}/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
        'rtl_monitor': 'rtl/amba/monitor',
        'rtl_amba_includes': 'rtl/amba/includes'})

    test_name = f"test_{worker_id}_{dut_name}_bytecount_d{data_width}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = sim_build_path(tests_dir, test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f"rtl/amba/filelists/{dut_name}.f")

    # Same suppressions the other monitor runners use; these are pre-existing
    # width warnings in the shared monitor core, not artifacts of this test.
    compile_args = [
        "-Wno-WIDTH", "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE", "-Wno-BLKANDNBLK",
        "--timescale", "1ns/1ps",
    ]

    run(
        python_search=[tests_dir],
        compile_args=compile_args,
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=os.path.splitext(os.path.basename(__file__))[0],
        parameters={
            'AXIL_ADDR_WIDTH': '32',
            'AXIL_DATA_WIDTH': str(data_width),
            'MAX_TRANSACTIONS': '8',
        },
        sim_build=sim_build,
        extra_env={
            'TEST_DATA_WIDTH': str(data_width),
            'TEST_BEATS': '8',
            'LOG_PATH': log_path,
            'COCOTB_LOG_LEVEL': 'INFO',
            'SEED': str(random.randint(0, 100000)),
            'DUT': dut_name,
        },
        waves=False,
        keep_files=True,
    )
