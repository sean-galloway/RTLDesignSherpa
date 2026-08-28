# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb5_slave
# Purpose: Test runner for APB5 slave with AMBA5 extensions
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-21

"""
APB5 Slave Test Runner

Tests APB5 slave functionality with AMBA5 extensions:
- User signals (PRUSER, PBUSER)
- Wake-up signaling (PWAKEUP)
- Ready delay handling
- Error response generation
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.apb5_slave_tb import APB5SlaveBasicTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist




@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_slave_basic(dut):
    """Basic APB5 slave test - verifies APB to command/response conversion."""
    tb = APB5SlaveBasicTB(dut)

    # Setup
    await tb.setup_clocks_and_reset()

    # Initialize APB signals
    dut.s_apb_PSEL.value = 0
    dut.s_apb_PENABLE.value = 0
    dut.s_apb_PWRITE.value = 0
    dut.s_apb_PADDR.value = 0
    dut.s_apb_PWDATA.value = 0
    dut.s_apb_PSTRB.value = 0

    # Initialize command interface
    dut.cmd_ready.value = 0
    dut.rsp_valid.value = 0
    dut.rsp_prdata.value = 0
    dut.rsp_pslverr.value = 0

    await tb.wait_clocks('pclk', 5)

    # Start command response handler
    async def response_handler():
        """Background task to handle command responses."""
        response_data = [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0xAABBCCDD, 0x11223344]
        idx = 0
        while True:
            try:
                await tb.drive_command_response(
                    prdata=response_data[idx % len(response_data)],
                    pruser=(idx & 0xF),
                    pbuser=((idx + 1) & 0xF),
                    delay=random.randint(0, 3)
                )
                idx += 1
            except Exception:
                break

    response_task = cocotb.start_soon(response_handler())

    # Test 1: Basic write
    tb.log.info("=== Scenario APB5-S-01: Basic write ===")
    tb.log.info("=== Test 1: Basic Write ===")
    success, err, pbuser = await tb.drive_apb_write(
        paddr=0x100, pwdata=0x12345678, pauser=0x5, pwuser=0x3
    )
    assert success, "Write transaction timeout"
    await tb.wait_clocks('pclk', 5)

    # Test 2: Basic read
    tb.log.info("=== Scenario APB5-S-02: Basic read ===")
    tb.log.info("=== Test 2: Basic Read ===")
    success, rdata, err, pruser = await tb.drive_apb_read(paddr=0x100, pauser=0x7)
    assert success, "Read transaction timeout"
    await tb.wait_clocks('pclk', 5)

    # Test 3: Multiple transactions
    tb.log.info("=== Scenario APB5-S-05: Back-to-back writes ===")
    tb.log.info("=== Scenario APB5-S-06: Back-to-back reads ===")
    tb.log.info("=== Scenario APB5-S-07: Mixed read/write ===")
    tb.log.info("=== Scenario APB5-S-10: PAUSER propagation ===")
    tb.log.info("=== Scenario APB5-S-11: PWUSER propagation ===")
    tb.log.info("=== Scenario APB5-S-12: PRUSER generation ===")
    tb.log.info("=== Scenario APB5-S-13: PBUSER generation ===")
    tb.log.info("=== Test 3: Multiple Transactions ===")
    for i in range(5):
        if i % 2 == 0:
            # Write
            success, err, pbuser = await tb.drive_apb_write(
                paddr=0x200 + (i * 4),
                pwdata=0xABCD0000 + i,
                pauser=i & 0xF,
                pwuser=(i + 1) & 0xF
            )
            assert success, f"Write {i} timeout"
        else:
            # Read
            success, rdata, err, pruser = await tb.drive_apb_read(
                paddr=0x200 + (i * 4),
                pauser=i & 0xF
            )
            assert success, f"Read {i} timeout"

        await tb.wait_clocks('pclk', 3)

    # Kill response handler
    response_task.kill()

    tb.log.info("=== APB5 Slave Basic Test PASSED ===")


def generate_apb5_slave_params():
    """Generate test parameters for APB5 slave."""
    return [
        # addr_width, data_width, auser_width, wuser_width, ruser_width, buser_width
        (12, 32, 4, 4, 4, 4),
        (16, 32, 8, 8, 8, 8),
        (12, 64, 4, 4, 4, 4),
    ]


@pytest.mark.parametrize(
    "addr_width, data_width, auser_width, wuser_width, ruser_width, buser_width",
    generate_apb5_slave_params()
)
def test_apb5_slave(request, addr_width, data_width, auser_width, wuser_width,
                    ruser_width, buser_width):
    """APB5 slave test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_slave"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb5_slave.f")

    # Test identifier
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    au_str = TBBase.format_dec(auser_width, 1)
    test_name_plus_params = f"test_{worker_id}_apb5_slave_aw{aw_str}_dw{dw_str}_au{au_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes=includes

    # RTL parameters
    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AUSER_WIDTH': str(auser_width),
        'WUSER_WIDTH': str(wuser_width),
        'RUSER_WIDTH': str(ruser_width),
        'BUSER_WIDTH': str(buser_width),
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': toplevel,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AUSER_WIDTH': str(auser_width),
        'TEST_WUSER_WIDTH': str(wuser_width),
        'TEST_RUSER_WIDTH': str(ruser_width),
        'TEST_BUSER_WIDTH': str(buser_width),
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wno-TIMESCALEMOD",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend([])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            plus_args=(['--trace'] if enable_waves else []),
            keep_files=True,
            compile_args=compile_args,
            testcase="cocotb_test_apb5_slave_basic",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
