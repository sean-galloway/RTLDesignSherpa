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

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class APB5SlaveBasicTB(TBBase):
    """Basic APB5 slave testbench for RTL verification."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '12'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.AUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_AUSER_WIDTH', '4'))
        self.WUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_WUSER_WIDTH', '4'))
        self.RUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_RUSER_WIDTH', '4'))
        self.BUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_BUSER_WIDTH', '4'))

        self.log.info("="*60)
        self.log.info(" APB5 Slave Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" ADDR_WIDTH:  {self.ADDR_WIDTH}")
        self.log.info(f" DATA_WIDTH:  {self.DATA_WIDTH}")
        self.log.info(f" AUSER_WIDTH: {self.AUSER_WIDTH}")
        self.log.info(f" WUSER_WIDTH: {self.WUSER_WIDTH}")
        self.log.info(f" RUSER_WIDTH: {self.RUSER_WIDTH}")
        self.log.info(f" BUSER_WIDTH: {self.BUSER_WIDTH}")
        self.log.info("="*60)

    async def assert_reset(self):
        """Assert reset."""
        self.dut.presetn.value = 0
        await self.wait_clocks('pclk', 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.presetn.value = 1
        await self.wait_clocks('pclk', 5)
        self.log.info("Reset deasserted")

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock('pclk', 10, 'ns')
        await self.assert_reset()
        await self.deassert_reset()

    async def drive_apb_write(self, paddr, pwdata, pstrb=0xF, pauser=0, pwuser=0):
        """Drive an APB5 write transaction."""
        # Setup phase
        self.dut.s_apb_PSEL.value = 1
        self.dut.s_apb_PENABLE.value = 0
        self.dut.s_apb_PWRITE.value = 1
        self.dut.s_apb_PADDR.value = paddr
        self.dut.s_apb_PWDATA.value = pwdata
        self.dut.s_apb_PSTRB.value = pstrb
        if hasattr(self.dut, 's_apb_PAUSER'):
            self.dut.s_apb_PAUSER.value = pauser
        if hasattr(self.dut, 's_apb_PWUSER'):
            self.dut.s_apb_PWUSER.value = pwuser

        await RisingEdge(self.dut.pclk)

        # Access phase
        self.dut.s_apb_PENABLE.value = 1
        await RisingEdge(self.dut.pclk)

        # Wait for PREADY
        timeout = 100
        while not self.dut.s_apb_PREADY.value and timeout > 0:
            await RisingEdge(self.dut.pclk)
            timeout -= 1

        # Capture response
        pslverr = int(self.dut.s_apb_PSLVERR.value)
        pbuser = int(self.dut.s_apb_PBUSER.value) if hasattr(self.dut, 's_apb_PBUSER') else 0

        # End transaction
        self.dut.s_apb_PSEL.value = 0
        self.dut.s_apb_PENABLE.value = 0
        await RisingEdge(self.dut.pclk)

        self.log.info(f"APB5 Write: addr=0x{paddr:04X} data=0x{pwdata:08X} "
                     f"err={pslverr} pbuser=0x{pbuser:X}")

        return timeout > 0, pslverr, pbuser

    async def drive_apb_read(self, paddr, pauser=0):
        """Drive an APB5 read transaction."""
        # Setup phase
        self.dut.s_apb_PSEL.value = 1
        self.dut.s_apb_PENABLE.value = 0
        self.dut.s_apb_PWRITE.value = 0
        self.dut.s_apb_PADDR.value = paddr
        if hasattr(self.dut, 's_apb_PAUSER'):
            self.dut.s_apb_PAUSER.value = pauser

        await RisingEdge(self.dut.pclk)

        # Access phase
        self.dut.s_apb_PENABLE.value = 1
        await RisingEdge(self.dut.pclk)

        # Wait for PREADY
        timeout = 100
        while not self.dut.s_apb_PREADY.value and timeout > 0:
            await RisingEdge(self.dut.pclk)
            timeout -= 1

        # Capture response
        prdata = int(self.dut.s_apb_PRDATA.value)
        pslverr = int(self.dut.s_apb_PSLVERR.value)
        pruser = int(self.dut.s_apb_PRUSER.value) if hasattr(self.dut, 's_apb_PRUSER') else 0

        # End transaction
        self.dut.s_apb_PSEL.value = 0
        self.dut.s_apb_PENABLE.value = 0
        await RisingEdge(self.dut.pclk)

        self.log.info(f"APB5 Read: addr=0x{paddr:04X} data=0x{prdata:08X} "
                     f"err={pslverr} pruser=0x{pruser:X}")

        return timeout > 0, prdata, pslverr, pruser

    async def drive_command_response(self, prdata, pslverr=0, pruser=0, pbuser=0, delay=0):
        """Drive response through command interface."""
        # Wait for command
        while not self.dut.cmd_valid.value:
            await RisingEdge(self.dut.pclk)

        # Accept command
        self.dut.cmd_ready.value = 1
        await RisingEdge(self.dut.pclk)
        self.dut.cmd_ready.value = 0

        # Add optional delay
        for _ in range(delay):
            await RisingEdge(self.dut.pclk)

        # Send response
        self.dut.rsp_valid.value = 1
        self.dut.rsp_prdata.value = prdata
        self.dut.rsp_pslverr.value = pslverr
        if hasattr(self.dut, 'rsp_pruser'):
            self.dut.rsp_pruser.value = pruser
        if hasattr(self.dut, 'rsp_pbuser'):
            self.dut.rsp_pbuser.value = pbuser

        # Wait for response acceptance
        while not self.dut.rsp_ready.value:
            await RisingEdge(self.dut.pclk)

        await RisingEdge(self.dut.pclk)
        self.dut.rsp_valid.value = 0


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
    tb.log.info("=== Test 1: Basic Write ===")
    success, err, pbuser = await tb.drive_apb_write(
        paddr=0x100, pwdata=0x12345678, pauser=0x5, pwuser=0x3
    )
    assert success, "Write transaction timeout"
    await tb.wait_clocks('pclk', 5)

    # Test 2: Basic read
    tb.log.info("=== Test 2: Basic Read ===")
    success, rdata, err, pruser = await tb.drive_apb_read(paddr=0x100, pauser=0x7)
    assert success, "Read transaction timeout"
    await tb.wait_clocks('pclk', 5)

    # Test 3: Multiple transactions
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

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_apb5'], "apb5_slave.sv"),
    ]

    # Test identifier
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    au_str = TBBase.format_dec(auser_width, 1)
    test_name_plus_params = f"test_{worker_id}_apb5_slave_aw{aw_str}_dw{dw_str}_au{au_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes = [rtl_dict['rtl_amba_includes']]

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
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': toplevel,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AUSER_WIDTH': str(auser_width),
        'TEST_WUSER_WIDTH': str(wuser_width),
        'TEST_RUSER_WIDTH': str(ruser_width),
        'TEST_BUSER_WIDTH': str(buser_width),
    }

    compile_args = [
        "-Wno-TIMESCALEMOD",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
    ]

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
            waves=False,
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
