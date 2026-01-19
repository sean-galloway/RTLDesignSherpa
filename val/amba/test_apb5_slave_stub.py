# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb5_slave_stub
# Purpose: Test runner for APB5 slave stub variant
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-23

"""
APB5 Slave Stub Test Runner

Tests APB5 slave stub with packed command/response interfaces.
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class APB5SlaveStubBasicTB(TBBase):
    """Basic APB5 slave stub testbench."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '12'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.AUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_AUSER_WIDTH', '4'))
        self.ENABLE_PARITY = self.convert_to_int(os.environ.get('TEST_ENABLE_PARITY', '0')) == 1

        self.log.info("="*60)
        self.log.info(" APB5 Slave Stub Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" ADDR_WIDTH:    {self.ADDR_WIDTH}")
        self.log.info(f" DATA_WIDTH:    {self.DATA_WIDTH}")
        self.log.info(f" AUSER_WIDTH:   {self.AUSER_WIDTH}")
        self.log.info(f" ENABLE_PARITY: {self.ENABLE_PARITY}")
        self.log.info("="*60)

    async def assert_reset(self):
        """Assert reset."""
        self.dut.presetn.value = 0
        await self.wait_clocks('pclk', 5)

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.presetn.value = 1
        await self.wait_clocks('pclk', 5)

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock('pclk', 10, 'ns')
        await self.assert_reset()
        await self.deassert_reset()


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_slave_stub_basic(dut):
    """Basic APB5 slave stub test."""
    tb = APB5SlaveStubBasicTB(dut)

    # Setup
    await tb.setup_clocks_and_reset()

    # Initialize APB signals
    dut.s_apb_PSEL.value = 0
    dut.s_apb_PENABLE.value = 0
    dut.s_apb_PADDR.value = 0
    dut.s_apb_PWRITE.value = 0
    dut.s_apb_PWDATA.value = 0
    dut.s_apb_PSTRB.value = 0xF
    dut.s_apb_PPROT.value = 0

    if hasattr(dut, 's_apb_PAUSER'):
        dut.s_apb_PAUSER.value = 0
    if hasattr(dut, 's_apb_PWUSER'):
        dut.s_apb_PWUSER.value = 0

    # Initialize backend interface
    dut.cmd_ready.value = 1
    dut.rsp_valid.value = 0
    dut.rsp_data.value = 0

    # Wake-up control
    dut.wakeup_request.value = 0

    await tb.wait_clocks('pclk', 10)

    tb.log.info("=== APB5 Slave Stub Basic Test PASSED ===")


def generate_apb5_slave_stub_params():
    """Generate test parameters for APB5 slave stub."""
    return [
        (12, 32, 4, 0),  # Basic
        (16, 32, 8, 0),  # 16-bit address
        (12, 64, 4, 1),  # With parity
    ]


@pytest.mark.parametrize(
    "addr_width, data_width, auser_width, enable_parity",
    generate_apb5_slave_stub_params()
)
def test_apb5_slave_stub(request, addr_width, data_width, auser_width, enable_parity):
    """APB5 slave stub test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_slave_stub"

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_apb5'], "apb5_slave_stub.sv"),
    ]

    # Test identifier
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    au_str = TBBase.format_dec(auser_width, 1)
    pr_str = 'pr' if enable_parity else 'np'
    test_name_plus_params = f"test_{worker_id}_apb5_slave_stub_aw{aw_str}_dw{dw_str}_au{au_str}_{pr_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes = [rtl_dict['rtl_amba_includes']]

    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AUSER_WIDTH': str(auser_width),
        'WUSER_WIDTH': str(auser_width),
        'RUSER_WIDTH': str(auser_width),
        'BUSER_WIDTH': str(auser_width),
        'ENABLE_PARITY': str(enable_parity),
    }

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
        'TEST_ENABLE_PARITY': str(enable_parity),
    }

    compile_args = [
        "-Wno-TIMESCALEMOD",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

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
            testcase="cocotb_test_apb5_slave_stub_basic",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
