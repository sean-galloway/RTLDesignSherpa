# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb5_slave_cdc
# Purpose: Test runner for APB5 slave clock domain crossing variant
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-23

"""
APB5 Slave CDC Test Runner

Tests APB5 slave with clock domain crossing.
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class APB5SlaveCDCBasicTB(TBBase):
    """Basic APB5 slave CDC testbench."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '12'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.AUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_AUSER_WIDTH', '4'))
        self.ENABLE_PARITY = self.convert_to_int(os.environ.get('TEST_ENABLE_PARITY', '0')) == 1

        self.log.info("="*60)
        self.log.info(" APB5 Slave CDC Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" ADDR_WIDTH:    {self.ADDR_WIDTH}")
        self.log.info(f" DATA_WIDTH:    {self.DATA_WIDTH}")
        self.log.info(f" AUSER_WIDTH:   {self.AUSER_WIDTH}")
        self.log.info(f" ENABLE_PARITY: {self.ENABLE_PARITY}")
        self.log.info("="*60)

    async def assert_reset(self):
        """Assert reset."""
        self.dut.presetn.value = 0
        self.dut.aresetn.value = 0
        await self.wait_clocks('pclk', 5)

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.presetn.value = 1
        self.dut.aresetn.value = 1
        await self.wait_clocks('pclk', 5)

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        # Start both clocks
        await self.start_clock('pclk', 10, 'ns')
        await self.start_clock('aclk', 8, 'ns')  # Slightly different frequency
        await self.assert_reset()
        await self.deassert_reset()


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_slave_cdc_basic(dut):
    """Basic APB5 slave CDC test."""
    tb = APB5SlaveCDCBasicTB(dut)

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

    # Initialize response interface (backend ready)
    dut.cmd_ready.value = 1
    dut.rsp_valid.value = 0
    dut.rsp_prdata.value = 0
    dut.rsp_pslverr.value = 0

    if hasattr(dut, 'rsp_pruser'):
        dut.rsp_pruser.value = 0
    if hasattr(dut, 'rsp_pbuser'):
        dut.rsp_pbuser.value = 0

    # Wake-up control
    dut.wakeup_request.value = 0

    tb.log.info("=== Test: CDC Basic Operation ===")

    await tb.wait_clocks('pclk', 20)

    tb.log.info("=== APB5 Slave CDC Basic Test PASSED ===")


def generate_apb5_slave_cdc_params():
    """Generate test parameters for APB5 slave CDC."""
    return [
        (12, 32, 4, 0),  # Basic
        (16, 32, 8, 0),  # 16-bit address
        (12, 64, 4, 1),  # With parity
    ]


@pytest.mark.parametrize(
    "addr_width, data_width, auser_width, enable_parity",
    generate_apb5_slave_cdc_params()
)
def test_apb5_slave_cdc(request, addr_width, data_width, auser_width, enable_parity):
    """APB5 slave CDC test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_shared': 'rtl/amba/shared',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_slave_cdc"

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "glitch_free_n_dff_arn.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'], "cdc_synchronizer.sv"),
        os.path.join(rtl_dict['rtl_amba_shared'], "cdc_handshake.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_apb5'], "apb5_slave.sv"),
        os.path.join(rtl_dict['rtl_apb5'], "apb5_slave_cdc.sv"),
    ]

    # Test identifier
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    au_str = TBBase.format_dec(auser_width, 1)
    pr_str = 'pr' if enable_parity else 'np'
    test_name_plus_params = f"test_{worker_id}_apb5_slave_cdc_aw{aw_str}_dw{dw_str}_au{au_str}_{pr_str}"
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
            testcase="cocotb_test_apb5_slave_cdc_basic",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
