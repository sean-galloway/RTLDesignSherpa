# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axis5_master_cg
# Purpose: Test runner for AXIS5 master clock-gated variant
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Master Clock-Gated Test Runner

Tests AXIS5 master with clock gating for power management.
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


class AXIS5MasterCGBasicTB(TBBase):
    """Basic AXIS5 master clock-gated testbench."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.SKID_DEPTH = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH', '4'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.ENABLE_WAKEUP = self.convert_to_int(os.environ.get('TEST_ENABLE_WAKEUP', '1')) == 1
        self.ENABLE_PARITY = self.convert_to_int(os.environ.get('TEST_ENABLE_PARITY', '0')) == 1
        self.STRB_WIDTH = self.DATA_WIDTH // 8

        self.log.info("="*60)
        self.log.info(" AXIS5 Master CG Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" SKID_DEPTH:    {self.SKID_DEPTH}")
        self.log.info(f" DATA_WIDTH:    {self.DATA_WIDTH}")
        self.log.info(f" ENABLE_WAKEUP: {self.ENABLE_WAKEUP}")
        self.log.info(f" ENABLE_PARITY: {self.ENABLE_PARITY}")
        self.log.info("="*60)

    async def assert_reset(self):
        """Assert reset."""
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 5)

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 5)

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        await self.deassert_reset()

    async def enable_clock_gating(self, enable=True):
        """Enable or disable clock gating."""
        self.dut.i_cg_enable.value = 1 if enable else 0
        await RisingEdge(self.dut.aclk)
        self.log.info(f"Clock gating {'enabled' if enable else 'disabled'}")


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_axis5_master_cg_basic(dut):
    """Basic AXIS5 master clock-gated test."""
    tb = AXIS5MasterCGBasicTB(dut)

    # Setup
    await tb.setup_clocks_and_reset()

    # Configure clock gating idle count
    dut.i_cg_idle_count.value = 8

    # Configure slave side
    dut.m_axis5_tready.value = 1

    # Test clock gating enable/disable
    tb.log.info("=== Test: Clock Gating Control ===")

    # Disable clock gating first
    await tb.enable_clock_gating(False)
    await tb.wait_clocks('aclk', 10)

    # Enable clock gating
    await tb.enable_clock_gating(True)
    await tb.wait_clocks('aclk', 20)

    # Disable clock gating
    await tb.enable_clock_gating(False)
    await tb.wait_clocks('aclk', 10)

    tb.log.info("=== AXIS5 Master CG Basic Test PASSED ===")


def generate_axis5_master_cg_params():
    """Generate test parameters for AXIS5 master clock-gated."""
    return [
        (4, 32, 1, 0),  # Basic with wakeup
        (4, 64, 1, 0),  # 64-bit data
        (8, 32, 1, 1),  # With parity
    ]


@pytest.mark.parametrize(
    "skid_depth, data_width, enable_wakeup, enable_parity",
    generate_axis5_master_cg_params()
)
def test_axis5_master_cg(request, skid_depth, data_width, enable_wakeup, enable_parity):
    """AXIS5 master clock-gated test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axis5': 'rtl/amba/axis5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_shared': 'rtl/amba/shared',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "axis5_master_cg"

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "icg.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_shared'], "amba_clock_gate_ctrl.sv"),
        os.path.join(rtl_dict['rtl_axis5'], "axis5_master.sv"),
        os.path.join(rtl_dict['rtl_axis5'], "axis5_master_cg.sv"),
    ]

    # Test identifier
    sd_str = TBBase.format_dec(skid_depth, 1)
    dw_str = TBBase.format_dec(data_width, 2)
    wk_str = 'wk' if enable_wakeup else 'nw'
    test_name_plus_params = f"test_{worker_id}_axis5_master_cg_sd{sd_str}_dw{dw_str}_{wk_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes = [rtl_dict['rtl_amba_includes']]

    rtl_parameters = {
        'SKID_DEPTH': str(skid_depth),
        'AXIS_DATA_WIDTH': str(data_width),
        'AXIS_ID_WIDTH': '8',
        'AXIS_DEST_WIDTH': '4',
        'AXIS_USER_WIDTH': '1',
        'ENABLE_WAKEUP': str(enable_wakeup),
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
        'TEST_SKID_DEPTH': str(skid_depth),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_ENABLE_WAKEUP': str(enable_wakeup),
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
            testcase="cocotb_test_axis5_master_cg_basic",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
