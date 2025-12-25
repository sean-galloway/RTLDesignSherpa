# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axis5_slave
# Purpose: Test runner for AXIS5 slave with AMBA5 extensions
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Slave Test Runner

Tests AXIS5 slave functionality with AMBA5 extensions:
- TWAKEUP: Wake-up signaling
- TPARITY: Data parity protection
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class AXIS5SlaveBasicTB(TBBase):
    """Basic AXIS5 slave testbench for RTL verification."""

    def __init__(self, dut):
        TBBase.__init__(self, dut)
        self.SKID_DEPTH = self.convert_to_int(os.environ.get('TEST_SKID_DEPTH', '4'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.DEST_WIDTH = self.convert_to_int(os.environ.get('TEST_DEST_WIDTH', '4'))
        self.USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.ENABLE_WAKEUP = self.convert_to_int(os.environ.get('TEST_ENABLE_WAKEUP', '1')) == 1
        self.ENABLE_PARITY = self.convert_to_int(os.environ.get('TEST_ENABLE_PARITY', '0')) == 1
        self.STRB_WIDTH = self.DATA_WIDTH // 8

        self.log.info("="*60)
        self.log.info(" AXIS5 Slave Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" SKID_DEPTH:    {self.SKID_DEPTH}")
        self.log.info(f" DATA_WIDTH:    {self.DATA_WIDTH}")
        self.log.info(f" ID_WIDTH:      {self.ID_WIDTH}")
        self.log.info(f" DEST_WIDTH:    {self.DEST_WIDTH}")
        self.log.info(f" USER_WIDTH:    {self.USER_WIDTH}")
        self.log.info(f" ENABLE_WAKEUP: {self.ENABLE_WAKEUP}")
        self.log.info(f" ENABLE_PARITY: {self.ENABLE_PARITY}")
        self.log.info("="*60)

    async def assert_reset(self):
        """Assert reset."""
        self.dut.aresetn.value = 0
        await self.wait_clocks('aclk', 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset."""
        self.dut.aresetn.value = 1
        await self.wait_clocks('aclk', 5)
        self.log.info("Reset deasserted")

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock('aclk', 10, 'ns')
        await self.assert_reset()
        await self.deassert_reset()

    async def drive_axis_packet(self, data, last=1, id=0, dest=0, user=0, wakeup=0, strb=None):
        """Drive a packet through the AXIS slave interface."""
        # Wait for ready
        while not self.dut.s_axis_tready.value:
            await RisingEdge(self.dut.aclk)

        # Drive AXIS signals
        self.dut.s_axis_tvalid.value = 1
        self.dut.s_axis_tdata.value = data
        self.dut.s_axis_tlast.value = last
        self.dut.s_axis_tstrb.value = strb if strb else (1 << self.STRB_WIDTH) - 1

        if hasattr(self.dut, 's_axis_tid'):
            self.dut.s_axis_tid.value = id
        if hasattr(self.dut, 's_axis_tdest'):
            self.dut.s_axis_tdest.value = dest
        if hasattr(self.dut, 's_axis_tuser'):
            self.dut.s_axis_tuser.value = user
        if hasattr(self.dut, 's_axis_twakeup'):
            self.dut.s_axis_twakeup.value = wakeup

        await RisingEdge(self.dut.aclk)
        self.dut.s_axis_tvalid.value = 0

        self.log.info(f"AXIS packet sent: data=0x{data:08X}, last={last}, wakeup={wakeup}")

    async def wait_for_fub_transaction(self, timeout_cycles=100):
        """Wait for FUB transaction to complete."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            if self.dut.fub_axis_tvalid.value and self.dut.fub_axis_tready.value:
                return True
        return False


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_axis5_slave_basic(dut):
    """Basic AXIS5 slave test - verifies AXIS to FUB conversion."""
    tb = AXIS5SlaveBasicTB(dut)

    # Setup
    await tb.setup_clocks_and_reset()

    # Configure FUB side (drive TREADY high)
    dut.fub_axis_tready.value = 1

    await tb.wait_clocks('aclk', 5)

    # Test 1: Basic data transfer
    tb.log.info("=== Test 1: Basic Data Transfer ===")
    await tb.drive_axis_packet(data=0x12345678, last=1)
    success = await tb.wait_for_fub_transaction()
    assert success, "Data transfer timeout"
    await tb.wait_clocks('aclk', 10)

    # Test 2: Multiple packets
    tb.log.info("=== Test 2: Multiple Packets ===")
    for i in range(5):
        data = 0xABCD0000 + i
        await tb.drive_axis_packet(data=data, last=1, id=i)
        success = await tb.wait_for_fub_transaction()
        assert success, f"Packet {i} timeout"
        await tb.wait_clocks('aclk', 5)

    # Test 3: Wakeup signaling (if enabled)
    tb.log.info("=== Test 3: Wakeup Signaling ===")
    if hasattr(dut, 's_axis_twakeup'):
        await tb.drive_axis_packet(data=0xFEED0001, last=1, wakeup=1)
        success = await tb.wait_for_fub_transaction()
        assert success, "Wakeup transfer timeout"
        await tb.wait_clocks('aclk', 10)

    tb.log.info("=== AXIS5 Slave Basic Test PASSED ===")


def generate_axis5_slave_params():
    """Generate test parameters for AXIS5 slave."""
    return [
        # skid_depth, data_width, id_width, dest_width, user_width, enable_wakeup, enable_parity
        (4, 32, 8, 4, 1, 1, 0),  # Basic with wakeup
        (4, 64, 8, 4, 1, 1, 0),  # 64-bit data
        (8, 32, 8, 4, 1, 1, 1),  # With parity
    ]


@pytest.mark.parametrize(
    "skid_depth, data_width, id_width, dest_width, user_width, enable_wakeup, enable_parity",
    generate_axis5_slave_params()
)
def test_axis5_slave(request, skid_depth, data_width, id_width, dest_width, user_width,
                     enable_wakeup, enable_parity):
    """AXIS5 slave test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axis5': 'rtl/amba/axis5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "axis5_slave"

    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axis5'], "axis5_slave.sv"),
    ]

    # Test identifier
    sd_str = TBBase.format_dec(skid_depth, 1)
    dw_str = TBBase.format_dec(data_width, 2)
    wk_str = 'wk' if enable_wakeup else 'nw'
    pr_str = 'pr' if enable_parity else 'np'
    test_name_plus_params = f"test_{worker_id}_axis5_slave_sd{sd_str}_dw{dw_str}_{wk_str}_{pr_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes = [rtl_dict['rtl_amba_includes']]

    # RTL parameters
    rtl_parameters = {
        'SKID_DEPTH': str(skid_depth),
        'AXIS_DATA_WIDTH': str(data_width),
        'AXIS_ID_WIDTH': str(id_width),
        'AXIS_DEST_WIDTH': str(dest_width),
        'AXIS_USER_WIDTH': str(user_width),
        'ENABLE_WAKEUP': str(enable_wakeup),
        'ENABLE_PARITY': str(enable_parity),
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
        'TEST_SKID_DEPTH': str(skid_depth),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_ID_WIDTH': str(id_width),
        'TEST_DEST_WIDTH': str(dest_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_ENABLE_WAKEUP': str(enable_wakeup),
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
            testcase="cocotb_test_axis5_slave_basic",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
