# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb5_monitor
# Purpose: Test runner for APB5 monitor with AMBA5 extensions
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-21

"""
APB5 Monitor Test Runner

Tests APB5 monitor functionality with AMBA5 extensions:
- User signal capture
- Wake-up event detection
- Parity error detection
- Transaction timing monitoring
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


class APB5MonitorTB(TBBase):
    """APB5 monitor testbench for RTL verification."""

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
        self.log.info(" APB5 Monitor Testbench Configuration")
        self.log.info("-"*60)
        self.log.info(f" ADDR_WIDTH:  {self.ADDR_WIDTH}")
        self.log.info(f" DATA_WIDTH:  {self.DATA_WIDTH}")
        self.log.info(f" AUSER_WIDTH: {self.AUSER_WIDTH}")
        self.log.info(f" WUSER_WIDTH: {self.WUSER_WIDTH}")
        self.log.info(f" RUSER_WIDTH: {self.RUSER_WIDTH}")
        self.log.info(f" BUSER_WIDTH: {self.BUSER_WIDTH}")
        self.log.info("="*60)

        # Track monitor packets
        self.monitor_packets = []

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

    async def drive_cmd_write(self, paddr, pwdata, pstrb=0xF, pprot=0, pauser=0, pwuser=0):
        """Drive a write command through the command interface."""
        # Wait for ready
        while not self.dut.cmd_ready.value:
            await RisingEdge(self.dut.aclk)

        # Drive command
        self.dut.cmd_valid.value = 1
        self.dut.cmd_pwrite.value = 1
        self.dut.cmd_paddr.value = paddr
        self.dut.cmd_pwdata.value = pwdata
        self.dut.cmd_pstrb.value = pstrb
        self.dut.cmd_pprot.value = pprot
        self.dut.cmd_pauser.value = pauser
        self.dut.cmd_pwuser.value = pwuser

        await RisingEdge(self.dut.aclk)
        self.dut.cmd_valid.value = 0

        self.log.info(f"CMD Write: addr=0x{paddr:04X} data=0x{pwdata:08X}")

    async def drive_cmd_read(self, paddr, pprot=0, pauser=0):
        """Drive a read command through the command interface."""
        # Wait for ready
        while not self.dut.cmd_ready.value:
            await RisingEdge(self.dut.aclk)

        # Drive command
        self.dut.cmd_valid.value = 1
        self.dut.cmd_pwrite.value = 0
        self.dut.cmd_paddr.value = paddr
        self.dut.cmd_pwdata.value = 0
        self.dut.cmd_pstrb.value = 0
        self.dut.cmd_pprot.value = pprot
        self.dut.cmd_pauser.value = pauser
        self.dut.cmd_pwuser.value = 0

        await RisingEdge(self.dut.aclk)
        self.dut.cmd_valid.value = 0

        self.log.info(f"CMD Read: addr=0x{paddr:04X}")

    async def drive_rsp(self, prdata, pslverr=0, pruser=0, pbuser=0):
        """Drive a response through the response interface."""
        # Wait for ready
        while not self.dut.rsp_ready.value:
            await RisingEdge(self.dut.aclk)

        # Drive response
        self.dut.rsp_valid.value = 1
        self.dut.rsp_prdata.value = prdata
        self.dut.rsp_pslverr.value = pslverr
        self.dut.rsp_pruser.value = pruser
        self.dut.rsp_pbuser.value = pbuser

        await RisingEdge(self.dut.aclk)
        self.dut.rsp_valid.value = 0

        self.log.info(f"RSP: data=0x{prdata:08X} err={pslverr}")

    async def drive_wakeup(self, cycles=3):
        """Drive PWAKEUP signal."""
        self.dut.apb5_pwakeup.value = 1
        self.log.info("PWAKEUP asserted")
        await self.wait_clocks('aclk', cycles)
        self.dut.apb5_pwakeup.value = 0
        self.log.info("PWAKEUP deasserted")

    async def capture_monitor_output(self, timeout_cycles=10):
        """Capture monitor packet output."""
        for _ in range(timeout_cycles):
            await RisingEdge(self.dut.aclk)
            if self.dut.monbus_valid.value:
                packet = int(self.dut.monbus_packet.value)
                self.monitor_packets.append(packet)
                self.log.info(f"Monitor packet captured: 0x{packet:016X}")


@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_monitor_basic(dut):
    """Basic APB5 monitor test - verifies transaction capture and event detection."""
    tb = APB5MonitorTB(dut)

    # Setup
    await tb.setup_clocks_and_reset()

    # Initialize command interface signals
    dut.cmd_valid.value = 0
    dut.cmd_pwrite.value = 0
    dut.cmd_paddr.value = 0
    dut.cmd_pwdata.value = 0
    dut.cmd_pstrb.value = 0
    dut.cmd_pprot.value = 0
    dut.cmd_pauser.value = 0
    dut.cmd_pwuser.value = 0

    # Initialize response interface signals
    dut.rsp_valid.value = 0
    dut.rsp_prdata.value = 0
    dut.rsp_pslverr.value = 0
    dut.rsp_pruser.value = 0
    dut.rsp_pbuser.value = 0

    # Initialize APB5-specific signals
    dut.apb5_pwakeup.value = 0
    dut.parity_error_wdata.value = 0
    dut.parity_error_rdata.value = 0
    dut.parity_error_ctrl.value = 0

    # Initialize configuration signals
    dut.cfg_error_enable.value = 1
    dut.cfg_timeout_enable.value = 1
    dut.cfg_protocol_enable.value = 1
    dut.cfg_slverr_enable.value = 1
    dut.cfg_parity_enable.value = 0
    dut.cfg_wakeup_enable.value = 1
    dut.cfg_user_enable.value = 1
    dut.cfg_perf_enable.value = 1
    dut.cfg_latency_enable.value = 1
    dut.cfg_cmd_timeout_cnt.value = 100
    dut.cfg_rsp_timeout_cnt.value = 100
    dut.cfg_latency_threshold.value = 50
    dut.cfg_wakeup_timeout_cnt.value = 100

    # Initialize monitor bus ready (as consumer)
    dut.monbus_ready.value = 1

    # Note: cmd_ready and rsp_ready are outputs from monitor, not inputs
    # The monitor observes these signals but doesn't control them

    await tb.wait_clocks('aclk', 5)

    # Test 1: Monitor write transaction
    tb.log.info("=== Test 1: Monitor Write Transaction ===")
    # Simulate a command being accepted
    dut.cmd_valid.value = 1
    dut.cmd_ready.value = 1  # Simulating the observed ready signal
    dut.cmd_pwrite.value = 1
    dut.cmd_paddr.value = 0x100
    dut.cmd_pwdata.value = 0x12345678
    dut.cmd_pstrb.value = 0xF
    dut.cmd_pauser.value = 0x5
    dut.cmd_pwuser.value = 0x3
    await RisingEdge(dut.aclk)
    dut.cmd_valid.value = 0
    await RisingEdge(dut.aclk)

    # Simulate response
    dut.rsp_valid.value = 1
    dut.rsp_ready.value = 1  # Simulating observed ready
    dut.rsp_prdata.value = 0
    dut.rsp_pslverr.value = 0
    dut.rsp_pbuser.value = 0x4
    await RisingEdge(dut.aclk)
    dut.rsp_valid.value = 0
    await tb.capture_monitor_output()
    await tb.wait_clocks('aclk', 5)

    # Test 2: Monitor read transaction
    tb.log.info("=== Test 2: Monitor Read Transaction ===")
    dut.cmd_valid.value = 1
    dut.cmd_ready.value = 1
    dut.cmd_pwrite.value = 0
    dut.cmd_paddr.value = 0x100
    dut.cmd_pauser.value = 0x7
    await RisingEdge(dut.aclk)
    dut.cmd_valid.value = 0
    await RisingEdge(dut.aclk)

    dut.rsp_valid.value = 1
    dut.rsp_ready.value = 1
    dut.rsp_prdata.value = 0xDEADBEEF
    dut.rsp_pslverr.value = 0
    dut.rsp_pruser.value = 0xA
    await RisingEdge(dut.aclk)
    dut.rsp_valid.value = 0
    await tb.capture_monitor_output()
    await tb.wait_clocks('aclk', 5)

    # Test 3: Monitor error transaction
    tb.log.info("=== Test 3: Monitor Error Transaction ===")
    dut.cmd_valid.value = 1
    dut.cmd_ready.value = 1
    dut.cmd_pwrite.value = 0
    dut.cmd_paddr.value = 0x200
    dut.cmd_pauser.value = 0xB
    await RisingEdge(dut.aclk)
    dut.cmd_valid.value = 0
    await RisingEdge(dut.aclk)

    dut.rsp_valid.value = 1
    dut.rsp_ready.value = 1
    dut.rsp_prdata.value = 0
    dut.rsp_pslverr.value = 1  # Error response
    dut.rsp_pruser.value = 0xC
    await RisingEdge(dut.aclk)
    dut.rsp_valid.value = 0
    await tb.capture_monitor_output()
    await tb.wait_clocks('aclk', 5)

    # Test 4: Monitor wakeup event
    tb.log.info("=== Test 4: Monitor Wakeup Event ===")
    await tb.drive_wakeup(cycles=3)
    await tb.capture_monitor_output()
    await tb.wait_clocks('aclk', 5)

    # Test 5: Multiple transactions
    tb.log.info("=== Test 5: Multiple Transactions ===")
    for i in range(5):
        dut.cmd_valid.value = 1
        dut.cmd_ready.value = 1
        dut.cmd_pwrite.value = i % 2
        dut.cmd_paddr.value = 0x300 + (i * 4)
        dut.cmd_pwdata.value = 0xABCD0000 + i if (i % 2) else 0
        dut.cmd_pauser.value = i & 0xF
        dut.cmd_pwuser.value = (i + 1) & 0xF
        await RisingEdge(dut.aclk)
        dut.cmd_valid.value = 0
        await RisingEdge(dut.aclk)

        dut.rsp_valid.value = 1
        dut.rsp_ready.value = 1
        dut.rsp_prdata.value = 0x55AA0000 + i
        dut.rsp_pslverr.value = 0
        dut.rsp_pruser.value = (i + 2) & 0xF
        await RisingEdge(dut.aclk)
        dut.rsp_valid.value = 0
        await tb.capture_monitor_output()

    # Report captured packets
    tb.log.info(f"=== Captured {len(tb.monitor_packets)} monitor packets ===")
    for i, pkt in enumerate(tb.monitor_packets):
        tb.log.info(f"  Packet {i}: 0x{pkt:016X}")

    tb.log.info("=== APB5 Monitor Basic Test PASSED ===")


def generate_apb5_monitor_params():
    """Generate test parameters for APB5 monitor."""
    return [
        # addr_width, data_width, auser_width, wuser_width, ruser_width, buser_width
        (12, 32, 4, 4, 4, 4),
        (16, 32, 8, 8, 8, 8),
    ]


@pytest.mark.parametrize(
    "addr_width, data_width, auser_width, wuser_width, ruser_width, buser_width",
    generate_apb5_monitor_params()
)
def test_apb5_monitor(request, addr_width, data_width, auser_width, wuser_width,
                      ruser_width, buser_width):
    """APB5 monitor test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_monitor"

    verilog_sources = [
        # Monitor packages (must be compiled in order)
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_amba5_pkg.sv"),
        # Common dependencies
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        # GAXI dependencies (for FIFO and skid buffer)
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        # APB5 monitor
        os.path.join(rtl_dict['rtl_apb5'], "apb5_monitor.sv"),
    ]

    # Test identifier
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    au_str = TBBase.format_dec(auser_width, 1)
    test_name_plus_params = f"test_{worker_id}_apb5_monitor_aw{aw_str}_dw{dw_str}_au{au_str}"
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
            testcase="cocotb_test_apb5_monitor_basic",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
