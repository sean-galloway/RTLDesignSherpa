# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PeakRDLAdapterTB
# Purpose: Test for PeakRDL to CMD/RSP Adapter
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test for PeakRDL to CMD/RSP Adapter

Validates the generic adapter that bridges PeakRDL passthrough interface
to rtldesignsherpa cmd/rsp valid/ready protocol.

Author: RTL Design Sherpa Project
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles
from cocotb.regression import TestFactory
import pytest
import random
import os
import sys

# Import utilities (PYTHONPATH configured in env_python)
from CocoTBFramework.tbclasses.shared.utilities import get_paths
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


class PeakRDLAdapterTB:
    """Testbench for PeakRDL to CMD/RSP adapter"""

    def __init__(self, dut):
        self.dut = dut
        self.clk_period = 10  # ns

    async def reset(self):
        """Reset the DUT"""
        self.dut.aresetn.value = 0
        self.dut.cmd_valid.value = 0
        self.dut.rsp_ready.value = 0

        # PeakRDL register block interface - idle
        self.dut.regblk_req_stall_wr.value = 0
        self.dut.regblk_req_stall_rd.value = 0
        self.dut.regblk_rd_ack.value = 0
        self.dut.regblk_rd_err.value = 0
        self.dut.regblk_rd_data.value = 0
        self.dut.regblk_wr_ack.value = 0
        self.dut.regblk_wr_err.value = 0

        await ClockCycles(self.dut.aclk, 5)
        self.dut.aresetn.value = 1
        await ClockCycles(self.dut.aclk, 2)

    async def send_cmd(self, pwrite, paddr, pwdata=0, pstrb=0xF):
        """Send a command through cmd interface"""
        self.dut.cmd_valid.value = 1
        self.dut.cmd_pwrite.value = pwrite
        self.dut.cmd_paddr.value = paddr
        self.dut.cmd_pwdata.value = pwdata
        self.dut.cmd_pstrb.value = pstrb

        # Wait for ready
        while True:
            await RisingEdge(self.dut.aclk)
            if self.dut.cmd_ready.value == 1:
                break

        self.dut.cmd_valid.value = 0

    async def send_regblk_ack(self, is_write, data=0, error=0):
        """Simulate register block acknowledging request"""
        await RisingEdge(self.dut.aclk)
        if is_write:
            self.dut.regblk_wr_ack.value = 1
            self.dut.regblk_wr_err.value = error
        else:
            self.dut.regblk_rd_ack.value = 1
            self.dut.regblk_rd_err.value = error
            self.dut.regblk_rd_data.value = data

        await RisingEdge(self.dut.aclk)
        self.dut.regblk_wr_ack.value = 0
        self.dut.regblk_rd_ack.value = 0

    async def recv_rsp(self):
        """Receive response through rsp interface"""
        self.dut.rsp_ready.value = 1

        # Wait for valid
        while True:
            await RisingEdge(self.dut.aclk)
            if self.dut.rsp_valid.value == 1:
                break

        prdata = int(self.dut.rsp_prdata.value)
        pslverr = int(self.dut.rsp_pslverr.value)

        await RisingEdge(self.dut.aclk)
        self.dut.rsp_ready.value = 0

        return prdata, pslverr


@cocotb.test()
async def peakrdl_adapter_basic(dut):
    """Test basic read and write operations"""

    tb = PeakRDLAdapterTB(dut)

    # Start clock
    cocotb.start_soon(Clock(dut.aclk, tb.clk_period, units='ns').start())

    # Reset
    await tb.reset()

    dut._log.info("=== Test: Basic Write ===")

    # Start a write command in parallel with ack
    cocotb.start_soon(tb.send_cmd(pwrite=1, paddr=0x10, pwdata=0xDEADBEEF, pstrb=0xF))

    # Wait for regblk_req
    await RisingEdge(dut.aclk)
    while dut.regblk_req.value == 0:
        await RisingEdge(dut.aclk)

    # Verify request
    assert dut.regblk_req_is_wr.value == 1, "Expected write request"
    assert dut.regblk_addr.value == 0x10, f"Address mismatch: {hex(dut.regblk_addr.value)}"
    assert dut.regblk_wr_data.value == 0xDEADBEEF, "Write data mismatch"
    assert dut.regblk_wr_biten.value == 0xFFFFFFFF, "Bit enable should be all 1s for strb=0xF"

    # Send ack
    await tb.send_regblk_ack(is_write=True, error=0)

    # Receive response
    prdata, pslverr = await tb.recv_rsp()
    assert pslverr == 0, "Expected no error"

    dut._log.info("✓ Basic write passed")

    dut._log.info("=== Test: Basic Read ===")

    # Start a read command
    cocotb.start_soon(tb.send_cmd(pwrite=0, paddr=0x20))

    # Wait for regblk_req
    await RisingEdge(dut.aclk)
    while dut.regblk_req.value == 0:
        await RisingEdge(dut.aclk)

    # Verify request
    assert dut.regblk_req_is_wr.value == 0, "Expected read request"
    assert dut.regblk_addr.value == 0x20, f"Address mismatch: {hex(dut.regblk_addr.value)}"

    # Send ack with data
    await tb.send_regblk_ack(is_write=False, data=0xCAFEBABE, error=0)

    # Receive response
    prdata, pslverr = await tb.recv_rsp()
    assert prdata == 0xCAFEBABE, f"Read data mismatch: {hex(prdata)}"
    assert pslverr == 0, "Expected no error"

    dut._log.info("✓ Basic read passed")


@cocotb.test()
async def peakrdl_adapter_backpressure(dut):
    """Test backpressure handling"""

    tb = PeakRDLAdapterTB(dut)

    # Start clock
    cocotb.start_soon(Clock(dut.aclk, tb.clk_period, units='ns').start())

    # Reset
    await tb.reset()

    dut._log.info("=== Test: Response Backpressure ===")

    # Keep rsp_ready low to create backpressure
    dut.rsp_ready.value = 0

    # Send write command
    cocotb.start_soon(tb.send_cmd(pwrite=1, paddr=0x30, pwdata=0x12345678))

    # Wait for regblk_req
    await RisingEdge(dut.aclk)
    while dut.regblk_req.value == 0:
        await RisingEdge(dut.aclk)

    # Send ack
    await tb.send_regblk_ack(is_write=True, error=0)

    # Response should be valid but held
    await ClockCycles(dut.aclk, 3)
    assert dut.rsp_valid.value == 1, "Response should be valid"

    # Now accept response
    prdata, pslverr = await tb.recv_rsp()
    assert pslverr == 0

    dut._log.info("✓ Backpressure test passed")


@cocotb.test()
async def peakrdl_adapter_byte_strobes(dut):
    """Test byte strobe to bit enable conversion"""

    tb = PeakRDLAdapterTB(dut)

    # Start clock
    cocotb.start_soon(Clock(dut.aclk, tb.clk_period, units='ns').start())

    # Reset
    await tb.reset()

    dut._log.info("=== Test: Byte Strobes ===")

    # Test different strobe patterns
    test_cases = [
        (0x1, 0x000000FF),  # Byte 0
        (0x2, 0x0000FF00),  # Byte 1
        (0x4, 0x00FF0000),  # Byte 2
        (0x8, 0xFF000000),  # Byte 3
        (0x3, 0x0000FFFF),  # Bytes 0-1
        (0xC, 0xFFFF0000),  # Bytes 2-3
        (0xF, 0xFFFFFFFF),  # All bytes
    ]

    for pstrb, expected_biten in test_cases:
        cocotb.start_soon(tb.send_cmd(pwrite=1, paddr=0x40, pwdata=0xAAAAAAAA, pstrb=pstrb))

        # Wait for regblk_req
        await RisingEdge(dut.aclk)
        while dut.regblk_req.value == 0:
            await RisingEdge(dut.aclk)

        actual_biten = int(dut.regblk_wr_biten.value)
        assert actual_biten == expected_biten, \
            f"Strobe {hex(pstrb)}: Expected biten {hex(expected_biten)}, got {hex(actual_biten)}"

        # Send ack
        await tb.send_regblk_ack(is_write=True, error=0)

        # Receive response
        await tb.recv_rsp()

    dut._log.info("✓ Byte strobe conversion passed")


@cocotb.test()
async def peakrdl_adapter_stress(dut):
    """Stress test with 300 random transactions"""

    tb = PeakRDLAdapterTB(dut)

    # Start clock
    cocotb.start_soon(Clock(dut.aclk, tb.clk_period, units='ns').start())

    # Reset
    await tb.reset()

    dut._log.info("=== Test: Stress Test (300 transactions) ===")

    num_transactions = 300
    for i in range(num_transactions):
        # Randomize transaction type, address, data, strobes
        pwrite = random.randint(0, 1)
        paddr = random.randint(0, 0xFFF) & ~0x3  # Word-aligned
        pwdata = random.randint(0, 0xFFFFFFFF)
        pstrb = random.randint(1, 0xF)  # At least one byte enabled

        # Send command
        cocotb.start_soon(tb.send_cmd(pwrite=pwrite, paddr=paddr, pwdata=pwdata, pstrb=pstrb))

        # Wait for regblk_req
        await RisingEdge(dut.aclk)
        while dut.regblk_req.value == 0:
            await RisingEdge(dut.aclk)

        # Verify request was propagated correctly
        assert dut.regblk_req_is_wr.value == pwrite, f"Transaction {i}: Write flag mismatch"
        assert dut.regblk_addr.value == paddr, f"Transaction {i}: Address mismatch"

        if pwrite:
            assert dut.regblk_wr_data.value == pwdata, f"Transaction {i}: Write data mismatch"
            # Send write ack (with occasional errors)
            error = 1 if random.randint(0, 99) < 5 else 0  # 5% error rate
            await tb.send_regblk_ack(is_write=True, error=error)
        else:
            # Send read ack with random data
            read_data = random.randint(0, 0xFFFFFFFF)
            error = 1 if random.randint(0, 99) < 5 else 0  # 5% error rate
            await tb.send_regblk_ack(is_write=False, data=read_data, error=error)

        # Receive response
        prdata, pslverr = await tb.recv_rsp()

        if not pwrite:
            # Verify read data matches
            assert prdata == read_data, f"Transaction {i}: Read data mismatch"

        # Verify error flag
        assert pslverr == error, f"Transaction {i}: Error flag mismatch"

        # Progress indicator every 50 transactions
        if (i + 1) % 50 == 0:
            dut._log.info(f"  Completed {i + 1}/{num_transactions} transactions")

    dut._log.info(f"✓ Stress test passed: {num_transactions} transactions")


# ==============================================================================
# Pytest Integration
# ==============================================================================

def test_peakrdl_to_cmdrsp():
    """Pytest entry point for PeakRDL adapter test"""

    # Get directory and module information using repository standard
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
    })

    sim_build = os.path.join(tests_dir, 'local_sim_build', 'test_peakrdl_to_cmdrsp')

    os.makedirs(sim_build, exist_ok=True)

    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/converters/rtl/filelists/peakrdl_to_cmdrsp.f'
    )

    # Parameters
    parameters = {
        'ADDR_WIDTH': 12,
        'DATA_WIDTH': 32
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    extra_env = {}
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    # Run test
    run(
        python_search=[tests_dir],  # Key: Let cocotb find the module
        verilog_sources=verilog_sources,
        toplevel='peakrdl_to_cmdrsp',
        module='test_peakrdl_to_cmdrsp',
        parameters=parameters,
        includes=includes,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,  # VCD controlled by compile_args, not cocotb-test
        keep_files=True,
        compile_args=compile_args,
        sim_args=sim_args,
        plusargs=plusargs,
    )


if __name__ == '__main__':
    test_peakrdl_to_cmdrsp()
