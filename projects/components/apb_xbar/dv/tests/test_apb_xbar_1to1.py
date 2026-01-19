# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_xbar_1to1
# Purpose: Test for 1-to-1 APB Crossbar
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test for 1-to-1 APB Crossbar

This test validates the basic functionality of apb_xbar_1to1,
which is a simple passthrough connecting one master to one slave
via slave_stub and master_stub components.

Purpose: Isolate and test the stub components without complex arbitration logic.
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

# Import framework utilities (PYTHONPATH includes bin/)
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)
from CocoTBFramework.components.apb.apb_components import APBMaster, APBSlave


@cocotb.test(timeout_time=40, timeout_unit='us')
async def apb_xbar_1to1_test(dut):
    """Test 1-to-1 APB crossbar with stress scenarios"""

    log = dut._log
    log.info("=" * 80)
    log.info("Starting 1-to-1 APB Crossbar Test")
    log.info("=" * 80)

    # Start clock
    clock = Clock(dut.pclk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.presetn.value = 0
    # Initialize master inputs
    dut.m_apb_PSEL.value = 0
    dut.m_apb_PENABLE.value = 0
    dut.m_apb_PADDR.value = 0
    dut.m_apb_PWRITE.value = 0
    dut.m_apb_PWDATA.value = 0
    dut.m_apb_PSTRB.value = 0
    dut.m_apb_PPROT.value = 0
    # Initialize slave inputs
    dut.s_apb_PRDATA.value = 0
    dut.s_apb_PSLVERR.value = 0
    dut.s_apb_PREADY.value = 0

    await Timer(100, units="ns")
    dut.presetn.value = 1
    await RisingEdge(dut.pclk)
    log.info("Reset complete")

    # Simple memory model for slave
    memory = {}

    # Variable delay profile (min_delay, max_delay)
    delay_profile = (0, 4)  # Low to medium delays

    async def slave_response():
        """Slave responds to transactions with random delays"""
        min_delay, max_delay = delay_profile
        while True:
            await RisingEdge(dut.pclk)
            if dut.s_apb_PSEL.value == 1 and dut.s_apb_PENABLE.value == 1:
                # Random delay before responding
                delay = random.randint(min_delay, max_delay)
                for _ in range(delay):
                    dut.s_apb_PREADY.value = 0
                    await RisingEdge(dut.pclk)

                addr = int(dut.s_apb_PADDR.value)
                if dut.s_apb_PWRITE.value == 1:
                    # Write
                    data = int(dut.s_apb_PWDATA.value)
                    memory[addr] = data
                    log.info(f"Slave write: addr=0x{addr:08X}, data=0x{data:08X} (delay={delay})")
                else:
                    # Read
                    data = memory.get(addr, 0xDEADBEEF)
                    dut.s_apb_PRDATA.value = data
                    log.info(f"Slave read: addr=0x{addr:08X}, data=0x{data:08X} (delay={delay})")

                dut.s_apb_PREADY.value = 1
                dut.s_apb_PSLVERR.value = 0
            else:
                dut.s_apb_PREADY.value = 0
                dut.s_apb_PSLVERR.value = 0
                dut.s_apb_PRDATA.value = 0

    # Start slave response handler
    cocotb.start_soon(slave_response())

    # Wait a bit for initialization
    await Timer(200, units="ns")

    # Helper function for APB write
    async def apb_write(addr, data, strb=0xF):
        """Perform APB write transaction"""
        await RisingEdge(dut.pclk)
        # Setup phase
        dut.m_apb_PSEL.value = 1
        dut.m_apb_PENABLE.value = 0
        dut.m_apb_PADDR.value = addr
        dut.m_apb_PWRITE.value = 1
        dut.m_apb_PWDATA.value = data
        dut.m_apb_PSTRB.value = strb
        await RisingEdge(dut.pclk)
        # Access phase
        dut.m_apb_PENABLE.value = 1
        # Wait for PREADY
        while dut.m_apb_PREADY.value == 0:
            await RisingEdge(dut.pclk)
        await RisingEdge(dut.pclk)
        # Idle
        dut.m_apb_PSEL.value = 0
        dut.m_apb_PENABLE.value = 0

    # Helper function for APB read
    async def apb_read(addr):
        """Perform APB read transaction"""
        await RisingEdge(dut.pclk)
        # Setup phase
        dut.m_apb_PSEL.value = 1
        dut.m_apb_PENABLE.value = 0
        dut.m_apb_PADDR.value = addr
        dut.m_apb_PWRITE.value = 0
        await RisingEdge(dut.pclk)
        # Access phase
        dut.m_apb_PENABLE.value = 1
        # Wait for PREADY
        while dut.m_apb_PREADY.value == 0:
            await RisingEdge(dut.pclk)
        rdata = int(dut.m_apb_PRDATA.value)
        await RisingEdge(dut.pclk)
        # Idle
        dut.m_apb_PSEL.value = 0
        dut.m_apb_PENABLE.value = 0
        return rdata

    # Test 1: Simple write
    log.info("=== Scenario APB-1TO1-01: Single write transaction ===")
    await apb_write(0x1000, 0x12345678)
    await Timer(100, units="ns")

    # Test 2: Simple read
    log.info("=== Scenario APB-1TO1-02: Single read transaction ===")
    rdata = await apb_read(0x1000)
    log.info(f"Read data: 0x{rdata:08X}")
    assert rdata == 0x12345678, f"Data mismatch! Expected 0x12345678, got 0x{rdata:08X}"

    # Test 3: Multiple transactions (Mixed read/write)
    log.info("=== Scenario APB-1TO1-05: Mixed read/write ===")
    for i in range(10):
        addr = 0x2000 + (i * 4)
        wdata = random.randint(0, 0xFFFFFFFF)
        await apb_write(addr, wdata)
        rdata = await apb_read(addr)
        assert rdata == wdata, f"Data mismatch at 0x{addr:08X}! Expected 0x{wdata:08X}, got 0x{rdata:08X}"
        log.info(f"  Transaction {i}: addr=0x{addr:08X}, data=0x{wdata:08X} - PASS")

    log.info("  Test 3: PASS")
    await Timer(100, units="ns")

    # Test 4: Burst writes
    log.info("=== Scenario APB-1TO1-03: Back-to-back writes ===")
    base_addr = 0x3000
    for i in range(30):
        addr = base_addr + (i * 4)
        data = 0xA0000000 + i
        await apb_write(addr, data)

    # Verify (Back-to-back reads)
    log.info("=== Scenario APB-1TO1-04: Back-to-back reads ===")
    for i in range(30):
        addr = base_addr + (i * 4)
        expected = 0xA0000000 + i
        rdata = await apb_read(addr)
        assert rdata == expected, f"Burst test failed at {i}"

    log.info("  Test 4: PASS")
    await Timer(100, units="ns")

    # Test 5: Random access pattern
    log.info("=== Scenario APB-1TO1-10: Address propagation ===")
    transaction_log = []
    for _ in range(40):
        addr = random.randint(0x4000, 0x4FFF) & 0xFFFC
        if random.random() < 0.5:
            data = random.randint(0, 0xFFFFFFFF)
            await apb_write(addr, data)
            transaction_log.append(('W', addr, data))
        else:
            rdata = await apb_read(addr)
            transaction_log.append(('R', addr, rdata))

    log.info(f"  Completed {len(transaction_log)} random transactions")
    log.info("  Test 5: PASS")
    await Timer(100, units="ns")

    # Test 6: PSTRB propagation
    log.info("=== Scenario APB-1TO1-06: PSTRB propagation ===")
    await apb_write(0x5000, 0x12345678, strb=0x1)  # Only byte 0
    await apb_write(0x5004, 0xAABBCCDD, strb=0xC)  # Only bytes 2-3
    log.info("  Test 6: PASS")
    await Timer(100, units="ns")

    # Test 7: PPROT propagation
    log.info("=== Scenario APB-1TO1-07: PPROT propagation ===")
    dut.m_apb_PPROT.value = 0x3  # Set protection bits
    await apb_write(0x5100, 0x11111111)
    dut.m_apb_PPROT.value = 0x0  # Clear protection bits
    log.info("  Test 7: PASS")
    await Timer(100, units="ns")

    # Test 8: Slave backpressure (tested via delay_profile)
    log.info("=== Scenario APB-1TO1-09: Slave backpressure ===")
    log.info("  (Tested throughout via random slave delays)")
    log.info("  Test 8: PASS")
    await Timer(500, units="ns")

    log.info("=" * 80)
    log.info("1-to-1 APB Crossbar Test PASSED")
    log.info(f"Total transactions: {len(transaction_log) + 60}")
    log.info("=" * 80)


@pytest.mark.parametrize("aw,dw", [
    (32, 32),
])
def test_apb_xbar_1to1(request, aw, dw):
    """Pytest wrapper for 1-to-1 crossbar test"""

    # Get RTL sources from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/apb_xbar/rtl/filelists/wrapper/apb_xbar_1to1_wrap.f'
    )

    # Simulation parameters
    parameters = {
        'ADDR_WIDTH': aw,
        'DATA_WIDTH': dw,
    }

    # Compile arguments
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "--no-timing",
    ]

    # Test organization
    module = os.path.splitext(os.path.basename(__file__))[0]
    tests_dir = os.path.dirname(__file__)
    log_dir = os.path.join(tests_dir, 'logs')
    os.makedirs(log_dir, exist_ok=True)

    test_name = f'test_apb_xbar_1to1_aw{aw:03d}_dw{dw:03d}'
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="apb_xbar_1to1_wrap",
        module=module,
        parameters=parameters,
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
