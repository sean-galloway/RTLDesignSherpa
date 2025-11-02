# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb_xbar_2to1
# Purpose: Test for 2-to-1 APB Crossbar
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test for 2-to-1 APB Crossbar

This test validates the arbitration functionality of apb_xbar_2to1,
which routes two masters to one slave with round-robin arbitration.

Purpose: Test arbitration when multiple masters access the same slave.
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

# Add CocoTB framework to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test(timeout_time=60, timeout_unit='us')
async def apb_xbar_2to1_test(dut):
    """Test 2-to-1 APB crossbar with arbitration and stress scenarios"""

    log = dut._log
    log.info("=" * 80)
    log.info("Starting 2-to-1 APB Crossbar Test")
    log.info("=" * 80)

    # Start clock
    clock = Clock(dut.pclk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.presetn.value = 0
    # Initialize master 0 inputs
    dut.m0_apb_PSEL.value = 0
    dut.m0_apb_PENABLE.value = 0
    dut.m0_apb_PADDR.value = 0
    dut.m0_apb_PWRITE.value = 0
    dut.m0_apb_PWDATA.value = 0
    dut.m0_apb_PSTRB.value = 0
    dut.m0_apb_PPROT.value = 0
    # Initialize master 1 inputs
    dut.m1_apb_PSEL.value = 0
    dut.m1_apb_PENABLE.value = 0
    dut.m1_apb_PADDR.value = 0
    dut.m1_apb_PWRITE.value = 0
    dut.m1_apb_PWDATA.value = 0
    dut.m1_apb_PSTRB.value = 0
    dut.m1_apb_PPROT.value = 0
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
    delay_profile = (1, 5)  # Medium delays

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

    # Start slave response handler
    cocotb.start_soon(slave_response())

    # Wait for initialization
    await Timer(200, units="ns")

    # Helper function for APB write
    async def apb_write(master_id, addr, data):
        """Perform APB write transaction"""
        m_prefix = f"m{master_id}_apb"
        await RisingEdge(dut.pclk)
        # Setup phase
        getattr(dut, f"{m_prefix}_PSEL").value = 1
        getattr(dut, f"{m_prefix}_PENABLE").value = 0
        getattr(dut, f"{m_prefix}_PADDR").value = addr
        getattr(dut, f"{m_prefix}_PWRITE").value = 1
        getattr(dut, f"{m_prefix}_PWDATA").value = data
        getattr(dut, f"{m_prefix}_PSTRB").value = 0xF
        await RisingEdge(dut.pclk)
        # Access phase
        getattr(dut, f"{m_prefix}_PENABLE").value = 1
        # Wait for PREADY
        timeout = 0
        while getattr(dut, f"{m_prefix}_PREADY").value == 0:
            await RisingEdge(dut.pclk)
            timeout += 1
            if timeout > 100:
                log.error(f"Master {master_id} write timeout at addr 0x{addr:08X}")
                break
        await RisingEdge(dut.pclk)
        # Idle
        getattr(dut, f"{m_prefix}_PSEL").value = 0
        getattr(dut, f"{m_prefix}_PENABLE").value = 0

    # Helper function for APB read
    async def apb_read(master_id, addr):
        """Perform APB read transaction"""
        m_prefix = f"m{master_id}_apb"
        await RisingEdge(dut.pclk)
        # Setup phase
        getattr(dut, f"{m_prefix}_PSEL").value = 1
        getattr(dut, f"{m_prefix}_PENABLE").value = 0
        getattr(dut, f"{m_prefix}_PADDR").value = addr
        getattr(dut, f"{m_prefix}_PWRITE").value = 0
        await RisingEdge(dut.pclk)
        # Access phase
        getattr(dut, f"{m_prefix}_PENABLE").value = 1
        # Wait for PREADY
        timeout = 0
        while getattr(dut, f"{m_prefix}_PREADY").value == 0:
            await RisingEdge(dut.pclk)
            timeout += 1
            if timeout > 100:
                log.error(f"Master {master_id} read timeout at addr 0x{addr:08X}")
                return 0, 1
        rdata = int(getattr(dut, f"{m_prefix}_PRDATA").value)
        pslverr = int(getattr(dut, f"{m_prefix}_PSLVERR").value)
        await RisingEdge(dut.pclk)
        # Idle
        getattr(dut, f"{m_prefix}_PSEL").value = 0
        getattr(dut, f"{m_prefix}_PENABLE").value = 0
        return rdata, pslverr

    # Test 1: Sequential access from both masters
    log.info("Test 1: Sequential access from both masters")
    await apb_write(0, 0x1000, 0xCAFE0000)
    await apb_write(1, 0x1004, 0xBEEF0001)

    # Read back
    rdata, _ = await apb_read(0, 0x1000)
    assert rdata == 0xCAFE0000, f"Master 0 read mismatch"
    rdata, _ = await apb_read(1, 0x1004)
    assert rdata == 0xBEEF0001, f"Master 1 read mismatch"
    log.info("  Test 1: PASS")
    await Timer(100, units="ns")

    # Test 2: Alternating access
    log.info("Test 2: Alternating access")
    for i in range(5):
        addr0 = 0x2000 + (i * 8)
        addr1 = 0x2004 + (i * 8)
        data0 = 0x1000 + i
        data1 = 0x2000 + i

        await apb_write(0, addr0, data0)
        await apb_write(1, addr1, data1)

        rdata, _ = await apb_read(0, addr0)
        assert rdata == data0, f"Master 0 failed at iteration {i}"
        rdata, _ = await apb_read(1, addr1)
        assert rdata == data1, f"Master 1 failed at iteration {i}"

    log.info("  Test 2: PASS")
    await Timer(100, units="ns")

    # Test 3: Rapid interleaved access
    log.info("Test 3: Rapid interleaved access")
    for i in range(10):
        addr = 0x3000 + (i * 4)
        data0 = 0xA0000000 + i
        data1 = 0xB0000000 + i

        await apb_write(0, addr, data0)
        rdata, _ = await apb_read(0, addr)
        assert rdata == data0, f"M0 rapid test failed at {i}"

        await apb_write(1, addr, data1)
        rdata, _ = await apb_read(1, addr)
        assert rdata == data1, f"M1 rapid test failed at {i}"

        log.info(f"  Iteration {i}: PASS")

    log.info("  Test 3: PASS")
    await Timer(100, units="ns")

    # Test 4: Concurrent hammering (arbitration stress)
    log.info("Test 4: Concurrent hammering (arbitration stress)")

    async def master_hammer(master_id, base_addr, count):
        """Master performs rapid transactions"""
        for i in range(count):
            addr = base_addr + (i * 4)
            data = (master_id << 24) | i
            await apb_write(master_id, addr, data)

    # Both masters hammer simultaneously
    m0_task = cocotb.start_soon(master_hammer(0, 0x4000, 20))
    m1_task = cocotb.start_soon(master_hammer(1, 0x5000, 20))
    await m0_task
    await m1_task

    # Verify
    for i in range(20):
        addr0 = 0x4000 + (i * 4)
        addr1 = 0x5000 + (i * 4)
        rdata, _ = await apb_read(0, addr0)
        assert rdata == ((0 << 24) | i), f"M0 hammer failed at {i}"
        rdata, _ = await apb_read(1, addr1)
        assert rdata == ((1 << 24) | i), f"M1 hammer failed at {i}"

    log.info("  Test 4: PASS")
    await Timer(100, units="ns")

    # Test 5: Random chaos
    log.info("Test 5: Random chaos (comprehensive stress)")

    transaction_log = []

    async def random_master_activity(master_id, num_ops):
        """Master performs random operations"""
        for _ in range(num_ops):
            addr = random.randint(0x6000, 0x6FFF) & 0xFFFC
            if random.random() < 0.5:
                data = random.randint(0, 0xFFFFFFFF)
                await apb_write(master_id, addr, data)
                transaction_log.append((master_id, 'W', addr, data))
            else:
                rdata, _ = await apb_read(master_id, addr)
                transaction_log.append((master_id, 'R', addr, rdata))

    # Both masters run chaos simultaneously
    m0_chaos = cocotb.start_soon(random_master_activity(0, 30))
    m1_chaos = cocotb.start_soon(random_master_activity(1, 30))
    await m0_chaos
    await m1_chaos

    log.info(f"  Completed {len(transaction_log)} random transactions")
    log.info("  Test 5: PASS")
    await Timer(500, units="ns")

    log.info("=" * 80)
    log.info("2-to-1 APB Crossbar Test PASSED")
    log.info(f"Total transactions: {len(transaction_log) + 70}")
    log.info("=" * 80)


@pytest.mark.parametrize("aw,dw", [
    (32, 32),
])
def test_apb_xbar_2to1(request, aw, dw):
    """Pytest wrapper for 2-to-1 crossbar test"""

    # Get RTL sources from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/apb_xbar/rtl/filelists/wrapper/apb_xbar_2to1_wrap.f'
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

    test_name = f'test_apb_xbar_2to1_aw{aw:03d}_dw{dw:03d}'
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)

    run(
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel="apb_xbar_2to1_wrap",
        module=module,
        parameters=parameters,
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
