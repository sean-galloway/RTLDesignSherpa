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

# Add CocoTB framework to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../bin'))
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
    async def apb_write(addr, data):
        """Perform APB write transaction"""
        await RisingEdge(dut.pclk)
        # Setup phase
        dut.m_apb_PSEL.value = 1
        dut.m_apb_PENABLE.value = 0
        dut.m_apb_PADDR.value = addr
        dut.m_apb_PWRITE.value = 1
        dut.m_apb_PWDATA.value = data
        dut.m_apb_PSTRB.value = 0xF
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
    log.info("Test 1: Write transaction")
    await apb_write(0x1000, 0x12345678)
    await Timer(100, units="ns")

    # Test 2: Simple read
    log.info("Test 2: Read transaction")
    rdata = await apb_read(0x1000)
    log.info(f"Read data: 0x{rdata:08X}")
    assert rdata == 0x12345678, f"Data mismatch! Expected 0x12345678, got 0x{rdata:08X}"

    # Test 3: Multiple transactions
    log.info("Test 3: Multiple transactions")
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
    log.info("Test 4: Burst writes (throughput test)")
    base_addr = 0x3000
    for i in range(30):
        addr = base_addr + (i * 4)
        data = 0xA0000000 + i
        await apb_write(addr, data)

    # Verify
    for i in range(30):
        addr = base_addr + (i * 4)
        expected = 0xA0000000 + i
        rdata = await apb_read(addr)
        assert rdata == expected, f"Burst test failed at {i}"

    log.info("  Test 4: PASS")
    await Timer(100, units="ns")

    # Test 5: Random access pattern
    log.info("Test 5: Random access pattern")
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

    # Get repository root
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))

    # RTL paths
    rtl_dict = {
        'rtl_cmn':  os.path.join(repo_root, 'rtl', 'common'),
        'rtl_gaxi': os.path.join(repo_root, 'rtl', 'amba', 'gaxi'),
        'rtl_apb':  os.path.join(repo_root, 'rtl', 'amba', 'apb'),
        'rtl_integ': os.path.join(repo_root, 'rtl', 'integ_amba', 'apb_xbar'),
    }

    # RTL sources
    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_apb'],  "apb_slave.sv"),
        os.path.join(rtl_dict['rtl_apb'],  "apb_master.sv"),
        os.path.join(rtl_dict['rtl_apb'],  "xbar", "apb_xbar_1to1.sv"),
        os.path.join(rtl_dict['rtl_integ'], "apb_xbar_1to1_wrap.sv"),
    ]

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

    module = os.path.splitext(os.path.basename(__file__))[0]
    sim_build = os.path.join(repo_root, 'val', 'integ_amba', 'local_sim_build',
                             f'test_apb_xbar_1to1_aw{aw:03d}_dw{dw:03d}')

    run(
        verilog_sources=verilog_sources,
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
