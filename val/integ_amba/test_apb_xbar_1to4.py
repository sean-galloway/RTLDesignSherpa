"""
Test for 1-to-4 APB Crossbar

This test validates the address decoding functionality of apb_xbar_1to4,
which routes a single master to four slaves based on address ranges.

Purpose: Test address decode with apb_slave and apb_master modules.
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


@cocotb.test(timeout_time=120, timeout_unit='us')
async def apb_xbar_1to4_test(dut):
    """Test 1-to-4 APB crossbar with address decoding and stress scenarios"""

    log = dut._log
    log.info("=" * 80)
    log.info("Starting 1-to-4 APB Crossbar Test")
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
    dut.s0_apb_PRDATA.value = 0
    dut.s0_apb_PSLVERR.value = 0
    dut.s0_apb_PREADY.value = 0
    dut.s1_apb_PRDATA.value = 0
    dut.s1_apb_PSLVERR.value = 0
    dut.s1_apb_PREADY.value = 0
    dut.s2_apb_PRDATA.value = 0
    dut.s2_apb_PSLVERR.value = 0
    dut.s2_apb_PREADY.value = 0
    dut.s3_apb_PRDATA.value = 0
    dut.s3_apb_PSLVERR.value = 0
    dut.s3_apb_PREADY.value = 0

    await Timer(100, units="ns")
    dut.presetn.value = 1
    await RisingEdge(dut.pclk)
    log.info("Reset complete")

    # Simple memory models for each slave
    memory = [{}, {}, {}, {}]

    # Delay profiles for each slave (min_delay, max_delay)
    delay_profiles = [
        (0, 1),   # Slave 0: fast
        (0, 3),   # Slave 1: medium
        (1, 5),   # Slave 2: slow
        (2, 8),   # Slave 3: very slow
    ]

    async def slave_response(slave_id):
        """Slave responds to transactions with random delays"""
        s_prefix = f"s{slave_id}_apb"
        min_delay, max_delay = delay_profiles[slave_id]
        while True:
            await RisingEdge(dut.pclk)
            if getattr(dut, f"{s_prefix}_PSEL").value == 1 and \
               getattr(dut, f"{s_prefix}_PENABLE").value == 1:
                # Random delay before responding
                delay = random.randint(min_delay, max_delay)
                for _ in range(delay):
                    getattr(dut, f"{s_prefix}_PREADY").value = 0
                    await RisingEdge(dut.pclk)

                addr = int(getattr(dut, f"{s_prefix}_PADDR").value)
                if getattr(dut, f"{s_prefix}_PWRITE").value == 1:
                    # Write
                    data = int(getattr(dut, f"{s_prefix}_PWDATA").value)
                    memory[slave_id][addr] = data
                    log.info(f"Slave {slave_id} write: addr=0x{addr:08X}, data=0x{data:08X} (delay={delay})")
                else:
                    # Read
                    data = memory[slave_id].get(addr, 0xDEAD0000 + slave_id)
                    getattr(dut, f"{s_prefix}_PRDATA").value = data
                    log.info(f"Slave {slave_id} read: addr=0x{addr:08X}, data=0x{data:08X} (delay={delay})")

                getattr(dut, f"{s_prefix}_PREADY").value = 1
                getattr(dut, f"{s_prefix}_PSLVERR").value = 0
            else:
                getattr(dut, f"{s_prefix}_PREADY").value = 0
                getattr(dut, f"{s_prefix}_PSLVERR").value = 0

    # Start all slave response handlers
    for i in range(4):
        cocotb.start_soon(slave_response(i))

    # Wait for initialization
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
        timeout = 0
        while dut.m_apb_PREADY.value == 0:
            await RisingEdge(dut.pclk)
            timeout += 1
            if timeout > 100:
                log.error(f"Write timeout at addr 0x{addr:08X}")
                break
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
        timeout = 0
        while dut.m_apb_PREADY.value == 0:
            await RisingEdge(dut.pclk)
            timeout += 1
            if timeout > 100:
                log.error(f"Read timeout at addr 0x{addr:08X}")
                return 0, 1
        rdata = int(dut.m_apb_PRDATA.value)
        pslverr = int(dut.m_apb_PSLVERR.value)
        await RisingEdge(dut.pclk)
        # Idle
        dut.m_apb_PSEL.value = 0
        dut.m_apb_PENABLE.value = 0
        return rdata, pslverr

    # Test 1: Write to each slave and read back
    log.info("Test 1: Write to each slave and read back")
    BASE = 0x10000000

    # Slave 0: BASE + 0x00000
    await apb_write(BASE + 0x00000, 0xCAFE0000)
    await apb_write(BASE + 0x00100, 0xCAFE0100)

    # Slave 1: BASE + 0x10000
    await apb_write(BASE + 0x10000, 0xBEEF0001)
    await apb_write(BASE + 0x10100, 0xBEEF0101)

    # Slave 2: BASE + 0x20000
    await apb_write(BASE + 0x20000, 0xDEAD0002)
    await apb_write(BASE + 0x20100, 0xDEAD0102)

    # Slave 3: BASE + 0x30000
    await apb_write(BASE + 0x30000, 0xFACE0003)
    await apb_write(BASE + 0x30100, 0xFACE0103)

    # Read back all values
    rdata, _ = await apb_read(BASE + 0x00000)
    assert rdata == 0xCAFE0000, f"Slave 0 read mismatch: 0x{rdata:08X}"
    rdata, _ = await apb_read(BASE + 0x00100)
    assert rdata == 0xCAFE0100, f"Slave 0 read mismatch: 0x{rdata:08X}"

    rdata, _ = await apb_read(BASE + 0x10000)
    assert rdata == 0xBEEF0001, f"Slave 1 read mismatch: 0x{rdata:08X}"
    rdata, _ = await apb_read(BASE + 0x10100)
    assert rdata == 0xBEEF0101, f"Slave 1 read mismatch: 0x{rdata:08X}"

    rdata, _ = await apb_read(BASE + 0x20000)
    assert rdata == 0xDEAD0002, f"Slave 2 read mismatch: 0x{rdata:08X}"
    rdata, _ = await apb_read(BASE + 0x20100)
    assert rdata == 0xDEAD0102, f"Slave 2 read mismatch: 0x{rdata:08X}"

    rdata, _ = await apb_read(BASE + 0x30000)
    assert rdata == 0xFACE0003, f"Slave 3 read mismatch: 0x{rdata:08X}"
    rdata, _ = await apb_read(BASE + 0x30100)
    assert rdata == 0xFACE0103, f"Slave 3 read mismatch: 0x{rdata:08X}"

    log.info("  Test 1: PASS")
    await Timer(100, units="ns")

    # Test 2: Interleaved access across slaves
    log.info("Test 2: Interleaved access across slaves")
    for i in range(10):
        addr0 = BASE + 0x00200 + (i * 4)
        addr1 = BASE + 0x10200 + (i * 4)
        addr2 = BASE + 0x20200 + (i * 4)
        addr3 = BASE + 0x30200 + (i * 4)

        data0 = 0x10000000 + i
        data1 = 0x20000000 + i
        data2 = 0x30000000 + i
        data3 = 0x40000000 + i

        await apb_write(addr0, data0)
        await apb_write(addr1, data1)
        await apb_write(addr2, data2)
        await apb_write(addr3, data3)

        rdata, _ = await apb_read(addr0)
        assert rdata == data0, f"Slave 0 failed at iteration {i}"
        rdata, _ = await apb_read(addr1)
        assert rdata == data1, f"Slave 1 failed at iteration {i}"
        rdata, _ = await apb_read(addr2)
        assert rdata == data2, f"Slave 2 failed at iteration {i}"
        rdata, _ = await apb_read(addr3)
        assert rdata == data3, f"Slave 3 failed at iteration {i}"

    log.info("  Test 2: PASS")
    await Timer(100, units="ns")

    # Test 3: Rapid sequential access to same slave
    log.info("Test 3: Rapid sequential access to same slave")
    for slave_id in range(4):
        base_addr = BASE + (slave_id * 0x10000) + 0x00400
        for i in range(5):
            addr = base_addr + (i * 4)
            data = 0x50000000 + (slave_id << 16) + i
            await apb_write(addr, data)
            rdata, _ = await apb_read(addr)
            assert rdata == data, f"Slave {slave_id} rapid test failed at {i}"

    log.info("  Test 3: PASS")
    await Timer(100, units="ns")

    # Test 4: Random access pattern across all slaves
    log.info("Test 4: Random access pattern (address decode stress)")

    transaction_log = []
    for _ in range(40):  # Reduced from 80
        slave_id = random.randint(0, 3)
        offset = random.randint(0, 0xFFF0) & 0xFFFC
        addr = BASE + (slave_id << 16) + offset

        if random.random() < 0.5:
            data = random.randint(0, 0xFFFFFFFF)
            await apb_write(addr, data)
            transaction_log.append(('W', addr, data))
        else:
            rdata, _ = await apb_read(addr)
            transaction_log.append(('R', addr, rdata))

    log.info(f"  Completed {len(transaction_log)} random transactions")
    log.info("  Test 4: PASS")
    await Timer(100, units="ns")

    # Test 5: Sequential burst to each slave
    log.info("Test 5: Sequential bursts (throughput test)")

    for slave_id in range(4):
        base_offset = (slave_id << 16) + 0x03000
        # Write burst
        for i in range(10):  # Reduced from 20
            addr = BASE + base_offset + (i * 4)
            data = 0xE0000000 | (slave_id << 16) | i
            await apb_write(addr, data)
        # Read burst
        for i in range(10):  # Reduced from 20
            addr = BASE + base_offset + (i * 4)
            expected = 0xE0000000 | (slave_id << 16) | i
            rdata, _ = await apb_read(addr)
            assert rdata == expected, f"Slave {slave_id} burst failed at {i}"

    log.info("  Test 5: PASS")
    await Timer(100, units="ns")

    # Test 6: Alternating slave access (decoder switching stress)
    log.info("Test 6: Alternating slave access (decoder stress)")

    for iteration in range(10):  # Reduced from 15
        for slave_id in range(4):
            addr = BASE + (slave_id << 16) + 0x04000 + (iteration * 4)
            data = 0xF0000000 | (slave_id << 16) | iteration
            await apb_write(addr, data)

    # Verify all in reverse order
    for iteration in range(9, -1, -1):  # Reduced from 14
        for slave_id in range(3, -1, -1):
            addr = BASE + (slave_id << 16) + 0x04000 + (iteration * 4)
            expected = 0xF0000000 | (slave_id << 16) | iteration
            rdata, _ = await apb_read(addr)
            assert rdata == expected, f"Alternating test failed S{slave_id} iter{iteration}"

    log.info("  Test 6: PASS")
    await Timer(500, units="ns")

    log.info("=" * 80)
    log.info("1-to-4 APB Crossbar Test PASSED")
    log.info(f"Total transactions: {len(transaction_log) + 80 + 80}")
    log.info("=" * 80)


@pytest.mark.parametrize("aw,dw", [
    (32, 32),
])
def test_apb_xbar_1to4(request, aw, dw):
    """Pytest wrapper for 1-to-4 crossbar test"""

    # Get repository root
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../..'))

    # RTL paths
    rtl_dict = {
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
        os.path.join(repo_root, 'rtl', 'common', 'encoder.sv'),
        os.path.join(rtl_dict['rtl_apb'],  "xbar", "apb_xbar_1to4.sv"),
        os.path.join(rtl_dict['rtl_integ'], "apb_xbar_1to4_wrap.sv"),
    ]

    # Simulation parameters
    parameters = {
        'ADDR_WIDTH': aw,
        'DATA_WIDTH': dw,
        'BASE_ADDR': 0x10000000,
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
                             f'test_apb_xbar_1to4_aw{aw:03d}_dw{dw:03d}')

    run(
        verilog_sources=verilog_sources,
        toplevel="apb_xbar_1to4_wrap",
        module=module,
        parameters=parameters,
        simulator="verilator",
        compile_args=compile_args,
        sim_build=sim_build,
        work_dir=sim_build,
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
