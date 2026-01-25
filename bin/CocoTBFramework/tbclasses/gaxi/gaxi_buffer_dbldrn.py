# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GaxiBufferDblDrnTB
# Purpose: Testbench for GAXI skid buffer with double-drain capability
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-01-25

"""Testbench for GAXI skid buffer with double-drain capability

Tests gaxi_skid_buffer_dbldrn.sv - a skid buffer that can drain two items
at once when rd_ready2 is asserted and rd_count >= 2.

Key features tested:
- Single drain (rd_ready=1, rd_ready2=0): drains 1 item
- Double drain (rd_ready=1, rd_ready2=1, rd_count>=2): drains 2 items
- rd_data and rd_data2 output correctness
- Count accuracy with single and double drains
- Simultaneous write with single/double drain
"""
import os
import random
import cocotb
from cocotb.triggers import RisingEdge

from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class GaxiBufferDblDrnTB(TBBase):
    """Testbench for GAXI skid buffer with double-drain capability"""

    def __init__(self, dut, clk, rstn):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '4'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))

        # Setup widths and limits
        self.DW = self.TEST_DATA_WIDTH
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH) - 1
        self.TIMEOUT_CYCLES = 1000
        self.total_errors = 0

        # Clock and reset
        self.clk = clk
        self.clk_name = clk._name
        self.rstn = rstn

        # Tracking for verification
        self.sent_data = []
        self.received_data = []

        # Log configuration
        msg = '\n' + '='*80 + '\n'
        msg += ' GaxiBufferDblDrnTB Settings:\n'
        msg += '-'*80 + '\n'
        msg += f' Depth:      {self.TEST_DEPTH}\n'
        msg += f' DataWidth:  {self.TEST_DATA_WIDTH}\n'
        msg += f' Max Data:   0x{self.MAX_DATA:X}\n'
        msg += '='*80 + '\n'
        self.log.info(msg)

    async def assert_reset(self):
        """Assert reset"""
        self.rstn.value = 0
        self.dut.wr_valid.value = 0
        self.dut.wr_data.value = 0
        self.dut.rd_ready.value = 0
        self.dut.rd_ready2.value = 0

    async def deassert_reset(self):
        """Deassert reset"""
        self.rstn.value = 1
        self.log.info(f"Reset complete{self.get_time_ns_str()}")

    async def setup_clocks_and_reset(self):
        """Full initialization sequence"""
        await self.start_clock(self.clk_name, 10, 'ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 5)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    def get_count(self):
        """Get current buffer count"""
        return int(self.dut.rd_count.value)

    def get_rd_valid(self):
        """Get rd_valid signal"""
        return int(self.dut.rd_valid.value)

    def get_wr_ready(self):
        """Get wr_ready signal"""
        return int(self.dut.wr_ready.value)

    async def write_item(self, data):
        """Write a single item to the buffer"""
        # Wait for wr_ready
        timeout = 0
        while not self.get_wr_ready() and timeout < self.TIMEOUT_CYCLES:
            await self.wait_clocks(self.clk_name, 1)
            timeout += 1

        if timeout >= self.TIMEOUT_CYCLES:
            self.log.error(f"Timeout waiting for wr_ready")
            self.total_errors += 1
            return False

        self.dut.wr_valid.value = 1
        self.dut.wr_data.value = data
        await self.wait_clocks(self.clk_name, 1)
        self.dut.wr_valid.value = 0
        self.sent_data.append(data)
        return True

    async def read_single(self):
        """Read a single item (rd_ready=1, rd_ready2=0)"""
        if not self.get_rd_valid():
            return None

        # Capture data while rd_valid is high
        data = int(self.dut.rd_data.value)

        # Assert rd_ready for one cycle
        self.dut.rd_ready.value = 1
        self.dut.rd_ready2.value = 0
        await self.wait_clocks(self.clk_name, 1)
        self.dut.rd_ready.value = 0

        # Wait for signals to update before returning
        await self.wait_clocks(self.clk_name, 1)

        self.received_data.append(data)
        return data

    async def read_double(self):
        """Read two items (rd_ready=1, rd_ready2=1) - only valid when count >= 2"""
        count = self.get_count()
        if count < 2:
            self.log.warning(f"Cannot double-drain with count={count} < 2")
            return None, None

        if not self.get_rd_valid():
            return None, None

        # Capture data while rd_valid is high and count >= 2
        data1 = int(self.dut.rd_data.value)
        data2 = int(self.dut.rd_data2.value)

        # Assert rd_ready and rd_ready2 for one cycle
        self.dut.rd_ready.value = 1
        self.dut.rd_ready2.value = 1
        await self.wait_clocks(self.clk_name, 1)
        self.dut.rd_ready.value = 0
        self.dut.rd_ready2.value = 0

        # Wait for signals to update before returning
        await self.wait_clocks(self.clk_name, 1)

        self.received_data.append(data1)
        self.received_data.append(data2)
        return data1, data2

    async def fill_buffer(self, count):
        """Fill the buffer with sequential data"""
        self.log.info(f"Filling buffer with {count} items")
        for i in range(count):
            data = (i + 1) & self.MAX_DATA
            success = await self.write_item(data)
            if not success:
                self.log.error(f"Failed to write item {i}")
                return False
        return True

    async def reset_buffer(self):
        """Reset the buffer to a clean state by draining and reinitializing"""
        # Drain any remaining items
        self.dut.rd_ready.value = 1
        self.dut.rd_ready2.value = 0
        for _ in range(self.TEST_DEPTH + 5):
            await self.wait_clocks(self.clk_name, 1)
            if self.get_count() == 0:
                break
        self.dut.rd_ready.value = 0

        # Apply and release reset
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 5)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        # Clear tracking
        self.sent_data.clear()
        self.received_data.clear()

    async def drain_buffer_single(self):
        """Drain the entire buffer using single reads"""
        drained = []
        while self.get_rd_valid():
            data = await self.read_single()
            if data is not None:
                drained.append(data)
            else:
                break
        return drained

    async def drain_buffer_double(self):
        """Drain the buffer using double reads where possible"""
        drained = []
        while self.get_rd_valid():
            count = self.get_count()
            if count >= 2:
                data1, data2 = await self.read_double()
                if data1 is not None:
                    drained.extend([data1, data2])
            else:
                data = await self.read_single()
                if data is not None:
                    drained.append(data)
        return drained

    def verify_data_order(self, expected, actual, test_name):
        """Verify data matches expected order"""
        if len(expected) != len(actual):
            self.log.error(f"{test_name}: Length mismatch - expected {len(expected)}, got {len(actual)}")
            self.total_errors += 1
            return False

        for i, (exp, act) in enumerate(zip(expected, actual)):
            if exp != act:
                self.log.error(f"{test_name}: Data mismatch at index {i} - expected 0x{exp:X}, got 0x{act:X}")
                self.total_errors += 1
                return False

        self.log.info(f"{test_name}: Data verification PASSED ({len(expected)} items)")
        return True

    async def test_single_drain_basic(self, count=None):
        """Test basic single-drain operation (like standard skid buffer)"""
        self.log.info("=== Scenario DBLDRN-01: Single drain basic ===")
        self.sent_data.clear()
        self.received_data.clear()

        # Default to DEPTH items (can't write more without draining)
        if count is None:
            count = self.TEST_DEPTH

        # Fill buffer
        await self.fill_buffer(count)
        await self.wait_clocks(self.clk_name, 2)

        # Drain using single reads
        drained = await self.drain_buffer_single()
        await self.wait_clocks(self.clk_name, 2)

        # Verify
        return self.verify_data_order(self.sent_data, drained, "Single drain basic")

    async def test_double_drain_basic(self, count=None):
        """Test basic double-drain operation"""
        self.log.info("=== Scenario DBLDRN-02: Double drain basic ===")
        self.sent_data.clear()
        self.received_data.clear()

        # Default to DEPTH items (can't write more without draining)
        if count is None:
            count = self.TEST_DEPTH

        # Fill buffer
        await self.fill_buffer(count)
        await self.wait_clocks(self.clk_name, 2)

        # Drain using double reads where possible
        drained = await self.drain_buffer_double()
        await self.wait_clocks(self.clk_name, 2)

        # Verify
        return self.verify_data_order(self.sent_data, drained, "Double drain basic")

    async def test_count_decrement_single(self):
        """Verify count decrements by 1 on single drain"""
        self.log.info("=== Scenario DBLDRN-03: Count decrement single ===")
        self.sent_data.clear()

        # Fill 4 items
        await self.fill_buffer(4)
        await self.wait_clocks(self.clk_name, 2)

        initial_count = self.get_count()
        if initial_count != 4:
            self.log.error(f"Expected count=4 after fill, got {initial_count}")
            self.total_errors += 1
            return False

        # Single drain
        await self.read_single()
        await self.wait_clocks(self.clk_name, 1)

        new_count = self.get_count()
        if new_count != 3:
            self.log.error(f"Expected count=3 after single drain, got {new_count}")
            self.total_errors += 1
            return False

        self.log.info("Count decrement single: PASSED")

        # Cleanup
        await self.drain_buffer_single()
        return True

    async def test_count_decrement_double(self):
        """Verify count decrements by 2 on double drain"""
        self.log.info("=== Scenario DBLDRN-04: Count decrement double ===")
        self.sent_data.clear()

        # Fill 4 items
        await self.fill_buffer(4)
        await self.wait_clocks(self.clk_name, 2)

        initial_count = self.get_count()
        if initial_count != 4:
            self.log.error(f"Expected count=4 after fill, got {initial_count}")
            self.total_errors += 1
            return False

        # Double drain
        await self.read_double()
        await self.wait_clocks(self.clk_name, 1)

        new_count = self.get_count()
        if new_count != 2:
            self.log.error(f"Expected count=2 after double drain, got {new_count}")
            self.total_errors += 1
            return False

        self.log.info("Count decrement double: PASSED")

        # Cleanup
        await self.drain_buffer_double()
        return True

    async def test_data2_correctness(self):
        """Verify rd_data2 returns the second item correctly"""
        self.log.info("=== Scenario DBLDRN-05: rd_data2 correctness ===")
        self.sent_data.clear()

        # Write known pattern
        await self.write_item(0xAA)
        await self.write_item(0xBB)
        await self.write_item(0xCC)
        await self.write_item(0xDD)
        await self.wait_clocks(self.clk_name, 2)

        # Double drain and verify
        data1, data2 = await self.read_double()
        if data1 != 0xAA or data2 != 0xBB:
            self.log.error(f"First double-drain: expected (0xAA, 0xBB), got (0x{data1:X}, 0x{data2:X})")
            self.total_errors += 1
            return False

        data1, data2 = await self.read_double()
        if data1 != 0xCC or data2 != 0xDD:
            self.log.error(f"Second double-drain: expected (0xCC, 0xDD), got (0x{data1:X}, 0x{data2:X})")
            self.total_errors += 1
            return False

        self.log.info("rd_data2 correctness: PASSED")
        return True

    async def test_mixed_drain_patterns(self, iterations=10):
        """Test mixed single and double drain patterns"""
        self.log.info("=== Scenario DBLDRN-06: Mixed drain patterns ===")

        for i in range(iterations):
            self.sent_data.clear()
            self.received_data.clear()

            # Random fill count
            fill_count = random.randint(2, self.TEST_DEPTH)
            await self.fill_buffer(fill_count)
            await self.wait_clocks(self.clk_name, 2)

            # Drain with random mix of single/double
            drained = []
            while self.get_rd_valid():
                count = self.get_count()
                use_double = random.choice([True, False]) and count >= 2

                if use_double:
                    data1, data2 = await self.read_double()
                    if data1 is not None:
                        drained.extend([data1, data2])
                else:
                    data = await self.read_single()
                    if data is not None:
                        drained.append(data)

            if not self.verify_data_order(self.sent_data, drained, f"Mixed drain iter {i}"):
                return False

            await self.wait_clocks(self.clk_name, 5)

        self.log.info(f"Mixed drain patterns: PASSED ({iterations} iterations)")
        return True

    async def test_simultaneous_write_single_drain(self):
        """Test write + single drain in same cycle"""
        self.log.info("=== Scenario DBLDRN-07: Write + single drain ===")
        self.sent_data.clear()

        # Pre-fill 2 items
        await self.write_item(0x11)
        await self.write_item(0x22)
        await self.wait_clocks(self.clk_name, 2)

        # Simultaneous write and single read
        self.dut.wr_valid.value = 1
        self.dut.wr_data.value = 0x33
        self.dut.rd_ready.value = 1
        self.dut.rd_ready2.value = 0
        data_out = int(self.dut.rd_data.value)
        await self.wait_clocks(self.clk_name, 1)
        self.dut.wr_valid.value = 0
        self.dut.rd_ready.value = 0

        # Count should stay same (write +1, read -1)
        await self.wait_clocks(self.clk_name, 1)
        count = self.get_count()
        if count != 2:
            self.log.error(f"Expected count=2 after write+single drain, got {count}")
            self.total_errors += 1
            return False

        if data_out != 0x11:
            self.log.error(f"Expected first read=0x11, got 0x{data_out:X}")
            self.total_errors += 1
            return False

        self.log.info("Write + single drain: PASSED")

        # Cleanup
        self.dut.rd_ready.value = 1
        for _ in range(3):
            await self.wait_clocks(self.clk_name, 1)
        self.dut.rd_ready.value = 0
        return True

    async def test_simultaneous_write_double_drain(self):
        """Test write + double drain in same cycle"""
        self.log.info("=== Scenario DBLDRN-08: Write + double drain ===")
        self.sent_data.clear()

        # Pre-fill 3 items
        await self.write_item(0xA1)
        await self.write_item(0xA2)
        await self.write_item(0xA3)
        await self.wait_clocks(self.clk_name, 2)

        initial_count = self.get_count()
        if initial_count != 3:
            self.log.error(f"Expected count=3, got {initial_count}")
            self.total_errors += 1
            return False

        # Simultaneous write and double read
        self.dut.wr_valid.value = 1
        self.dut.wr_data.value = 0xA4
        self.dut.rd_ready.value = 1
        self.dut.rd_ready2.value = 1
        data1 = int(self.dut.rd_data.value)
        data2 = int(self.dut.rd_data2.value)
        await self.wait_clocks(self.clk_name, 1)
        self.dut.wr_valid.value = 0
        self.dut.rd_ready.value = 0
        self.dut.rd_ready2.value = 0

        # Count should be 2 (write +1, double-read -2 = net -1)
        await self.wait_clocks(self.clk_name, 1)
        count = self.get_count()
        if count != 2:
            self.log.error(f"Expected count=2 after write+double drain, got {count}")
            self.total_errors += 1
            return False

        if data1 != 0xA1 or data2 != 0xA2:
            self.log.error(f"Expected (0xA1, 0xA2), got (0x{data1:X}, 0x{data2:X})")
            self.total_errors += 1
            return False

        self.log.info("Write + double drain: PASSED")

        # Cleanup
        self.dut.rd_ready.value = 1
        for _ in range(3):
            await self.wait_clocks(self.clk_name, 1)
        self.dut.rd_ready.value = 0
        return True

    async def test_full_buffer_double_drain(self):
        """Fill buffer completely, drain with double reads"""
        self.log.info("=== Scenario DBLDRN-09: Full buffer double drain ===")
        self.sent_data.clear()
        self.received_data.clear()

        # Fill to capacity
        await self.fill_buffer(self.TEST_DEPTH)
        await self.wait_clocks(self.clk_name, 2)

        count = self.get_count()
        if count != self.TEST_DEPTH:
            self.log.error(f"Expected count={self.TEST_DEPTH}, got {count}")
            self.total_errors += 1
            return False

        # Drain with double reads
        drained = await self.drain_buffer_double()
        await self.wait_clocks(self.clk_name, 2)

        return self.verify_data_order(self.sent_data, drained, "Full buffer double drain")

    async def test_back_to_back_double_drain(self, count=20):
        """Continuous back-to-back double drain operations"""
        self.log.info("=== Scenario DBLDRN-10: Back-to-back double drain ===")
        self.sent_data.clear()
        self.received_data.clear()

        # Fill half, then alternate write/read
        await self.fill_buffer(self.TEST_DEPTH // 2)

        # Producer and consumer running concurrently
        produced = self.TEST_DEPTH // 2
        consumed = 0
        drained = []

        for i in range(count):
            # Try to write if space available
            if self.get_wr_ready() and produced < count + self.TEST_DEPTH // 2:
                data = ((produced + 1) & self.MAX_DATA)
                self.dut.wr_valid.value = 1
                self.dut.wr_data.value = data
                self.sent_data.append(data)
                produced += 1
            else:
                self.dut.wr_valid.value = 0

            # Try to double-drain if count >= 2
            current_count = self.get_count()
            if current_count >= 2 and self.get_rd_valid():
                self.dut.rd_ready.value = 1
                self.dut.rd_ready2.value = 1
                data1 = int(self.dut.rd_data.value)
                data2 = int(self.dut.rd_data2.value)
                drained.extend([data1, data2])
                consumed += 2
            elif current_count >= 1 and self.get_rd_valid():
                self.dut.rd_ready.value = 1
                self.dut.rd_ready2.value = 0
                data = int(self.dut.rd_data.value)
                drained.append(data)
                consumed += 1
            else:
                self.dut.rd_ready.value = 0
                self.dut.rd_ready2.value = 0

            await self.wait_clocks(self.clk_name, 1)

        self.dut.wr_valid.value = 0
        self.dut.rd_ready.value = 0
        self.dut.rd_ready2.value = 0

        # Drain remaining
        await self.wait_clocks(self.clk_name, 5)
        remaining = await self.drain_buffer_double()
        drained.extend(remaining)

        return self.verify_data_order(self.sent_data, drained, "Back-to-back double drain")

    async def test_stress_random(self, operations=100):
        """Random stress test with all operations"""
        self.log.info(f"=== Scenario DBLDRN-11: Random stress test ({operations} ops) ===")
        self.sent_data.clear()
        drained = []

        for _ in range(operations):
            action = random.choice(['write', 'single_read', 'double_read', 'write_single', 'write_double', 'nop'])
            count = self.get_count()

            if action == 'write' and self.get_wr_ready():
                data = random.randint(0, self.MAX_DATA)
                await self.write_item(data)

            elif action == 'single_read' and count >= 1 and self.get_rd_valid():
                data = await self.read_single()
                if data is not None:
                    drained.append(data)

            elif action == 'double_read' and count >= 2 and self.get_rd_valid():
                data1, data2 = await self.read_double()
                if data1 is not None:
                    drained.extend([data1, data2])

            elif action == 'write_single' and self.get_wr_ready() and count >= 1 and self.get_rd_valid():
                # Simultaneous write + single read
                data_in = random.randint(0, self.MAX_DATA)
                self.dut.wr_valid.value = 1
                self.dut.wr_data.value = data_in
                self.dut.rd_ready.value = 1
                self.dut.rd_ready2.value = 0
                data_out = int(self.dut.rd_data.value)
                await self.wait_clocks(self.clk_name, 1)
                self.dut.wr_valid.value = 0
                self.dut.rd_ready.value = 0
                self.sent_data.append(data_in)
                drained.append(data_out)

            elif action == 'write_double' and self.get_wr_ready() and count >= 2 and self.get_rd_valid():
                # Simultaneous write + double read
                data_in = random.randint(0, self.MAX_DATA)
                self.dut.wr_valid.value = 1
                self.dut.wr_data.value = data_in
                self.dut.rd_ready.value = 1
                self.dut.rd_ready2.value = 1
                data1 = int(self.dut.rd_data.value)
                data2 = int(self.dut.rd_data2.value)
                await self.wait_clocks(self.clk_name, 1)
                self.dut.wr_valid.value = 0
                self.dut.rd_ready.value = 0
                self.dut.rd_ready2.value = 0
                self.sent_data.append(data_in)
                drained.extend([data1, data2])

            else:
                # No-op
                await self.wait_clocks(self.clk_name, 1)

        # Drain remaining
        await self.wait_clocks(self.clk_name, 5)
        remaining = await self.drain_buffer_double()
        drained.extend(remaining)

        return self.verify_data_order(self.sent_data, drained, f"Random stress ({operations} ops)")

    async def run_all_tests(self, test_level='basic'):
        """Run all tests based on test level"""
        self.log.info(f"Running {test_level.upper()} test level")

        all_passed = True

        # Basic tests (always run)
        if not await self.test_single_drain_basic():
            all_passed = False
        await self.reset_buffer()

        if not await self.test_double_drain_basic():
            all_passed = False
        await self.reset_buffer()

        if not await self.test_count_decrement_single():
            all_passed = False
        await self.reset_buffer()

        if not await self.test_count_decrement_double():
            all_passed = False
        await self.reset_buffer()

        if not await self.test_data2_correctness():
            all_passed = False
        await self.reset_buffer()

        # Medium tests
        if test_level in ['medium', 'full']:
            if not await self.test_mixed_drain_patterns(iterations=20):
                all_passed = False
            await self.reset_buffer()

            if not await self.test_simultaneous_write_single_drain():
                all_passed = False
            await self.reset_buffer()

            if not await self.test_simultaneous_write_double_drain():
                all_passed = False
            await self.reset_buffer()

            if not await self.test_full_buffer_double_drain():
                all_passed = False
            await self.reset_buffer()

            if not await self.test_back_to_back_double_drain(count=30):
                all_passed = False
            await self.reset_buffer()

        # Full tests
        if test_level == 'full':
            if not await self.test_mixed_drain_patterns(iterations=50):
                all_passed = False
            await self.reset_buffer()

            if not await self.test_stress_random(operations=200):
                all_passed = False
            await self.reset_buffer()

        if all_passed:
            self.log.info(f"ALL {test_level.upper()} TESTS PASSED!")
        else:
            self.log.error(f"SOME TESTS FAILED! Total errors: {self.total_errors}")

        return all_passed
