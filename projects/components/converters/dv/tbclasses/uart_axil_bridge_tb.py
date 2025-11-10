# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
#
# Module: uart_axil_bridge_tb
# Purpose: Testbench class for uart_axil_bridge
#
# Author: RTL Design Sherpa
# Created: 2025-11-09

"""
Testbench for uart_axil_bridge

Tests UART to AXI4-Lite protocol bridge:
- UART command parsing (Write: W <addr> <data>, Read: R <addr>)
- AXI4-Lite master transaction generation
- Response formatting and UART transmission
- Command error handling

Architecture:
- UART BFM drives i_uart_rx (sends commands)
- UART monitor on o_uart_tx (captures responses)
- AXIL4 slave responder on master side (responds to AXI4-Lite transactions)
"""

import os
import sys
import cocotb
from cocotb.triggers import RisingEdge, Timer
import random

# Add framework to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, os.path.join(repo_root, 'bin'))

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.uart import UARTMaster, UARTMonitor
from CocoTBFramework.components.axil4.axil4_interfaces import AXIL4SlaveRead, AXIL4SlaveWrite
from CocoTBFramework.components.shared.memory_model import MemoryModel


class UARTAXILBridgeTB(TBBase):
    """
    Testbench for uart_axil_bridge.

    Tests UART command parsing and AXI4-Lite transaction generation.

    Key Validations:
    - Write command parsing and AXI4-Lite write execution
    - Read command parsing and AXI4-Lite read execution
    - Response generation (OK for writes, hex data for reads)
    - Command error handling (invalid commands, malformed input)
    """

    def __init__(self, dut):
        super().__init__(dut)

        # Clock and reset
        self.clk = dut.aclk
        self.clk_name = 'aclk'
        self.rst_n = dut.aresetn

        # Extract parameters from DUT or environment
        self.axil_data_width = self.convert_to_int(os.environ.get('AXIL_DATA_WIDTH', '32'))
        self.axil_addr_width = self.convert_to_int(os.environ.get('AXIL_ADDR_WIDTH', '32'))
        self.clks_per_bit = self.convert_to_int(os.environ.get('CLKS_PER_BIT', '868'))

        # Statistics
        self.stats = {
            'commands_sent': 0,
            'writes_completed': 0,
            'reads_completed': 0,
            'errors': 0,
            'uart_errors': 0,
            'axil_errors': 0,
        }

        # Initialize UART master (drives i_uart_rx)
        self.uart_tx_master = UARTMaster(
            entity=dut,
            title="UART_TX",
            signal_name="i_uart_rx",
            clock=self.clk,
            clks_per_bit=self.clks_per_bit,
            log=self.log
        )

        # Initialize UART monitor (captures o_uart_tx)
        self.uart_rx_monitor = UARTMonitor(
            entity=dut,
            title="UART_RX_MON",
            signal_name="o_uart_tx",
            clock=self.clk,
            clks_per_bit=self.clks_per_bit,
            direction='RX',
            log=self.log
        )

        # Create memory model (4GB address space, 32-bit data)
        # Memory model needs byte addressing
        bytes_per_line = self.axil_data_width // 8
        num_lines = 1024 * 1024  # 1M lines = 4MB memory (enough for testing)
        self.memory_model = MemoryModel(
            num_lines=num_lines,
            bytes_per_line=bytes_per_line,
            log=self.log,
            debug=False
        )

        # Initialize AXIL4 slave write responder (responds on master side)
        self.axil4_slave_wr = AXIL4SlaveWrite(
            dut=dut,
            clock=self.clk,
            prefix="m_axil_",
            log=self.log,
            data_width=self.axil_data_width,
            addr_width=self.axil_addr_width,
            multi_sig=True,
            response_delay=1,
            memory_model=self.memory_model  # Pass memory model
        )

        # Initialize AXIL4 slave read responder (responds on master side)
        self.axil4_slave_rd = AXIL4SlaveRead(
            dut=dut,
            clock=self.clk,
            prefix="m_axil_",
            log=self.log,
            data_width=self.axil_data_width,
            addr_width=self.axil_addr_width,
            multi_sig=True,
            response_delay=1,
            memory_model=self.memory_model  # Pass memory model
        )

        self.log.info(f"Initialized UART→AXIL Bridge TB: "
                     f"data_width={self.axil_data_width}, "
                     f"addr_width={self.axil_addr_width}, "
                     f"clks_per_bit={self.clks_per_bit}")

    # =========================================================================
    # MANDATORY METHODS - Required by TBBase
    # =========================================================================

    async def setup_clocks_and_reset(self, period_ns=10):
        """Complete initialization - start clocks and perform reset"""
        # Start clock
        await self.start_clock(self.clk_name, freq=period_ns, units='ns')

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        self.log.info("Reset sequence complete")

    async def assert_reset(self):
        """Assert reset signal (active-low)"""
        self.rst_n.value = 0
        self.log.debug("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset signal (active-low)"""
        self.rst_n.value = 1
        self.log.debug("Reset deasserted")

    # =========================================================================
    # TEST HELPER METHODS
    # =========================================================================

    async def send_uart_write_command(self, addr, data):
        """
        Send UART write command and verify response.

        Args:
            addr: Address (int)
            data: Data value (int)

        Returns:
            True if successful, False otherwise
        """
        # Format command: "W <addr_hex> <data_hex>\n"
        cmd = f"W {addr:X} {data:X}\n"
        self.log.info(f"Sending write command: {cmd.strip()}")

        # Clear previous responses
        self.uart_rx_monitor._recvQ.clear()

        # Send command
        await self.uart_tx_master.send_string(cmd)
        self.stats['commands_sent'] += 1

        # Wait for AXIL4 write transaction and response
        # Calculate: cmd length + response length = worst case
        # Worst case: "W FFFFFFFF FFFFFFFF\n" = 21 chars in, "OK\n" = 3 chars out
        # UART timing: clks_per_bit * 10 bits/char * chars
        # Add margin for AXI transaction latency
        wait_clocks = (21 + 3) * 10 * self.clks_per_bit + 10000
        await self.wait_clocks(self.clk_name, wait_clocks)

        # Check for "OK\n" response
        if len(self.uart_rx_monitor._recvQ) >= 3:
            pkt0 = self.uart_rx_monitor._recvQ.popleft()
            pkt1 = self.uart_rx_monitor._recvQ.popleft()
            pkt2 = self.uart_rx_monitor._recvQ.popleft()

            response = chr(pkt0.data) + chr(pkt1.data) + chr(pkt2.data)
            if response == "OK\n":
                self.log.info(f"✅ Write command successful: addr=0x{addr:X}, data=0x{data:X}")
                self.stats['writes_completed'] += 1
                # Memory model is automatically updated by AXIL4SlaveWrite
                return True
            else:
                self.log.error(f"❌ Unexpected response: '{response}' (expected 'OK\\n')")
                self.stats['errors'] += 1
                return False
        else:
            self.log.error(f"❌ No response received (expected 'OK\\n')")
            self.stats['errors'] += 1
            return False

    async def send_uart_read_command(self, addr):
        """
        Send UART read command and verify response.

        Args:
            addr: Address (int)

        Returns:
            Tuple (success: bool, data: int or None)
        """
        # Format command: "R <addr_hex>\n"
        cmd = f"R {addr:X}\n"
        self.log.info(f"Sending read command: {cmd.strip()}")

        # Clear previous responses
        self.uart_rx_monitor._recvQ.clear()

        # Send command
        await self.uart_tx_master.send_string(cmd)
        self.stats['commands_sent'] += 1

        # Wait for AXIL4 read transaction and response
        # Calculate: cmd length + response length = worst case
        # Worst case: "R FFFFFFFF\n" = 11 chars in, "0xDEADBEEF\n" = 11 chars out
        # UART timing: clks_per_bit * 10 bits/char * chars
        # Add margin for AXI transaction latency
        wait_clocks = (11 + 11) * 10 * self.clks_per_bit + 10000
        await self.wait_clocks(self.clk_name, wait_clocks)

        # Check for "0xDEADBEEF\n" response format
        if len(self.uart_rx_monitor._recvQ) >= 11:
            response_chars = []
            for _ in range(11):
                pkt = self.uart_rx_monitor._recvQ.popleft()
                response_chars.append(chr(pkt.data))

            response = ''.join(response_chars)
            self.log.debug(f"Received response: '{response.strip()}'")

            # Parse hex response: "0xDEADBEEF\n"
            if response.startswith("0x") and response.endswith("\n"):
                try:
                    data_hex = response[2:-1]  # Strip "0x" and "\n"
                    data = int(data_hex, 16)
                    self.log.info(f"✅ Read command successful: addr=0x{addr:X}, data=0x{data:X}")
                    self.stats['reads_completed'] += 1
                    return True, data
                except ValueError:
                    self.log.error(f"❌ Invalid hex response: '{response.strip()}'")
                    self.stats['errors'] += 1
                    return False, None
            else:
                self.log.error(f"❌ Malformed response: '{response.strip()}' (expected '0x<hex>\\n')")
                self.stats['errors'] += 1
                return False, None
        else:
            self.log.error(f"❌ No response received (expected '0x<hex>\\n')")
            self.stats['errors'] += 1
            return False, None

    # =========================================================================
    # TEST SUITES
    # =========================================================================

    async def run_basic_test(self):
        """
        Basic smoke test: Simple write and read operations.

        Returns:
            True if all tests pass, False otherwise
        """
        self.log.info("Running BASIC test suite")

        success = True

        # Test 1: Single write
        if not await self.send_uart_write_command(0x1000, 0xDEADBEEF):
            success = False

        # Test 2: Single read (should return what we wrote)
        read_success, read_data = await self.send_uart_read_command(0x1000)
        if not read_success:
            success = False
        elif read_data != 0xDEADBEEF:
            self.log.error(f"❌ Read data mismatch: expected 0xDEADBEEF, got 0x{read_data:X}")
            self.stats['errors'] += 1
            success = False

        # Test 3: Write to different address
        if not await self.send_uart_write_command(0x2000, 0x12345678):
            success = False

        # Test 4: Read from new address
        read_success, read_data = await self.send_uart_read_command(0x2000)
        if not read_success:
            success = False
        elif read_data != 0x12345678:
            self.log.error(f"❌ Read data mismatch: expected 0x12345678, got 0x{read_data:X}")
            self.stats['errors'] += 1
            success = False

        return success

    async def run_medium_test(self):
        """
        Medium test: Multiple write/read pairs.

        Returns:
            True if all tests pass, False otherwise
        """
        self.log.info("Running MEDIUM test suite")

        success = True
        num_operations = 10

        for i in range(num_operations):
            addr = 0x1000 + (i * 0x100)
            data = random.randint(0, 0xFFFFFFFF)

            # Write
            if not await self.send_uart_write_command(addr, data):
                success = False

            # Read back
            read_success, read_data = await self.send_uart_read_command(addr)
            if not read_success:
                success = False
            elif read_data != data:
                self.log.error(f"❌ Read data mismatch at addr 0x{addr:X}: expected 0x{data:X}, got 0x{read_data:X}")
                self.stats['errors'] += 1
                success = False

        return success

    async def run_full_test(self):
        """
        Full test: Comprehensive validation with edge cases.

        Returns:
            True if all tests pass, False otherwise
        """
        self.log.info("Running FULL test suite")

        success = True
        num_operations = 30

        # Test various addresses and data patterns
        for i in range(num_operations):
            # Use various address patterns
            addr = random.choice([
                0x00000000,  # Address 0
                0xFFFFFFFC,  # High address (aligned)
                0x1000 + (i * 4),  # Sequential
                random.randint(0, 0xFFFF) << 2  # Random aligned
            ])

            # Use various data patterns
            data = random.choice([
                0x00000000,  # All zeros
                0xFFFFFFFF,  # All ones
                0xAAAAAAAA,  # Alternating bits
                0x55555555,  # Alternating bits
                random.randint(0, 0xFFFFFFFF)  # Random
            ])

            # Write
            if not await self.send_uart_write_command(addr, data):
                success = False
                continue

            # Read back
            read_success, read_data = await self.send_uart_read_command(addr)
            if not read_success:
                success = False
            elif read_data != data:
                self.log.error(f"❌ Read data mismatch at addr 0x{addr:X}: expected 0x{data:X}, got 0x{read_data:X}")
                self.stats['errors'] += 1
                success = False

        return success

    def get_statistics(self):
        """Return current test statistics"""
        return self.stats.copy()
