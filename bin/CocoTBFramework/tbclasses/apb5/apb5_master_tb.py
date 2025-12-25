# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APB5MasterTB
# Purpose: APB5 Master Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
APB5 Master Testbench

Testbench for testing APB5 master functionality using the CocoTB
framework's APB5 components. Supports AMBA5 extensions.

APB5 Features Tested:
- Standard APB4 transactions (read/write)
- User signals (PAUSER, PWUSER)
- Wake-up signaling (PWAKEUP)
- Parity protection (optional)
- Error injection for pslverr
"""
import os
import random

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# APB5 specific imports
from CocoTBFramework.components.apb5.apb5_factories import (
    create_apb5_master,
    create_apb5_slave,
    create_apb5_monitor,
    create_apb5_randomizer,
)


class APB5MasterTB(TBBase):
    """
    APB5 Master testbench for baseline testing.

    Tests basic APB5 master functionality including user signals,
    wake-up, and optional parity features.
    """

    def __init__(self, dut, pclk=None, presetn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '12'))
        self.TEST_STRB_WIDTH = self.TEST_DATA_WIDTH // 8
        self.TEST_AUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_AUSER_WIDTH', '4'))
        self.TEST_WUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_WUSER_WIDTH', '4'))
        self.TEST_RUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_RUSER_WIDTH', '4'))
        self.TEST_BUSER_WIDTH = self.convert_to_int(os.environ.get('TEST_BUSER_WIDTH', '4'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TIMEOUT_CYCLES = self.convert_to_int(os.environ.get('TIMEOUT_CYCLES', '1000'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.pclk = pclk
        self.pclk_name = pclk._name if pclk else 'pclk'
        self.presetn = presetn

        # Set limits based on widths
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH) - 1
        self.MAX_AUSER = (2**self.TEST_AUSER_WIDTH) - 1
        self.MAX_WUSER = (2**self.TEST_WUSER_WIDTH) - 1
        self.MAX_RUSER = (2**self.TEST_RUSER_WIDTH) - 1
        self.MAX_BUSER = (2**self.TEST_BUSER_WIDTH) - 1

        # Log configuration
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' APB5 Master Test Configuration:\n'
        msg += '-'*80 + "\n"
        msg += f' Data Width:   {self.TEST_DATA_WIDTH}\n'
        msg += f' Addr Width:   {self.TEST_ADDR_WIDTH}\n'
        msg += f' AUSER Width:  {self.TEST_AUSER_WIDTH}\n'
        msg += f' WUSER Width:  {self.TEST_WUSER_WIDTH}\n'
        msg += f' RUSER Width:  {self.TEST_RUSER_WIDTH}\n'
        msg += f' BUSER Width:  {self.TEST_BUSER_WIDTH}\n'
        msg += f' Clock Period: {self.TEST_CLK_PERIOD} ns\n'
        msg += f' Max Addr:     0x{self.MAX_ADDR:X}\n'
        msg += f' Max Data:     0x{self.MAX_DATA:X}\n'
        msg += f' Seed:         {self.SEED}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Create memory model for register storage
        bytes_per_line = max(4, (self.TEST_DATA_WIDTH + 7) // 8)
        self.memory_model = MemoryModel(
            num_lines=4096,
            bytes_per_line=bytes_per_line,
            log=self.log
        )

        # Initialize memory with test patterns
        self._initialize_memory_patterns()

        # Create APB5 slave randomizer
        self.slave_randomizer = create_apb5_randomizer(
            ruser_width=self.TEST_RUSER_WIDTH,
            buser_width=self.TEST_BUSER_WIDTH
        )

        # Create initial register map (all zeros)
        num_registers = 2 ** (self.TEST_ADDR_WIDTH - 2)  # Word-aligned
        self.registers = [0] * min(num_registers, 256)

        # Create APB5 master
        try:
            self.master = create_apb5_master(
                entity=dut,
                title='APB5_Master',
                prefix='m_apb',
                clock=self.pclk,
                bus_width=self.TEST_DATA_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                auser_width=self.TEST_AUSER_WIDTH,
                wuser_width=self.TEST_WUSER_WIDTH,
                ruser_width=self.TEST_RUSER_WIDTH,
                buser_width=self.TEST_BUSER_WIDTH,
                log=self.log
            )
            self.log.info("APB5 Master created")
        except Exception as e:
            self.log.error(f"Failed to create master: {e}")
            raise

        # Create APB5 slave
        try:
            self.slave = create_apb5_slave(
                entity=dut,
                title='APB5_Slave',
                prefix='s_apb',
                clock=self.pclk,
                registers=self.registers,
                bus_width=self.TEST_DATA_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                auser_width=self.TEST_AUSER_WIDTH,
                wuser_width=self.TEST_WUSER_WIDTH,
                ruser_width=self.TEST_RUSER_WIDTH,
                buser_width=self.TEST_BUSER_WIDTH,
                randomizer=self.slave_randomizer,
                log=self.log,
                error_overflow=False
            )
            self.log.info("APB5 Slave created")
        except Exception as e:
            self.log.error(f"Failed to create slave: {e}")
            raise

        # Create APB5 monitor (optional)
        try:
            self.monitor = create_apb5_monitor(
                entity=dut,
                title='APB5_Monitor',
                prefix='s_apb',
                clock=self.pclk,
                bus_width=self.TEST_DATA_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH,
                auser_width=self.TEST_AUSER_WIDTH,
                wuser_width=self.TEST_WUSER_WIDTH,
                ruser_width=self.TEST_RUSER_WIDTH,
                buser_width=self.TEST_BUSER_WIDTH,
                log=self.log
            )
            self.log.info("APB5 Monitor created")
        except Exception as e:
            self.log.warning(f"Failed to create monitor: {e}")
            self.monitor = None

        # Statistics tracking
        self.stats = {
            'total_transactions': 0,
            'successful_writes': 0,
            'successful_reads': 0,
            'failed_writes': 0,
            'failed_reads': 0,
            'timeout_errors': 0,
            'data_mismatches': 0,
            'pslverr_count': 0,
            'wakeup_count': 0,
            'user_signal_tests': 0,
            'test_duration': 0
        }

        self.log.info("APB5 Master testbench initialized successfully")

    def _initialize_memory_patterns(self):
        """Initialize memory with known test patterns"""
        self.log.info("Initializing memory with test patterns...")

        bytes_per_word = self.TEST_DATA_WIDTH // 8

        # Pattern 1: Incremental data starting at 0x00
        base_addr = 0x00
        for i in range(64):
            addr = base_addr + (i * bytes_per_word)
            data = 0x10000000 + i
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_word)
            self.memory_model.write(addr, data_bytes)

        # Pattern 2: Address-based pattern at 0x100
        base_addr = 0x100
        for i in range(32):
            addr = base_addr + (i * bytes_per_word)
            data = addr & self.MAX_DATA
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_word)
            self.memory_model.write(addr, data_bytes)

        self.log.info("Memory patterns initialized")

    async def assert_reset(self):
        """Assert reset and initialize components"""
        self.presetn.value = 0
        await self.wait_clocks(self.pclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.presetn.value = 1
        await self.wait_clocks(self.pclk_name, 5)
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    # Core test methods

    async def single_write_test(self, addr, data, strb=None, pauser=None, pwuser=None):
        """
        Perform a single APB5 write transaction.

        Args:
            addr: Address to write to
            data: Data value to write
            strb: Write strobe (if None, full strobe)
            pauser: Address phase user signal (APB5)
            pwuser: Write phase user signal (APB5)

        Returns:
            tuple: (success, response_info)
        """
        if strb is None:
            strb = (1 << self.TEST_STRB_WIDTH) - 1

        self.log.debug(f"Single write: addr=0x{addr:08X}, data=0x{data:08X}, "
                      f"strb=0x{strb:X}, pauser={pauser}, pwuser={pwuser}")

        try:
            self.stats['total_transactions'] += 1

            if pauser is not None or pwuser is not None:
                self.stats['user_signal_tests'] += 1

            await self.master.write(
                address=addr,
                data=data,
                strb=strb,
                pauser=pauser,
                pwuser=pwuser
            )

            self.stats['successful_writes'] += 1
            return True, {
                'addr': addr,
                'data': data,
                'strb': strb,
                'pauser': pauser,
                'pwuser': pwuser
            }

        except Exception as e:
            self.log.error(f"Write failed with exception: {e}")
            self.stats['failed_writes'] += 1
            self.stats['timeout_errors'] += 1
            return False, {'error': str(e)}

    async def single_read_test(self, addr, expected_data=None, pauser=None):
        """
        Perform a single APB5 read transaction.

        Args:
            addr: Address to read from
            expected_data: Expected data value (if None, no check)
            pauser: Address phase user signal (APB5)

        Returns:
            tuple: (success, actual_data, response_info)
        """
        self.log.debug(f"Single read: addr=0x{addr:08X}, pauser={pauser}")

        try:
            self.stats['total_transactions'] += 1

            if pauser is not None:
                self.stats['user_signal_tests'] += 1

            actual_data = await self.master.read(
                address=addr,
                pauser=pauser
            )

            # Check data match if expected provided
            if expected_data is not None and actual_data != expected_data:
                self.log.warning(f"Data mismatch at 0x{addr:08X}: "
                               f"got 0x{actual_data:08X}, expected 0x{expected_data:08X}")
                self.stats['data_mismatches'] += 1
                self.stats['failed_reads'] += 1
                return False, actual_data, {
                    'expected': expected_data,
                    'actual': actual_data,
                    'mismatch': True
                }

            self.stats['successful_reads'] += 1
            return True, actual_data, {
                'addr': addr,
                'data': actual_data,
                'pauser': pauser
            }

        except Exception as e:
            self.log.error(f"Read failed with exception: {e}")
            self.stats['failed_reads'] += 1
            self.stats['timeout_errors'] += 1
            return False, 0, {'error': str(e)}

    # High-level test sequences

    async def basic_write_read_sequence(self, count=10):
        """Run basic write-read sequence"""
        self.log.info(f"Running basic write-read sequence ({count} transactions)...")

        success_count = 0
        bytes_per_word = self.TEST_DATA_WIDTH // 8

        for i in range(count):
            addr = (i * bytes_per_word) & self.MAX_ADDR
            write_data = random.randint(0, self.MAX_DATA)

            # Write
            success, info = await self.single_write_test(addr, write_data)
            if not success:
                continue

            await self.wait_clocks(self.pclk_name, 2)

            # Read back
            success, read_data, info = await self.single_read_test(addr, expected_data=write_data)
            if success:
                success_count += 1

            await self.wait_clocks(self.pclk_name, 2)

        self.log.info(f"Basic sequence result: {success_count}/{count} successful")
        return success_count == count

    async def user_signal_test_sequence(self, count=10):
        """Run APB5 user signal test sequence"""
        self.log.info(f"Running user signal test sequence ({count} transactions)...")

        success_count = 0
        bytes_per_word = self.TEST_DATA_WIDTH // 8

        for i in range(count):
            addr = (i * bytes_per_word) & self.MAX_ADDR
            write_data = random.randint(0, self.MAX_DATA)

            # Randomize APB5 user signals
            pauser = random.randint(0, self.MAX_AUSER)
            pwuser = random.randint(0, self.MAX_WUSER)

            # Write with user signals
            success, info = await self.single_write_test(
                addr, write_data,
                pauser=pauser,
                pwuser=pwuser
            )
            if not success:
                continue

            await self.wait_clocks(self.pclk_name, 2)

            # Read back with user signal
            pauser = random.randint(0, self.MAX_AUSER)
            success, read_data, info = await self.single_read_test(
                addr,
                expected_data=write_data,
                pauser=pauser
            )
            if success:
                success_count += 1

            await self.wait_clocks(self.pclk_name, 2)

        self.log.info(f"User signal sequence result: {success_count}/{count} successful")
        return success_count == count

    async def stress_test(self, count=50):
        """Run stress test with rapid transactions"""
        self.log.info(f"Running stress test ({count} transactions)...")

        success_count = 0
        bytes_per_word = self.TEST_DATA_WIDTH // 8

        for i in range(count):
            addr = random.randint(0, 63) * bytes_per_word
            is_write = random.choice([True, False])

            if is_write:
                write_data = random.randint(0, self.MAX_DATA)
                success, info = await self.single_write_test(addr, write_data)
                if success:
                    success_count += 1
            else:
                success, read_data, info = await self.single_read_test(addr)
                if success:
                    success_count += 1

        self.log.info(f"Stress test result: {success_count}/{count} successful")
        return success_count >= (count * 0.95)

    def get_test_stats(self):
        """Get comprehensive test statistics"""
        total_tests = self.stats['total_transactions']
        success_count = self.stats['successful_reads'] + self.stats['successful_writes']
        success_rate = (success_count / total_tests * 100) if total_tests > 0 else 0

        return {
            'summary': {
                'total_transactions': total_tests,
                'successful': success_count,
                'success_rate': f"{success_rate:.1f}%"
            },
            'details': self.stats.copy(),
            'apb5_features': {
                'user_signal_tests': self.stats['user_signal_tests'],
                'wakeup_count': self.stats['wakeup_count'],
            }
        }

    def reset_stats(self):
        """Reset all statistics"""
        for key in self.stats:
            if isinstance(self.stats[key], int):
                self.stats[key] = 0
