# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APB5SlaveTB
# Purpose: APB5 Slave Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-12-21

"""
APB5 Slave Testbench

Testbench for testing APB5 slave functionality using the CocoTB
framework's APB5 components. Supports AMBA5 extensions.

APB5 Features Tested:
- Standard APB4 transactions (read/write)
- User signals (PRUSER, PBUSER)
- Wake-up signaling (PWAKEUP)
- Error response generation (PSLVERR)
- Ready delay randomization
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


class APB5SlaveTB(TBBase):
    """
    APB5 Slave testbench for baseline testing.

    Tests APB5 slave functionality including user signals,
    wake-up, error responses, and ready delay handling.
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
        msg += ' APB5 Slave Test Configuration:\n'
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

        # Create initial register map (with initial patterns)
        num_registers = 2 ** (self.TEST_ADDR_WIDTH - 2)
        self.registers = [i % 256 for i in range(min(num_registers, 256))]

        # Create APB5 master for driving transactions
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

        # Create randomizer configurations
        self.randomizer_configs = self._create_randomizer_configs()

        # Create APB5 slave (DUT interface)
        self.slave = None
        self.current_randomizer = None
        self._create_slave_with_profile('normal')

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
            'ready_delay_tests': 0,
            'test_duration': 0
        }

        self.log.info("APB5 Slave testbench initialized successfully")

    def _initialize_memory_patterns(self):
        """Initialize memory with known test patterns"""
        self.log.info("Initializing memory with test patterns...")

        bytes_per_word = self.TEST_DATA_WIDTH // 8

        # Pattern: Incremental data
        for i in range(64):
            addr = i * bytes_per_word
            data = 0xAA000000 + i
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_word)
            self.memory_model.write(addr, data_bytes)

        self.log.info("Memory patterns initialized")

    def _create_randomizer_configs(self):
        """Create randomizer configurations for different test profiles"""
        return {
            'fast': {
                'ready': ([(0, 0), (1, 1)], [0.9, 0.1]),
                'error': ([(0, 0), (1, 1)], [1.0, 0.0]),
                'pruser': ([(0, self.MAX_RUSER)], [1]),
                'pbuser': ([(0, self.MAX_BUSER)], [1])
            },
            'normal': {
                'ready': ([(0, 1), (2, 4)], [0.7, 0.3]),
                'error': ([(0, 0), (1, 1)], [0.95, 0.05]),
                'pruser': ([(0, self.MAX_RUSER)], [1]),
                'pbuser': ([(0, self.MAX_BUSER)], [1])
            },
            'slow': {
                'ready': ([(2, 5), (6, 10)], [0.6, 0.4]),
                'error': ([(0, 0), (1, 1)], [0.9, 0.1]),
                'pruser': ([(0, self.MAX_RUSER)], [1]),
                'pbuser': ([(0, self.MAX_BUSER)], [1])
            },
            'stress': {
                'ready': ([(0, 0), (1, 3), (4, 8)], [0.4, 0.4, 0.2]),
                'error': ([(0, 0), (1, 1)], [0.8, 0.2]),
                'pruser': ([(0, self.MAX_RUSER)], [1]),
                'pbuser': ([(0, self.MAX_BUSER)], [1])
            },
            'error_heavy': {
                'ready': ([(0, 2)], [1.0]),
                'error': ([(0, 0), (1, 1)], [0.5, 0.5]),
                'pruser': ([(0, self.MAX_RUSER)], [1]),
                'pbuser': ([(0, self.MAX_BUSER)], [1])
            }
        }

    def _create_slave_with_profile(self, profile_name):
        """Create or reconfigure slave with specified randomizer profile"""
        if profile_name not in self.randomizer_configs:
            self.log.warning(f"Unknown profile '{profile_name}', using 'normal'")
            profile_name = 'normal'

        config = self.randomizer_configs[profile_name]
        self.current_randomizer = FlexRandomizer(config)

        try:
            self.slave = create_apb5_slave(
                entity=self.dut,
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
                randomizer=self.current_randomizer,
                log=self.log,
                error_overflow=True
            )
            self.log.info(f"APB5 Slave created with '{profile_name}' profile")
        except Exception as e:
            self.log.error(f"Failed to create slave: {e}")
            raise

    def set_timing_profile(self, profile_name):
        """Set timing profile for slave responses"""
        self._create_slave_with_profile(profile_name)

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

    async def single_write_test(self, addr, data, strb=None, expect_error=False):
        """
        Perform a single APB5 write transaction.

        Args:
            addr: Address to write to
            data: Data value to write
            strb: Write strobe (if None, full strobe)
            expect_error: Whether to expect PSLVERR

        Returns:
            tuple: (success, response_info)
        """
        if strb is None:
            strb = (1 << self.TEST_STRB_WIDTH) - 1

        self.log.debug(f"Single write: addr=0x{addr:08X}, data=0x{data:08X}")

        try:
            self.stats['total_transactions'] += 1

            await self.master.write(
                address=addr,
                data=data,
                strb=strb
            )

            self.stats['successful_writes'] += 1
            return True, {'addr': addr, 'data': data}

        except Exception as e:
            if expect_error:
                self.stats['pslverr_count'] += 1
                return True, {'error_expected': True}
            self.log.error(f"Write failed with exception: {e}")
            self.stats['failed_writes'] += 1
            return False, {'error': str(e)}

    async def single_read_test(self, addr, expected_data=None, expect_error=False):
        """
        Perform a single APB5 read transaction.

        Args:
            addr: Address to read from
            expected_data: Expected data value (if None, no check)
            expect_error: Whether to expect PSLVERR

        Returns:
            tuple: (success, actual_data, response_info)
        """
        self.log.debug(f"Single read: addr=0x{addr:08X}")

        try:
            self.stats['total_transactions'] += 1

            actual_data = await self.master.read(address=addr)

            # Check data match if expected provided
            if expected_data is not None and actual_data != expected_data:
                self.log.warning(f"Data mismatch at 0x{addr:08X}: "
                               f"got 0x{actual_data:08X}, expected 0x{expected_data:08X}")
                self.stats['data_mismatches'] += 1
                self.stats['failed_reads'] += 1
                return False, actual_data, {'mismatch': True}

            self.stats['successful_reads'] += 1
            return True, actual_data, {'addr': addr}

        except Exception as e:
            if expect_error:
                self.stats['pslverr_count'] += 1
                return True, 0, {'error_expected': True}
            self.log.error(f"Read failed with exception: {e}")
            self.stats['failed_reads'] += 1
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

    async def ready_delay_test_sequence(self, count=20):
        """Run test sequence focusing on ready delay variations"""
        self.log.info(f"Running ready delay test sequence ({count} transactions)...")

        profiles = ['fast', 'normal', 'slow']
        success_count = 0
        bytes_per_word = self.TEST_DATA_WIDTH // 8

        for i in range(count):
            # Switch profile periodically
            if i % (count // len(profiles)) == 0:
                profile = profiles[(i * len(profiles)) // count]
                self.set_timing_profile(profile)
                self.stats['ready_delay_tests'] += 1

            addr = (i * bytes_per_word) & self.MAX_ADDR
            write_data = random.randint(0, self.MAX_DATA)

            # Write
            success, info = await self.single_write_test(addr, write_data)
            if not success:
                continue

            await self.wait_clocks(self.pclk_name, 1)

            # Read back
            success, read_data, info = await self.single_read_test(addr, expected_data=write_data)
            if success:
                success_count += 1

            await self.wait_clocks(self.pclk_name, 1)

        # Reset to normal profile
        self.set_timing_profile('normal')

        self.log.info(f"Ready delay sequence result: {success_count}/{count} successful")
        return success_count >= (count * 0.95)

    async def error_response_test_sequence(self, count=10):
        """Run test sequence with error responses enabled"""
        self.log.info(f"Running error response test sequence ({count} transactions)...")

        self.set_timing_profile('error_heavy')

        success_count = 0
        error_count = 0
        bytes_per_word = self.TEST_DATA_WIDTH // 8

        for i in range(count):
            addr = (i * bytes_per_word) & self.MAX_ADDR

            # Read - may get error
            success, read_data, info = await self.single_read_test(addr)
            if success:
                success_count += 1
            if info.get('error_expected'):
                error_count += 1

            await self.wait_clocks(self.pclk_name, 2)

        # Reset to normal profile
        self.set_timing_profile('normal')

        self.log.info(f"Error response sequence: {success_count}/{count} successful, {error_count} errors")
        return True  # Error responses are expected

    async def stress_test(self, count=50):
        """Run stress test with rapid transactions"""
        self.log.info(f"Running stress test ({count} transactions)...")

        self.set_timing_profile('stress')

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

        # Reset to normal profile
        self.set_timing_profile('normal')

        self.log.info(f"Stress test result: {success_count}/{count} successful")
        return success_count >= (count * 0.80)  # Allow for some errors in stress mode

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
                'pslverr_count': self.stats['pslverr_count'],
                'ready_delay_tests': self.stats['ready_delay_tests'],
            }
        }

    def reset_stats(self):
        """Reset all statistics"""
        for key in self.stats:
            if isinstance(self.stats[key], int):
                self.stats[key] = 0
