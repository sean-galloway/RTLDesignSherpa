# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL4MasterReadTB
# Purpose: AXIL4 Read Master Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Read Master Testbench

Simple testbench for testing AXIL4 read master functionality using the CocoTB
framework's AXIL4 components. Focuses on AR and R channel validation.

Based on the AXI4 master read testbench pattern but simplified for AXIL4 register access.
"""
import os
import random

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXIL4 specific imports
from CocoTBFramework.components.axil4.axil4_factories import create_axil4_master_rd, create_axil4_slave_rd, print_unified_compliance_reports
from CocoTBFramework.components.axil4.axil4_packet import AXIL4Packet
from CocoTBFramework.components.axil4.axil4_compliance_checker import AXIL4ComplianceChecker


class AXIL4MasterReadTB(TBBase):
    """
    Simple AXIL4 Read Master testbench for baseline testing.

    Tests basic read functionality using AR and R channels with the
    axil4_master_rd.sv RTL module.
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TIMEOUT_CYCLES = self.convert_to_int(os.environ.get('TIMEOUT_CYCLES', '1000'))

        # AXIL4 always uses multi_sig=True for real RTL (no stub versions)
        self.use_multi_sig = True

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.aclk = aclk
        self.aclk_name = aclk._name if aclk else 'aclk'
        self.aresetn = aresetn

        # Set limits based on widths
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH) - 1

        # Log configuration
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' AXIL4 Read Master Test Configuration:\n'
        msg += '-'*80 + "\n"
        msg += f' Addr Width:   {self.TEST_ADDR_WIDTH}\n'
        msg += f' Data Width:   {self.TEST_DATA_WIDTH}\n'
        msg += f' Clock Period: {self.TEST_CLK_PERIOD} ns\n'
        msg += f' Max Addr:     0x{self.MAX_ADDR:X}\n'
        msg += f' Max Data:     0x{self.MAX_DATA:X}\n'
        msg += f' Seed:         {self.SEED}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Create memory model for the slave side
        bytes_per_line = max(4, (self.TEST_DATA_WIDTH + 7) // 8)
        self.memory_model = MemoryModel(
            num_lines=65536,
            bytes_per_line=bytes_per_line,
            log=self.log
        )

        # Initialize memory with test patterns
        self._initialize_memory_patterns()

        # Create AXIL4 master (AR + R channels only)
        try:
            self.master_components = create_axil4_master_rd(
                dut=dut,
                clock=self.aclk,
                prefix='fub_',
                log=self.log,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                multi_sig=self.use_multi_sig
            )

            # Access individual components
            self.ar_master = self.master_components['AR']  # Drives AR channel
            self.r_slave = self.master_components['R']     # Receives R channel
            self.axil4_master = self.master_components['interface']

            self.log.info("AXIL4 Master Read components created")
        except Exception as e:
            self.log.error(f"Failed to create master components: {e}")
            raise

        # Create AXIL4 slave to respond on the master interface side
        try:
            self.slave_components = create_axil4_slave_rd(
                dut=dut,
                clock=self.aclk,
                prefix='m_axil_',                 # Receives m_axil_ar*, drives m_axil_r*
                log=self.log,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                memory_model=self.memory_model,
                multi_sig=True
            )

            # Access individual components
            self.ar_slave = self.slave_components['AR']    # Receives AR requests
            self.r_master = self.slave_components['R']     # Drives R responses

            self.log.info("AXIL4 Slave Read components created")
        except Exception as e:
            self.log.error(f"Failed to create slave components: {e}")
            raise

        # Compliance checker
        self.axil4_compliance_checker = AXIL4ComplianceChecker.create_if_enabled(
            dut=dut, 
            clock=self.aclk, 
            prefix='m_axil_', 
            log=self.log, 
            data_width=self.TEST_DATA_WIDTH, 
            addr_width=self.TEST_ADDR_WIDTH
        )

        # Statistics tracking
        self.stats = {
            'total_reads': 0,
            'successful_reads': 0,
            'failed_reads': 0,
            'timeout_errors': 0,
            'response_errors': 0,
            'data_mismatches': 0,
            'register_reads': 0,
            'test_duration': 0
        }

        # Create randomizer configurations for different test profiles
        self.randomizer_configs = self._create_axil4_randomizer_configs()
        self.set_timing_profile('normal')

        self.log.info("AXIL4 Read Master testbench initialized successfully")

    def _initialize_memory_patterns(self):
        """Initialize memory with known test patterns"""
        self.log.info("Initializing memory with test patterns...")

        # Calculate bytes per word
        bytes_per_word = self.TEST_DATA_WIDTH // 8

        # Pattern 1: Incremental data starting at 0x1000
        base_addr = 0x1000
        for i in range(64):  # 64 words
            addr = base_addr + (i * bytes_per_word)
            data = 0x10000000 + i

            # Convert integer to bytearray before writing
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_word)
            self.memory_model.write(addr, data_bytes)

        # Pattern 2: Address-based pattern at 0x2000
        base_addr = 0x2000
        for i in range(32):
            addr = base_addr + (i * bytes_per_word)
            data = addr & self.MAX_DATA  # Address as data

            # Convert integer to bytearray before writing
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_word)
            self.memory_model.write(addr, data_bytes)

        # Pattern 3: Fixed patterns at 0x3000
        test_patterns = [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0xABCDEF00]
        base_addr = 0x3000
        for i, pattern in enumerate(test_patterns * 8):  # Repeat patterns
            addr = base_addr + (i * bytes_per_word)
            data = pattern & self.MAX_DATA

            # Convert integer to bytearray before writing
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_word)
            self.memory_model.write(addr, data_bytes)

        self.log.info("Memory patterns initialized")

    def _create_axil4_randomizer_configs(self):
        """Create AXIL4-specific randomizer configurations"""
        configs = {
            'fast': {
                'master_delay': ([(0, 0), (1, 2)], [0.8, 0.2]),
                'slave_delay': ([(0, 1), (1, 2)], [0.7, 0.3])
            },
            'normal': {
                'master_delay': ([(0, 2), (3, 5)], [0.6, 0.4]),
                'slave_delay': ([(1, 3), (4, 6)], [0.6, 0.4])
            },
            'slow': {
                'master_delay': ([(2, 5), (6, 10)], [0.5, 0.5]),
                'slave_delay': ([(3, 7), (8, 12)], [0.5, 0.5])
            },
            'backtoback': {
                'master_delay': ([(0, 0)], [1.0]),
                'slave_delay': ([(0, 0)], [1.0])
            },
            'stress': {
                'master_delay': ([(0, 0), (1, 3), (4, 8)], [0.5, 0.3, 0.2]),
                'slave_delay': ([(0, 1), (2, 5), (6, 10)], [0.4, 0.4, 0.2])
            }
        }
        return configs

    def set_timing_profile(self, profile_name):
        """Set timing profile for the test"""
        if profile_name in self.randomizer_configs:
            config = self.randomizer_configs[profile_name]
            # Apply timing configuration to master and slave
            self.log.info(f"Set timing profile to '{profile_name}'")
        else:
            self.log.warning(f"Unknown timing profile '{profile_name}', using 'normal'")

    async def assert_reset(self):
        """Assert reset and initialize components"""
        self.aresetn.value = 0
        await self.ar_master.reset_bus()
        await self.r_master.reset_bus()
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    # Core test methods

    async def register_read_test(self, addr, expected_data=None, prot=0):
        """
        Perform a single AXIL4 register read transaction

        Args:
            addr: Address to read from
            expected_data: Expected data value (if None, read from memory model)
            prot: Protection field value

        Returns:
            tuple: (success, actual_data, response_info)
        """
        # Get expected data from memory model if not provided
        if expected_data is None:
            bytes_per_word = self.TEST_DATA_WIDTH // 8
            expected_data_bytes = self.memory_model.read(addr, bytes_per_word)
            expected_data = int.from_bytes(expected_data_bytes, byteorder='little')
        
        self.log.debug(f"Register read: addr=0x{addr:08X}, prot={prot}, expected=0x{expected_data:08X}")

        try:
            # Update statistics
            self.stats['total_reads'] += 1
            self.stats['register_reads'] += 1

            # Use the AXIL4 interface method (single transfer only)
            actual_data = await self.axil4_master.single_read(
                address=addr,
                prot=prot
            )

            # Check data match
            if actual_data != expected_data:
                self.log.warning(f"Data mismatch at 0x{addr:08X}: got 0x{actual_data:08X}, expected 0x{expected_data:08X}")
                self.stats['data_mismatches'] += 1
                self.stats['failed_reads'] += 1
                return False, actual_data, {
                    'expected': expected_data, 
                    'actual': actual_data, 
                    'mismatch': True
                }

            # Success case
            self.stats['successful_reads'] += 1
            return True, actual_data, {
                'expected': expected_data, 
                'actual': actual_data,
                'prot': prot
            }

        except Exception as e:
            self.log.error(f"Register read failed with exception: {e}")
            self.stats['failed_reads'] += 1
            self.stats['timeout_errors'] += 1
            return False, 0, {'error': str(e)}

    async def simple_read_test(self, addr, expected_data=None):
        """
        Perform a simple AXIL4 read using the simple_read interface method

        Args:
            addr: Address to read from
            expected_data: Expected data value (if None, read from memory model)

        Returns:
            tuple: (success, actual_data, response_info)
        """
        # Get expected data from memory model if not provided
        if expected_data is None:
            bytes_per_word = self.TEST_DATA_WIDTH // 8
            expected_data_bytes = self.memory_model.read(addr, bytes_per_word)
            expected_data = int.from_bytes(expected_data_bytes, byteorder='little')
        
        self.log.debug(f"Simple read: addr=0x{addr:08X}, expected=0x{expected_data:08X}")

        try:
            # Update statistics
            self.stats['total_reads'] += 1

            # Use the simple_read interface method (backward compatibility)
            actual_data = await self.axil4_master.simple_read(address=addr)

            # Check data match
            if actual_data != expected_data:
                self.log.warning(f"Data mismatch at 0x{addr:08X}: got 0x{actual_data:08X}, expected 0x{expected_data:08X}")
                self.stats['data_mismatches'] += 1
                self.stats['failed_reads'] += 1
                return False, actual_data, {
                    'expected': expected_data, 
                    'actual': actual_data, 
                    'mismatch': True
                }

            # Success case
            self.stats['successful_reads'] += 1
            return True, actual_data, {
                'expected': expected_data, 
                'actual': actual_data
            }

        except Exception as e:
            self.log.error(f"Simple read failed with exception: {e}")
            self.stats['failed_reads'] += 1
            self.stats['timeout_errors'] += 1
            return False, 0, {'error': str(e)}

    # High-level test sequences

    async def basic_read_sequence(self, count=10):
        """Run basic single read sequence"""
        self.log.info(f"Running basic read sequence ({count} reads)...")

        success_count = 0
        base_addr = 0x1000

        for i in range(count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            success, data, info = await self.register_read_test(addr)
            if success:
                success_count += 1

            # Small delay between reads
            await self.wait_clocks(self.aclk_name, 2)

        self.log.info(f"Basic sequence result: {success_count}/{count} successful")
        return success_count == count

    async def register_access_sequence(self, count=10):
        """Run register access sequence using different interface methods"""
        self.log.info(f"Running register access sequence ({count} reads)...")

        success_count = 0
        base_addr = 0x2000

        for i in range(count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            
            # Alternate between different interface methods
            if i % 3 == 0:
                success, data, info = await self.register_read_test(addr)
            elif i % 3 == 1:
                success, data, info = await self.simple_read_test(addr)
            else:
                # Use read_register method (API consistency)
                try:
                    actual_data = await self.axil4_master.read_register(address=addr)
                    success = True
                    self.stats['total_reads'] += 1
                    self.stats['successful_reads'] += 1
                except Exception as e:
                    self.log.error(f"Read register failed: {e}")
                    success = False
                    self.stats['total_reads'] += 1
                    self.stats['failed_reads'] += 1

            if success:
                success_count += 1

            # Small delay between reads
            await self.wait_clocks(self.aclk_name, 2)

        self.log.info(f"Register access sequence result: {success_count}/{count} successful")
        return success_count == count

    async def stress_read_test(self, count=50):
        """Run stress test with rapid reads"""
        self.log.info(f"Running stress read test ({count} reads)...")

        # Set fast timing
        self.set_timing_profile('stress')

        success_count = 0
        for i in range(count):
            # Random address in test ranges
            addr_ranges = [0x1000, 0x2000, 0x3000]
            base_addr = random.choice(addr_ranges)
            offset = random.randint(0, 31) * (self.TEST_DATA_WIDTH // 8)
            addr = base_addr + offset

            success, data, info = await self.register_read_test(addr)
            if success:
                success_count += 1

        self.log.info(f"Stress test result: {success_count}/{count} successful")
        return success_count >= (count * 0.95)  # Allow 5% failure in stress test

    async def address_alignment_test(self):
        """Test address alignment requirements for AXIL4"""
        self.log.info("Running address alignment test...")

        bytes_per_word = self.TEST_DATA_WIDTH // 8
        success_count = 0
        test_count = 0

        # Test aligned addresses (should work)
        aligned_addresses = [0x1000, 0x1000 + bytes_per_word, 0x1000 + 2*bytes_per_word]
        for addr in aligned_addresses:
            test_count += 1
            success, data, info = await self.register_read_test(addr)
            if success:
                success_count += 1
                self.log.debug(f"Aligned address 0x{addr:08X}: SUCCESS")
            else:
                self.log.warning(f"Aligned address 0x{addr:08X}: FAILED")

        # Test misaligned addresses (may fail depending on implementation)
        if bytes_per_word > 1:
            misaligned_addresses = [0x1001, 0x1002, 0x1003]
            for addr in misaligned_addresses:
                if addr < 0x1000 + bytes_per_word:  # Keep within valid range
                    test_count += 1
                    success, data, info = await self.register_read_test(addr)
                    # Note: AXIL4 may or may not support misaligned access
                    self.log.debug(f"Misaligned address 0x{addr:08X}: {'SUCCESS' if success else 'FAILED (expected)'}")
                    # Don't count misaligned failures as test failures

        self.log.info(f"Address alignment test: {success_count}/{len(aligned_addresses)} aligned addresses successful")
        return success_count == len(aligned_addresses)

    def get_test_stats(self):
        """Get comprehensive test statistics"""
        total_tests = self.stats['total_reads']
        success_rate = (self.stats['successful_reads'] / total_tests * 100) if total_tests > 0 else 0
        
        self.finalize_test()

        return {
            'summary': {
                'total_reads': total_tests,
                'successful_reads': self.stats['successful_reads'],
                'success_rate': f"{success_rate:.1f}%"
            },
            'details': self.stats.copy()
        }

    def reset_stats(self):
        """Reset all statistics"""
        for key in self.stats:
            if isinstance(self.stats[key], int):
                self.stats[key] = 0

    def finalize_test(self):
        """Print compliance reports for all AXIL4 components."""
        # Print compliance reports for master and slave components  
        print_unified_compliance_reports(self.master_components)
        print_unified_compliance_reports(self.slave_components)
        
        # Print standalone compliance checker report if enabled
        if hasattr(self, 'axil4_compliance_checker') and self.axil4_compliance_checker:
            self.axil4_compliance_checker.print_compliance_report()
