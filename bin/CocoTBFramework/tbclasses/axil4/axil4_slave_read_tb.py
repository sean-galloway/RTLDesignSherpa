# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL4SlaveReadTB
# Purpose: AXIL4 Slave Read Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Slave Read Testbench

Testbench for testing AXIL4 slave read functionality using the CocoTB
framework's AXIL4 components. Focuses on AR and R channel validation
for register-oriented single transfer operations.

Based on AXI4 slave read testbench but simplified for AXIL4 specification:
- No burst support (single transfers only)
- No ID fields or transaction ordering
- Register access patterns
- Simplified timing and validation
"""
import os
import random

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXIL4 specific imports
from CocoTBFramework.components.axil4.axil4_factories import (
    create_axil4_master_rd, 
    create_axil4_slave_rd, 
    print_unified_compliance_reports
)
from CocoTBFramework.components.axil4.axil4_packet import AXIL4Packet
from CocoTBFramework.components.axil4.axil4_compliance_checker import AXIL4ComplianceChecker


class AXIL4SlaveReadTB(TBBase):
    """
    AXIL4 Slave Read testbench for register access testing.

    Tests basic read response functionality using AR and R channels with the
    axil4_slave_rd.sv RTL module. Focuses on single transfer operations
    typical of register interfaces.
    
    The slave receives read requests and validates proper data response behavior
    without the complexity of burst transactions or ID management.
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TIMEOUT_CYCLES = self.convert_to_int(os.environ.get('TIMEOUT_CYCLES', '1000'))

        # AXIL4 uses multi_sig=False for simpler signal handling
        self.use_multi_sig = True

        # Initialize random generator
        random.seed(self.SEED)

        # Setup clock and reset signals
        self.aclk = aclk
        self.aclk_name = aclk._name if aclk else 'aclk'
        self.aresetn = aresetn

        # Set limits based on widths (no ID limit for AXIL4)
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH) - 1
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH) - 1

        # Log configuration
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' AXIL4 Slave Read Test Configuration:\n'
        msg += '-'*80 + "\n"
        msg += f' Addr Width:   {self.TEST_ADDR_WIDTH}\n'
        msg += f' Data Width:   {self.TEST_DATA_WIDTH}\n'
        msg += f' Clock Period: {self.TEST_CLK_PERIOD} ns\n'
        msg += f' Max Addr:     0x{self.MAX_ADDR:X}\n'
        msg += f' Max Data:     0x{self.MAX_DATA:X}\n'
        msg += f' Seed:         {self.SEED}\n'
        msg += f' Single Transfer Protocol (AXIL4)\n'
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

        # Create AXIL4 slave (AR + R channels) - DUT side
        try:
            self.slave_components = create_axil4_slave_rd(
                dut=dut,
                clock=self.aclk,
                prefix='fub_',  # Slave backend interface
                log=self.log,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                memory_model=self.memory_model,
                multi_sig=self.use_multi_sig
            )

            # Access individual components
            self.ar_slave = self.slave_components['AR']    # Receives AR requests
            self.r_master = self.slave_components['R']     # Drives R responses
            self.axil4_slave = self.slave_components['interface']

            self.log.info("✅ AXIL4 Slave Read components created")
        except Exception as e:
            self.log.error(f"Failed to create slave components: {e}")
            raise

        # Create AXIL4 master to generate test transactions
        try:
            self.master_components = create_axil4_master_rd(
                dut=dut,
                clock=self.aclk,
                prefix='s_axil_',  # Master interface to slave
                log=self.log,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                multi_sig=True  # Use multi_sig for test master
            )

            # Access individual components
            self.ar_master = self.master_components['AR']  # Drives AR channel
            self.r_slave = self.master_components['R']     # Receives R channel
            self.test_master = self.master_components['interface']

            # Create compliance checker
            self.axil4_compliance_checker = AXIL4ComplianceChecker.create_if_enabled(
                dut=dut, 
                clock=self.aclk, 
                prefix='s_axil_', 
                log=self.log,
                data_width=self.TEST_DATA_WIDTH,
                addr_width=self.TEST_ADDR_WIDTH
            )

            self.log.info("✅ AXIL4 Master Read components created")
        except Exception as e:
            self.log.error(f"Failed to create master components: {e}")
            raise

        # Statistics tracking (simplified for AXIL4)
        self.stats = {
            'total_reads': 0,
            'successful_reads': 0,
            'failed_reads': 0,
            'timeout_errors': 0,
            'response_errors': 0,
            'data_mismatches': 0,
            'register_reads': 0,  # AXIL4 specific
            'test_duration': 0,
            'protocol_violations': 0
        }

        # Create timing profiles for register access patterns
        self.timing_profiles = {
            'fast': {'ar_delay': 0, 'r_delay': 1},
            'normal': {'ar_delay': 1, 'r_delay': 2},
            'slow': {'ar_delay': 3, 'r_delay': 5},
            'backtoback': {'ar_delay': 0, 'r_delay': 0},
            'stress': {'ar_delay': 0, 'r_delay': 1}
        }
        
        self.current_timing = 'normal'

        self.log.info("AXIL4 Slave Read testbench initialized successfully")

    def _initialize_memory_patterns(self):
        """Initialize memory with known test patterns for register emulation"""
        self.log.info("Initializing memory with register test patterns...")

        # Calculate bytes per register
        bytes_per_reg = self.TEST_DATA_WIDTH // 8

        # Pattern 1: Incremental register data starting at 0x1000
        base_addr = 0x1000
        for i in range(64):  # 64 registers
            addr = base_addr + (i * bytes_per_reg)
            data = 0x10000000 + i

            # Convert integer to bytearray before writing
            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_reg)
            self.memory_model.write(addr, data_bytes)

        # Pattern 2: Address-based pattern at 0x2000 (useful for address decode testing)
        base_addr = 0x2000
        for i in range(32):
            addr = base_addr + (i * bytes_per_reg)
            data = addr & self.MAX_DATA  # Address as data

            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_reg)
            self.memory_model.write(addr, data_bytes)

        # Pattern 3: Fixed register patterns at 0x3000
        test_patterns = [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0xABCDEF00]
        base_addr = 0x3000
        for i, pattern in enumerate(test_patterns * 16):  # Repeat patterns
            addr = base_addr + (i * bytes_per_reg)
            data = pattern & self.MAX_DATA

            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_reg)
            self.memory_model.write(addr, data_bytes)

        # Pattern 4: Status/control register simulation at 0x4000
        base_addr = 0x4000
        status_patterns = [0x00000001, 0x80000000, 0x55555555, 0xAAAAAAAA]
        for i, pattern in enumerate(status_patterns * 8):
            addr = base_addr + (i * bytes_per_reg)
            data = pattern & self.MAX_DATA

            data_bytes = self.memory_model.integer_to_bytearray(data, bytes_per_reg)
            self.memory_model.write(addr, data_bytes)

        self.log.info("✅ Memory register patterns initialized")

    def set_timing_profile(self, profile_name):
        """Set timing profile for register access testing"""
        if profile_name in self.timing_profiles:
            self.current_timing = profile_name
            self.log.info(f"Set timing profile to '{profile_name}'")
        else:
            self.log.warning(f"Unknown timing profile '{profile_name}', using 'normal'")
            self.current_timing = 'normal'

    def get_time_ns_str(self) -> str:
        """Get current simulation time as string."""
        try:
            import cocotb
            time_ns = cocotb.simulator.get_sim_time(units='ns')
            return f" @ {time_ns}ns"
        except:
            return ""

    async def assert_reset(self):
        """Assert reset and initialize components"""
        self.aresetn.value = 0
        await self.ar_slave.reset_bus()
        await self.r_master.reset_bus()
        await self.ar_master.reset_bus()
        await self.r_slave.reset_bus()
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    # Core test methods - AXIL4 slave perspective

    async def single_read_response_test(self, addr, expected_data=None):
        """
        Test slave response to a single AXIL4 read transaction.
        
        Uses test master to send read request, validates slave's data response.
        AXIL4 specific: Always single transfer, no ID field.

        Args:
            addr: Register address to read from
            expected_data: Expected data value (if None, read from memory model)

        Returns:
            tuple: (success, actual_data, response_info)
        """
        # Get expected data from memory model if not provided
        if expected_data is None:
            bytes_per_reg = self.TEST_DATA_WIDTH // 8
            expected_bytes = self.memory_model.read(addr, bytes_per_reg)
            if expected_bytes is None:
                expected_data = 0
            else:
                expected_data = int.from_bytes(expected_bytes, 'little') & self.MAX_DATA

        self.log.debug(f"AXIL4 slave read test: addr=0x{addr:08X}, expected=0x{expected_data:08X}")

        try:
            # Update statistics
            self.stats['total_reads'] += 1
            self.stats['register_reads'] += 1

            # Use test master to send single read request to slave
            # AXIL4: Always single transfer, no burst_len or ID parameters
            actual_data = await self.test_master.single_read(address=addr)

            # Validate the response
            actual_data &= self.MAX_DATA
            expected_data &= self.MAX_DATA

            if actual_data == expected_data:
                self.stats['successful_reads'] += 1
                return True, actual_data, {
                    'expected': expected_data,
                    'response': 'OKAY'
                }
            else:
                self.log.error(f"AXIL4 slave read data mismatch: addr=0x{addr:08X}, "
                              f"expected=0x{expected_data:08X}, actual=0x{actual_data:08X}")
                self.stats['failed_reads'] += 1
                self.stats['data_mismatches'] += 1
                return False, actual_data, {
                    'expected': expected_data,
                    'actual': actual_data,
                    'error': 'Data mismatch'
                }

        except Exception as e:
            self.log.error(f"AXIL4 slave read failed with exception: {e}")
            self.stats['failed_reads'] += 1
            self.stats['timeout_errors'] += 1
            return False, 0, {'error': str(e)}

    async def register_read_sequence_test(self, base_addr, reg_count, stride=None):
        """
        Test slave response to sequential register reads.
        
        AXIL4 specific: Tests register access patterns common in embedded systems.

        Args:
            base_addr: Starting register address
            reg_count: Number of registers to read
            stride: Address stride between registers (default: data_width/8)

        Returns:
            tuple: (success, results_list)
        """
        if stride is None:
            stride = self.TEST_DATA_WIDTH // 8

        self.log.debug(f"AXIL4 register sequence test: base=0x{base_addr:08X}, count={reg_count}")

        results = []
        success_count = 0

        for i in range(reg_count):
            addr = base_addr + (i * stride)
            success, data, info = await self.single_read_response_test(addr)
            
            results.append({
                'addr': addr,
                'success': success,
                'data': data,
                'info': info
            })

            if success:
                success_count += 1

            # Small delay between register reads
            profile = self.timing_profiles[self.current_timing]
            if profile['ar_delay'] > 0:
                await self.wait_clocks(self.aclk_name, profile['ar_delay'])

        overall_success = success_count == reg_count
        return overall_success, results

    # High-level test sequences

    async def basic_register_read_sequence(self, count=10):
        """Run basic single register read sequence on slave"""
        self.log.info(f"Running basic AXIL4 register read sequence ({count} reads)...")

        base_addr = 0x1000
        success, results = await self.register_read_sequence_test(base_addr, count)

        if success:
            self.log.info(f"Basic register sequence result: {len(results)}/{count} successful")
        else:
            failed_count = sum(1 for r in results if not r['success'])
            self.log.warning(f"Basic register sequence: {failed_count}/{count} failed")

        return success

    async def address_decode_test(self, address_ranges):
        """Test slave address decoding across different memory regions"""
        self.log.info(f"Running AXIL4 address decode test across {len(address_ranges)} ranges...")

        success_count = 0
        total_tests = 0

        for range_name, (base_addr, reg_count) in address_ranges.items():
            self.log.debug(f"Testing {range_name}: base=0x{base_addr:08X}, count={reg_count}")
            
            success, results = await self.register_read_sequence_test(base_addr, reg_count)
            total_tests += 1
            
            if success:
                success_count += 1
                self.log.info(f"✅ {range_name} address decode: PASS")
            else:
                failed_regs = [r for r in results if not r['success']]
                self.log.error(f"❌ {range_name} address decode: {len(failed_regs)} failures")

        overall_success = success_count == total_tests
        self.log.info(f"Address decode test result: {success_count}/{total_tests} ranges successful")
        return overall_success

    async def stress_register_access_test(self, count=50):
        """Run stress test with rapid register accesses"""
        self.log.info(f"Running AXIL4 stress register access test ({count} reads)...")

        # Set fast timing
        self.set_timing_profile('stress')

        success_count = 0
        address_ranges = [0x1000, 0x2000, 0x3000, 0x4000]

        for i in range(count):
            # Random register address in test ranges
            base_addr = random.choice(address_ranges)
            reg_offset = random.randint(0, 15) * (self.TEST_DATA_WIDTH // 8)
            addr = base_addr + reg_offset

            success, data, info = await self.single_read_response_test(addr)
            if success:
                success_count += 1

            # Minimal delay for stress testing
            await self.wait_clocks(self.aclk_name, 1)

        success_rate = success_count / count if count > 0 else 0
        self.log.info(f"AXIL4 stress test result: {success_count}/{count} successful ({success_rate:.1%})")
        return success_rate >= 0.95  # Allow 5% failure in stress test

    async def timing_profile_test(self, profile_name, test_count=20):
        """Test slave responses with specific timing profile"""
        self.log.info(f"Running AXIL4 timing profile test: {profile_name}")

        self.set_timing_profile(profile_name)
        
        success_count = 0
        base_addr = 0x2000

        for i in range(test_count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            success, data, info = await self.single_read_response_test(addr)
            
            if success:
                success_count += 1

            # Apply timing profile delays
            profile = self.timing_profiles[profile_name]
            await self.wait_clocks(self.aclk_name, profile['r_delay'])

        success_rate = success_count / test_count if test_count > 0 else 0
        self.log.info(f"Timing profile '{profile_name}' result: {success_count}/{test_count} ({success_rate:.1%})")
        return success_rate >= 0.90

    async def register_pattern_validation_test(self):
        """Test slave responses against known register patterns"""
        self.log.info("Running AXIL4 register pattern validation test...")

        # Calculate byte stride based on data width (capture in lambda closure)
        bytes_per_reg = self.TEST_DATA_WIDTH // 8

        pattern_tests = [
            ("Incremental Pattern", 0x1000, 16, lambda i: 0x10000000 + i),
            ("Address Pattern", 0x2000, 8, lambda i, bpr=bytes_per_reg: (0x2000 + i*bpr) & self.MAX_DATA),
            ("Fixed Patterns", 0x3000, 4, lambda i: [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0xABCDEF00][i % 4]),
            ("Status Patterns", 0x4000, 4, lambda i: [0x00000001, 0x80000000, 0x55555555, 0xAAAAAAAA][i % 4])
        ]

        pattern_results = []
        
        for pattern_name, base_addr, count, pattern_func in pattern_tests:
            self.log.debug(f"Testing {pattern_name}...")
            
            success_count = 0
            for i in range(count):
                addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
                expected_data = pattern_func(i) & self.MAX_DATA
                
                success, actual_data, info = await self.single_read_response_test(addr, expected_data)
                if success:
                    success_count += 1
                else:
                    self.log.error(f"{pattern_name} failed at offset {i}: "
                                  f"expected=0x{expected_data:08X}, actual=0x{actual_data:08X}")

            pattern_success = success_count == count
            pattern_results.append((pattern_name, pattern_success, success_count, count))
            
            status = "✅ PASS" if pattern_success else "❌ FAIL"
            self.log.info(f"{pattern_name}: {status} ({success_count}/{count})")

        overall_success = all(result[1] for result in pattern_results)
        return overall_success, pattern_results

    def get_test_stats(self):
        """Get comprehensive test statistics"""
        total_tests = self.stats['total_reads']
        success_rate = (self.stats['successful_reads'] / total_tests * 100) if total_tests > 0 else 0
        
        return {
            'summary': {
                'total_reads': total_tests,
                'successful_reads': self.stats['successful_reads'],
                'success_rate': f"{success_rate:.1f}%",
                'register_reads': self.stats['register_reads']
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
        self.log.info("Printing AXIL4 compliance reports...")
        
        print_unified_compliance_reports(self.master_components)
        print_unified_compliance_reports(self.slave_components)
        
        # Print standalone compliance checker report if enabled
        if hasattr(self, 'axil4_compliance_checker') and self.axil4_compliance_checker:
            self.axil4_compliance_checker.print_compliance_report()
        else:
            self.log.info("AXIL4 compliance checking disabled (set AXIL4_COMPLIANCE_CHECK=1 to enable)")
