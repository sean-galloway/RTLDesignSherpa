# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL4SlaveWriteTB
# Purpose: AXIL4 Slave Write Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Slave Write Testbench

Testbench for testing AXIL4 slave write functionality using the CocoTB
framework's AXIL4 components. Focuses on AW, W, and B channel validation
for single transfer register write operations.

Based on AXI4 slave write testbench but simplified for AXIL4 specification:
- No burst support (single transfers only)
- No ID fields or transaction ordering
- Register write patterns and validation
- Simplified timing and response verification
"""
import os
import random
import asyncio
from typing import List, Dict, Any, Tuple, Optional

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel

# AXIL4 specific imports
from CocoTBFramework.components.axil4.axil4_factories import (
    create_axil4_master_wr, 
    create_axil4_slave_wr, 
    print_unified_compliance_reports
)
from CocoTBFramework.components.axil4.axil4_packet import AXIL4Packet
from CocoTBFramework.components.axil4.axil4_compliance_checker import AXIL4ComplianceChecker


class AXIL4SlaveWriteTB(TBBase):
    """
    AXIL4 Slave Write testbench for register write testing.

    Tests write response functionality using AW, W, and B channels with the
    axil4_slave_wr.sv RTL module. Focuses on single transfer operations
    typical of register interfaces.
    
    The slave receives write requests and validates proper response behavior
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
        msg += ' AXIL4 Slave Write Test Configuration:\n'
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
            num_lines=65536*2,  # Large memory for testing
            bytes_per_line=bytes_per_line,
            log=self.log,
            debug=True
        )

        # Statistics tracking (simplified for AXIL4)
        self.stats = {
            'total_writes': 0,
            'successful_writes': 0,
            'failed_writes': 0,
            'register_writes': 0,  # AXIL4 specific
            'data_mismatches': 0,
            'response_errors': 0,
            'timeout_errors': 0,
            'protocol_violations': 0
        }

        # Create AXIL4 slave write interface (DUT side)
        try:
            self.slave_components = create_axil4_slave_wr(
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
            self.aw_slave = self.slave_components['AW']    # Receives AW requests
            self.w_slave = self.slave_components['W']      # Receives W data
            self.b_master = self.slave_components['B']     # Drives B responses
            self.axil4_slave = self.slave_components['interface']

            self.log.info("✅ AXIL4 Slave Write components created")
        except Exception as e:
            self.log.error(f"Failed to create slave components: {e}")
            raise

        # Create AXIL4 master to generate test transactions
        try:
            self.master_components = create_axil4_master_wr(
                dut=dut,
                clock=self.aclk,
                prefix='s_axil_',  # Master interface to slave
                log=self.log,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                multi_sig=True  # Use multi_sig for test master
            )

            # Access individual components
            self.aw_master = self.master_components['AW']  # Drives AW channel
            self.w_master = self.master_components['W']    # Drives W channel
            self.b_slave = self.master_components['B']     # Receives B channel
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

            self.log.info("✅ AXIL4 Master Write components created")
        except Exception as e:
            self.log.error(f"Failed to create master components: {e}")
            raise

        # Create timing profiles for register write patterns
        self.timing_profiles = {
            'fast': {'aw_delay': 0, 'w_delay': 0, 'b_delay': 1},
            'normal': {'aw_delay': 1, 'w_delay': 1, 'b_delay': 2},
            'slow': {'aw_delay': 3, 'w_delay': 3, 'b_delay': 5},
            'backtoback': {'aw_delay': 0, 'w_delay': 0, 'b_delay': 0},
            'stress': {'aw_delay': 0, 'w_delay': 0, 'b_delay': 1}
        }
        
        self.current_timing = 'normal'

        self.log.info("AXIL4 Slave Write testbench initialized successfully")

    def set_timing_profile(self, profile_name):
        """Set timing profile for register write testing"""
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
        await self.aw_slave.reset_bus()
        await self.w_slave.reset_bus()
        await self.b_master.reset_bus()
        await self.aw_master.reset_bus()
        await self.w_master.reset_bus()
        await self.b_slave.reset_bus()
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    # Core test methods - AXIL4 slave perspective

    async def single_write_response_test(self, address: int, data: int, strb: Optional[int] = None) -> Tuple[bool, Dict[str, Any]]:
        """
        Test slave response to a single AXIL4 write transaction.
        
        Uses test master to send write request, validates slave's response.
        AXIL4 specific: Always single transfer, no ID field.

        Args:
            address: Register address to write to
            data: Data value to write
            strb: Write strobes (None = all bytes enabled)

        Returns:
            tuple: (success, response_info)
        """
        try:
            # Update statistics
            self.stats['total_writes'] += 1
            self.stats['register_writes'] += 1

            # Calculate default strobe if not provided
            if strb is None:
                strb_width = self.TEST_DATA_WIDTH // 8
                strb = (1 << strb_width) - 1  # All bytes enabled

            self.log.debug(f"AXIL4 slave write test: addr=0x{address:08X}, data=0x{data:08X}, strb=0x{strb:X}")

            # Use test master to send single write request to slave
            # AXIL4: Always single transfer, no ID parameters
            result = await self.test_master.single_write(address=address, data=data, strb=strb)

            # Verify the slave received and processed the write correctly
            verify_success = await self.verify_slave_write(address, data, strb)
            if not verify_success:
                self.stats['failed_writes'] += 1
                self.stats['data_mismatches'] += 1

                error_info = {
                    'error': 'Slave write verification failed',
                    'address': address,
                    'data': data,
                    'strobe': strb
                }
                self.log.warning(f"AXIL4 slave verification failed: {error_info}")
                return False, error_info

            # Success
            self.stats['successful_writes'] += 1

            success_info = {
                'success': True,
                'response': result if isinstance(result, int) else 0,  # AXIL4 returns response code
                'address': address,
                'data': data,
                'strobe': strb
            }

            return True, success_info

        except asyncio.TimeoutError:
            self.stats['failed_writes'] += 1
            self.stats['timeout_errors'] += 1
            error_info = {'error': 'Transaction timeout', 'address': address, 'data': data}
            self.log.error(f"AXIL4 write timeout: {error_info}")
            return False, error_info

        except Exception as e:
            self.stats['failed_writes'] += 1
            error_info = {
                'error': str(e),
                'exception': type(e).__name__,
                'address': address,
                'data': data
            }
            self.log.error(f"AXIL4 write exception: {error_info}")
            return False, error_info

    async def verify_slave_write(self, address: int, expected_data: int, strb: int) -> bool:
        """
        Verify that the slave correctly processed a write transaction.

        Args:
            address: Address to verify
            expected_data: Expected data value
            strb: Write strobes used

        Returns:
            True if verification passed
        """
        try:
            # Calculate bytes per register
            bytes_per_reg = self.TEST_DATA_WIDTH // 8

            # Read from memory model
            read_data = self.memory_model.read(address, bytes_per_reg)
            if read_data is None:
                self.log.warning(f"AXIL4 verify failed: No data at address 0x{address:08X}")
                return False

            # Convert bytes to integer
            actual_data = int.from_bytes(read_data, 'little')

            # Apply strobe mask to expected data for comparison
            expected_masked = 0
            actual_masked = 0
            
            for byte_idx in range(bytes_per_reg):
                if strb & (1 << byte_idx):
                    # This byte should have been written
                    byte_mask = 0xFF << (byte_idx * 8)
                    expected_masked |= expected_data & byte_mask
                    actual_masked |= actual_data & byte_mask

            # Mask both values to the actual data width
            expected_masked &= self.MAX_DATA
            actual_masked &= self.MAX_DATA

            if actual_masked == expected_masked:
                return True
            else:
                self.log.warning(f"AXIL4 verify failed: addr=0x{address:08X}, "
                               f"expected=0x{expected_masked:08X}, actual=0x{actual_masked:08X}, strb=0x{strb:X}")
                return False

        except Exception as e:
            self.log.error(f"AXIL4 verify exception at address 0x{address:08X}: {str(e)}")
            return False

    async def register_write_sequence_test(self, base_addr, reg_count, data_pattern=None, stride=None):
        """
        Test slave response to sequential register writes.
        
        AXIL4 specific: Tests register write patterns common in embedded systems.

        Args:
            base_addr: Starting register address
            reg_count: Number of registers to write
            data_pattern: Data pattern function (default: incremental)
            stride: Address stride between registers (default: data_width/8)

        Returns:
            tuple: (success, results_list)
        """
        if stride is None:
            stride = self.TEST_DATA_WIDTH // 8

        if data_pattern is None:
            data_pattern = lambda i: 0x12340000 + i

        self.log.debug(f"AXIL4 register sequence test: base=0x{base_addr:08X}, count={reg_count}")

        results = []
        success_count = 0

        for i in range(reg_count):
            addr = base_addr + (i * stride)
            data = data_pattern(i) & self.MAX_DATA
            
            success, info = await self.single_write_response_test(addr, data)
            
            results.append({
                'addr': addr,
                'data': data,
                'success': success,
                'info': info
            })

            if success:
                success_count += 1

            # Small delay between register writes
            profile = self.timing_profiles[self.current_timing]
            if profile['aw_delay'] > 0 or profile['w_delay'] > 0:
                await self.wait_clocks(self.aclk_name, max(profile['aw_delay'], profile['w_delay']))

        overall_success = success_count == reg_count
        return overall_success, results

    # High-level test sequences

    async def basic_register_write_sequence(self, count=10):
        """Run basic single register write sequence on slave"""
        self.log.info(f"Running basic AXIL4 register write sequence ({count} writes)...")

        base_addr = 0x1000
        success, results = await self.register_write_sequence_test(base_addr, count)

        if success:
            self.log.info(f"Basic register write sequence result: {len(results)}/{count} successful")
        else:
            failed_count = sum(1 for r in results if not r['success'])
            self.log.warning(f"Basic register write sequence: {failed_count}/{count} failed")

        return success

    async def strobe_pattern_test(self, address_base=0x2000):
        """Test slave write responses with different strobe patterns"""
        self.log.info("Running AXIL4 write strobe pattern test...")

        strb_width = self.TEST_DATA_WIDTH // 8
        
        # Test different strobe patterns
        strobe_patterns = [
            (0xF, "all_bytes", 0xDEADBEEF),
            (0x1, "byte0_only", 0x000000EF),
            (0x2, "byte1_only", 0x0000BE00),
            (0xC, "upper_bytes", 0xDEAD0000),
            (0x3, "lower_bytes", 0x0000BEEF),
        ]

        # Filter patterns valid for current data width
        valid_patterns = [(s, n, d) for s, n, d in strobe_patterns if s < (1 << strb_width)]
        
        success_count = 0
        for i, (strb, name, data) in enumerate(valid_patterns):
            addr = address_base + (i * (self.TEST_DATA_WIDTH // 8))
            
            self.log.debug(f"Testing {name} pattern: strb=0x{strb:X}")
            success, info = await self.single_write_response_test(addr, data, strb)
            
            if success:
                success_count += 1
                self.log.info(f"✅ {name} strobe pattern: PASS")
            else:
                self.log.error(f"❌ {name} strobe pattern: FAIL - {info}")

        overall_success = success_count == len(valid_patterns)
        return overall_success, success_count, len(valid_patterns)

    async def address_decode_test(self, address_ranges):
        """Test slave write address decoding across different memory regions"""
        self.log.info(f"Running AXIL4 write address decode test across {len(address_ranges)} ranges...")

        success_count = 0
        total_tests = 0

        for range_name, (base_addr, reg_count) in address_ranges.items():
            self.log.debug(f"Testing {range_name}: base=0x{base_addr:08X}, count={reg_count}")
            
            # Use different data patterns for each range
            data_pattern = lambda i: (base_addr & 0xFFFF0000) | (0x1000 + i)
            success, results = await self.register_write_sequence_test(base_addr, reg_count, data_pattern)
            
            total_tests += 1
            
            if success:
                success_count += 1
                self.log.info(f"✅ {range_name} address decode: PASS")
            else:
                failed_regs = [r for r in results if not r['success']]
                self.log.error(f"❌ {range_name} address decode: {len(failed_regs)} failures")

        overall_success = success_count == total_tests
        self.log.info(f"Address decode write test result: {success_count}/{total_tests} ranges successful")
        return overall_success

    async def stress_register_write_test(self, count=50):
        """Run stress test with rapid register write accesses"""
        self.log.info(f"Running AXIL4 stress register write test ({count} writes)...")

        # Set fast timing
        self.set_timing_profile('stress')

        success_count = 0
        address_ranges = [0x1000, 0x2000, 0x3000, 0x4000]

        for i in range(count):
            # Random register address in test ranges
            base_addr = random.choice(address_ranges)
            reg_offset = random.randint(0, 15) * (self.TEST_DATA_WIDTH // 8)
            addr = base_addr + reg_offset
            data = 0xCAFE0000 + i

            success, info = await self.single_write_response_test(addr, data)
            if success:
                success_count += 1

            # Minimal delay for stress testing
            await self.wait_clocks(self.aclk_name, 1)

        success_rate = success_count / count if count > 0 else 0
        self.log.info(f"AXIL4 stress write test result: {success_count}/{count} successful ({success_rate:.1%})")
        return success_rate >= 0.95  # Allow 5% failure in stress test

    async def timing_profile_test(self, profile_name, test_count=20):
        """Test slave write responses with specific timing profile"""
        self.log.info(f"Running AXIL4 write timing profile test: {profile_name}")

        self.set_timing_profile(profile_name)
        
        success_count = 0
        base_addr = 0x3000

        for i in range(test_count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            data = 0xBEEF0000 + i
            
            success, info = await self.single_write_response_test(addr, data)
            
            if success:
                success_count += 1

            # Apply timing profile delays
            profile = self.timing_profiles[profile_name]
            delay = max(profile['aw_delay'], profile['w_delay'], profile['b_delay'])
            if delay > 0:
                await self.wait_clocks(self.aclk_name, delay)

        success_rate = success_count / test_count if test_count > 0 else 0
        self.log.info(f"Timing profile '{profile_name}' result: {success_count}/{test_count} ({success_rate:.1%})")
        return success_rate >= 0.90

    async def register_pattern_validation_test(self):
        """Test slave write responses with known register patterns"""
        self.log.info("Running AXIL4 register write pattern validation test...")

        # Calculate byte stride based on data width (capture in lambda closure)
        bytes_per_reg = self.TEST_DATA_WIDTH // 8

        pattern_tests = [
            ("Incremental Pattern", 0x4000, 8, lambda i: 0x10000000 + i),
            ("Address Pattern", 0x5000, 8, lambda i, bpr=bytes_per_reg: (0x5000 + i*bpr) & self.MAX_DATA),
            ("Fixed Patterns", 0x6000, 4, lambda i: [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0xABCDEF00][i % 4]),
            ("Alternating Pattern", 0x7000, 8, lambda i: 0x55555555 if i % 2 == 0 else 0xAAAAAAAA)
        ]

        pattern_results = []
        
        for pattern_name, base_addr, count, pattern_func in pattern_tests:
            self.log.debug(f"Testing {pattern_name}...")
            
            success, results = await self.register_write_sequence_test(base_addr, count, pattern_func)
            pattern_results.append((pattern_name, success, len([r for r in results if r['success']]), count))
            
            status = "✅ PASS" if success else "❌ FAIL"
            success_count = len([r for r in results if r['success']])
            self.log.info(f"{pattern_name}: {status} ({success_count}/{count})")

            if not success:
                # Log details of failures
                failed_results = [r for r in results if not r['success']]
                for failed in failed_results[:3]:  # Show first 3 failures
                    self.log.debug(f"  Failed: addr=0x{failed['addr']:08X}, data=0x{failed['data']:08X}")

        overall_success = all(result[1] for result in pattern_results)
        return overall_success, pattern_results

    def get_test_stats(self):
        """Get comprehensive test statistics"""
        total_tests = self.stats['total_writes']
        success_rate = (self.stats['successful_writes'] / total_tests * 100) if total_tests > 0 else 0
        
        return {
            'summary': {
                'total_writes': total_tests,
                'successful_writes': self.stats['successful_writes'],
                'success_rate': f"{success_rate:.1f}%",
                'register_writes': self.stats['register_writes']
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
