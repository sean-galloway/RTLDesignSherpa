# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXIL4MasterWriteTB
# Purpose: AXIL4 Write Master Testbench
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Write Master Testbench

Testbench for testing AXIL4 write master functionality using the CocoTB
framework's AXIL4 components. Focuses on AW, W, and B channel validation.

Based on the AXI4 master write testbench pattern but simplified for AXIL4 register access.
"""
import os
import random
import asyncio
from typing import List, Dict, Any, Tuple, Optional, Union

# Framework imports
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer

# AXIL4 specific imports
from CocoTBFramework.components.axil4.axil4_factories import create_axil4_master_wr, create_axil4_slave_wr, print_unified_compliance_reports
from CocoTBFramework.components.axil4.axil4_packet import AXIL4Packet
from CocoTBFramework.components.axil4.axil4_compliance_checker import AXIL4ComplianceChecker


class AXIL4MasterWriteTB(TBBase):
    """
    Simple AXIL4 Write Master testbench for baseline testing.

    Tests basic write functionality using AW, W, and B channels with the
    axil4_master_wr.sv RTL module.
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
        msg += ' AXIL4 Write Master Test Configuration:\n'
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
            log=self.log,
            debug=True
        )

        # Initialize statistics
        self.stats = {
            'total_writes': 0,
            'successful_writes': 0,
            'register_writes': 0,
            'failed_writes': 0,
            'data_mismatches': 0,
            'response_errors': 0,
            'timeout_errors': 0
        }

        # Create randomizer configurations
        self.randomizer_configs = self._create_axil4_randomizer_configs()
        self.current_profile = 'normal'

        # Create AXIL4 write master interface
        try:
            self.master_components = create_axil4_master_wr(
                dut=dut,
                clock=self.aclk,
                prefix='fub_',
                log=self.log,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                multi_sig=self.use_multi_sig
            )

            # Access individual components
            self.aw_master = self.master_components['AW']  # Drives AW channel
            self.w_master = self.master_components['W']    # Drives W channel
            self.b_slave = self.master_components['B']     # Receives B responses
            self.axil4_master = self.master_components['interface']

            self.log.info("AXIL4 Master Write components created")
        except Exception as e:
            self.log.error(f"Failed to create master components: {e}")
            raise

        # Create AXIL4 slave to respond on the master interface side
        try:
            self.slave_components = create_axil4_slave_wr(
                dut=dut,
                clock=self.aclk,
                prefix='m_axil_',  # Receives m_axil_aw*, m_axil_w*, drives m_axil_b*
                log=self.log,
                addr_width=self.TEST_ADDR_WIDTH,
                data_width=self.TEST_DATA_WIDTH,
                memory_model=self.memory_model,
                multi_sig=True
            )

            # Access individual components
            self.aw_slave = self.slave_components['AW']    # Receives AW requests
            self.w_slave = self.slave_components['W']      # Receives W data
            self.b_master = self.slave_components['B']     # Drives B responses

            self.log.info("AXIL4 Slave Write components created")
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

        self.log.info("AXIL4 Write Master testbench initialization complete")

    def _create_axil4_randomizer_configs(self) -> Dict[str, Any]:
        """Create randomizer configurations for different test profiles."""
        configs = {
            'fast': {
                'aw_delay': [(0, 0), (1, 2)],
                'w_delay': [(0, 0), (1, 2)],
                'b_delay': [(0, 1), (1, 2)]
            },
            'normal': {
                'aw_delay': [(0, 2), (3, 5)],
                'w_delay': [(0, 2), (3, 5)],
                'b_delay': [(1, 3), (4, 6)]
            },
            'slow': {
                'aw_delay': [(2, 5), (6, 10)],
                'w_delay': [(2, 5), (6, 10)],
                'b_delay': [(3, 7), (8, 12)]
            },
            'backtoback': {
                'aw_delay': [(0, 0)],
                'w_delay': [(0, 0)],
                'b_delay': [(0, 0)]
            },
            'stress': {
                'aw_delay': [(0, 0), (1, 3), (4, 8)],
                'w_delay': [(0, 0), (1, 3), (4, 8)],
                'b_delay': [(0, 1), (2, 5), (6, 10)]
            }
        }
        return configs

    def set_timing_profile(self, profile_name: str):
        """Set timing profile for randomizers."""
        if profile_name in self.randomizer_configs:
            self.current_profile = profile_name
            self.log.info(f"Set timing profile to: {profile_name}")
        else:
            available = list(self.randomizer_configs.keys())
            self.log.warning(f"Unknown timing profile: {profile_name}, available: {available}")

    async def assert_reset(self):
        """Assert reset and initialize components"""
        self.aresetn.value = 0
        
        # Reset bus interfaces safely
        try:
            await self.aw_master.reset_bus()
            await self.w_master.reset_bus()
            if hasattr(self, 'b_master'):
                await self.b_master.reset_bus()
        except Exception as e:
            self.log.debug(f"Reset bus warning: {e}")

        await self.wait_clocks(self.aclk_name, 5)
        self.log.info("Reset asserted")

    async def deassert_reset(self):
        """Deassert reset"""
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    async def register_write_test(self, address: int, data: int, strb: Optional[int] = None, prot: int = 0) -> Tuple[bool, Dict[str, Any]]:
        """
        Perform a single AXIL4 register write transaction

        Args:
            address: Write address
            data: Data to write
            strb: Write strobes (None = all bytes enabled)
            prot: Protection field value

        Returns:
            Tuple of (success, response_info)
        """
        try:
            self.stats['total_writes'] += 1
            self.stats['register_writes'] += 1

            # Calculate default strobe if not provided
            if strb is None:
                strb_width = self.TEST_DATA_WIDTH // 8
                strb = (1 << strb_width) - 1

            self.log.debug(f"Register write: addr=0x{address:08X}, data=0x{data:08X}, strb=0x{strb:X}, prot={prot}")

            # Use the AXIL4 interface method (single transfer only)
            response_code = await self.axil4_master.single_write(
                address=address,
                data=data,
                strb=strb,
                prot=prot
            )

            # Check response code
            if response_code != 0:  # 0 = OKAY
                self.stats['response_errors'] += 1
                self.stats['failed_writes'] += 1
                resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
                error_info = {
                    'error': f'Write response error: {resp_names.get(response_code, "UNKNOWN")}',
                    'response_code': response_code,
                    'address': address,
                    'data': data
                }
                return False, error_info

            # Verify the write by reading back from memory model
            verify_success = await self.verify_write(address, data, strb)
            if not verify_success:
                self.stats['failed_writes'] += 1
                self.stats['data_mismatches'] += 1
                error_info = {
                    'error': 'Write verification failed',
                    'address': address,
                    'data': data,
                    'strb': strb
                }
                return False, error_info

            # Success
            self.stats['successful_writes'] += 1
            success_info = {
                'success': True,
                'response_code': response_code,
                'address': address,
                'data': data,
                'strb': strb
            }
            return True, success_info

        except asyncio.TimeoutError:
            self.stats['failed_writes'] += 1
            self.stats['timeout_errors'] += 1
            error_info = {'error': 'Transaction timeout', 'address': address, 'data': data}
            self.log.error(f"Write timeout: {error_info}")
            return False, error_info

        except Exception as e:
            self.stats['failed_writes'] += 1
            error_info = {
                'error': str(e),
                'exception': type(e).__name__,
                'address': address,
                'data': data
            }
            self.log.error(f"Write exception: {error_info}")
            return False, error_info

    async def simple_write_test(self, address: int, data: int, strb: Optional[int] = None) -> Tuple[bool, Dict[str, Any]]:
        """
        Perform a simple AXIL4 write using the simple_write interface method

        Args:
            address: Write address
            data: Data to write
            strb: Write strobes (None = all bytes enabled)

        Returns:
            Tuple of (success, response_info)
        """
        try:
            self.stats['total_writes'] += 1

            # Calculate default strobe if not provided
            if strb is None:
                strb_width = self.TEST_DATA_WIDTH // 8
                strb = (1 << strb_width) - 1

            self.log.debug(f"Simple write: addr=0x{address:08X}, data=0x{data:08X}, strb=0x{strb:X}")

            # Use the simple_write interface method (backward compatibility)
            response_code = await self.axil4_master.simple_write(
                address=address,
                data=data,
                strb=strb
            )

            # Check response code
            if response_code != 0:
                self.stats['response_errors'] += 1
                self.stats['failed_writes'] += 1
                resp_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
                error_info = {
                    'error': f'Write response error: {resp_names.get(response_code, "UNKNOWN")}',
                    'response_code': response_code,
                    'address': address,
                    'data': data
                }
                return False, error_info

            # Verify the write
            verify_success = await self.verify_write(address, data, strb)
            if not verify_success:
                self.stats['failed_writes'] += 1
                self.stats['data_mismatches'] += 1
                error_info = {
                    'error': 'Write verification failed',
                    'address': address,
                    'data': data
                }
                return False, error_info

            # Success
            self.stats['successful_writes'] += 1
            success_info = {
                'success': True,
                'response_code': response_code
            }
            return True, success_info

        except Exception as e:
            self.stats['failed_writes'] += 1
            self.stats['timeout_errors'] += 1
            error_info = {'error': str(e), 'address': address, 'data': data}
            return False, error_info

    async def verify_write(self, address: int, expected_data: int, strb: int) -> bool:
        """
        Verify a write by reading back from memory model with strobe consideration.

        Args:
            address: Address to verify
            expected_data: Expected data value
            strb: Write strobes that were used

        Returns:
            True if verification passed
        """
        try:
            bytes_per_word = self.TEST_DATA_WIDTH // 8
            read_data_bytes = self.memory_model.read(address, bytes_per_word)
            if read_data_bytes is None:
                self.log.warning(f"Verify failed: No data at address 0x{address:08X}")
                return False

            # Convert bytes to integer
            actual_data = int.from_bytes(read_data_bytes, 'little')

            # Apply strobe mask to expected data for comparison
            masked_expected = 0
            masked_actual = 0
            
            for byte_idx in range(bytes_per_word):
                if strb & (1 << byte_idx):
                    # This byte was written
                    expected_byte = (expected_data >> (byte_idx * 8)) & 0xFF
                    actual_byte = (actual_data >> (byte_idx * 8)) & 0xFF
                    masked_expected |= expected_byte << (byte_idx * 8)
                    masked_actual |= actual_byte << (byte_idx * 8)

            # Mask to data width
            masked_expected &= self.MAX_DATA
            masked_actual &= self.MAX_DATA

            if masked_actual == masked_expected:
                return True
            else:
                self.log.warning(f"Verify failed: addr=0x{address:08X}, strb=0x{strb:X}, "
                               f"expected=0x{masked_expected:08X}, actual=0x{masked_actual:08X}")
                return False

        except Exception as e:
            self.log.error(f"Verify exception at address 0x{address:08X}: {str(e)}")
            return False

    # High-level test sequences

    async def basic_write_sequence(self, count=10):
        """Run basic single write sequence"""
        self.log.info(f"Running basic write sequence ({count} writes)...")

        success_count = 0
        base_addr = 0x1000

        for i in range(count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            data = 0x12340000 + i
            success, info = await self.register_write_test(addr, data)
            if success:
                success_count += 1

            # Small delay between writes
            await self.wait_clocks(self.aclk_name, 2)

        self.log.info(f"Basic sequence result: {success_count}/{count} successful")
        return success_count == count

    async def register_access_sequence(self, count=10):
        """Run register access sequence using different interface methods"""
        self.log.info(f"Running register access sequence ({count} writes)...")

        success_count = 0
        base_addr = 0x2000

        for i in range(count):
            addr = base_addr + (i * (self.TEST_DATA_WIDTH // 8))
            data = 0x87650000 + i
            
            # Alternate between different interface methods
            if i % 3 == 0:
                success, info = await self.register_write_test(addr, data)
            elif i % 3 == 1:
                success, info = await self.simple_write_test(addr, data)
            else:
                # Use write_register method (API consistency)
                try:
                    response_code = await self.axil4_master.write_register(address=addr, data=data)
                    success = (response_code == 0)
                    self.stats['total_writes'] += 1
                    if success:
                        self.stats['successful_writes'] += 1
                    else:
                        self.stats['failed_writes'] += 1
                except Exception as e:
                    self.log.error(f"Write register failed: {e}")
                    success = False
                    self.stats['total_writes'] += 1
                    self.stats['failed_writes'] += 1

            if success:
                success_count += 1

            # Small delay between writes
            await self.wait_clocks(self.aclk_name, 2)

        self.log.info(f"Register access sequence result: {success_count}/{count} successful")
        return success_count == count

    async def strobe_pattern_test(self):
        """Test different write strobe patterns"""
        self.log.info("Running write strobe pattern test...")

        bytes_per_word = self.TEST_DATA_WIDTH // 8
        success_count = 0
        test_count = 0

        # Test various strobe patterns
        strobe_patterns = [
            (0x1, "Byte 0 only"),
            (0x3, "Bytes 0-1"),
            (0xF, "All bytes") if bytes_per_word >= 4 else (0x3, "All bytes"),
            (0x5, "Alternating") if bytes_per_word >= 4 else (0x1, "Single byte"),
        ]

        base_addr = 0x3000
        for i, (strb, description) in enumerate(strobe_patterns):
            if strb >= (1 << bytes_per_word):  # Skip invalid patterns
                continue
                
            test_count += 1
            addr = base_addr + (i * bytes_per_word)
            data = 0xDEADBEEF if bytes_per_word >= 4 else 0xDEAD
            
            success, info = await self.register_write_test(addr, data, strb=strb)
            if success:
                success_count += 1
                self.log.debug(f"Strobe pattern {description} (0x{strb:X}): SUCCESS")
            else:
                self.log.warning(f"Strobe pattern {description} (0x{strb:X}): FAILED")

        self.log.info(f"Strobe pattern test: {success_count}/{test_count} successful")
        return success_count == test_count

    async def stress_write_test(self, count=50):
        """Run stress test with rapid writes"""
        self.log.info(f"Running stress write test ({count} writes)...")

        # Set fast timing
        self.set_timing_profile('stress')

        success_count = 0
        for i in range(count):
            # Random address in test ranges
            addr_ranges = [0x4000, 0x5000, 0x6000]
            base_addr = random.choice(addr_ranges)
            offset = random.randint(0, 31) * (self.TEST_DATA_WIDTH // 8)
            addr = base_addr + offset
            data = 0xCAFE0000 + i

            success, info = await self.register_write_test(addr, data)
            if success:
                success_count += 1

        self.log.info(f"Stress test result: {success_count}/{count} successful")
        return success_count >= (count * 0.95)  # Allow 5% failure in stress test

    def get_time_ns_str(self) -> str:
        """Helper to get current simulation time as string."""
        try:
            import cocotb
            time_ns = cocotb.simulator.get_sim_time(units='ns')
            return f" @ {time_ns}ns"
        except:
            return ""

    def get_test_stats(self) -> Dict[str, Any]:
        """Get comprehensive test statistics"""
        total_writes = self.stats['total_writes']
        success_rate = (self.stats['successful_writes'] / total_writes * 100) if total_writes > 0 else 0
        
        self.finalize_test()

        return {
            'summary': {
                'total_writes': total_writes,
                'successful_writes': self.stats['successful_writes'],
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
