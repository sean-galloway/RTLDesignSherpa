# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXI4ACEMasterWriteTB
# Purpose: AXI4-ACE Write Master Testbench
#
# Documentation: cocotb-framework PyPI package
# Subsystem: framework
#
# Author: sean galloway
# Created: 2026-10-05

"""
AXI4-ACE Write Master Testbench

Tests the axi4ace_master_wr skid-buffer transport using the CocoTB framework's
AXI4/ACE components. Verifies that write data reaches the memory model, that the
AWSNOOP field passes through untouched, and that the DUT auto-pulses m_axi_wack
one cycle after the output-side B handshake.
"""
import os
import random
import asyncio
from typing import List, Dict, Any, Tuple, Optional

import cocotb
from cocotb.triggers import RisingEdge, Event, with_timeout

from TBClasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor

from CocoTBFramework.components.ace.ace_factories import create_axi4ace_master_wr
from CocoTBFramework.components.ace.ace_field_configs import AXI4ACEFieldConfigHelper
from CocoTBFramework.components.ace.ace_transaction import ACETransactionType
from CocoTBFramework.components.axi4.axi4_factories import (
    create_axi4_slave_wr,
    print_compliance_reports_from_components,
)
from CocoTBFramework.components.axi4.axi4_compliance_checker import AXI4ComplianceChecker


class AXI4ACEMasterWriteTB(TBBase):
    """
    Testbench for the AXI4-ACE write master transport module.

    Drives the FUB-side input with an ACE master write BFM, terminates the
    master-side AXI4 interface with a slave write responder, and passively
    monitors the output AW channel with an ACE-configured GAXIMonitor so the
    AWSNOOP field can be verified.
    """

    def __init__(self, dut, aclk=None, aresetn=None):
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_ID_WIDTH = self.convert_to_int(os.environ.get('TEST_ID_WIDTH', '8'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.TEST_USER_WIDTH = self.convert_to_int(os.environ.get('TEST_USER_WIDTH', '1'))
        self.TEST_CLK_PERIOD = self.convert_to_int(os.environ.get('TEST_CLK_PERIOD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
        self.TIMEOUT_CYCLES = self.convert_to_int(os.environ.get('TIMEOUT_CYCLES', '1000'))

        # ACE write modules have no stub variant: always individual signals
        self.use_multi_sig = True

        random.seed(self.SEED)

        self.aclk = aclk
        self.aclk_name = aclk._name if aclk else 'aclk'
        self.aresetn = aresetn

        self.MAX_ADDR = (2 ** self.TEST_ADDR_WIDTH) - 1
        self.MAX_DATA = (2 ** self.TEST_DATA_WIDTH) - 1
        self.MAX_ID = (2 ** self.TEST_ID_WIDTH) - 1

        msg = '\n'
        msg += '=' * 80 + "\n"
        msg += ' AXI4-ACE Write Master Test Configuration:\n'
        msg += '-' * 80 + "\n"
        msg += f' ID Width:     {self.TEST_ID_WIDTH}\n'
        msg += f' Addr Width:   {self.TEST_ADDR_WIDTH}\n'
        msg += f' Data Width:   {self.TEST_DATA_WIDTH}\n'
        msg += f' User Width:   {self.TEST_USER_WIDTH}\n'
        msg += f' Clock Period: {self.TEST_CLK_PERIOD} ns\n'
        msg += f' Max Addr:     0x{self.MAX_ADDR:X}\n'
        msg += f' Max Data:     0x{self.MAX_DATA:X}\n'
        msg += f' Max ID:       {self.MAX_ID}\n'
        msg += f' Seed:         {self.SEED}\n'
        msg += '=' * 80 + "\n"
        self.log.info(msg)

        bytes_per_line = max(4, (self.TEST_DATA_WIDTH + 7) // 8)
        self.memory_model = MemoryModel(
            num_lines=65536,
            bytes_per_line=bytes_per_line,
            log=self.log,
            debug=True
        )

        self.stats = {
            'total_writes': 0,
            'successful_writes': 0,
            'single_writes': 0,
            'burst_writes': 0,
            'failed_writes': 0,
            'data_mismatches': 0,
            'response_errors': 0,
            'timeout_errors': 0,
            'verification_errors': 0,
            'exception_errors': 0,
        }

        self.randomizer_configs = self._create_axi4_randomizer_configs()
        self.current_profile = 'normal'

        # ACE write master on the FUB input side
        self.write_master = create_axi4ace_master_wr(
            dut=dut,
            clock=self.aclk,
            prefix='fub_axi_',
            log=self.log,
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            addr_width=self.TEST_ADDR_WIDTH,
            user_width=self.TEST_USER_WIDTH,
            multi_sig=self.use_multi_sig,
            timeout_cycles=self.TIMEOUT_CYCLES
        )
        self.aw_master = self.write_master['AW']
        self.w_master = self.write_master['W']
        self.b_slave = self.write_master['B']
        self.interface = self.write_master['interface']

        # AXI4 slave write responder on the master output side
        self.write_slave = create_axi4_slave_wr(
            dut=dut,
            clock=self.aclk,
            prefix='m_axi_',
            log=self.log,
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            addr_width=self.TEST_ADDR_WIDTH,
            user_width=self.TEST_USER_WIDTH,
            multi_sig=True,
            memory_model=self.memory_model
        )
        self.b_master = self.write_slave['B']

        # Passive ACE AW monitor on the master output to observe AWSNOOP
        self.aw_monitor = GAXIMonitor(
            dut=dut,
            title='AW_Output_Monitor',
            prefix='m_axi_',
            clock=self.aclk,
            field_config=AXI4ACEFieldConfigHelper.create_aw_field_config(
                self.TEST_ID_WIDTH, self.TEST_ADDR_WIDTH, self.TEST_USER_WIDTH
            ),
            multi_sig=True,
            log=self.log,
            protocol_type='axi4ace_aw_master',
        )
        self.aw_monitor.enable_completed_packet_tracking()

        # Compliance checker on the master AXI4 interface (AXI4 subset)
        self.axi4_compliance_checker = AXI4ComplianceChecker.create_if_enabled(
            dut=dut,
            clock=self.aclk,
            prefix='m_axi_',
            log=self.log,
            data_width=self.TEST_DATA_WIDTH,
            id_width=self.TEST_ID_WIDTH,
            addr_width=self.TEST_ADDR_WIDTH,
            user_width=self.TEST_USER_WIDTH
        )

        # WACK is only present on the master output side; input side has none
        if not hasattr(dut, 'fub_axi_wack'):
            self.log.info('No fub_axi_wack pin present; ACE master BFM operates without input WACK pulse')

        self.log.info('AXI4-ACE Write Master testbench initialization complete')

    def _create_axi4_randomizer_configs(self) -> Dict[str, Any]:
        """Create randomizer configurations for different test profiles."""
        configs = {}

        configs['normal'] = FlexRandomizer({
            'aw_delay': [(0, 5), (10, 20)],
            'w_delay': [(0, 3), (5, 15)],
            'b_delay': [(1, 8), (10, 25)]
        })

        configs['fast'] = FlexRandomizer({
            'aw_delay': [(0, 2)],
            'w_delay': [(0, 1)],
            'b_delay': [(1, 3)]
        })

        configs['slow'] = FlexRandomizer({
            'aw_delay': [(5, 15), (20, 50)],
            'w_delay': [(3, 10), (15, 40)],
            'b_delay': [(10, 30), (40, 80)]
        })

        configs['backtoback'] = FlexRandomizer({
            'aw_delay': [(0, 0)],
            'w_delay': [(0, 0)],
            'b_delay': [(1, 1)]
        })

        configs['stress'] = FlexRandomizer({
            'aw_delay': [(0, 100)],
            'w_delay': [(0, 50)],
            'b_delay': [(1, 200)]
        })

        return configs

    def set_timing_profile(self, profile_name: str):
        """Set timing profile for randomizers."""
        if not hasattr(self, 'randomizer_configs'):
            self.randomizer_configs = {
                'normal': None, 'fast': None, 'slow': None,
                'backtoback': None, 'stress': None
            }

        if profile_name not in self.randomizer_configs:
            self.log.warning(f"Unknown timing profile '{profile_name}', using 'normal'")
            profile_name = 'normal'

        self.current_randomizer = self.randomizer_configs[profile_name]
        self.current_profile = profile_name
        self.log.info(f"Set timing profile to '{profile_name}'")

    def get_time_ns_str(self) -> str:
        """Get current simulation time as string."""
        try:
            time_ns = cocotb.simulator.get_sim_time(units='ns')
            return f" @ {time_ns}ns"
        except Exception:
            return ""

    async def assert_reset(self):
        """Assert reset and initialize components."""
        self.aresetn.value = 0
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
        """Deassert reset."""
        self.aresetn.value = 1
        await self.wait_clocks(self.aclk_name, 5)
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    async def verify_write(self, address: int, expected_data: int) -> bool:
        """Verify a write by reading back from the memory model."""
        try:
            bytes_per_word = self.TEST_DATA_WIDTH // 8
            read_data = self.memory_model.read(address, bytes_per_word)
            if read_data is None:
                self.log.warning(f"Verify failed: No data at address 0x{address:08X}")
                return False

            actual_data = int.from_bytes(read_data, 'little')
            expected_data &= self.MAX_DATA
            actual_data &= self.MAX_DATA

            if actual_data == expected_data:
                return True
            else:
                self.log.warning(
                    f"Verify failed: addr=0x{address:08X}, "
                    f"expected=0x{expected_data:08X}, actual=0x{actual_data:08X}"
                )
                self.stats['data_mismatches'] += 1
                return False
        except Exception as e:
            self.log.error(f"Verify exception at address 0x{address:08X}: {str(e)}")
            return False

    def get_test_stats(self) -> Dict[str, Any]:
        """Get comprehensive test statistics."""
        total_writes = self.stats.get('total_writes', 0)
        successful_writes = self.stats.get('successful_writes', 0)
        failed_writes = self.stats.get('failed_writes', 0)
        success_rate = (successful_writes / total_writes) if total_writes > 0 else 0

        return {
            'summary': {
                'total_writes': total_writes,
                'successful_writes': successful_writes,
                'failed_writes': failed_writes,
                'success_rate': success_rate,
                'single_writes': self.stats.get('single_writes', 0),
                'burst_writes': self.stats.get('burst_writes', 0),
                'test_duration': 0
            },
            'errors': {
                'timeout_errors': self.stats.get('timeout_errors', 0),
                'verification_errors': self.stats.get('verification_errors', 0),
                'exception_errors': self.stats.get('exception_errors', 0),
                'response_errors': self.stats.get('response_errors', 0),
                'data_mismatches': self.stats.get('data_mismatches', 0)
            },
            'configuration': {
                'id_width': self.TEST_ID_WIDTH,
                'addr_width': self.TEST_ADDR_WIDTH,
                'data_width': self.TEST_DATA_WIDTH,
                'user_width': self.TEST_USER_WIDTH,
                'seed': self.SEED
            }
        }

    async def single_write_test(self, address: int, data: int,
                                transaction_id: Optional[int] = None,
                                snoop_type: ACETransactionType = ACETransactionType.WRITE_UNIQUE) -> Tuple[bool, Dict[str, Any]]:
        """Perform a single ACE write transaction."""
        try:
            self.stats['total_writes'] += 1

            kwargs = {'snoop_type': snoop_type}
            if transaction_id is not None:
                kwargs['id'] = transaction_id & self.MAX_ID

            self.log.debug(f"Starting write: addr=0x{address:08X}, data=0x{data:08X}, snoop={snoop_type.name}")
            result = await self.interface.write_transaction(address, data, **kwargs)

            if not result.get('success', False):
                self.stats['failed_writes'] += 1
                error_info = {
                    'error': 'Write transaction failed',
                    'details': result,
                    'address': address,
                    'data': data
                }
                self.log.warning(f"Write transaction failed: {error_info}")
                return False, error_info

            verify_success = await self.verify_write(address, data)
            if not verify_success:
                self.stats['failed_writes'] += 1
                self.stats['verification_errors'] += 1
                error_info = {
                    'error': 'Write verification failed',
                    'address': address,
                    'data': data,
                    'response': result
                }
                return False, error_info

            self.stats['successful_writes'] += 1
            self.stats['single_writes'] += 1

            return True, {
                'success': True,
                'response': result.get('response', 0),
                'id': result.get('id', 0)
            }

        except asyncio.TimeoutError:
            self.stats['failed_writes'] += 1
            self.stats['timeout_errors'] += 1
            error_info = {'error': 'Transaction timeout', 'address': address, 'data': data}
            self.log.error(f"Write timeout: {error_info}")
            return False, error_info
        except Exception as e:
            self.stats['failed_writes'] += 1
            self.stats['exception_errors'] += 1
            error_info = {
                'error': str(e),
                'exception': type(e).__name__,
                'address': address,
                'data': data
            }
            self.log.error(f"Write exception: {error_info}")
            return False, error_info

    async def burst_write_test(self, address: int, data_list: List[int],
                               transaction_id: Optional[int] = None,
                               snoop_type: ACETransactionType = ACETransactionType.WRITE_UNIQUE) -> Tuple[bool, Dict[str, Any]]:
        """Perform a burst ACE write transaction."""
        try:
            burst_len = len(data_list)
            self.stats['total_writes'] += burst_len
            self.stats['burst_writes'] += 1

            kwargs = {'snoop_type': snoop_type}
            if transaction_id is not None:
                kwargs['id'] = transaction_id & self.MAX_ID

            self.log.debug(
                f"Starting burst write: addr=0x{address:08X}, len={burst_len}, snoop={snoop_type.name}"
            )
            result = await self.interface.write_transaction(address, data_list, **kwargs)

            if not result.get('success', False):
                self.stats['failed_writes'] += burst_len
                error_info = {
                    'error': 'Burst write transaction failed',
                    'details': result,
                    'address': address,
                    'burst_length': burst_len
                }
                self.log.warning(f"Burst write failed: {error_info}")
                return False, error_info

            bytes_per_word = self.TEST_DATA_WIDTH // 8
            all_success = True
            for i, data in enumerate(data_list):
                write_addr = address + (i * bytes_per_word)
                if not await self.verify_write(write_addr, data):
                    all_success = False
                    self.log.warning(f"Burst verification failed at index {i}")
                    break

            if all_success:
                self.stats['successful_writes'] += burst_len
                return True, {
                    'success': True,
                    'burst_length': burst_len,
                    'response': result.get('response', 0),
                    'id': result.get('id', 0)
                }
            else:
                self.stats['failed_writes'] += burst_len
                error_info = {
                    'error': 'Burst write verification failed',
                    'address': address,
                    'burst_length': burst_len
                }
                return False, error_info

        except Exception as e:
            self.stats['failed_writes'] += len(data_list)
            self.stats['exception_errors'] += 1
            error_info = {
                'error': str(e),
                'exception': type(e).__name__,
                'address': address,
                'burst_length': len(data_list)
            }
            self.log.error(f"Burst write exception: {error_info}")
            return False, error_info

    async def run_single_writes(self, count: int) -> Tuple[bool, Dict[str, Any]]:
        """Run a series of single write tests."""
        success_count = 0
        failed_count = 0
        base_addr = 0x10000

        for i in range(count):
            addr = base_addr + (i * 4)
            data = 0x12340000 + i
            success, info = await self.single_write_test(addr, data)
            if success:
                success_count += 1
            else:
                failed_count += 1
                self.log.debug(f"Single write {i} failed: {info}")
            await self.wait_clocks('aclk', 2)

        success_rate = success_count / count if count > 0 else 0
        stats = {
            'total_count': count,
            'success_count': success_count,
            'failed_count': failed_count,
            'success_rate': success_rate
        }
        return success_rate >= 0.95, stats

    async def run_burst_writes(self, burst_lengths: List[int], count: int = 10) -> Tuple[bool, Dict[str, Any]]:
        """Run a series of burst write tests with different lengths."""
        try:
            success = await self.burst_write_sequence(burst_lengths)
            total_bursts = len(burst_lengths) * count
            stats = {
                'total_bursts': total_bursts,
                'successful_bursts': total_bursts if success else 0,
                'success_rate': 1.0 if success else 0.0,
                'burst_lengths': burst_lengths
            }
            return success, stats
        except Exception as e:
            self.log.error(f"run_burst_writes failed: {str(e)}")
            stats = {
                'total_bursts': 0,
                'successful_bursts': 0,
                'success_rate': 0.0,
                'burst_lengths': burst_lengths,
                'error': str(e)
            }
            return False, stats

    async def burst_write_sequence(self, burst_lengths: List[int]) -> bool:
        """Perform a sequence of burst write operations."""
        success_count = 0
        total_count = len(burst_lengths)

        for i, burst_len in enumerate(burst_lengths):
            addr = 0x2000 + (i * burst_len * 4)
            data_list = [0xDEAD0000 + j for j in range(burst_len)]
            success, info = await self.burst_write_test(addr, data_list)
            if success:
                success_count += 1
            await self.wait_clocks('aclk', 5)

        success_rate = success_count / total_count if total_count > 0 else 0
        self.log.info(
            f"Burst write sequence: {success_count}/{total_count} successful ({success_rate*100:.1f}%)"
        )
        return success_rate >= 0.9

    async def stress_test(self, count: int) -> Tuple[bool, Dict[str, Any]]:
        """Perform stress testing with a mix of single and burst writes."""
        success_count = 0
        total_operations = 0
        base_addr = 0x30000

        for i in range(count):
            total_operations += 1
            if i % 3 == 0:
                burst_len = random.choice([2, 4, 8])
                addr = base_addr + (i * 16)
                data_list = [0xCAFE0000 + j + (i << 8) for j in range(burst_len)]
                success, _ = await self.burst_write_test(addr, data_list)
            else:
                addr = base_addr + (i * 4)
                data = 0xBEEF0000 + i
                success, _ = await self.single_write_test(addr, data)

            if success:
                success_count += 1
            await self.wait_clocks('aclk', 1)

        success_rate = success_count / total_operations if total_operations > 0 else 0
        stats = {
            'total_operations': total_operations,
            'successful_operations': success_count,
            'success_rate': success_rate
        }
        return success_rate >= 0.85, stats

    async def run_error_injection_tests(self):
        """Run error injection tests as observational probes only."""
        self.log.info("Starting error injection tests...")
        stats_before = dict(self.stats)

        try:
            self.log.info("Testing unaligned address...")
            success, info = await self.single_write_test(0x1001, 0x12345678)
            if not success:
                self.log.info("Unaligned address properly rejected")
            else:
                self.log.info("Unaligned address accepted (system supports unaligned)")
        except Exception as e:
            self.log.info(f"Unaligned address test caused exception: {str(e)}")

        try:
            self.log.info("Testing maximum data values...")
            max_data = (1 << self.TEST_DATA_WIDTH) - 1
            success, info = await self.single_write_test(0x5000, max_data)
            if success:
                self.log.info("Maximum data value handled correctly")
            else:
                self.log.warning(f"Maximum data value failed: {info}")
        except Exception as e:
            self.log.warning(f"Maximum data value test caused exception: {str(e)}")

        try:
            self.log.info("Testing zero address...")
            success, info = await self.single_write_test(0x0, 0xDEADBEEF)
            if success:
                self.log.info("Zero address handled correctly")
        except Exception as e:
            self.log.info(f"Zero address test caused exception: {str(e)}")

        self.stats = stats_before

    async def test_outstanding_transactions(self, count: int = 20) -> Tuple[bool, Dict[str, Any]]:
        """Test outstanding transactions with 100% success required."""
        success_count = 0
        failed_transactions = []
        base_addr = 0x6000

        self.log.info(f"Testing {count} outstanding transactions (100% success required)...")
        for i in range(count):
            addr = base_addr + (i * 4)
            data = 0xDEAD0000 + i
            try:
                success, info = await self.single_write_test(addr, data)
                if success:
                    success_count += 1
                else:
                    failed_transactions.append({
                        'index': i,
                        'address': addr,
                        'data': data,
                        'error': info.get('error', 'Unknown error')
                    })
                    self.log.error(
                        f"Outstanding transaction {i} FAILED: addr=0x{addr:08X}, "
                        f"data=0x{data:08X}, error={info}"
                    )
                await self.wait_clocks('aclk', 1)
            except Exception as e:
                failed_transactions.append({
                    'index': i,
                    'address': addr,
                    'data': data,
                    'error': f"Exception: {str(e)}"
                })
                self.log.error(f"Outstanding transaction {i} EXCEPTION: {str(e)}")

        success_rate = success_count / count if count > 0 else 0
        stats = {
            'total_transactions': count,
            'successful_transactions': success_count,
            'failed_transactions': len(failed_transactions),
            'success_rate': success_rate,
            'failures': failed_transactions
        }

        if success_count == count:
            self.log.info(f"Outstanding transaction test PASSED: {success_count}/{count} (100%)")
            return True, stats
        else:
            self.log.error(f"Outstanding transaction test FAILED: {success_count}/{count}")
            return False, stats

    # ------------------------------------------------------------------
    # ACE-specific checks
    # ------------------------------------------------------------------

    async def _drain_aw_monitor(self) -> None:
        """Drain any previously captured AW packets from the output monitor."""
        self.aw_monitor.get_completed_packets()

    async def _capture_output_aw(self, timeout_cycles: Optional[int] = None) -> Any:
        """Wait for and return the next captured output AW packet."""
        if timeout_cycles is None:
            timeout_cycles = self.TIMEOUT_CYCLES

        cycles = 0
        while cycles < timeout_cycles:
            packets = self.aw_monitor.get_completed_packets()
            if packets:
                return packets[0]
            await RisingEdge(self.aclk)
            cycles += 1
        raise TimeoutError(f"No output AW packet captured within {timeout_cycles} cycles")

    async def _check_output_aw_packet(self, aw_packet, expected_snoop: int,
                                      expected_id: int, expected_addr: int,
                                      expected_len: int) -> None:
        """Assert that a captured AW packet matches expectations."""
        snoop = getattr(aw_packet, 'snoop', 0)
        pkt_id = getattr(aw_packet, 'id', 0)
        addr = getattr(aw_packet, 'addr', 0)
        length = getattr(aw_packet, 'len', 0)

        if snoop != expected_snoop:
            raise AssertionError(
                f"AWSNOOP mismatch: expected 0x{expected_snoop:X}, got 0x{snoop:X}"
            )
        if pkt_id != expected_id:
            raise AssertionError(f"AWID mismatch: expected {expected_id}, got {pkt_id}")
        if addr != expected_addr:
            raise AssertionError(
                f"AWADDR mismatch: expected 0x{expected_addr:08X}, got 0x{addr:08X}"
            )
        if length != expected_len:
            raise AssertionError(f"AWLEN mismatch: expected {expected_len}, got {length}")

    async def awsnoop_matrix_test(self) -> None:
        """
        Issue every AWSNOOP-applicable ACETransactionType value and verify that
        the output AW packet preserves snoop, id, addr and len.
        """
        self.log.info("=== AWSNOOP Matrix Test ===")

        # Build the set of 3-bit AWSNOOP values present in ACETransactionType
        snoop_values = {}
        for member in ACETransactionType:
            value = int(member)
            if value <= 0x7:
                snoop_values.setdefault(value, member.name)

        base_addr = 0x5000
        txn_id = 0x5
        bytes_per_word = self.TEST_DATA_WIDTH // 8

        for idx, (snoop_value, representative_name) in enumerate(sorted(snoop_values.items())):
            snoop_type = ACETransactionType(snoop_value)
            addr = base_addr + (idx * 0x100)
            data = 0xAABB0000 + idx

            self.log.info(
                f"Testing AWSNOOP=0x{snoop_value:X} ({representative_name}) single write"
            )
            await self._drain_aw_monitor()
            success, info = await self.single_write_test(addr, data, transaction_id=txn_id, snoop_type=snoop_type)
            if not success:
                raise AssertionError(f"AWSNOOP 0x{snoop_value:X} single write failed: {info}")
            aw_packet = await self._capture_output_aw()
            await self._check_output_aw_packet(aw_packet, snoop_value, txn_id, addr, 0)

            burst_len = 4
            burst_addr = addr + 0x40
            data_list = [0xCCDD0000 + j + (idx << 8) for j in range(burst_len)]
            self.log.info(
                f"Testing AWSNOOP=0x{snoop_value:X} ({representative_name}) burst write len={burst_len}"
            )
            await self._drain_aw_monitor()
            success, info = await self.burst_write_test(
                burst_addr, data_list, transaction_id=txn_id, snoop_type=snoop_type
            )
            if not success:
                raise AssertionError(f"AWSNOOP 0x{snoop_value:X} burst write failed: {info}")
            aw_packet = await self._capture_output_aw()
            await self._check_output_aw_packet(aw_packet, snoop_value, txn_id, burst_addr, burst_len - 1)

            for beat, beat_data in enumerate(data_list):
                beat_addr = burst_addr + (beat * bytes_per_word)
                if not await self.verify_write(beat_addr, beat_data):
                    raise AssertionError(
                        f"AWSNOOP 0x{snoop_value:X} burst beat {beat} verify failed"
                    )

        self.log.info("AWSNOOP matrix test PASSED")

    async def wack_check(self, address: int = 0x7000, data: int = 0xBEEFCAFE) -> None:
        """
        Verify that m_axi_wack is low during the data phase and pulses exactly
        one cycle starting the cycle after the output-side B handshake.
        """
        self.log.info("=== WACK Check ===")

        # Wait for any stale wack pulse to clear
        for _ in range(10):
            await RisingEdge(self.aclk)
            if int(self.dut.m_axi_wack.value) != 0:
                while int(self.dut.m_axi_wack.value) != 0:
                    await RisingEdge(self.aclk)

        # Pre-check: wack must be low before the transaction
        await RisingEdge(self.aclk)
        if int(self.dut.m_axi_wack.value) != 0:
            raise AssertionError("m_axi_wack not low before write")

        # Start the write in the background
        write_task = cocotb.start_soon(
            self.interface.write_transaction(address, data)
        )

        # Wait for the output-side B handshake
        cycles = 0
        while cycles < self.TIMEOUT_CYCLES:
            await RisingEdge(self.aclk)
            if (int(self.dut.m_axi_bvalid.value) and int(self.dut.m_axi_bready.value)):
                break
            cycles += 1
        else:
            raise TimeoutError("Timed out waiting for m_axi B handshake during WACK check")

        # WACK must still be low during the handshake cycle
        if int(self.dut.m_axi_wack.value) != 0:
            raise AssertionError("m_axi_wack high during B handshake (pulse too early)")

        # Exactly one cycle later WACK should be high
        await RisingEdge(self.aclk)
        if int(self.dut.m_axi_wack.value) != 1:
            raise AssertionError("m_axi_wack did not pulse one cycle after B handshake")

        # One more cycle: WACK must return to low (single-cycle pulse)
        await RisingEdge(self.aclk)
        if int(self.dut.m_axi_wack.value) != 0:
            raise AssertionError("m_axi_wack pulse was wider than one cycle")

        # Ensure the underlying write transaction completed successfully
        result = await write_task
        if not result.get('success', False):
            raise AssertionError(f"Write during WACK check failed: {result}")

        # Verify data integrity
        if not await self.verify_write(address, data):
            raise AssertionError("WACK check write data did not land in memory model")

        self.log.info("WACK check PASSED")

    async def check_busy(self) -> None:
        """Assert that the DUT busy output is low after quiescence."""
        # Allow any in-flight skid activity to drain
        await self.wait_clocks('aclk', 20)
        busy_val = int(self.dut.busy.value)
        self.log.info(f"busy output sampled as {busy_val} after quiescence")
        if busy_val != 0:
            raise AssertionError(f"busy output is high ({busy_val}) after quiescence")

    def finalize_test(self):
        """Print compliance reports for all AXI4 components."""
        self.log.info('------------> Finalize Test')
        print_compliance_reports_from_components(self.write_master)
        print_compliance_reports_from_components(self.write_slave)
        if hasattr(self, 'axi4_compliance_checker') and self.axi4_compliance_checker:
            self.axi4_compliance_checker.print_compliance_report()
