# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: CDCHandshakeTB
# Purpose: CDC Handshake Testbench with FlexConfigGen Sophistication
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""CDC Handshake Testbench with FlexConfigGen Sophistication

File: cdc_handshake.py
Location: CocoTBFramework/tbclasses/gaxi/cdc_handshake.py

CDC Handshake Testbench that combines:
- CDC-focused architecture (multiple clock domains, APB-like fields, memory integration)
- FlexConfigGen sophistication (20+ randomizer profiles, test levels, comprehensive patterns)
- Advanced verification (timing analysis, performance metrics, error tracking)
"""
import os
import random
from collections import deque

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.shared.field_config import FieldConfig
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_factories import (
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
)
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen


class CDCHandshakeTB(TBBase):
    """
    CDC Handshake Testbench with sophisticated randomization and test patterns.

    Combines the CDC-focused architecture with FlexConfigGen sophistication:
    - Multiple clock domains (clk_src, clk_dst)
    - APB-like fields (pwrite, paddr, pwdata, pstrb, pprot)
    - Memory model integration
    - FlexConfigGen with 20+ randomizer profiles
    - Test level control (basic/medium/full)
    - Comprehensive test patterns (stress, walking bits, burst, back-to-back)
    - Performance metrics and statistics
    """

    def __init__(self, dut):
        """Initialize the CDC handshake testbench"""
        TBBase.__init__(self, dut)

        # Get test parameters from environment variables
        self.ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '32'))
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '32'))
        self.STRB_WIDTH = self.DATA_WIDTH // 8
        self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'basic').lower()
        self.clk_src_PERIOD_NS = self.convert_to_int(os.environ.get('clk_src_PERIOD_NS', '50'))
        self.clk_dst_PERIOD_NS = self.convert_to_int(os.environ.get('clk_dst_PERIOD_NS', '10'))
        self.super_debug = os.environ.get('SUPER_DEBUG', 'false').lower() == 'true'

        # Calculate clock frequencies and ratios for CDC analysis
        self.clk_src_FREQ_MHZ = 1000 / self.clk_src_PERIOD_NS
        self.clk_dst_FREQ_MHZ = 1000 / self.clk_dst_PERIOD_NS
        self.clock_ratio = self.clk_dst_PERIOD_NS / self.clk_src_PERIOD_NS

        # test control and statistics
        self.done = False
        self.total_errors = 0
        self.test_start_time = 0
        self.transactions_sent = 0
        self.transactions_verified = 0
        self.cdc_violations = 0
        self.timing_errors = 0
        self.data_errors = 0

        # Memory configuration
        self.num_lines = 32768
        self.MAX_ADDR = (2**self.ADDR_WIDTH) - 1
        self.MAX_DATA = (2**self.DATA_WIDTH) - 1
        self.TIMEOUT_CYCLES = 10000

        # Create memory model with diagnostics
        self.mem = MemoryModel(
            num_lines=self.num_lines,
            bytes_per_line=self.STRB_WIDTH,
            log=self.log,
            debug=self.super_debug
        )

        # Define comprehensive field configuration for CDC handshake
        self.field_config = self._create_apb_field_config()

        # Create sophisticated randomizer configurations using FlexConfigGen
        self.randomizer_configs = self._create_cdc_randomizer_configs()

        # Create GAXI components for source domain
        src_randomizer = self._get_randomizer_for_level('moderate')
        self.src_master = create_gaxi_master(
            dut=dut,
            title='CDC_Source_Master',
            prefix='',
            bus_name='src',
            clock=dut.clk_src,
            field_config=self.field_config,
            randomizer=src_randomizer,
            memory_model=self.mem,
            log=self.log
        )

        self.src_monitor = create_gaxi_monitor(
            dut=dut,
            title='CDC_Source_Monitor',
            prefix='',
            bus_name='src',
            clock=dut.clk_src,
            field_config=self.field_config,
            is_slave=False,
            log=self.log
        )

        # Create GAXI components for destination domain
        dst_randomizer = self._get_randomizer_for_level('moderate')
        self.dst_slave = create_gaxi_slave(
            dut=dut,
            title='CDC_Destination_Slave',
            prefix='',
            bus_name='dst',
            clock=dut.clk_dst,
            field_config=self.field_config,
            randomizer=dst_randomizer,
            memory_model=self.mem,
            log=self.log
        )

        self.dst_monitor = create_gaxi_monitor(
            dut=dut,
            title='CDC_Destination_Monitor',
            prefix='',
            bus_name='dst',
            clock=dut.clk_dst,
            field_config=self.field_config,
            is_slave=True,
            log=self.log
        )

        # Create monitoring queues with metadata
        self.src_transactions = deque()
        self.dst_transactions = deque()
        self.timing_analysis = []

        # Add callbacks to store transactions with timing analysis
        self.src_monitor.add_callback(self.src_transaction_callback)
        self.dst_monitor.add_callback(self.dst_transaction_callback)

        # Validate test level
        valid_levels = ['basic', 'medium', 'full']
        if self.TEST_LEVEL not in valid_levels:
            self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'basic'. Valid: {valid_levels}")
            self.TEST_LEVEL = 'basic'

        # Log comprehensive configuration
        self._log_configuration()

    def _create_apb_field_config(self):
        """Create comprehensive APB-like field configuration"""
        field_config = FieldConfig()

        field_config.add_field_dict('pwrite', {
            'bits': 1,
            'default': 0,
            'format': 'bin',
            'display_width': 1,
            'active_bits': (0, 0),
            'description': 'Write enable',
            'encoding': {0: 'READ', 1: 'WRITE'}
        })

        field_config.add_field_dict('paddr', {
            'bits': self.ADDR_WIDTH,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (self.ADDR_WIDTH-1, 0),
            'description': 'Address'
        })

        field_config.add_field_dict('pwdata', {
            'bits': self.DATA_WIDTH,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (self.DATA_WIDTH-1, 0),
            'description': 'Write data'
        })

        field_config.add_field_dict('pstrb', {
            'bits': self.STRB_WIDTH,
            'default': (2**self.STRB_WIDTH - 1),  # All bytes enabled by default
            'format': 'bin',
            'display_width': self.STRB_WIDTH,
            'active_bits': (self.STRB_WIDTH-1, 0),
            'description': 'Byte strobe'
        })

        field_config.add_field_dict('pprot', {
            'bits': 3,
            'default': 0,
            'format': 'bin',
            'display_width': 3,
            'active_bits': (2, 0),
            'description': 'Protection bits',
            'encoding': {
                0: 'NORMAL', 1: 'PRIVILEGED', 2: 'SECURE', 3: 'PRIV_SEC',
                4: 'DATA', 5: 'PRIV_DATA', 6: 'SEC_DATA', 7: 'PRIV_SEC_DATA'
            }
        })

        return field_config

    def _create_cdc_randomizer_configs(self):
        """Create sophisticated CDC-focused randomizer configurations using FlexConfigGen"""

        # CDC-specific custom profiles optimized for cross-domain testing
        cdc_custom_profiles = {
            # CDC-specific timing patterns
            'cdc_conservative': ([(2, 5), (8, 12), (15, 20)], [3, 2, 1]),        # Safe CDC timing
            'cdc_aggressive': ([(0, 0), (1, 1), (2, 3)], [5, 3, 2]),             # Fast CDC timing
            'cdc_mixed_freq': ([(0, 1), (3, 7), (12, 18), (25, 40)], [4, 3, 2, 1]), # Mixed frequency aware
            'cdc_burst_stress': ([(0, 0), (1, 2), (20, 35)], [8, 4, 1]),         # Burst with pauses
            'cdc_jitter': ([(0, 2), (3, 6), (7, 10), (11, 15)], [4, 3, 2, 1]),   # Jittery timing
            'cdc_slow_domain': ([(5, 15), (20, 40), (50, 80)], [3, 2, 1]),       # Slow domain simulation
            'cdc_fast_domain': ([(0, 0), (1, 3), (4, 8)], [6, 3, 1]),            # Fast domain simulation
            'cdc_metastable': ([(1, 3), (4, 8), (12, 25)], [2, 3, 2]),           # Metastability testing

            # Clock ratio aware patterns (dynamically calculated)
            'cdc_ratio_sync': self._get_ratio_aware_pattern('sync'),
            'cdc_ratio_async': self._get_ratio_aware_pattern('async'),
        }

        # Create FlexConfigGen with CDC focus
        config_gen = FlexConfigGen(
            profiles=[
                # Standard profiles adapted for CDC
                'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
                'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
                'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
                # CDC-specific profiles
                'cdc_conservative', 'cdc_aggressive', 'cdc_mixed_freq', 'cdc_burst_stress',
                'cdc_jitter', 'cdc_slow_domain', 'cdc_fast_domain', 'cdc_metastable',
                'cdc_ratio_sync', 'cdc_ratio_async'
            ],
            fields=['valid_delay', 'ready_delay'],
            custom_profiles=cdc_custom_profiles
        )

        # Customize profiles for CDC testing
        self._customize_cdc_profiles(config_gen)

        # Build configurations
        randomizer_dict = config_gen.build(return_flexrandomizer=False)

        # Convert to source/destination domain format
        converted_configs = {}
        for profile_name, profile_config in randomizer_dict.items():
            converted_configs[profile_name] = {
                'source': {field: constraints for field, constraints in profile_config.items()},
                'destination': {field: constraints for field, constraints in profile_config.items()}
            }

        self.log.info(f"Created {len(converted_configs)} CDC-optimized randomizer configurations")
        return converted_configs

    def _get_ratio_aware_pattern(self, sync_type):
        """Generate clock ratio aware delay patterns"""
        if sync_type == 'sync':
            # Synchronous to clock edges
            base_delay = max(2, int(self.clock_ratio * 2))
            return ([(0, 0), (base_delay, base_delay), (base_delay*2, base_delay*3)], [4, 3, 1])
        else:
            # Asynchronous patterns
            ratio_delays = [int(self.clock_ratio * i) for i in [1, 2, 4, 8]]
            return ([(0, 1)] + [(d, d+2) for d in ratio_delays], [5, 2, 2, 1, 1])

    def _customize_cdc_profiles(self, config_gen):
        """Customize FlexConfigGen profiles for CDC testing"""

        # Backtoback for CDC stress testing
        config_gen.backtoback.valid_delay.fixed_value(0)
        config_gen.backtoback.ready_delay.fixed_value(0)

        # CDC conservative timing
        config_gen.slow.valid_delay.uniform_range(5, 15)
        config_gen.slow.ready_delay.uniform_range(8, 20)

        # CDC burst patterns
        config_gen.bursty.valid_delay.burst_pattern(fast_cycles=0, pause_range=(10, 25), burst_ratio=8)
        config_gen.bursty.ready_delay.burst_pattern(fast_cycles=0, pause_range=(15, 30), burst_ratio=6)

        # CDC stress with metastability windows
        config_gen.stress.valid_delay.probability_split([
            ((0, 1), 0.4), ((2, 5), 0.3), ((8, 15), 0.2), ((20, 40), 0.1)
        ])
        config_gen.stress.ready_delay.probability_split([
            ((0, 2), 0.35), ((3, 8), 0.35), ((12, 25), 0.2), ((30, 50), 0.1)
        ])

    def _get_randomizer_for_level(self, config_name):
        """Get FlexRandomizer for specified configuration"""
        if config_name in self.randomizer_configs:
            # Use source domain config (both domains get same base pattern)
            config = self.randomizer_configs[config_name]['source']
            return FlexRandomizer(config)
        else:
            # Fallback to moderate config
            moderate_config = {
                'valid_delay': ([(0, 2), (3, 8), (10, 15)], [4, 3, 1]),
                'ready_delay': ([(0, 3), (4, 10), (12, 20)], [4, 3, 1])
            }
            return FlexRandomizer(moderate_config)

    def get_randomizer_config_names(self):
        """Get list of available randomizer configuration names"""
        return list(self.randomizer_configs.keys())

    def _log_configuration(self):
        """Log comprehensive testbench configuration"""
        msg = '\n' + '='*80 + '\n'
        msg += 'CDC Handshake Testbench Configuration\n'
        msg += '-'*80 + '\n'
        msg += f' Test Level:      {self.TEST_LEVEL.upper()}\n'
        msg += f' Address Width:   {self.ADDR_WIDTH} bits\n'
        msg += f' Data Width:      {self.DATA_WIDTH} bits\n'
        msg += f' Strobe Width:    {self.STRB_WIDTH} bits\n'
        msg += f' Memory Lines:    {self.num_lines}\n'
        msg += f' Max Address:     0x{self.MAX_ADDR:08X}\n'
        msg += f' Max Data:        0x{self.MAX_DATA:08X}\n'
        msg += '-'*80 + '\n'
        msg += f' Clock Source:    {self.clk_src_PERIOD_NS}ns ({self.clk_src_FREQ_MHZ:.1f}MHz)\n'
        msg += f' Clock Dest:      {self.clk_dst_PERIOD_NS}ns ({self.clk_dst_FREQ_MHZ:.1f}MHz)\n'
        msg += f' Clock Ratio:     {self.clock_ratio:.3f} (dst/src)\n'
        msg += f' CDC Type:        {"Fast->Slow" if self.clock_ratio > 1 else "Slow->Fast" if self.clock_ratio < 1 else "Same Freq"}\n'
        msg += '-'*80 + '\n'
        msg += f' Randomizer Configs: {len(self.randomizer_configs)}\n'
        msg += f' Timeout Cycles:     {self.TIMEOUT_CYCLES}\n'
        msg += f' Super Debug:        {self.super_debug}\n'
        msg += '='*80
        self.log.info(msg)

    def src_transaction_callback(self, transaction):
        """Callback for source domain transactions with timing analysis"""
        transaction.domain = 'source'
        transaction.clock_freq = self.clk_src_FREQ_MHZ
        self.src_transactions.append(transaction)
        self.transactions_sent += 1

    def dst_transaction_callback(self, transaction):
        """Callback for destination domain transactions with timing analysis"""
        transaction.domain = 'destination'
        transaction.clock_freq = self.clk_dst_FREQ_MHZ
        self.dst_transactions.append(transaction)

        # CDC timing analysis
        if self.src_transactions:
            self._analyze_cdc_timing(transaction)

    def _analyze_cdc_timing(self, dst_transaction):
        """Analyze CDC timing for the destination transaction"""
        # Find corresponding source transaction
        src_transaction = None
        for src_trans in reversed(self.src_transactions):
            if self._transactions_match(src_trans, dst_transaction):
                src_transaction = src_trans
                break

        if src_transaction:
            # Calculate CDC timing metrics
            cdc_latency = dst_transaction.end_time - src_transaction.end_time
            src_cycles = cdc_latency / self.clk_src_PERIOD_NS
            dst_cycles = cdc_latency / self.clk_dst_PERIOD_NS

            timing_data = {
                'src_transaction': src_transaction,
                'dst_transaction': dst_transaction,
                'cdc_latency_ns': cdc_latency,
                'src_cycles': src_cycles,
                'dst_cycles': dst_cycles,
                'clock_ratio': self.clock_ratio
            }
            self.timing_analysis.append(timing_data)

            # Check for timing violations
            if cdc_latency < 0:
                self.log.error(f"CDC timing violation: dst before src! Latency: {cdc_latency}ns")
                self.cdc_violations += 1
                self.timing_errors += 1
            elif cdc_latency > (self.TIMEOUT_CYCLES * max(self.clk_src_PERIOD_NS, self.clk_dst_PERIOD_NS)):
                self.log.warning(f"CDC excessive latency: {cdc_latency}ns ({src_cycles:.1f} src cycles)")

    def _transactions_match(self, src_trans, dst_trans):
        """Check if source and destination transactions match"""
        return (src_trans.pwrite == dst_trans.pwrite and
                src_trans.paddr == dst_trans.paddr and
                src_trans.pwdata == dst_trans.pwdata and
                src_trans.pstrb == dst_trans.pstrb and
                src_trans.pprot == dst_trans.pprot)

    async def reset_dut(self):
        """Reset with comprehensive initialization"""
        self.log.debug('Starting reset_dut')
        self.test_start_time = get_sim_time('ns')

        # Reset DUT control signals
        self.dut.rst_src_n.value = 0
        self.dut.rst_dst_n.value = 0

        # Reset BFM components
        await self.src_master.reset_bus()
        await self.dst_slave.reset_bus()

        # Hold reset for multiple cycles (CDC safe)
        await self.wait_clocks('clk_src', 10)
        await self.wait_clocks('clk_dst', 10)

        # Release reset
        self.dut.rst_src_n.value = 1
        self.dut.rst_dst_n.value = 1

        # Wait for stabilization (CDC safe)
        await self.wait_clocks('clk_src', 15)
        await self.wait_clocks('clk_dst', 15)

        # Clear all monitoring data and statistics
        self.src_transactions.clear()
        self.dst_transactions.clear()
        self.timing_analysis.clear()
        self.total_errors = 0
        self.transactions_sent = 0
        self.transactions_verified = 0
        self.cdc_violations = 0
        self.timing_errors = 0
        self.data_errors = 0

        # Reset memory model
        self.mem.reset()

        self.log.debug('Reset_dut completed')

    async def send_transaction(self, is_write, addr, data=None, strobe=None, prot=0):
        """Transaction sending with better patterns and logging"""
        start_time = get_sim_time('ns')

        # Create packet with the specified fields
        packet = GAXIPacket(self.field_config)
        packet.pwrite = 1 if is_write else 0
        packet.paddr = addr & self.MAX_ADDR  # Mask to valid address range

        # For write transactions, set data and strobe
        if is_write:
            if data is None:
                data = random.randint(0, self.MAX_DATA)
            packet.pwdata = data & self.MAX_DATA

            if strobe is None:
                strobe = (2**self.STRB_WIDTH - 1)  # All bytes enabled
            packet.pstrb = strobe & ((2**self.STRB_WIDTH) - 1)

            # Store write data in memory model for verification
            try:
                data_ba = self.mem.integer_to_bytearray(packet.pwdata, self.STRB_WIDTH)
                self.mem.write(packet.paddr, data_ba, packet.pstrb)
            except Exception as e:
                self.log.warning(f"Memory write failed: {e}")
        else:
            # For read, set default values
            packet.pwdata = 0
            packet.pstrb = 0

        # Set protection bits
        packet.pprot = prot & 0x7  # Mask to 3 bits

        # logging
        trans_type = 'WRITE' if is_write else 'READ'
        if self.super_debug:
            self.log.debug(f"Sending {trans_type}: addr=0x{packet.paddr:08X}" +
                            (f" data=0x{packet.pwdata:08X} strb=0x{packet.pstrb:X}" if is_write else "") +
                            f" prot=0x{packet.pprot:X}")

        # Send transaction
        packet.start_time = start_time
        await self.src_master.send(packet)

        return packet

    async def wait_for_completion(self, expected_count=None, timeout_cycles=None):
        """Completion waiting with CDC considerations"""
        if timeout_cycles is None:
            timeout_cycles = self.TIMEOUT_CYCLES

        # Wait for source master to complete sending
        count = 0
        while self.src_master.transfer_busy and count < timeout_cycles:
            await self.wait_clocks('clk_src', 1)
            count += 1

        if count >= timeout_cycles:
            self.log.error(f"Timeout waiting for src_master after {timeout_cycles} cycles")
            return False

        # Wait additional cycles for CDC crossing (ratio-aware)
        cdc_wait_cycles = max(20, int(self.clock_ratio * 10 + 10))
        await self.wait_clocks('clk_src', cdc_wait_cycles)
        await self.wait_clocks('clk_dst', cdc_wait_cycles)

        # If expected count specified, wait for that many transactions
        if expected_count is not None:
            count = 0
            while len(self.dst_transactions) < expected_count and count < timeout_cycles:
                await self.wait_clocks('clk_dst', 1)
                count += 1

            if count >= timeout_cycles:
                self.log.error(f"Timeout waiting for {expected_count} transactions. Got {len(self.dst_transactions)}")
                return False

        return True

    def compare_transactions(self, expected_count=None, test_name=""):
        """Transaction comparison with CDC-specific analysis"""
        src_count = len(self.src_transactions)
        dst_count = len(self.dst_transactions)

        self.log.info(f"[{test_name}] Comparing {src_count} source and {dst_count} destination transactions")

        # Count verification
        errors_found = 0

        if expected_count is not None:
            if src_count != expected_count:
                self.log.error(f"Source transaction count mismatch: {src_count} vs {expected_count} expected")
                errors_found += 1

            if dst_count != expected_count:
                self.log.error(f"Destination transaction count mismatch: {dst_count} vs {expected_count} expected")
                errors_found += 1

        if src_count != dst_count:
            self.log.error(f"Cross-domain count mismatch: {src_count} source vs {dst_count} destination")
            errors_found += 1

        # Field-by-field comparison
        min_count = min(src_count, dst_count)
        field_errors = 0
        timing_errors = 0

        for i in range(min_count):
            src_trans = self.src_transactions[i]
            dst_trans = self.dst_transactions[i]

            # Compare all fields
            fields_match = True
            mismatches = []

            for field in ['pwrite', 'paddr', 'pwdata', 'pstrb', 'pprot']:
                src_val = getattr(src_trans, field, None)
                dst_val = getattr(dst_trans, field, None)

                if src_val != dst_val:
                    fields_match = False
                    mismatches.append(f"{field}: src=0x{src_val:X} vs dst=0x{dst_val:X}")

            if not fields_match:
                self.log.error(f"Transaction {i+1} field mismatch: " + ", ".join(mismatches))
                field_errors += 1

            # CDC timing verification
            if (hasattr(src_trans, 'end_time') and hasattr(dst_trans, 'end_time') and
                dst_trans.end_time <= src_trans.end_time):
                self.log.error(f"Transaction {i+1} CDC timing violation: "
                             f"dst={dst_trans.end_time}ns <= src={src_trans.end_time}ns")
                timing_errors += 1

        # Update error counters
        self.data_errors += field_errors
        self.timing_errors += timing_errors
        total_errors = errors_found + field_errors + timing_errors
        self.total_errors += total_errors

        # CDC performance analysis
        if self.timing_analysis:
            latencies = [t['cdc_latency_ns'] for t in self.timing_analysis]
            avg_latency = sum(latencies) / len(latencies)
            min_latency = min(latencies)
            max_latency = max(latencies)

            self.log.info(f"[{test_name}] CDC Performance Analysis:")
            self.log.info(f"  Average latency: {avg_latency:.2f}ns")
            self.log.info(f"  Latency range: {min_latency:.2f}ns - {max_latency:.2f}ns")
            self.log.info(f"  Clock ratio: {self.clock_ratio:.3f}")

        # Report results
        if total_errors == 0:
            self.log.info(f"[{test_name}] All {min_count} transactions verified successfully")
            self.transactions_verified += min_count
            return True
        else:
            self.log.error(f"[{test_name}] Found {total_errors} errors: {field_errors} data, {timing_errors} timing")
            return False

    def get_comprehensive_statistics(self):
        """Get comprehensive testbench statistics"""
        current_time = get_sim_time('ns')
        test_duration = current_time - self.test_start_time if self.test_start_time > 0 else 0

        stats = {
            # Basic counts
            'transactions_sent': self.transactions_sent,
            'transactions_verified': self.transactions_verified,
            'src_transactions': len(self.src_transactions),
            'dst_transactions': len(self.dst_transactions),

            # Error tracking
            'total_errors': self.total_errors,
            'cdc_violations': self.cdc_violations,
            'timing_errors': self.timing_errors,
            'data_errors': self.data_errors,

            # Performance metrics
            'test_duration_ns': test_duration,
            'throughput_tps': self.transactions_verified / (test_duration / 1e9) if test_duration > 0 else 0,

            # CDC analysis
            'clock_ratio': self.clock_ratio,
            'src_freq_mhz': self.clk_src_FREQ_MHZ,
            'dst_freq_mhz': self.clk_dst_FREQ_MHZ,
            'timing_analysis_count': len(self.timing_analysis),

            # Component statistics
            'src_master_stats': self.src_master.get_stats() if hasattr(self.src_master, 'get_stats') else {},
            'dst_slave_stats': self.dst_slave.get_stats() if hasattr(self.dst_slave, 'get_stats') else {},
            'memory_stats': self.mem.get_stats() if hasattr(self.mem, 'get_stats') else {},
        }

        # Add latency statistics if available
        if self.timing_analysis:
            latencies = [t['cdc_latency_ns'] for t in self.timing_analysis]
            stats.update({
                'avg_cdc_latency_ns': sum(latencies) / len(latencies),
                'min_cdc_latency_ns': min(latencies),
                'max_cdc_latency_ns': max(latencies),
            })

        return stats

    # Test Patterns (adapted from GAXI buffer TB)

    async def run_simple_incremental_test(self, count, randomizer_config='moderate', test_name="Simple Incremental"):
        """Run simple incremental test with specified randomizer configuration"""
        self.log.info(f"[{test_name}] Starting with {count} transactions, config='{randomizer_config}'")

        # Set randomizers
        if randomizer_config in self.randomizer_configs:
            src_config = self.randomizer_configs[randomizer_config]['source']
            dst_config = self.randomizer_configs[randomizer_config]['destination']

            self.src_master.set_randomizer(FlexRandomizer(src_config))
            self.dst_slave.set_randomizer(FlexRandomizer(dst_config))

        # Reset and prepare
        await self.reset_dut()

        # Send transactions
        base_addr = 0x1000
        for i in range(count):
            is_write = (i % 3 != 2)  # 2/3 writes, 1/3 reads
            addr = base_addr + (i * 4)
            data = (i * 0x11223344) & self.MAX_DATA if is_write else None

            await self.send_transaction(is_write, addr, data)

            # Add small delay between transactions
            if i % 10 == 9:
                await self.wait_clocks('clk_src', 5)

        # Wait for completion
        success = await self.wait_for_completion(expected_count=count)
        if not success:
            return False

        # Verify results
        return self.compare_transactions(count, test_name)

    async def run_walking_bits_test(self, test_name="Walking Bits"):
        """Test with walking 1s and 0s patterns"""
        self.log.info(f"[{test_name}] Starting walking bits test")

        # Use stress config for walking bits
        self.src_master.set_randomizer(self._get_randomizer_for_level('stress'))
        self.dst_slave.set_randomizer(self._get_randomizer_for_level('stress'))

        await self.reset_dut()

        patterns = []
        base_addr = 0x2000

        # Walking 1s
        for bit in range(min(32, self.DATA_WIDTH)):
            patterns.append((1 << bit, f"walking_1_bit_{bit}"))

        # Walking 0s
        all_ones = self.MAX_DATA
        for bit in range(min(32, self.DATA_WIDTH)):
            patterns.append((all_ones & ~(1 << bit), f"walking_0_bit_{bit}"))

        # Send patterns
        for i, (pattern, description) in enumerate(patterns):
            addr = base_addr + (i * 4)
            await self.send_transaction(True, addr, pattern)

            if self.super_debug:
                self.log.debug(f"Sent {description}: 0x{pattern:08X}")

        # Wait and verify
        success = await self.wait_for_completion(expected_count=len(patterns))
        return success and self.compare_transactions(len(patterns), test_name)

    async def run_stress_test(self, count=100, randomizer_config='cdc_aggressive', test_name="Stress Test"):
        """Run stress test with aggressive timing and complex patterns"""
        self.log.info(f"[{test_name}] Starting with {count} transactions, config='{randomizer_config}'")

        # Set aggressive randomizers
        if randomizer_config in self.randomizer_configs:
            config = self.randomizer_configs[randomizer_config]
            self.src_master.set_randomizer(FlexRandomizer(config['source']))
            self.dst_slave.set_randomizer(FlexRandomizer(config['destination']))

        await self.reset_dut()

        # Generate stress patterns
        base_addr = 0x4000
        patterns = []

        # Address stress patterns
        addr_patterns = [0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA, 0x12345678]
        data_patterns = [0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA, 0xDEADBEEF]
        strobe_patterns = [0x1, 0x3, 0x7, 0xF, 0x5, 0xA, 0xC] if self.STRB_WIDTH == 4 else [0xF]

        for i in range(count):
            # Mix of deterministic and random patterns
            if i < len(addr_patterns) * len(data_patterns):
                addr_idx = i % len(addr_patterns)
                data_idx = (i // len(addr_patterns)) % len(data_patterns)
                addr = (base_addr + addr_patterns[addr_idx]) & self.MAX_ADDR
                data = data_patterns[data_idx] & self.MAX_DATA
            else:
                addr = (base_addr + random.randint(0, 0xFFFF)) & self.MAX_ADDR
                data = random.randint(0, self.MAX_DATA)

            is_write = random.choice([True, True, False])  # 2:1 write:read ratio
            strobe = random.choice(strobe_patterns) if is_write else None
            prot = random.choice([0, 1, 2, 4]) if random.random() < 0.1 else 0

            await self.send_transaction(is_write, addr, data, strobe, prot)

            # Occasional bursts
            if i % 20 == 19:
                await self.wait_clocks('clk_src', random.randint(1, 5))

        # Wait and verify
        success = await self.wait_for_completion(expected_count=count)
        return success and self.compare_transactions(count, test_name)

    async def run_comprehensive_randomizer_sweep(self, packets_per_config=20, test_name="Randomizer Sweep"):
        """Test all available randomizer configurations"""
        self.log.info(f"[{test_name}] Testing {len(self.randomizer_configs)} configurations with {packets_per_config} packets each")

        total_configs = len(self.randomizer_configs)
        failures = 0

        for i, config_name in enumerate(self.randomizer_configs.keys()):
            self.log.info(f"[{test_name}] Config {i+1}/{total_configs}: {config_name}")

            try:
                success = await self.run_simple_incremental_test(
                    count=packets_per_config,
                    randomizer_config=config_name,
                    test_name=f"{test_name}-{config_name}"
                )

                if success:
                    self.log.info(f"✓ Config '{config_name}' passed")
                else:
                    self.log.error(f"✗ Config '{config_name}' failed")
                    failures += 1

            except Exception as e:
                self.log.error(f"✗ Config '{config_name}' exception: {e}")
                failures += 1

        self.log.info(f"[{test_name}] Completed: {total_configs - failures}/{total_configs} configs passed")
        return failures == 0

    async def run_back_to_back_test(self, count=50, test_name="Back-to-Back"):
        """Test back-to-back transactions with minimal delays"""
        self.log.info(f"[{test_name}] Starting with {count} transactions")

        # Use backtoback configuration
        config = self.randomizer_configs.get('backtoback', self.randomizer_configs['fast'])
        self.src_master.set_randomizer(FlexRandomizer(config['source']))
        self.dst_slave.set_randomizer(FlexRandomizer(config['destination']))

        await self.reset_dut()

        # Send back-to-back transactions
        base_addr = 0x8000
        for i in range(count):
            addr = base_addr + (i * 4)
            data = (i * 7 + 13) & self.MAX_DATA
            is_write = (i % 2 == 0)

            await self.send_transaction(is_write, addr, data if is_write else None)

        # Wait and verify
        success = await self.wait_for_completion(expected_count=count)
        return success and self.compare_transactions(count, test_name)

    # Main test orchestration methods

    async def run_basic_tests(self):
        """Run basic test suite (2-3 minutes)"""
        self.log.info("=== BASIC TEST SUITE ===")

        tests = [
            (self.run_simple_incremental_test, [10, 'moderate']),
            (self.run_back_to_back_test, [15]),
            (self.run_walking_bits_test, []),
        ]

        return await self._run_test_suite(tests, "Basic")

    async def run_medium_tests(self):
        """Run medium test suite (5-8 minutes)"""
        self.log.info("=== MEDIUM TEST SUITE ===")

        tests = [
            (self.run_simple_incremental_test, [20, 'moderate']),
            (self.run_simple_incremental_test, [20, 'cdc_conservative']),
            (self.run_back_to_back_test, [30]),
            (self.run_walking_bits_test, []),
            (self.run_stress_test, [50, 'cdc_mixed_freq']),
            (self.run_comprehensive_randomizer_sweep, [10]),
        ]

        return await self._run_test_suite(tests, "Medium")

    async def run_full_tests(self):
        """Run full test suite (15-25 minutes)"""
        self.log.info("=== FULL TEST SUITE ===")

        tests = [
            (self.run_simple_incremental_test, [50, 'moderate']),
            (self.run_simple_incremental_test, [50, 'cdc_conservative']),
            (self.run_simple_incremental_test, [50, 'cdc_aggressive']),
            (self.run_back_to_back_test, [100]),
            (self.run_walking_bits_test, []),
            (self.run_stress_test, [100, 'cdc_mixed_freq']),
            (self.run_stress_test, [100, 'cdc_burst_stress']),
            (self.run_stress_test, [100, 'cdc_metastable']),
            (self.run_comprehensive_randomizer_sweep, [25]),
        ]

        return await self._run_test_suite(tests, "Full")

    async def _run_test_suite(self, tests, suite_name):
        """Run a suite of tests with error tracking"""
        total_tests = len(tests)
        passed_tests = 0

        for i, (test_func, args) in enumerate(tests):
            test_name = f"{suite_name}-{test_func.__name__}-{i+1}"
            self.log.info(f"Running test {i+1}/{total_tests}: {test_name}")

            try:
                success = await test_func(*args)
                if success:
                    passed_tests += 1
                    self.log.info(f"✓ {test_name} PASSED")
                else:
                    self.log.error(f"✗ {test_name} FAILED")

            except Exception as e:
                self.log.error(f"✗ {test_name} EXCEPTION: {e}")
                import traceback
                self.log.error(traceback.format_exc())

        # Final statistics
        stats = self.get_comprehensive_statistics()
        self.log.info(f"{suite_name} Suite Results: {passed_tests}/{total_tests} tests passed")
        self.log.info(f"Total errors: {stats['total_errors']}")
        self.log.info(f"Transactions verified: {stats['transactions_verified']}")

        return passed_tests == total_tests and stats['total_errors'] == 0