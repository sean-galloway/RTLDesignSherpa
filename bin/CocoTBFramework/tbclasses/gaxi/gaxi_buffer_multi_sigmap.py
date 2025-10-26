# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GaxiMultiSigMapBufferTB
# Purpose: Updated Testbench for GAXI multi-signal components - FIXED timing issues
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated Testbench for GAXI multi-signal components - FIXED timing issues

Key fixes:
- Added proper completion checking after sending packets
- Wait for expected number of packets to be received before verification
- Account for buffer depth and mode-specific delays
- Added timeout protection to prevent infinite waits
- Enhanced timing calculations based on buffer characteristics
"""
import os
import random

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.shared.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.shared.flex_config_gen import FlexConfigGen

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_seq import GAXIBufferSequence
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_configs import FIELD_CONFIGS
from CocoTBFramework.components.shared.memory_model import MemoryModel


class GaxiMultiSigMapBufferTB(TBBase):
    """
    Multi-signal GAXI buffer testbench with FIXED timing and completion checking.
    
    Fixed timing issues:
    - Proper completion checking after sending packets
    - Wait for expected packet counts before verification
    - Buffer-depth-aware timing calculations
    - Mode-specific delay considerations
    - Timeout protection for completion waits
    """

    def __init__(self, dut,
                    wr_clk=None, wr_rstn=None,
                    rd_clk=None, rd_rstn=None):
        super().__init__(dut)

        # Get test parameters from environment - UNCHANGED API
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '2'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '4'))
        self.TEST_CTRL_WIDTH = self.convert_to_int(os.environ.get('TEST_CTRL_WIDTH', '3'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '8'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'skid')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Setup widths and limits - UNCHANGED API
        self.AW = self.TEST_ADDR_WIDTH
        self.MAX_ADDR = (2**self.TEST_ADDR_WIDTH)-1
        self.CW = self.TEST_CTRL_WIDTH
        self.MAX_CTRL = (2**self.TEST_CTRL_WIDTH)-1
        self.DW = self.TEST_DATA_WIDTH
        self.MAX_DATA = (2**self.TEST_DATA_WIDTH)-1
        self.TIMEOUT_CYCLES = 1000

        # FIXED: Enhanced timing calculations based on buffer characteristics
        self.COMPLETION_TIMEOUT_CYCLES = max(1000, self.TEST_DEPTH * 100)  # Scale with buffer depth
        self.MODE_SPECIFIC_DELAYS = {
            'skid': 3,        # Skid buffer: ~3 cycle latency
            'fifo_mux': 2,    # FIFO mux: ~2 cycle latency  
            'fifo_flop': 3    # FIFO flop: ~3 cycle latency
        }
        self.BASE_COMPLETION_DELAY = self.MODE_SPECIFIC_DELAYS.get(self.TEST_MODE, 3)
        
        # Setup clock and reset signals - UNCHANGED API
        self.wr_clk = wr_clk
        self.wr_clk_name = wr_clk.name
        self.wr_rstn = wr_rstn
        self.rd_clk = self.wr_clk if rd_clk is None else rd_clk
        self.rd_clk_name = self.wr_clk_name if rd_clk is None else rd_clk.name
        self.rd_rstn = self.wr_rstn if rd_rstn is None else rd_rstn

        # Enhanced verification settings
        self.strict_verification = True
        self.fail_fast = True  # Stop on first verification error
        self.max_allowed_errors = 0  # No errors allowed

        # Log the test configuration with timing info
        msg = '\n'
        msg += '='*80 + "\n"
        msg += ' Settings:\n'
        msg += '-'*80 + "\n"
        msg += f' Depth:    {self.TEST_DEPTH}\n'
        msg += f' AddrW:    {self.TEST_ADDR_WIDTH}\n'
        msg += f' CtrlW:    {self.TEST_CTRL_WIDTH}\n'
        msg += f' DataW:    {self.TEST_DATA_WIDTH}\n'
        msg += f' Max Addr: {self.MAX_ADDR}\n'
        msg += f' Max Ctrl: {self.MAX_CTRL}\n'
        msg += f' Max Data: {self.MAX_DATA}\n'
        msg += f' MODE:     {self.TEST_MODE}\n'
        msg += f' clk_wr:   {self.TEST_CLK_WR}\n'
        msg += f' clk_rd:   {self.TEST_CLK_RD}\n'
        msg += f' SEED:     {self.SEED}\n'
        msg += f' STRICT:   {self.strict_verification}\n'
        msg += f' FAIL_FAST:{self.fail_fast}\n'
        msg += f' COMPLETION_TIMEOUT: {self.COMPLETION_TIMEOUT_CYCLES}\n'
        msg += f' BASE_DELAY: {self.BASE_COMPLETION_DELAY}\n'
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Create FlexConfigGen manager and get randomizer instances directly
        self.randomizer_manager = self._create_comprehensive_randomizer_manager()

        self.master_signal_map = {
            'valid' : 'wr_valid',
            'ready' : 'wr_ready',
            'addr'  : 'wr_siga',
            'ctrl'  : 'wr_sigb',
            'data0' : 'wr_sigc',
            'data1' : 'wr_sigd'
        }
        self.slave_signal_map = {
            'valid' : 'rd_valid',
            'ready' : 'rd_ready',
            'addr'  : 'rd_sige',
            'ctrl'  : 'rd_sigf',
            'data0' : 'rd_sigg',
            'data1' : 'rd_sigh'
        }

        # Define field configuration using new unified infrastructure
        base_config = FIELD_CONFIGS.get('field', {
            'addr': {'bits': self.AW, 'start_bit': 0},
            'ctrl': {'bits': self.CW, 'start_bit': self.AW},
            'data0': {'bits': self.DW, 'start_bit': self.AW + self.CW},
            'data1': {'bits': self.DW, 'start_bit': self.AW + self.CW + self.DW}
        })

        # Create normalized field configuration
        self.field_config = FieldConfig.validate_and_create(field_dict=base_config, lsb_first=True)

        # Update field widths from test parameters
        self.field_config.update_field_width('addr', self.AW)
        self.field_config.update_field_width('ctrl', self.CW)
        self.field_config.update_field_width('data0', self.DW)
        self.field_config.update_field_width('data1', self.DW)

        self.log.debug(f"\n{self.field_config}")

        # Create memory models
        self.input_memory_model = MemoryModel(
            num_lines=16,
            bytes_per_line=4,  # addr + ctrl + data0 + data1
            log=self.log
        )

        self.output_memory_model = MemoryModel(
            num_lines=self.TEST_DEPTH,
            bytes_per_line=4,  # addr + ctrl + data0 + data1
            log=self.log
        )
        self.super_debug = True

        # Create BFM components using FlexConfigGen randomizer instances
        default_master_randomizer = self.get_randomizer('balanced', 'master')
        self.write_master = GAXIMaster(
            dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            multi_sig=True,  # Enable multi-signal mode
            mode=self.TEST_MODE,
            timeout_cycles=self.TIMEOUT_CYCLES,
            memory_model=self.input_memory_model,
            signal_map=self.master_signal_map,
            log=self.log,
            super_debug=self.super_debug
        )
        # Set default randomizer
        self.write_master.set_randomizer(default_master_randomizer)

        default_slave_randomizer = self.get_randomizer('balanced', 'slave')
        self.read_slave = GAXISlave(
            dut, 'read_slave', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            multi_sig=True,  # Enable multi-signal mode
            timeout_cycles=self.TIMEOUT_CYCLES,
            memory_model=self.output_memory_model,
            signal_map=self.slave_signal_map,
            log=self.log,
            super_debug=self.super_debug
        )
        # Set default randomizer
        self.read_slave.set_randomizer(default_slave_randomizer)

        # Set up monitors using new infrastructure
        self.wr_monitor = GAXIMonitor(
            dut, 'WrMon', '', self.wr_clk,
            field_config=self.field_config,
            multi_sig=True,  # Enable multi-signal mode
            is_slave=False,  # Monitor master side
            mode=self.TEST_MODE,
            signal_map=self.master_signal_map,
            log=self.log,
            super_debug=self.super_debug
        )

        self.rd_monitor = GAXIMonitor(
            dut, 'RdMon', '', self.rd_clk,
            field_config=self.field_config,
            multi_sig=True,  # Enable multi-signal mode
            is_slave=True,  # Monitor slave side
            mode=self.TEST_MODE,
            signal_map=self.slave_signal_map,
            log=self.log,
            super_debug=self.super_debug
        )

        # Setup sequence generator with new infrastructure patterns
        self.sequence_gen = GAXIBufferSequence(
            name="multi_buffer_test",
            field_config=self.field_config,
            packet_class=GAXIPacket
        )

        # Enhanced statistics tracking with verification details
        self.stats = {
            'total_sent': 0,
            'total_received': 0,
            'total_errors': 0,
            'verification_errors': 0,
            'field_mismatch_errors': 0,
            'sequence_completed': False,
            'test_duration': 0,
            'failed_tests': [],
            'last_error_details': None,
            'packet_errors': {},  # Track errors per packet
            'completion_timeouts': 0,  # Track completion timeout events
            'expected_packets': 0      # Track expected packet count
        }

        # Enhanced error tracking
        self.verification_failures = []
        self.field_error_counts = {
            'addr': 0,
            'ctrl': 0,
            'data0': 0,
            'data1': 0
        }

        # Compatibility attributes for existing test runners
        self.total_sent = 0
        self.total_received = 0
        self.total_errors = 0

        self.log.info(f"Testbench initialized with mode='{self.TEST_MODE}', depth={self.TEST_DEPTH}")
        self.log.info(f"Verification: strict={self.strict_verification}, fail_fast={self.fail_fast}")
        self.log.info(f"Timing: completion_timeout={self.COMPLETION_TIMEOUT_CYCLES}, base_delay={self.BASE_COMPLETION_DELAY}")

    # [Keep all the existing randomizer and sequence methods unchanged - they're fine]
    def _create_comprehensive_randomizer_manager(self):
        """Create FlexConfigGen manager that returns FlexRandomizer instances directly"""

        # Define GAXI buffer-specific profiles
        gaxi_buffer_profiles = {
            # Buffer-specific patterns optimized for throughput and latency testing
            'buffer_throughput': ([(0, 0), (1, 1)], [8, 1]),                    # Maximize throughput
            'buffer_latency': ([(0, 2), (3, 6)], [4, 1]),                       # Test latency sensitivity
            'buffer_backpressure': ([(0, 0), (4, 12)], [2, 1]),                 # Test backpressure handling
            'buffer_mixed': ([(0, 1), (2, 4), (8, 15)], [5, 3, 1]),            # Mixed behavior
            'buffer_burst': ([(0, 0), (5, 8)], [15, 1]),                        # Burst testing
            'buffer_coordinated': ([(1, 3), (4, 7)], [3, 2]),                   # Coordinated timing
        }

        # Create FlexConfigGen - NOTE: return_flexrandomizer=True
        config_gen = FlexConfigGen(
            profiles=[
                # Standard canned profiles
                'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
                'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
                'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
                'slow_consumer', 'slow_producer', 'burst_pause', 'fixed',
                # Buffer-specific profiles
                'buffer_throughput', 'buffer_latency', 'buffer_backpressure',
                'buffer_mixed', 'buffer_burst', 'buffer_coordinated'
            ],
            fields=['valid_delay', 'ready_delay'],
            custom_profiles=gaxi_buffer_profiles
        )

        # Customize profiles for buffer-specific behavior
        self._customize_profiles(config_gen)

        # Build and get FlexRandomizer instances directly
        self.randomizer_instances = config_gen.build(return_flexrandomizer=True)

        # Create master/slave domain mapping
        self.domain_randomizers = {}
        for profile_name, randomizer in self.randomizer_instances.items():
            self.domain_randomizers[profile_name] = {
                'master': randomizer,  # Master gets the randomizer instance
                'slave': randomizer    # Slave gets the same randomizer instance
            }

        self.log.info(f"Created {len(self.randomizer_instances)} buffer randomizer instances via FlexConfigGen:")
        for profile_name in self.randomizer_instances.keys():
            self.log.info(f"  - {profile_name}")

        return config_gen

    def _customize_profiles(self, config_gen):
        """Customize FlexConfigGen profiles for buffer-specific behavior"""

        # Ultra-aggressive for maximum throughput
        config_gen.backtoback.valid_delay.fixed_value(0)
        config_gen.backtoback.ready_delay.fixed_value(0)

        # Fixed delays for predictable testing
        config_gen.fixed.valid_delay.fixed_value(0)
        config_gen.fixed.ready_delay.fixed_value(0)

        # Fast patterns optimized for buffer testing
        config_gen.fast.valid_delay.mostly_zero(zero_weight=50, fallback_range=(1, 2), fallback_weight=1)
        config_gen.fast.ready_delay.mostly_zero(zero_weight=45, fallback_range=(1, 3), fallback_weight=2)

        # Stress test with buffer variations
        config_gen.stress.valid_delay.weighted_ranges([
            ((0, 0), 10), ((1, 3), 6), ((4, 8), 3), ((12, 18), 1)
        ])
        config_gen.stress.ready_delay.weighted_ranges([
            ((0, 1), 8), ((2, 5), 5), ((6, 12), 3), ((18, 25), 1)
        ])

        # Buffer throughput optimized
        config_gen.buffer_throughput.valid_delay.mostly_zero(zero_weight=80, fallback_range=(1, 1), fallback_weight=1)
        config_gen.buffer_throughput.ready_delay.mostly_zero(zero_weight=75, fallback_range=(1, 1), fallback_weight=1)

        # Buffer latency testing
        config_gen.buffer_latency.valid_delay.uniform_range(0, 3)
        config_gen.buffer_latency.ready_delay.uniform_range(1, 5)

        # Buffer backpressure testing
        config_gen.buffer_backpressure.valid_delay.mostly_zero(zero_weight=30, fallback_range=(1, 2), fallback_weight=1)
        config_gen.buffer_backpressure.ready_delay.weighted_ranges([((0, 0), 2), ((4, 12), 1)])

        # Slow consumer pattern for buffer overflow testing
        config_gen.slow_consumer.valid_delay.mostly_zero(zero_weight=70, fallback_range=(1, 2), fallback_weight=1)
        config_gen.slow_consumer.ready_delay.weighted_ranges([((0, 1), 3), ((8, 15), 1)])

        # Slow producer pattern
        config_gen.slow_producer.valid_delay.weighted_ranges([((0, 1), 3), ((6, 12), 1)])
        config_gen.slow_producer.ready_delay.mostly_zero(zero_weight=70, fallback_range=(1, 2), fallback_weight=1)

        # Burst pause for buffer depth testing
        config_gen.burst_pause.valid_delay.burst_pattern(fast_cycles=0, pause_range=(self.TEST_DEPTH, self.TEST_DEPTH*2), burst_ratio=20)
        config_gen.burst_pause.ready_delay.burst_pattern(fast_cycles=0, pause_range=(self.TEST_DEPTH//2, self.TEST_DEPTH), burst_ratio=15)

    def get_randomizer(self, profile_name, domain='master'):
        """Get FlexRandomizer instance for specified profile and domain"""
        if profile_name in self.domain_randomizers:
            return self.domain_randomizers[profile_name][domain]
        else:
            self.log.warning(f"Randomizer profile '{profile_name}' not found, using 'balanced'")
            return self.domain_randomizers['balanced'][domain]

    def get_available_profiles(self):
        """Get list of available randomizer profile names"""
        return list(self.randomizer_instances.keys())

    def set_randomizer_profile(self, profile_name):
        """Set randomizer profile for all components using FlexConfigGen instances"""
        master_randomizer = self.get_randomizer(profile_name, 'master')
        slave_randomizer = self.get_randomizer(profile_name, 'slave')

        # Set randomizers directly from FlexConfigGen instances
        self.write_master.set_randomizer(master_randomizer)
        self.read_slave.set_randomizer(slave_randomizer)

        self.log.info(f"Set randomizers to profile '{profile_name}' - both domains updated")

    # Enhanced sequence generation methods using FlexConfigGen randomizers

    def basic_sequence(self, count=100):
        """Generate basic sequence with simple patterns"""
        self.sequence_gen.clear()
        self.sequence_gen.add_incrementing_pattern(count // 2)
        self.sequence_gen.add_random_pattern(count // 2)
        return self.sequence_gen

    def walking_ones_sequence(self, count=None):
        """Generate walking ones pattern sequence"""
        self.sequence_gen.clear()
        self.sequence_gen.add_walking_ones_pattern()
        if count and count > 32:  # If more patterns needed beyond walking ones
            self.sequence_gen.add_random_pattern(count - 32)
        return self.sequence_gen

    def alternating_sequence(self, count=50):
        """Generate alternating bit patterns"""
        self.sequence_gen.clear()
        self.sequence_gen.add_alternating_patterns(count)
        return self.sequence_gen

    def burst_sequence(self, count=80):
        """Generate burst patterns for testing buffer depth"""
        self.sequence_gen.clear()
        self.sequence_gen.add_burst_pattern(count)
        return self.sequence_gen

    def random_sequence(self, count=100):
        """Generate random data sequence"""
        self.sequence_gen.clear()
        self.sequence_gen.add_random_pattern(count)
        return self.sequence_gen

    def comprehensive_sequence(self, count=200):
        """Generate comprehensive test sequence"""
        self.sequence_gen.clear()
        self.sequence_gen.add_boundary_values()
        self.sequence_gen.add_walking_ones_pattern()
        self.sequence_gen.add_alternating_patterns(count // 4)
        self.sequence_gen.add_max_value_pattern()
        self.sequence_gen.add_random_pattern(count - 50)  # Fill remainder
        return self.sequence_gen

    def stress_sequence(self, count=150):
        """Generate stress test sequence"""
        self.sequence_gen.clear()
        self.sequence_gen.add_boundary_values()
        self.sequence_gen.add_overflow_test()
        self.sequence_gen.add_max_value_pattern()
        self.sequence_gen.add_burst_pattern(count // 3)
        self.sequence_gen.add_random_pattern(count - 70)  # Fill remainder
        return self.sequence_gen

    # FIXED API Methods with proper completion checking

    async def simple_incremental_loops(self, count=100, delay_key='fixed', delay_clks_after=10):
        """
        Legacy simple incremental test with FIXED COMPLETION CHECKING.
        """
        test_name = f"simple_incremental_loops(count={count})"
        self.log.info(f"Running {test_name} with delay_key='{delay_key}'")

        try:
            # Set randomizer profile using FlexConfigGen instances
            self.set_randomizer_profile(delay_key)

            # Reset statistics
            self.reset_statistics()

            # Generate simple incrementing sequence
            sequence = self.basic_sequence(count)

            # Run the sequence with proper completion checking
            await self.run_sequence_with_completion(sequence, test_name)

            # FIXED: Use calculated completion delay instead of fixed delay_clks_after
            calculated_delay = self._calculate_completion_delay(count)
            additional_delay = max(delay_clks_after, calculated_delay)
            
            self.log.info(f"Waiting additional {additional_delay} cycles for final completion")
            await self.wait_clocks(self.wr_clk_name, additional_delay)

            # STRICT VERIFICATION
            result = self.verify_transactions_strict(test_name)

            if result:
                self.log.info(f"✅ {test_name} completed successfully")
            else:
                self.log.error(f"❌ {test_name} FAILED verification")
                if self.fail_fast:
                    raise AssertionError(f"VERIFICATION FAILED: {test_name}")

            return result

        except Exception as e:
            self.log.error(f"❌ Exception in {test_name}: {e}")
            self.stats['failed_tests'].append(test_name)
            self.stats['last_error_details'] = str(e)
            if self.fail_fast:
                raise
            return False

    async def run_sequence_test(self, sequence_generator, delay_key='balanced', delay_clks_after=20):
        """
        Run sequence test with FIXED COMPLETION CHECKING.
        """
        # Get test name from sequence generator
        test_name = f"sequence_test({sequence_generator.__name__ if callable(sequence_generator) else str(sequence_generator)})"
        self.log.info(f"Running {test_name} with delay_key='{delay_key}'")

        try:
            # Set randomizer profile using FlexConfigGen instances
            self.set_randomizer_profile(delay_key)

            # Reset statistics
            self.reset_statistics()

            # Get the sequence (generator is a callable that returns sequence)
            if callable(sequence_generator):
                sequence = sequence_generator()
            else:
                sequence = sequence_generator

            # Run the sequence with proper completion checking
            await self.run_sequence_with_completion(sequence, test_name)

            # FIXED: Use calculated completion delay
            transaction_count = len(sequence.get_transactions()) if hasattr(sequence, 'get_transactions') else 50
            calculated_delay = self._calculate_completion_delay(transaction_count)
            additional_delay = max(delay_clks_after, calculated_delay)
            
            self.log.info(f"Waiting additional {additional_delay} cycles for final completion")
            await self.wait_clocks(self.wr_clk_name, additional_delay)

            # STRICT VERIFICATION
            result = self.verify_transactions_strict(test_name)

            if result:
                self.log.info(f"✅ {test_name} completed successfully")
            else:
                self.log.error(f"❌ {test_name} FAILED verification")
                if self.fail_fast:
                    raise AssertionError(f"VERIFICATION FAILED: {test_name}")

            return result

        except Exception as e:
            self.log.error(f"❌ Exception in {test_name}: {e}")
            self.stats['failed_tests'].append(test_name)
            self.stats['last_error_details'] = str(e)
            if self.fail_fast:
                raise
            return False

    async def run_sequence_with_completion(self, sequence_gen, test_name="Unknown"):
        """
        FIXED: Run test sequence with proper completion checking.
        """
        if sequence_gen is None:
            sequence_gen = self.sequence_gen

        transactions = sequence_gen.get_transactions()
        expected_count = len(transactions)
        self.stats['expected_packets'] = expected_count
        
        self.log.info(f"Running sequence '{test_name}' with {expected_count} transactions")

        # Clear monitor queues before starting
        if hasattr(self.wr_monitor, '_recvQ'):
            self.wr_monitor._recvQ.clear()
        if hasattr(self.rd_monitor, '_recvQ'):
            self.rd_monitor._recvQ.clear()

        # Send all packets
        for i, transaction_data in enumerate(transactions):
            packet = GAXIPacket(self.field_config)

            if isinstance(transaction_data, tuple) and len(transaction_data) >= 1:
                field_values = transaction_data[0]
                delay = transaction_data[1] if len(transaction_data) > 1 else 0
            elif isinstance(transaction_data, dict):
                field_values = transaction_data
                delay = 0
            else:
                self.log.error(f"Invalid transaction data format: {transaction_data}")
                continue

            for field_name, value in field_values.items():
                if hasattr(packet, field_name):
                    setattr(packet, field_name, value)

            await self.write_master.send(packet)
            self.stats['total_sent'] += 1
            self.total_sent += 1

            if delay > 0:
                await self.wait_clocks(self.wr_clk_name, delay)

            if (i + 1) % 50 == 0:
                self.log.debug(f"Sent {i+1}/{expected_count} transactions")

        self.log.info(f"Completed sending {expected_count} transactions")

        # FIXED: Wait for master transmission to complete
        await self._wait_for_master_completion(test_name)

        # FIXED: Wait for expected packets to be received
        await self._wait_for_packet_reception(expected_count, test_name)

    async def _wait_for_master_completion(self, test_name="Unknown"):
        """FIXED: Wait for master transmission pipeline to complete"""
        self.log.debug(f"Waiting for master transmission completion for {test_name}")
        
        timeout_cycles = 0
        max_timeout = self.COMPLETION_TIMEOUT_CYCLES
        
        # Wait for master to finish transmitting
        while self.write_master.transfer_busy and timeout_cycles < max_timeout:
            await self.wait_clocks(self.wr_clk_name, 1)
            timeout_cycles += 1
            
            if timeout_cycles % 100 == 0:
                self.log.debug(f"Master completion wait: {timeout_cycles}/{max_timeout} cycles")
        
        if timeout_cycles >= max_timeout:
            self.log.error(f"❌ Master completion timeout after {timeout_cycles} cycles for {test_name}")
            self.stats['completion_timeouts'] += 1
            raise TimeoutError(f"Master completion timeout for {test_name}")
        
        # Additional buffer-specific delay
        buffer_delay = self.BASE_COMPLETION_DELAY + self.TEST_DEPTH
        self.log.debug(f"Waiting {buffer_delay} additional cycles for buffer pipeline")
        await self.wait_clocks(self.wr_clk_name, buffer_delay)
        
        self.log.debug(f"Master transmission completed for {test_name} after {timeout_cycles} cycles")

    async def _wait_for_packet_reception(self, expected_count, test_name="Unknown"):
        """FIXED: Wait for expected number of packets to be received by monitors"""
        self.log.debug(f"Waiting for {expected_count} packets to be received for {test_name}")
        
        timeout_cycles = 0
        max_timeout = self.COMPLETION_TIMEOUT_CYCLES
        check_interval = 10  # Check every 10 cycles
        
        while timeout_cycles < max_timeout:
            # Check both monitors for received packets
            wr_received = len(self.wr_monitor._recvQ) if hasattr(self.wr_monitor, '_recvQ') else 0
            rd_received = len(self.rd_monitor._recvQ) if hasattr(self.rd_monitor, '_recvQ') else 0
            
            # We need both monitors to have received all packets
            if wr_received >= expected_count and rd_received >= expected_count:
                self.log.debug(f"Packet reception completed for {test_name}: wr={wr_received}, rd={rd_received}")
                return
            
            # Log progress periodically
            if timeout_cycles % (check_interval * 10) == 0:
                self.log.debug(f"Packet reception progress: wr={wr_received}/{expected_count}, rd={rd_received}/{expected_count}, cycles={timeout_cycles}")
            
            await self.wait_clocks(self.wr_clk_name, check_interval)
            timeout_cycles += check_interval
        
        # Timeout occurred
        wr_received = len(self.wr_monitor._recvQ) if hasattr(self.wr_monitor, '_recvQ') else 0
        rd_received = len(self.rd_monitor._recvQ) if hasattr(self.rd_monitor, '_recvQ') else 0
        
        self.log.error(f"❌ Packet reception timeout for {test_name} after {timeout_cycles} cycles")
        self.log.error(f"   Expected: {expected_count}, WR received: {wr_received}, RD received: {rd_received}")
        self.stats['completion_timeouts'] += 1
        
        # Don't raise timeout error, let verification catch the packet count mismatch
        self.log.warning(f"⚠️  Proceeding to verification with incomplete packet reception")

    def _calculate_completion_delay(self, transaction_count):
        """Calculate appropriate completion delay based on transaction count and buffer characteristics"""
        # Base delay for buffer pipeline
        base_delay = self.BASE_COMPLETION_DELAY + self.TEST_DEPTH
        
        # Scale with transaction count (more transactions may need more time)
        scaled_delay = max(10, transaction_count // 10)
        
        # Mode-specific adjustments
        mode_multiplier = {
            'skid': 1.0,
            'fifo_mux': 1.2,    # FIFO may have more pipeline stages
            'fifo_flop': 1.5    # FIFO flop typically has more latency
        }
        
        total_delay = int((base_delay + scaled_delay) * mode_multiplier.get(self.TEST_MODE, 1.0))
        
        self.log.debug(f"Calculated completion delay: {total_delay} cycles (base={base_delay}, scaled={scaled_delay}, mode={self.TEST_MODE})")
        return total_delay

    # [Keep all the existing verification methods - they're good]
    def verify_transactions_strict(self, test_name="Unknown"):
        """ENHANCED STRICT VERIFICATION with detailed error reporting."""
        self.log.info(f"🔍 Starting strict verification for {test_name}")
        
        sent_packets = list(self.wr_monitor._recvQ)
        received_packets = list(self.rd_monitor._recvQ)

        self.stats['total_received'] = len(received_packets)
        self.total_received = len(received_packets)

        # Check packet count first
        if len(sent_packets) != len(received_packets):
            error_msg = f"❌ PACKET COUNT MISMATCH in {test_name}: sent={len(sent_packets)}, received={len(received_packets)}"
            self.log.error(error_msg)
            self.stats['total_errors'] += 1
            self.stats['verification_errors'] += 1
            self.stats['last_error_details'] = error_msg
            self.verification_failures.append(error_msg)
            self.total_errors += 1
            return False

        if len(sent_packets) == 0:
            self.log.warning(f"⚠️ No packets to verify in {test_name}")
            return True

        # Detailed packet-by-packet verification
        total_errors = 0
        for i, (sent, received) in enumerate(zip(sent_packets, received_packets)):
            packet_errors = self._compare_packets_detailed(sent, received, i, test_name)
            if packet_errors > 0:
                total_errors += packet_errors
                self.stats['packet_errors'][i] = packet_errors
                
                # Log first few packet details for debugging
                if total_errors <= 5:  # Only log first 5 errors to avoid spam
                    self._log_packet_details(sent, received, i, test_name)

        # Update statistics
        self.stats['total_errors'] += total_errors
        self.stats['verification_errors'] += total_errors
        self.stats['field_mismatch_errors'] += total_errors
        self.total_errors += total_errors

        # Results summary
        if total_errors == 0:
            self.log.info(f"✅ VERIFICATION PASSED for {test_name}: {len(sent_packets)} packets verified successfully")
            return True
        else:
            error_summary = f"❌ VERIFICATION FAILED for {test_name}: {total_errors} errors in {len(sent_packets)} packets"
            self.log.error(error_summary)
            
            # Log field error breakdown
            self._log_field_error_summary()
            
            self.stats['last_error_details'] = error_summary
            self.verification_failures.append(error_summary)
            
            # In strict mode, any error is a failure
            if self.strict_verification:
                return False
            
            # Otherwise, check against allowed error threshold
            return total_errors <= self.max_allowed_errors

    def _compare_packets_detailed(self, sent, received, packet_index, test_name):
        """Compare two packets with detailed field-by-field analysis."""
        errors = 0
        field_errors = []

        for field_name in ['addr', 'ctrl', 'data0', 'data1']:
            if not hasattr(sent, field_name) or not hasattr(received, field_name):
                continue

            sent_value = getattr(sent, field_name, 0)
            received_value = getattr(received, field_name, 0)

            # Apply field masks for comparison
            field_def = self.field_config.get_field(field_name)
            if field_def:
                field_mask = (1 << field_def.bits) - 1
                sent_value &= field_mask
                received_value &= field_mask

            if sent_value != received_value:
                error_details = {
                    'field': field_name,
                    'sent': sent_value,
                    'received': received_value,
                    'sent_hex': f"0x{sent_value:X}",
                    'received_hex': f"0x{received_value:X}",
                    'packet_index': packet_index,
                    'test_name': test_name
                }
                field_errors.append(error_details)
                
                self.log.error(f"❌ Field {field_name} mismatch in packet {packet_index}: "
                             f"sent=0x{sent_value:X}, received=0x{received_value:X}")
                
                # Track field-specific error counts
                self.field_error_counts[field_name] += 1
                errors += 1

        if errors > 0:
            self.log.error(f"❌ Packet {packet_index} data mismatch: {errors} field errors")

        return errors

    def _log_packet_details(self, sent, received, packet_index, test_name):
        """Log detailed packet information for debugging."""
        self.log.error(f"🔍 PACKET {packet_index} DETAILS for {test_name}:")
        self.log.error(f"  SENT:     {sent.formatted(compact=True) if hasattr(sent, 'formatted') else str(sent)}")
        self.log.error(f"  RECEIVED: {received.formatted(compact=True) if hasattr(received, 'formatted') else str(received)}")

    def _log_field_error_summary(self):
        """Log summary of field-specific errors."""
        self.log.error("🔍 FIELD ERROR BREAKDOWN:")
        for field_name, error_count in self.field_error_counts.items():
            if error_count > 0:
                self.log.error(f"  {field_name}: {error_count} errors")

    # [Keep existing methods for compatibility]
    async def run_sequence(self, sequence_gen=None):
        """Legacy method - redirects to proper completion checking"""
        if sequence_gen is None:
            sequence_gen = self.sequence_gen
        await self.run_sequence_with_completion(sequence_gen, "legacy_run_sequence")

    def verify_transactions(self):
        """Legacy verification method - redirects to strict verification."""
        return self.verify_transactions_strict("legacy_verify")

    def _compare_packets(self, sent, received):
        """Legacy packet comparison - redirects to detailed comparison."""
        errors = self._compare_packets_detailed(sent, received, -1, "legacy_compare")
        return errors == 0

    def get_statistics(self):
        """Get ENHANCED test statistics."""
        enhanced_stats = self.stats.copy()
        enhanced_stats['master_stats'] = self.write_master.get_stats()
        enhanced_stats['slave_stats'] = self.read_slave.get_stats()
        enhanced_stats['wr_monitor_stats'] = self.wr_monitor.get_stats()
        enhanced_stats['rd_monitor_stats'] = self.rd_monitor.get_stats()
        enhanced_stats['input_memory_stats'] = self.input_memory_model.get_stats()
        enhanced_stats['output_memory_stats'] = self.output_memory_model.get_stats()
        enhanced_stats['available_profiles'] = len(self.randomizer_instances)
        enhanced_stats['field_error_counts'] = self.field_error_counts.copy()
        enhanced_stats['verification_failures'] = self.verification_failures.copy()
        return enhanced_stats

    def reset_statistics(self):
        """Reset all statistics including enhanced tracking."""
        self.stats = {
            'total_sent': 0,
            'total_received': 0,
            'total_errors': 0,
            'verification_errors': 0,
            'field_mismatch_errors': 0,
            'sequence_completed': False,
            'test_duration': 0,
            'failed_tests': [],
            'last_error_details': None,
            'packet_errors': {},
            'completion_timeouts': 0,
            'expected_packets': 0
        }

        self.total_sent = 0
        self.total_received = 0
        self.total_errors = 0
        
        # Reset enhanced tracking
        self.verification_failures.clear()
        self.field_error_counts = {
            'addr': 0,
            'ctrl': 0,
            'data0': 0,
            'data1': 0
        }

        if hasattr(self.wr_monitor, '_recvQ'):
            self.wr_monitor._recvQ.clear()
        if hasattr(self.rd_monitor, '_recvQ'):
            self.rd_monitor._recvQ.clear()

    # Keep existing helper methods unchanged

    async def assert_reset(self):
        """Assert reset signals"""
        self.wr_rstn.value = 0
        if self.rd_rstn != self.wr_rstn:
            self.rd_rstn.value = 0

        await self.write_master.reset_bus()
        await self.read_slave.reset_bus()

    async def deassert_reset(self):
        """Deassert reset signals"""
        self.wr_rstn.value = 1
        if self.rd_rstn != self.wr_rstn:
            self.rd_rstn.value = 1

        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    def get_component_statistics(self):
        """Get comprehensive component statistics"""
        return {
            'master': self.write_master.get_stats(),
            'slave': self.read_slave.get_stats(),
            'wr_monitor': self.wr_monitor.get_stats(),
            'rd_monitor': self.rd_monitor.get_stats(),
            'input_memory': self.input_memory_model.get_stats(),
            'output_memory': self.output_memory_model.get_stats(),
            'sequence_gen': self.sequence_gen.get_enhanced_stats() if hasattr(self.sequence_gen, 'get_enhanced_stats') else {},
            'randomizer_profiles': len(self.randomizer_instances),
            'verification_summary': {
                'strict_mode': self.strict_verification,
                'fail_fast': self.fail_fast,
                'total_failures': len(self.verification_failures),
                'field_errors': self.field_error_counts,
                'completion_timeouts': self.stats['completion_timeouts']
            }
        }
