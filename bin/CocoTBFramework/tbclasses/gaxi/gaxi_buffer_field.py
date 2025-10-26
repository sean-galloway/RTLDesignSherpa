# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GaxiFieldBufferTB
# Purpose: Updated Testbench for GAXI field-based components with FlexConfigGen integration
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated Testbench for GAXI field-based components with FlexConfigGen integration

Updated to use new unified infrastructure while preserving all existing APIs
for test runner compatibility. Now includes comprehensive FlexConfigGen
integration for randomizer profiles and all sequence generation methods.

Key improvements:
- Uses GAXIComponentBase infrastructure for all components
- Leverages unified FieldConfig patterns with proper field width handling
- Integrates FlexConfigGen for comprehensive randomizer configurations
- Uses base MemoryModel directly (no wrapper classes needed)
- Enhanced field-based testing with new infrastructure
- Maintains exact same API for test runners
- Added comprehensive sequence generation methods
- Updated to use FlexConfigGen returning FlexRandomizer instances directly
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


class GaxiFieldBufferTB(TBBase):
    """
    Updated testbench for field-based GAXI components using new unified infrastructure with FlexConfigGen.

    Supports gaxi_fifo_sync_field and gaxi_skid_buffer_field components.
    All existing APIs are preserved for test runner compatibility.
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

        # Setup clock and reset signals - UNCHANGED API
        self.wr_clk = wr_clk
        self.wr_clk_name = wr_clk.name
        self.wr_rstn = wr_rstn
        self.rd_clk = self.wr_clk if rd_clk is None else rd_clk
        self.rd_clk_name = self.wr_clk_name if rd_clk is None else rd_clk.name
        self.rd_rstn = self.wr_rstn if rd_rstn is None else rd_rstn

        # Log the test configuration - UNCHANGED API
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
        msg += '='*80 + "\n"
        self.log.info(msg)

        # Create comprehensive randomizer configurations using FlexConfigGen
        self.randomizer_manager = self._create_randomizer_manager()

        # Define field configuration using new unified infrastructure
        # Use FIELD_CONFIGS as base, then create FieldConfig with FieldDefinition
        base_config = FIELD_CONFIGS.get('field', {
            'addr': {'bits': self.AW, 'start_bit': 0},
            'ctrl': {'bits': self.CW, 'start_bit': self.AW},
            'data0': {'bits': self.DW, 'start_bit': self.AW + self.CW},
            'data1': {'bits': self.DW, 'start_bit': self.AW + self.CW + self.DW}
        })

        # Create proper FieldConfig with FieldDefinition objects
        self.field_config = FieldConfig(lsb_first=True)

        # Add fields with proper bit assignments for field-based testing
        self.field_config.add_field(FieldDefinition(
            name='addr',
            bits=self.AW,
            default=0,
            format='hex',
            display_width=((self.AW + 3) // 4),  # Hex digits needed
            active_bits=(self.AW-1, 0),
            description=f'Address field ({self.AW} bits)'
        ))

        self.field_config.add_field(FieldDefinition(
            name='ctrl',
            bits=self.CW,
            default=0,
            format='hex',
            display_width=((self.CW + 3) // 4),  # Hex digits needed
            active_bits=(self.CW-1, 0),
            description=f'Control field ({self.CW} bits)'
        ))

        self.field_config.add_field(FieldDefinition(
            name='data0',
            bits=self.DW,
            default=0,
            format='hex',
            display_width=((self.DW + 3) // 4),  # Hex digits needed
            active_bits=(self.DW-1, 0),
            description=f'Data0 field ({self.DW} bits)'
        ))

        self.field_config.add_field(FieldDefinition(
            name='data1',
            bits=self.DW,
            default=0,
            format='hex',
            display_width=((self.DW + 3) // 4),  # Hex digits needed
            active_bits=(self.DW-1, 0),
            description=f'Data1 field ({self.DW} bits)'
        ))

        self.log.debug(f"Field Configuration:\n{self.field_config}")

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

        # Create BFM components using new infrastructure
        self.write_master = GAXIMaster(
            dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            multi_sig=False,
            mode=self.TEST_MODE,
            timeout_cycles=self.TIMEOUT_CYCLES,
            memory_model=self.input_memory_model,
            log=self.log
        )

        self.read_slave = GAXISlave(
            dut, 'read_slave', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            multi_sig=False,
            timeout_cycles=self.TIMEOUT_CYCLES,
            memory_model=self.output_memory_model,
            log=self.log
        )

        # Set up monitors using new infrastructure
        self.wr_monitor = GAXIMonitor(
            dut, 'WrMon', '', self.wr_clk,
            field_config=self.field_config,
            multi_sig=False,
            is_slave=False,  # Monitor master side
            mode=self.TEST_MODE,
            log=self.log
        )

        self.rd_monitor = GAXIMonitor(
            dut, 'RdMon', '', self.rd_clk,
            field_config=self.field_config,
            multi_sig=False,
            is_slave=True,  # Monitor slave side
            mode=self.TEST_MODE,
            log=self.log
        )

        self.log.info(f"🔍 DEBUG: About to create GAXIBufferSequence (mode={self.TEST_MODE})")
        self.log.info(f"🔍 DEBUG: field_config type: {type(self.field_config)}")
        self.log.info(f"🔍 DEBUG: field_config: {self.field_config}")

        try:
            self.log.info(f"🔍 DEBUG: Calling GAXIBufferSequence.__init__...")
            self.sequence_gen = GAXIBufferSequence(
                name="field_buffer_test",
                field_config=self.field_config,
                packet_class=GAXIPacket,
            )
            self.log.info(f"🔍 DEBUG: ✅ GAXIBufferSequence created successfully!")
            
        except Exception as e:
            self.log.error(f"🚨 ERROR: GAXIBufferSequence creation failed: {e}")
            import traceback
            self.log.error(f"🚨 ERROR: Traceback:\n{traceback.format_exc()}")
            raise

        self.log.info(f"🔍 DEBUG: About to setup statistics...")

        # Statistics tracking - enhanced with field-specific and new infrastructure patterns
        self.stats = {
            'total_sent': 0,
            'total_received': 0,
            'total_errors': 0,
            'field_errors': {'addr': 0, 'ctrl': 0, 'data0': 0, 'data1': 0},
            'boundary_tests': 0,
            'field_combinations_tested': 0,
            'sequence_completed': False,
            'test_duration': 0,
            'verification_errors': 0
        }

        # Compatibility attributes for existing test runners
        # These are simple attributes that mirror the stats for backward compatibility
        self.total_sent = 0
        self.total_received = 0
        self.total_errors = 0

        # Set default randomizer profile
        self.set_randomizer_profile('balanced')

        self.log.info(f"Field testbench initialized with mode='{self.TEST_MODE}', depth={self.TEST_DEPTH}")

    def _create_randomizer_manager(self):
        """Create FlexConfigGen manager that returns FlexRandomizer instances directly"""

        # Define GAXI field-specific profiles
        gaxi_field_profiles = {
            # Field-specific patterns optimized for field-level testing
            'field_intensive': ([(0, 0), (1, 2)], [6, 1]),                     # Field intensive testing
            'field_boundary': ([(0, 1), (2, 5)], [4, 1]),                      # Field boundary testing
            'field_stress': ([(0, 0), (3, 8)], [3, 1]),                        # Field stress testing
            'field_coordinated': ([(1, 2), (3, 6)], [5, 2]),                   # Coordinated field timing
            'field_alternating': ([(0, 1), (4, 7)], [4, 2]),                   # Alternating field patterns
            'field_comprehensive': ([(0, 2), (3, 6), (10, 15)], [6, 3, 1]),    # Comprehensive field testing
        }

        # Create FlexConfigGen for comprehensive field testing - NOTE: return_flexrandomizer=True
        config_gen = FlexConfigGen(
            profiles=[
                # Standard canned profiles
                'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
                'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
                'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
                'slow_consumer', 'slow_producer', 'burst_pause', 'fixed',
                # Field-specific profiles
                'field_intensive', 'field_boundary', 'field_stress',
                'field_coordinated', 'field_alternating', 'field_comprehensive'
            ],
            fields=['valid_delay', 'ready_delay'],
            custom_profiles=gaxi_field_profiles
        )

        # Customize profiles for field-specific behavior
        self._customize_profiles(config_gen)

        # Build configurations and get FlexRandomizer instances directly
        self.randomizer_instances = config_gen.build(return_flexrandomizer=True)

        # Create write/read domain mapping for easier access
        self.domain_randomizers = {}
        for profile_name, randomizer in self.randomizer_instances.items():
            self.domain_randomizers[profile_name] = {
                'write': randomizer,  # Write domain gets the randomizer
                'read': randomizer    # Read domain gets the same randomizer
            }

        self.log.info(f"Created {len(self.randomizer_instances)} FlexRandomizer instances via FlexConfigGen:")
        for profile_name in self.randomizer_instances.keys():
            self.log.info(f"  - {profile_name}")

        return config_gen

    def _customize_profiles(self, config_gen):
        """Customize FlexConfigGen profiles for field-specific behavior"""

        # Ultra-aggressive for maximum field throughput
        config_gen.backtoback.valid_delay.fixed_value(0)
        config_gen.backtoback.ready_delay.fixed_value(0)

        # Fixed delays for predictable field testing
        config_gen.fixed.valid_delay.fixed_value(0)
        config_gen.fixed.ready_delay.fixed_value(0)

        # Fast patterns optimized for field testing
        config_gen.fast.valid_delay.mostly_zero(zero_weight=60, fallback_range=(1, 2), fallback_weight=1)
        config_gen.fast.ready_delay.mostly_zero(zero_weight=55, fallback_range=(1, 3), fallback_weight=2)

        # Stress test with field variations
        config_gen.stress.valid_delay.weighted_ranges([
            ((0, 0), 12), ((1, 3), 6), ((4, 8), 2), ((12, 16), 1)
        ])
        config_gen.stress.ready_delay.weighted_ranges([
            ((0, 1), 10), ((2, 5), 5), ((6, 10), 2), ((15, 20), 1)
        ])

        # Field intensive testing
        config_gen.field_intensive.valid_delay.mostly_zero(zero_weight=85, fallback_range=(1, 2), fallback_weight=1)
        config_gen.field_intensive.ready_delay.mostly_zero(zero_weight=80, fallback_range=(1, 2), fallback_weight=1)

        # Field boundary testing
        config_gen.field_boundary.valid_delay.uniform_range(0, 2)
        config_gen.field_boundary.ready_delay.uniform_range(1, 4)

        # Field stress testing
        config_gen.field_stress.valid_delay.mostly_zero(zero_weight=25, fallback_range=(1, 3), fallback_weight=1)
        config_gen.field_stress.ready_delay.weighted_ranges([((0, 0), 2), ((3, 8), 1)])

        # Slow consumer pattern for field overflow testing
        config_gen.slow_consumer.valid_delay.mostly_zero(zero_weight=75, fallback_range=(1, 2), fallback_weight=1)
        config_gen.slow_consumer.ready_delay.weighted_ranges([((0, 1), 3), ((6, 12), 1)])

        # Slow producer pattern
        config_gen.slow_producer.valid_delay.weighted_ranges([((0, 1), 3), ((5, 10), 1)])
        config_gen.slow_producer.ready_delay.mostly_zero(zero_weight=75, fallback_range=(1, 2), fallback_weight=1)

        # Burst pause for field depth testing
        config_gen.burst_pause.valid_delay.burst_pattern(fast_cycles=0, pause_range=(self.TEST_DEPTH, self.TEST_DEPTH*2), burst_ratio=25)
        config_gen.burst_pause.ready_delay.burst_pattern(fast_cycles=0, pause_range=(self.TEST_DEPTH//2, self.TEST_DEPTH), burst_ratio=20)

    def get_randomizer(self, profile_name, domain='write'):
        """Get FlexRandomizer instance for specified profile and domain"""
        if profile_name in self.domain_randomizers:
            return self.domain_randomizers[profile_name][domain]
        else:
            # Fallback to balanced profile
            self.log.warning(f"Profile '{profile_name}' not found, using 'balanced'")
            return self.domain_randomizers['balanced'][domain]

    def set_randomizer_profile(self, profile_name):
        """Set randomizer profile for write and read components"""
        self.log.info(f"🔍 STEP 1: Starting set_randomizer_profile('{profile_name}') for mode={self.TEST_MODE}")

        self.log.info(f"🔍 STEP 2: Getting write randomizer...")
        write_randomizer = self.get_randomizer(profile_name, 'write')
        self.log.info(f"🔍 STEP 2: Got write randomizer: {type(write_randomizer)}")

        self.log.info(f"🔍 STEP 3: Getting read randomizer...")
        read_randomizer = self.get_randomizer(profile_name, 'read')
        self.log.info(f"🔍 STEP 3: Got read randomizer: {type(read_randomizer)}")

        # Apply randomizers to components
        self.log.info(f"🔍 STEP 4: About to call write_master.set_randomizer() (mode={self.TEST_MODE})")
        self.write_master.set_randomizer(write_randomizer)
        self.log.info(f"🔍 STEP 4: ✅ write_master.set_randomizer() completed successfully")

        self.log.info(f"🔍 STEP 5: About to call read_slave.set_randomizer() (mode={self.TEST_MODE})")
        self.read_slave.set_randomizer(read_randomizer)
        self.log.info(f"🔍 STEP 5: ✅ read_slave.set_randomizer() completed successfully")

        self.log.info(f"🔍 STEP 6: All randomizer setup completed successfully for mode={self.TEST_MODE}")
        self.log.info(f"Set randomizers to profile '{profile_name}' for write/read domains")

        def get_randomizer_config_names(self):
            """Get list of available randomizer configuration names"""
            return list(self.randomizer_instances.keys())

        def get_available_profiles(self):
            """Get list of available profiles (alias for compatibility)"""
            return self.get_randomizer_config_names()

    # Enhanced sequence generation methods - same as multi buffer but field-focused

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
        # Add various patterns for comprehensive field testing
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

    # API Methods - ENHANCED for field testing but maintaining compatibility

    def create_field_sequence(self, sequence_type='basic', count=100):
        """
        Create field-specific test sequence - ENHANCED API for field testing.

        Args:
            sequence_type: Type of sequence to generate
            count: Number of transactions

        Returns:
            Generated sequence
        """
        self.sequence_gen.clear()  # Reset sequence

        if sequence_type == 'incrementing':
            self.sequence_gen.add_incrementing_pattern(count)
        elif sequence_type == 'random':
            self.sequence_gen.add_random_pattern(count)
        elif sequence_type == 'boundary':
            self.sequence_gen.add_boundary_values()
            self.sequence_gen.add_random_pattern(count - 20)  # Fill remaining
            self.stats['boundary_tests'] += 1
        elif sequence_type == 'field_stress':
            # Comprehensive field testing
            self.sequence_gen.add_boundary_values()
            self.sequence_gen.add_overflow_test()
            self.sequence_gen.add_max_value_pattern()
            self.sequence_gen.add_alternating_patterns(20)
            self.sequence_gen.add_random_pattern(count - 50)  # Fill remaining
            self.stats['boundary_tests'] += 1
            self.stats['field_combinations_tested'] += 1
        elif sequence_type == 'field_combinations':
            # Test all field combinations
            self.sequence_gen.add_max_value_pattern()
            self.sequence_gen.add_alternating_patterns(count // 4)
            self.sequence_gen.add_boundary_values()
            self.sequence_gen.add_random_pattern(count // 2)
            self.stats['field_combinations_tested'] += 1
        else:  # basic
            self.sequence_gen.add_incrementing_pattern(count // 2)
            self.sequence_gen.add_random_pattern(count // 2)

        return self.sequence_gen

    # Backward compatibility - delegate to new method
    def create_sequence(self, sequence_type='basic', count=100):
        """
        Create test sequence - UNCHANGED API for test runners.

        Args:
            sequence_type: Type of sequence to generate
            count: Number of transactions

        Returns:
            Generated sequence
        """
        return self.create_field_sequence(sequence_type, count)

    async def simple_incremental_loops(self, count=100, delay_key='fixed', delay_clks_after=10):
        """
        Legacy simple incremental test - UNCHANGED API for test runners.
        """
        self.log.info(f"Running simple incremental loops with count={count}, delay_key='{delay_key}'")

        # Set randomizer profile
        self.set_randomizer_profile(delay_key)

        # Reset statistics
        self.reset_statistics()

        # Generate simple incrementing sequence
        sequence = self.basic_sequence(count)

        # Run the sequence
        await self.run_sequence(sequence)

        # Wait for completion
        await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Verify results
        result = self.verify_transactions()

        if result:
            self.log.info(f"✓ Simple incremental loops completed successfully")
        else:
            self.log.error(f"✗ Simple incremental loops failed verification")

        return result

    async def run_sequence_test(self, sequence_generator, delay_key='balanced', delay_clks_after=20):
        """
        Run sequence test with specified generator - UNCHANGED API for test runners.
        """
        # Set randomizer profile
        self.set_randomizer_profile(delay_key)

        # Reset statistics
        self.reset_statistics()

        # Get the sequence (generator is a callable that returns sequence)
        if callable(sequence_generator):
            sequence = sequence_generator()
        else:
            sequence = sequence_generator

        # Run the sequence
        await self.run_sequence(sequence)

        # Wait for completion
        await self.wait_clocks(self.wr_clk_name, delay_clks_after)

        # Verify results
        result = self.verify_transactions()

        return result

    async def run_sequence(self, sequence_gen=None):
        """
        Run test sequence - UNCHANGED API for test runners.
        """
        if sequence_gen is None:
            sequence_gen = self.sequence_gen

        # Execute sequence using new infrastructure's unified methods
        transactions = sequence_gen.get_transactions()

        self.log.info(f"Running sequence with {len(transactions)} transactions")

        for i, transaction_data in enumerate(transactions):
            # Create packet with proper field values
            packet = GAXIPacket(self.field_config)

            # Handle different transaction data formats
            if isinstance(transaction_data, tuple) and len(transaction_data) >= 1:
                field_values = transaction_data[0]  # First element is field values
                delay = transaction_data[1] if len(transaction_data) > 1 else 0
            elif isinstance(transaction_data, dict):
                field_values = transaction_data
                delay = 0
            else:
                self.log.error(f"Invalid transaction data format: {transaction_data}")
                continue

            # Set field values from transaction data
            for field_name, value in field_values.items():
                if hasattr(packet, field_name):
                    setattr(packet, field_name, value)

            # Send transaction using new infrastructure
            await self.write_master.send(packet)
            self.stats['total_sent'] += 1
            self.total_sent += 1  # Update compatibility attribute

            # Handle delay
            if delay > 0:
                await self.wait_clocks(self.wr_clk_name, delay)

            # Log progress periodically
            if (i + 1) % 50 == 0:
                self.log.debug(f"Sent {i+1}/{len(transactions)} transactions")

        self.log.info(f"Completed sending {len(transactions)} transactions")

    def verify_transactions(self):
        """
        Verify received transactions with enhanced field verification - ENHANCED API.
        """
        # Get received packets using new infrastructure
        sent_packets = list(self.wr_monitor._recvQ)
        received_packets = list(self.rd_monitor._recvQ)

        self.stats['total_received'] = len(received_packets)
        self.total_received = len(received_packets)  # Update compatibility attribute

        # Basic count verification
        if len(sent_packets) != len(received_packets):
            self.log.error(f"Packet count mismatch: sent={len(sent_packets)}, received={len(received_packets)}")
            self.stats['total_errors'] += 1
            self.stats['verification_errors'] += 1
            self.total_errors += 1  # Update compatibility attribute
            return False

        # Enhanced field-by-field verification
        errors = 0
        for i, (sent, received) in enumerate(zip(sent_packets, received_packets)):
            field_errors = self._compare_packets_detailed(sent, received, i)
            if field_errors:
                errors += len(field_errors)

        self.stats['total_errors'] += errors
        self.stats['verification_errors'] += errors
        self.total_errors += errors  # Update compatibility attribute

        if errors == 0:
            self.log.info(f"✓ Verification passed: {len(sent_packets)} packets verified")
            return True
        else:
            self.log.error(f"✗ Verification failed: {errors} field mismatches")
            return False

    def _compare_packets_detailed(self, sent, received, packet_index):
        """
        Compare two packets with detailed field-level error reporting.

        Args:
            sent: Sent packet
            received: Received packet
            packet_index: Index of packet being compared

        Returns:
            List of field errors found
        """
        field_errors = []

        # Use field configuration to compare relevant fields
        for field_name in ['addr', 'ctrl', 'data0', 'data1']:
            if not hasattr(sent, field_name) or not hasattr(received, field_name):
                continue

            sent_value = getattr(sent, field_name, 0)
            received_value = getattr(received, field_name, 0)

            # Apply field mask using new infrastructure patterns
            field_def = self.field_config.get_field(field_name)
            if field_def:
                field_mask = (1 << field_def.bits) - 1
                sent_value &= field_mask
                received_value &= field_mask

            if sent_value != received_value:
                error_msg = (f"Packet {packet_index}, Field {field_name} mismatch: "
                           f"sent=0x{sent_value:X}, received=0x{received_value:X}")
                self.log.error(error_msg)
                field_errors.append(field_name)
                self.stats['field_errors'][field_name] += 1

        return field_errors

    def _compare_packets(self, sent, received):
        """
        Compare two packets for data integrity - uses new infrastructure.

        Args:
            sent: Sent packet
            received: Received packet

        Returns:
            True if packets match, False otherwise
        """
        return len(self._compare_packets_detailed(sent, received, -1)) == 0

    def verify_field_integrity(self):
        """
        Verify field-level data integrity - NEW method for field testing.

        Returns:
            Dictionary containing field-specific verification results
        """
        field_results = {}

        # Get packets using new infrastructure
        sent_packets = list(self.wr_monitor._recvQ)
        received_packets = list(self.rd_monitor._recvQ)

        if len(sent_packets) != len(received_packets):
            field_results['count_mismatch'] = True
            return field_results

        field_results['count_mismatch'] = False
        field_results['field_errors'] = {}

        # Check each field individually
        for field_name in ['addr', 'ctrl', 'data0', 'data1']:
            field_errors = 0
            field_def = self.field_config.get_field(field_name)
            field_mask = (1 << field_def.bits) - 1 if field_def else 0xFFFFFFFF

            for sent, received in zip(sent_packets, received_packets):
                sent_value = getattr(sent, field_name, 0) & field_mask
                received_value = getattr(received, field_name, 0) & field_mask

                if sent_value != received_value:
                    field_errors += 1

            field_results['field_errors'][field_name] = field_errors

        return field_results

    def get_statistics(self):
        """
        Get test statistics - ENHANCED with field-specific stats.
        """
        # Enhance with new infrastructure stats
        enhanced_stats = self.stats.copy()

        # Add component statistics using new infrastructure
        enhanced_stats['master_stats'] = self.write_master.get_stats()
        enhanced_stats['slave_stats'] = self.read_slave.get_stats()
        enhanced_stats['wr_monitor_stats'] = self.wr_monitor.get_stats()
        enhanced_stats['rd_monitor_stats'] = self.rd_monitor.get_stats()

        # Add memory model stats
        enhanced_stats['input_memory_stats'] = self.input_memory_model.get_stats()
        enhanced_stats['output_memory_stats'] = self.output_memory_model.get_stats()

        # Add field configuration details
        enhanced_stats['field_config'] = {
            'field_names': ['addr', 'ctrl', 'data0', 'data1'],
            'field_widths': {
                'addr': self.AW,
                'ctrl': self.CW,
                'data0': self.DW,
                'data1': self.DW
            },
            'total_width': self.AW + self.CW + self.DW + self.DW
        }

        # Add error analysis
        total_field_errors = sum(self.stats['field_errors'].values())
        if total_field_errors > 0:
            enhanced_stats['error_analysis'] = {
                'total_field_errors': total_field_errors,
                'error_rate_by_field': {
                    field: (errors / self.stats['total_sent'] if self.stats['total_sent'] > 0 else 0)
                    for field, errors in self.stats['field_errors'].items()
                }
            }

        return enhanced_stats

    def reset_statistics(self):
        """Reset all statistics - ENHANCED for field testing."""
        self.stats = {
            'total_sent': 0,
            'total_received': 0,
            'total_errors': 0,
            'field_errors': {'addr': 0, 'ctrl': 0, 'data0': 0, 'data1': 0},
            'boundary_tests': 0,
            'field_combinations_tested': 0,
            'sequence_completed': False,
            'test_duration': 0,
            'verification_errors': 0
        }

        # Reset compatibility attributes
        self.total_sent = 0
        self.total_received = 0
        self.total_errors = 0

        # Clear monitor queues using new infrastructure
        if hasattr(self.wr_monitor, '_recvQ'):
            self.wr_monitor._recvQ.clear()
        if hasattr(self.rd_monitor, '_recvQ'):
            self.rd_monitor._recvQ.clear()

    def get_field_error_summary(self):
        """
        Get summary of field-specific errors - NEW method.

        Returns:
            Dictionary of field error analysis
        """
        total_errors = sum(self.stats['field_errors'].values())
        total_transactions = self.stats['total_sent']

        summary = {
            'total_field_errors': total_errors,
            'total_transactions': total_transactions,
            'overall_error_rate': total_errors / total_transactions if total_transactions > 0 else 0,
            'field_breakdown': {}
        }

        field_widths = {'addr': self.AW, 'ctrl': self.CW, 'data0': self.DW, 'data1': self.DW}

        for field_name, error_count in self.stats['field_errors'].items():
            summary['field_breakdown'][field_name] = {
                'errors': error_count,
                'error_rate': error_count / total_transactions if total_transactions > 0 else 0,
                'field_width': field_widths.get(field_name, 0)
            }

        return summary

    # Additional helper methods

    async def assert_reset(self):
        """Assert reset signals"""
        self.wr_rstn.value = 0
        if self.rd_rstn != self.wr_rstn:
            self.rd_rstn.value = 0

        # Reset all components
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
            'field_error_summary': self.get_field_error_summary()
        }
