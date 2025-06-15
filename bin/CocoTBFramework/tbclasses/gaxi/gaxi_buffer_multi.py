"""
Updated Testbench for GAXI multi-signal components with FlexConfigGen integration

Updated to use new unified infrastructure while preserving all existing APIs
for test runner compatibility. Now includes comprehensive FlexConfigGen
integration for randomizer profiles.

Key improvements:
- Uses GAXIComponentBase infrastructure for all components
- Leverages unified FieldConfig patterns with proper field width handling
- Integrates FlexConfigGen for comprehensive randomizer configurations
- Uses base MemoryModel directly (no wrapper classes needed)
- Maintains exact same API for test runners
- Added comprehensive sequence generation methods
"""
import os
import random

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.tbclasses.flex_config_gen import FlexConfigGen

from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_seq import GAXIBufferSequence
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_configs import FIELD_CONFIGS
from CocoTBFramework.components.memory_model import MemoryModel


class GaxiMultiBufferTB(TBBase):
    """
    Updated testbench for multi-signal GAXI components using new unified infrastructure with FlexConfigGen.

    Supports gaxi_fifo_sync_multi and gaxi_skid_buffer_multi components.
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
        self.randomizer_configs = self._create_comprehensive_randomizer_configs()

        # Define field configuration using new unified infrastructure
        # Use FieldConfig.validate_and_create for consistent handling
        base_config = FIELD_CONFIGS.get('field', {
            'addr': {'bits': self.AW, 'start_bit': 0},
            'ctrl': {'bits': self.CW, 'start_bit': self.AW},
            'data0': {'bits': self.DW, 'start_bit': self.AW + self.CW},
            'data1': {'bits': self.DW, 'start_bit': self.AW + self.CW + self.DW}
        })

        # Create normalized field configuration
        self.field_config = FieldConfig.validate_and_create(base_config)

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

        # Create BFM components using new infrastructure
        self.write_master = GAXIMaster(
            dut, 'write_master', '', self.wr_clk,
            field_config=self.field_config,
            multi_sig=True,  # Enable multi-signal mode
            mode=self.TEST_MODE,
            timeout_cycles=self.TIMEOUT_CYCLES,
            memory_model=self.input_memory_model,
            log=self.log
        )

        self.read_slave = GAXISlave(
            dut, 'read_slave', '', self.rd_clk,
            mode=self.TEST_MODE,
            field_config=self.field_config,
            multi_sig=True,  # Enable multi-signal mode
            timeout_cycles=self.TIMEOUT_CYCLES,
            memory_model=self.output_memory_model,
            log=self.log
        )

        # Set up monitors using new infrastructure
        self.wr_monitor = GAXIMonitor(
            dut, 'WrMon', '', self.wr_clk,
            field_config=self.field_config,
            multi_sig=True,  # Enable multi-signal mode
            is_slave=False,  # Monitor master side
            mode=self.TEST_MODE,
            log=self.log
        )

        self.rd_monitor = GAXIMonitor(
            dut, 'RdMon', '', self.rd_clk,
            field_config=self.field_config,
            multi_sig=True,  # Enable multi-signal mode
            is_slave=True,  # Monitor slave side
            mode=self.TEST_MODE,
            log=self.log
        )

        # Setup sequence generator with new infrastructure patterns
        self.sequence_gen = GAXIBufferSequence(
            name="multi_buffer_test",
            field_config=self.field_config,
            packet_class=GAXIPacket
        )

        # Statistics tracking - enhanced with new infrastructure patterns
        self.stats = {
            'total_sent': 0,
            'total_received': 0,
            'total_errors': 0,
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

        self.log.info(f"Testbench initialized with mode='{self.TEST_MODE}', depth={self.TEST_DEPTH}")

    def _create_comprehensive_randomizer_configs(self):
        """Create comprehensive randomizer configurations using FlexConfigGen"""

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

        # Create FlexConfigGen for comprehensive buffer testing
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

        # Build all configurations
        randomizer_dict = config_gen.build(return_flexrandomizer=False)

        # Convert to the format expected by the testbench
        converted_configs = {}
        for profile_name, profile_config in randomizer_dict.items():
            converted_configs[profile_name] = {
                'master': {field: constraints for field, constraints in profile_config.items() if 'valid' in field},
                'slave': {field: constraints for field, constraints in profile_config.items() if 'ready' in field}
            }

        self.log.info(f"Created {len(converted_configs)} comprehensive buffer randomizer configurations:")
        for profile_name in converted_configs.keys():
            self.log.info(f"  - {profile_name}")

        return converted_configs

    def get_available_profiles(self):
        """Get list of available randomizer profile names"""
        return list(self.randomizer_configs.keys())

    def set_randomizer_profile(self, profile_name):
        """Set randomizer profile for all components"""
        if profile_name in self.randomizer_configs:
            master_config = self.randomizer_configs[profile_name]['master']
            slave_config = self.randomizer_configs[profile_name]['slave']

            # Set master randomizer
            self.write_master.set_randomizer(FlexRandomizer(master_config))

            # Set slave randomizer
            self.read_slave.set_randomizer(FlexRandomizer(slave_config))

            self.log.info(f"Set randomizers to profile '{profile_name}' - "
                            f"Master: {master_config}, Slave: {slave_config}")
        else:
            self.log.warning(f"Randomizer profile '{profile_name}' not found, using 'balanced'")
            fallback_config = self.randomizer_configs.get('balanced', {
                'master': {'valid_delay': ([(0, 1), (2, 5)], [0.7, 0.3])},
                'slave': {'ready_delay': ([(0, 1), (2, 5)], [0.7, 0.3])}
            })

            self.write_master.set_randomizer(FlexRandomizer(fallback_config['master']))
            self.read_slave.set_randomizer(FlexRandomizer(fallback_config['slave']))

    # Enhanced sequence generation methods

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
        # Add various patterns for comprehensive testing
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

    # API Methods - UNCHANGED for test runner compatibility

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
        Verify received transactions - UNCHANGED API for test runners.
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

        # Data integrity verification
        errors = 0
        for i, (sent, received) in enumerate(zip(sent_packets, received_packets)):
            if not self._compare_packets(sent, received):
                self.log.error(f"Packet {i} data mismatch")
                errors += 1

        self.stats['total_errors'] += errors
        self.stats['verification_errors'] += errors
        self.total_errors += errors  # Update compatibility attribute

        if errors == 0:
            self.log.info(f"✓ Verification passed: {len(sent_packets)} packets verified")
            return True
        else:
            self.log.error(f"✗ Verification failed: {errors} packet mismatches")
            return False

    def _compare_packets(self, sent, received):
        """
        Compare two packets for data integrity - uses new infrastructure.
        """
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
                self.log.error(f"Field {field_name} mismatch: sent=0x{sent_value:X}, received=0x{received_value:X}")
                return False

        return True

    def get_statistics(self):
        """
        Get test statistics - UNCHANGED API for test runners.
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

        return enhanced_stats

    def reset_statistics(self):
        """Reset all statistics - UNCHANGED API for test runners."""
        self.stats = {
            'total_sent': 0,
            'total_received': 0,
            'total_errors': 0,
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
            'sequence_gen': self.sequence_gen.get_enhanced_stats() if hasattr(self.sequence_gen, 'get_enhanced_stats') else {}
        }
