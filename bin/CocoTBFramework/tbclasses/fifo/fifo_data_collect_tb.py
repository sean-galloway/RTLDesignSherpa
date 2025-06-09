"""
Enhanced testbench for data_collect module using modern framework with FlexConfigGen
"""
import os
import logging
import random
import time
import cocotb
from collections import deque

from CocoTBFramework.tbclasses.tbbase import TBBase
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition
from CocoTBFramework.components.fifo.fifo_packet import FIFOPacket
from CocoTBFramework.components.fifo.fifo_master import FIFOMaster
from CocoTBFramework.components.fifo.fifo_slave import FIFOSlave
from CocoTBFramework.components.fifo.fifo_monitor import FIFOMonitor
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.tbclasses.flex_config_gen import FlexConfigGen
from CocoTBFramework.components.arbiter_monitor import WeightedRoundRobinArbiterMonitor


class DataCollectScoreboard:
    """
    Specialized scoreboard for data_collect module with enhanced field validation and error detection.
    Updated to use modern framework components.
    """
    def __init__(self, title, input_field_config, output_field_config, log=None):
        """Initialize the scoreboard"""
        self.title = title

        # Convert to FieldConfig if received as dictionaries
        if isinstance(input_field_config, dict):
            self.input_field_config = FieldConfig.validate_and_create(input_field_config)
        else:
            self.input_field_config = input_field_config

        if isinstance(output_field_config, dict):
            self.output_field_config = FieldConfig.validate_and_create(output_field_config)
        else:
            self.output_field_config = output_field_config

        # Create a logger if not provided
        if log is None:
            self.log = logging.getLogger(f"{title}")
            self.log.setLevel(logging.INFO)
        else:
            self.log = log

        # Channel configuration using loops for maintainability
        self.channels = ['A', 'B', 'C', 'D']
        self.channel_ids = {
            'A': [0xAA, 0xA],
            'B': [0xBB, 0xB], 
            'C': [0xCC, 0xC],
            'D': [0xDD, 0xD]
        }
        self.channel_id_map = {
            # Forward mapping: ID -> Channel
            0xAA: 'A', 0xA: 'A',
            0xBB: 'B', 0xB: 'B',
            0xCC: 'C', 0xC: 'C',
            0xDD: 'D', 0xD: 'D'
        }

        # Initialize queues using loops
        self.input_queues = {}
        self.combined_queues = {}
        for channel in self.channels:
            self.input_queues[channel] = deque()      # Raw input packets
            self.combined_queues[channel] = deque()   # Combined packets (groups of 4)

        # Queue for actual output packets
        self.actual_queue = deque()

        # Create field mask cache for improved performance
        self._field_masks = {}

        # Error tracking
        self.error_count = 0
        self.comparison_count = 0
        self.field_error_counts = {}

        # Statistics
        self.stats = {
            'packets_processed': 0,
            'groups_created': 0,
            'field_errors': 0
        }

        # Arbiter-related tracking
        self.arbiter_stats = {
            'channel_selections': {channel: 0 for channel in self.channels},
            'weight_compliance_errors': 0,
            'fairness_violations': 0
        }

    def add_arbiter_transaction(self, transaction, expected_weights=None):
        """Add an arbiter transaction for analysis"""
        if transaction.gnt_id < len(self.channels):  # Valid client ID
            channel = self.channels[transaction.gnt_id]
            self.arbiter_stats['channel_selections'][channel] += 1

            self.log.debug(f"Arbiter granted channel {channel} (ID {transaction.gnt_id}) "
                            f"after {transaction.cycle_count} cycles")

    def verify_arbiter_weights(self, expected_weights, tolerance=0.2):
        """Verify that the arbiter is respecting the configured weights"""
        total_selections = sum(self.arbiter_stats['channel_selections'].values())
        if total_selections < 20:  # Need sufficient data
            self.log.warning("Insufficient arbiter transactions for weight verification")
            return True

        total_weight = sum(expected_weights)
        if total_weight == 0:
            return True  # All weights zero, can't verify

        weight_errors = 0

        for i, channel in enumerate(self.channels):
            expected_ratio = expected_weights[i] / total_weight
            actual_selections = self.arbiter_stats['channel_selections'][channel]
            actual_ratio = actual_selections / total_selections

            deviation = abs(expected_ratio - actual_ratio)

            self.log.info(f"Channel {channel}: Expected {expected_ratio:.2%}, "
                            f"Actual {actual_ratio:.2%}, Deviation {deviation:.2%}")

            if expected_ratio > 0 and deviation > tolerance:
                weight_errors += 1
                self.arbiter_stats['weight_compliance_errors'] += 1
                self.log.error(f"Weight compliance error for channel {channel}: "
                                f"deviation {deviation:.2%} exceeds tolerance {tolerance:.2%}")

        return weight_errors == 0

    def clear(self):
        """Clear all queues and reset counters"""
        for channel in self.channels:
            self.input_queues[channel].clear()
            self.combined_queues[channel].clear()

        self.actual_queue.clear()
        self.error_count = 0
        self.comparison_count = 0
        self.field_error_counts = {}

        # Reset statistics
        for key in self.stats:
            self.stats[key] = 0

        # Reset arbiter stats using loops
        for channel in self.channels:
            self.arbiter_stats['channel_selections'][channel] = 0
        self.arbiter_stats['weight_compliance_errors'] = 0
        self.arbiter_stats['fairness_violations'] = 0

    def _get_field_mask(self, field_name, field_config):
        """Get a mask for a field based on its bit width with caching."""
        if field_name in self._field_masks:
            return self._field_masks[field_name]

        # Calculate mask based on field width
        if hasattr(field_config, 'get_field'):
            field_def = field_config.get_field(field_name)
            if field_def:
                bits = field_def.bits
                mask = (1 << bits) - 1
                self._field_masks[field_name] = mask
                return mask

        # Default to all ones if field width can't be determined
        return 0xFFFFFFFF

    def add_input_packet(self, packet):
        """Add an input packet to the appropriate queue based on ID"""
        self.stats['packets_processed'] += 1

        # Determine which queue to add to based on ID
        packet_id = packet.id if hasattr(packet, 'id') else None
        channel = self.channel_id_map.get(packet_id)

        if channel is None:
            self.log.warning(f"Received packet with unknown ID: 0x{packet_id:X}")
            return

        # Add packet to the appropriate input queue
        self.input_queues[channel].append(packet)

        # Check if we have 4 packets to combine
        if len(self.input_queues[channel]) >= 4:
            self._combine_packets(channel)

    def _combine_packets(self, channel):
        """Combine 4 packets from a channel into a single output packet with field validation"""
        if channel not in self.channels:
            self.log.error(f"Unknown channel: {channel}")
            return

        input_queue = self.input_queues[channel]
        combined_queue = self.combined_queues[channel]

        # Get the primary ID for this channel (first ID in the list)
        id_value = self.channel_ids[channel][0]

        # Ensure we have at least 4 packets
        if len(input_queue) < 4:
            return

        # Take 4 packets from the queue
        packets = [input_queue.popleft() for _ in range(4)]

        # Get data values from each packet
        data_values = []
        for pkt in packets:
            data = pkt.data if hasattr(pkt, 'data') else 0
            data_values.append(data)

        # Get mask for data field
        data_mask = self._get_field_mask('data', self.input_field_config)

        # Mask values to ensure they're within field width
        data_values = [data & data_mask for data in data_values]

        # Create a combined output packet
        output_pkt = FIFOPacket(self.output_field_config)
        output_pkt.id = id_value

        # Set data fields using loop
        for i, data_value in enumerate(data_values):
            setattr(output_pkt, f'data{i}', data_value)

        # Add to the combined queue
        combined_queue.append(output_pkt)

        # Update statistics
        self.stats['groups_created'] += 1

        self.log.debug(f"Combined 4 packets from channel {channel} into output packet with ID=0x{id_value:X}")

    def add_output_packet(self, packet):
        """Add an output packet from the E monitor"""
        self.actual_queue.append(packet)
        # Perform comparison immediately
        self._check_next_packet()

    def _check_next_packet(self):
        """Check the next output packet against expected data with enhanced field validation"""
        if not self.actual_queue:
            return

        # Get the next output packet
        actual = self.actual_queue.popleft()

        # Get the ID from the packet
        actual_id = actual.id if hasattr(actual, 'id') else None
        channel = self.channel_id_map.get(actual_id)

        if channel is None:
            self.log.error(f"Output packet has unknown ID: 0x{actual_id:X}")
            self.error_count += 1
            return

        # Get the appropriate combined queue
        expected_queue = self.combined_queues[channel]

        # Check if we have an expected packet
        if not expected_queue:
            self.log.error(f"No expected packets for channel {channel} (ID=0x{actual_id:X})")
            self.error_count += 1
            return

        # Get expected packet and compare
        expected = expected_queue.popleft()
        self.comparison_count += 1

        # Get data values using loops
        expected_data = []
        actual_data = []

        for i in range(4):  # 4 data fields: data0, data1, data2, data3
            field_name = f'data{i}'
            expected_value = getattr(expected, field_name, 0)
            actual_value = getattr(actual, field_name, 0)
            expected_data.append(expected_value)
            actual_data.append(actual_value)

        # Get mask for data fields
        data_mask = self._get_field_mask('data0', self.output_field_config)

        # Compare packets using loop
        errors = []
        for i in range(4):
            field_name = f'data{i}'
            expected_value = expected_data[i]
            actual_value = actual_data[i]

            if (actual_value & data_mask) != (expected_value & data_mask):
                errors.append(f"{field_name}: expected=0x{expected_value:X}, actual=0x{actual_value:X}")
                self._increment_field_error(field_name)

        if errors:
            self.log.error(f"Packet mismatch for channel {channel} (ID=0x{actual_id:X}):")
            for error in errors:
                self.log.error(f"  {error}")
            self.error_count += 1
        else:
            self.log.debug(f"Packet match for channel {channel} (ID=0x{actual_id:X})")

    def _increment_field_error(self, field_name):
        """Increment error counter for a specific field"""
        if field_name not in self.field_error_counts:
            self.field_error_counts[field_name] = 0
        self.field_error_counts[field_name] += 1
        self.stats['field_errors'] += 1

    def check_remaining_data(self):
        """Check if any queues have leftover data"""
        errors = 0

        # Check input and combined queues using loops
        for channel in self.channels:
            input_queue = self.input_queues[channel]
            combined_queue = self.combined_queues[channel]

            if input_queue:
                self.log.error(f"Channel {channel} has {len(input_queue)} leftover input packets")
                errors += 1

            if combined_queue:
                self.log.error(f"Channel {channel} has {len(combined_queue)} leftover combined packets")
                errors += 1

        # Check output queue
        if self.actual_queue:
            self.log.error(f"Output queue has {len(self.actual_queue)} leftover packets")
            errors += 1

        return errors

    def get_statistics(self):
        """Get statistics about packet processing and errors"""
        stats = self.stats.copy()
        stats['comparisons'] = self.comparison_count
        stats['errors'] = self.error_count
        stats['field_error_details'] = self.field_error_counts.copy()
        stats['arbiter_stats'] = self.arbiter_stats.copy()

        # Add per-channel queue statistics
        stats['queue_status'] = {}
        for channel in self.channels:
            stats['queue_status'][channel] = {
                'input_packets': len(self.input_queues[channel]),
                'combined_packets': len(self.combined_queues[channel])
            }
        stats['queue_status']['actual_output'] = len(self.actual_queue)

        return stats

    def report(self):
        """Generate a report and return the number of errors"""
        # Check for any leftover data
        leftover_errors = self.check_remaining_data()
        total_errors = self.error_count + leftover_errors + self.arbiter_stats['weight_compliance_errors']

        # Log summary
        self.log.info(f"Scoreboard report for {self.title}:")
        self.log.info(f"  Packets compared: {self.comparison_count}")
        self.log.info(f"  Data mismatches: {self.error_count}")
        self.log.info(f"  Leftover data errors: {leftover_errors}")
        self.log.info(f"  Arbiter weight errors: {self.arbiter_stats['weight_compliance_errors']}")
        self.log.info(f"  Total errors: {total_errors}")

        # Log arbiter statistics using loop
        self.log.info("  Arbiter Channel Selections:")
        for channel in self.channels:
            count = self.arbiter_stats['channel_selections'][channel]
            self.log.info(f"    Channel {channel}: {count}")

        # Log field-specific error details if any
        if self.field_error_counts:
            self.log.info("  Field error details:")
            for field, count in self.field_error_counts.items():
                self.log.info(f"    {field}: {count} errors")

        # Log per-channel queue status
        self.log.info("  Queue Status:")
        for channel in self.channels:
            input_count = len(self.input_queues[channel])
            combined_count = len(self.combined_queues[channel])
            self.log.info(f"    Channel {channel}: {input_count} input, {combined_count} combined")

        if total_errors == 0:
            self.log.info("  TEST PASSED: All packets verified successfully")
        else:
            self.log.error(f"  TEST FAILED: {total_errors} errors detected")

        return total_errors


class DataCollectTB(TBBase):
    """
    Enhanced testbench for the data_collect module using modern framework with FlexConfigGen.
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('DATA_WIDTH', '8'))
        self.ID_WIDTH = self.convert_to_int(os.environ.get('ID_WIDTH', '4'))
        self.OUTPUT_FIFO_DEPTH = self.convert_to_int(os.environ.get('OUTPUT_FIFO_DEPTH', '16'))
        self.CHUNKS = self.convert_to_int(os.environ.get('CHUNKS', '4'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))

        # Initialize random generator
        random.seed(self.SEED)

        # Clock and reset signals
        self.clock = self.dut.i_clk
        self.reset_n = self.dut.i_rst_n
        self.super_debug = True

        # Channel configuration
        self.channels = ['a', 'b', 'c', 'd']
        self.channel_names = ['A', 'B', 'C', 'D']
        self.channel_ids = [0xAA, 0xBB, 0xCC, 0xDD]

        # Log configuration
        self.log.info(f"Data Collect TB initialized with DATA_WIDTH={self.DATA_WIDTH}, ID_WIDTH={self.ID_WIDTH}")
        self.log.info(f"OUTPUT_FIFO_DEPTH={self.OUTPUT_FIFO_DEPTH}, CHUNKS={self.CHUNKS}, SEED={self.SEED}")

        # Create comprehensive randomizer configurations using FlexConfigGen
        self.randomizer_configs = self._create_comprehensive_randomizer_configs()

        # Define field configuration for input channels (data+id)
        self.input_field_config = FieldConfig()
        self.input_field_config.add_field(FieldDefinition(
            name='data',
            bits=self.DATA_WIDTH,
            default=0,
            format='hex',
            display_width=2,
            active_bits=(self.DATA_WIDTH-1, 0),
            description='Data value'
        ))
        self.input_field_config.add_field(FieldDefinition(
            name='id',
            bits=self.ID_WIDTH,
            default=0,
            format='hex',
            display_width=1,
            active_bits=(self.ID_WIDTH-1, 0),
            description='ID value'
        ))

        # Define field configuration for output channel (id + CHUNKS data fields)
        self.output_field_config = FieldConfig()
        for i in range(self.CHUNKS):
            self.output_field_config.add_field(FieldDefinition(
                name=f'data{i}',
                bits=self.DATA_WIDTH,
                default=0,
                format='hex',
                display_width=2,
                active_bits=(self.DATA_WIDTH-1, 0),
                description=f'Data{i} value'
            ))
        self.output_field_config.add_field(FieldDefinition(
            name='id',
            bits=self.ID_WIDTH,
            default=0,
            format='hex',
            display_width=1,
            active_bits=(self.ID_WIDTH-1, 0),
            description='ID value'
        ))

        # Create memory models for each input channel
        self.input_memory_models = {}
        for i, channel_name in enumerate(self.channel_names):
            self.input_memory_models[channel_name] = MemoryModel(
                num_lines=16,
                bytes_per_line=2,
                log=self.log
            )

        self.output_memory_model = MemoryModel(
            num_lines=self.OUTPUT_FIFO_DEPTH,
            bytes_per_line=self.CHUNKS * self.DATA_WIDTH // 8 or 1,
            log=self.log
        )

        # Create dictionaries to store masters and monitors
        self.masters = {}
        self.monitors = {}

        # Create input channel masters and monitors in a loop
        for i, (channel, channel_name) in enumerate(zip(self.channels, self.channel_names)):
            # Create FIFO master for this input channel
            self.masters[channel_name] = FIFOMaster(
                dut=dut,
                title=f'Master {channel_name}',
                prefix='',
                clock=self.clock,
                field_config=self.input_field_config,
                timeout_cycles=1000,
                mode='fifo_mux',
                multi_sig=True,
                bus_name=channel,  # 'a', 'b', 'c', 'd'
                pkt_prefix='',
                super_debug=self.super_debug,
                log=self.log
            )

            # Create monitor for this input channel
            self.monitors[channel_name] = FIFOMonitor(
                dut, f'Monitor {channel_name}', '', self.clock,
                field_config=self.input_field_config,
                is_slave=False,
                mode='fifo_mux',
                bus_name=channel,  # 'a', 'b', 'c', 'd'
                pkt_prefix='',
                fifo_depth=2,
                super_debug=self.super_debug,
                log=self.log
            )

        # Create FIFO slave for output channel E
        self.slave_e = FIFOSlave(
            dut, 'Slave E', '', self.clock,
            field_config=self.output_field_config,
            timeout_cycles=1000,
            mode='fifo_mux',
            multi_sig=True,
            super_debug=self.super_debug,
            bus_name='e',
            log=self.log
        )

        # Create output monitor
        self.monitor_e = FIFOMonitor(
            dut, 'Monitor E', '', self.clock,
            field_config=self.output_field_config,
            is_slave=True,
            mode='fifo_mux',
            bus_name='e',
            fifo_depth=16,
            super_debug=self.super_debug,
            log=self.log
        )

        # Create specialized scoreboard for data_collect
        self.scoreboard = DataCollectScoreboard('DataCollect Scoreboard',
                                                self.input_field_config,
                                                self.output_field_config,
                                                log=self.log)

        # Initialize the arbiter monitor with proper integration
        self.dut_arb = dut.inst_arbiter
        try:
            # Create Arbiter Monitor
            self.arbiter_monitor = WeightedRoundRobinArbiterMonitor(
                dut=self.dut_arb,
                title="WRR Arbiter Monitor",
                clock=self.dut_arb.i_clk,
                clock_period_ns=10,
                reset_n=self.dut_arb.i_rst_n,
                req_signal=self.dut_arb.i_req,
                gnt_valid_signal=self.dut_arb.ow_gnt_valid,
                gnt_signal=self.dut_arb.ow_gnt,
                gnt_id_signal=self.dut_arb.ow_gnt_id,
                gnt_ack_signal=self.dut_arb.i_gnt_ack if hasattr(self.dut_arb, 'i_gnt_ack') else None,
                block_arb_signal=self.dut_arb.i_block_arb,
                max_thresh_signal=self.dut_arb.i_max_thresh,
                clients=self.dut_arb.CLIENTS,
                log=self.log
            )

            # Add callback to forward arbiter transactions to scoreboard
            self.arbiter_monitor.add_transaction_callback(self._on_arbiter_transaction)

            # Current weight configuration for verification
            self.current_weights = [0, 0, 0, 0]

            self.log.info("Arbiter monitor initialized successfully")
        except (ImportError, AttributeError) as e:
            self.log.warning(f"WRR Monitor not available: {e}, skipping arbiter monitoring")
            self.arbiter_monitor = None

        # Test counters
        self.total_errors = 0
        self.weight_configs = []
        self.error_log = []

        self.log.info(f"Testbench initialized with {len(self.masters)} input masters and {len(self.monitors)} input monitors")

    def _create_comprehensive_randomizer_configs(self):
        """Create comprehensive randomizer configurations using FlexConfigGen"""
        
        # Define custom data collect specific profiles
        data_collect_custom_profiles = {
            # Data collection specific patterns
            'collect_stress': ([(0, 0), (1, 2), (5, 8), (15, 25)], [6, 4, 3, 1]),          # Stress collection
            'collect_pipeline': ([(1, 3), (4, 6)], [3, 2]),                                 # Pipeline friendly
            'collect_burst': ([(0, 0), (10, 15)], [15, 1]),                                 # Burst collection
            'collect_realistic': ([(0, 1), (2, 4), (8, 12)], [5, 4, 2]),                   # Real-world collection
            'collect_fine_grain': ([(0, 1), (2, 3), (4, 6), (7, 10)], [4, 3, 2, 1]),      # Fine control
            'collect_weighted': ([(0, 0), (1, 2), (self.CHUNKS, self.CHUNKS*2)], [8, 3, 1]) # Chunk-aware
        }

        # Create FlexConfigGen for comprehensive data collection testing
        config_gen = FlexConfigGen(
            profiles=[
                # Standard canned profiles
                'backtoback', 'fast', 'constrained', 'bursty', 'slow', 'stress',
                'moderate', 'balanced', 'heavy_pause', 'gradual', 'jittery',
                'pipeline', 'throttled', 'chaotic', 'smooth', 'efficient',
                # Custom data collection profiles
                'collect_stress', 'collect_pipeline', 'collect_burst', 'collect_realistic',
                'collect_fine_grain', 'collect_weighted'
            ],
            fields=['write_delay', 'read_delay'],
            custom_profiles=data_collect_custom_profiles
        )

        # Customize profiles for data collection behavior
        
        # Ultra-aggressive backtoback for maximum throughput
        config_gen.backtoback.write_delay.fixed_value(0)
        config_gen.backtoback.read_delay.fixed_value(0)
        
        # Fast patterns optimized for data collection
        config_gen.fast.write_delay.mostly_zero(zero_weight=40, fallback_range=(1, 2), fallback_weight=1)
        config_gen.fast.read_delay.mostly_zero(zero_weight=35, fallback_range=(1, 3), fallback_weight=2)
        
        # Stress test with data collection variations
        config_gen.stress.write_delay.weighted_ranges([
            ((0, 0), 8), ((1, 3), 6), ((4, 8), 4), ((12, 18), 2), ((25, 35), 1)
        ])
        config_gen.stress.read_delay.weighted_ranges([
            ((0, 1), 6), ((2, 5), 5), ((6, 12), 4), ((18, 28), 2), ((35, 45), 1)
        ])
        
        # Data collection optimized pipeline timing
        config_gen.pipeline.write_delay.uniform_range(1, 2)
        config_gen.pipeline.read_delay.uniform_range(2, 4)
        
        # Chaotic data collection testing
        config_gen.chaotic.write_delay.probability_split([
            ((0, 1), 0.5), ((2, 6), 0.3), ((8, 15), 0.15), ((20, 30), 0.05)
        ])
        config_gen.chaotic.read_delay.probability_split([
            ((0, 2), 0.5), ((3, 8), 0.3), ((12, 20), 0.15), ((25, 40), 0.05)
        ])

        # Data collection burst patterns
        config_gen.bursty.write_delay.burst_pattern(fast_cycles=0, pause_range=(6, 12), burst_ratio=25)
        config_gen.bursty.read_delay.burst_pattern(fast_cycles=0, pause_range=(8, 15), burst_ratio=15)

        # Heavy pause for overflow testing
        config_gen.heavy_pause.write_delay.mostly_zero(zero_weight=20, fallback_range=(1, 2), fallback_weight=1)
        config_gen.heavy_pause.read_delay.weighted_ranges([((0, 0), 4), ((15, 25), 1)])

        # Build all configurations
        randomizer_dict = config_gen.build(return_flexrandomizer=False)
        
        # Convert to the format expected by the rest of the testbench
        converted_configs = {}
        for profile_name, profile_config in randomizer_dict.items():
            converted_configs[profile_name] = {
                'write': {field: constraints for field, constraints in profile_config.items() if 'write' in field},
                'read': {field: constraints for field, constraints in profile_config.items() if 'read' in field}
            }
        
        self.log.info(f"Created {len(converted_configs)} comprehensive data collection randomizer configurations:")
        for profile_name in converted_configs.keys():
            self.log.info(f"  - {profile_name}")
            
        return converted_configs

    def get_randomizer_config_names(self):
        """Get list of available randomizer configuration names"""
        return list(self.randomizer_configs.keys())

    def _on_arbiter_transaction(self, transaction):
        """Callback function called when arbiter monitor observes a transaction"""
        self.scoreboard.add_arbiter_transaction(transaction, self.current_weights)
        self.log.debug(f"Arbiter transaction: Client {transaction.gnt_id} granted "
                        f"after {transaction.cycle_count} cycles, "
                        f"req_vector=0x{transaction.req_vector:x}{self.get_time_ns_str()}")

    def start_arbiter_monitoring(self):
        """Start the arbiter monitoring if available"""
        if self.arbiter_monitor:
            self.arbiter_monitor.start_monitoring()
            self.log.info("Arbiter monitoring started")

    def get_arbiter_statistics(self):
        """Get statistics from the arbiter monitor"""
        if self.arbiter_monitor:
            stats = self.arbiter_monitor.get_stats_summary()
            fairness = self.arbiter_monitor.get_fairness_index()
            stats['fairness_index'] = fairness
            return stats
        return {}

    def verify_arbiter_weight_compliance(self, tolerance=0.25):
        """Verify that the arbiter is following the configured weights"""
        if not self.arbiter_monitor:
            self.log.warning("No arbiter monitor available for weight verification")
            return True

        stats = self.arbiter_monitor.get_stats_summary()
        if stats['total_grants'] < 20:
            self.log.warning("Insufficient arbiter grants for weight verification")
            return True

        return self.scoreboard.verify_arbiter_weights(self.current_weights, tolerance)

    def log_error(self, error_type, details):
        """Log an error with timestamp for later analysis"""
        self.error_log.append({
            'time': self.get_time_ns_str(),
            'type': error_type,
            'details': details
        })
        self.total_errors += 1

    async def wait_for_expected_outputs(self, expected_count, timeout_clocks=5000):
        """Wait until the expected number of outputs have been received or timeout"""
        count = 0
        while len(self.monitor_e._recvQ) < expected_count and count < timeout_clocks:
            await self.wait_clocks('i_clk', 1)
            count += 1

            if count % 200 == 0:
                self.log.info(f"Waiting for outputs: {len(self.monitor_e._recvQ)}/{expected_count} received{self.get_time_ns_str()}")

        received = len(self.monitor_e._recvQ)
        if received < expected_count:
            self.log.warning(f"Timeout waiting for outputs: {received}/{expected_count} received{self.get_time_ns_str()}")
            self.log_error('timeout', f"Expected {expected_count} outputs, got {received}")
            return False

        self.log.info(f"All expected outputs received: {received}/{expected_count}{self.get_time_ns_str()}")
        return True

    async def assert_reset(self):
        """Assert the reset signal"""
        self.reset_n.value = 0

        # Reset all masters and slave using loops
        for channel_name in self.channel_names:
            await self.masters[channel_name].reset_bus()

        await self.slave_e.reset_bus()

    async def deassert_reset(self):
        """Deassert the reset signal"""
        self.reset_n.value = 1
        self.log.info(f"Reset deasserted{self.get_time_ns_str()}")

    def set_arbiter_weights(self, weight_a, weight_b, weight_c, weight_d):
        """Set the weights for the weighted round-robin arbiter"""
        weights = [weight_a, weight_b, weight_c, weight_d]

        # Validate weights are within 0-15 range
        for i, (channel_name, weight) in enumerate(zip(self.channel_names, weights)):
            if weight < 0 or weight > 15:
                self.log.error(f"Invalid weight for channel {channel_name}: {weight}. Must be 0-15.")
                self.log_error('invalid_weight', f"Channel {channel_name} weight {weight} out of range 0-15")
                return

        # Set the weights
        self.dut.i_weight_a.value = weight_a
        self.dut.i_weight_b.value = weight_b
        self.dut.i_weight_c.value = weight_c
        self.dut.i_weight_d.value = weight_d

        # Store current weights for arbiter verification
        self.current_weights = weights

        # Log the configuration
        self.log.info(f"Arbiter weights set: A={weight_a}, B={weight_b}, C={weight_c}, D={weight_d}")
        self.weight_configs.append(tuple(weights))

    def set_randomizers(self, config_name):
        """Set randomizers for all masters and slave using FlexConfigGen configurations"""
        if config_name in self.randomizer_configs:
            write_config = self.randomizer_configs[config_name]['write']
            read_config = self.randomizer_configs[config_name]['read']
            
            # Set all master randomizers
            for channel_name in self.channel_names:
                self.masters[channel_name].set_randomizer(FlexRandomizer(write_config))
            
            # Set slave randomizer
            self.slave_e.set_randomizer(FlexRandomizer(read_config))
            
            self.log.info(f"Set all randomizers to config '{config_name}' - "
                         f"Write: {write_config}, Read: {read_config}")
        else:
            self.log.warning(f"Randomizer config '{config_name}' not found, using 'constrained'")
            fallback_config = self.randomizer_configs['constrained']
            
            for channel_name in self.channel_names:
                self.masters[channel_name].set_randomizer(FlexRandomizer(fallback_config['write']))
            self.slave_e.set_randomizer(FlexRandomizer(fallback_config['read']))

    async def send_packets_on_channel(self, channel_name, count, id_value=None, base_data=0, expected_weight=None):
        """
        Send packets on a specific channel with proper timeout handling

        Args:
            channel_name: Channel name ('A', 'B', 'C', or 'D')
            count: Number of packets to send
            id_value: ID value to use (None for channel default)
            base_data: Base value for data (incremented for each packet)
            expected_weight: Expected weight for this channel (for timeout handling)
        """
        if channel_name not in self.channel_names:
            self.log.error(f"Unknown channel: {channel_name}")
            self.log_error('unknown_channel', f"Unknown channel: {channel_name}")
            return []

        # Get the channel index and corresponding components
        channel_index = self.channel_names.index(channel_name)
        master = self.masters[channel_name]
        default_id = self.channel_ids[channel_index]
        memory_model = self.input_memory_models[channel_name]

        # Use provided ID or default
        if id_value is None:
            id_value = default_id

        # Handle zero-weight channels
        if expected_weight is not None and expected_weight == 0:
            actual_count = min(count, 10)  # Limit packets for zero-weight channels
            self.log.info(f"Channel {channel_name} has zero weight, limiting to {actual_count} packets")
        else:
            actual_count = count

        # Create and send packets
        sent_packets = []
        for i in range(actual_count):
            # Create packet
            pkt = FIFOPacket(self.input_field_config)
            pkt.id = id_value
            pkt.data = (base_data + i) & ((1 << self.DATA_WIDTH) - 1)  # Mask to WIDTH bits

            # Store in memory model if available
            if memory_model:
                addr = i % memory_model.num_lines
                data = pkt.data
                data_bytes = memory_model.integer_to_bytearray(data, 2)
                memory_model.write(addr, data_bytes)

            try:
                # For zero-weight channels, use shorter timeout
                if expected_weight is not None and expected_weight == 0:
                    original_timeout = master.timeout_cycles
                    master.timeout_cycles = 50

                await master.send(pkt)

                # Restore original timeout
                if expected_weight is not None and expected_weight == 0:
                    master.timeout_cycles = original_timeout

                sent_packets.append(pkt)

            except Exception as e:
                if expected_weight is not None and expected_weight == 0:
                    self.log.info(f"Expected timeout on zero-weight channel {channel_name} after {len(sent_packets)} packets: {e}")
                    break
                else:
                    self.log.error(f"Unexpected timeout on channel {channel_name}: {e}")
                    raise

            # Log progress
            if expected_weight is None or expected_weight > 0:
                if (i + 1) % 20 == 0 or i == 0 or i == actual_count - 1:
                    self.log.info(f"Sent {i+1}/{actual_count} packets on channel {channel_name}")

        self.log.info(f"Channel {channel_name} sent {len(sent_packets)} packets (requested {count})")
        return sent_packets

    async def wait_for_all_masters_idle(self):
        """Wait until all masters have completed their transmissions"""
        while any(self.masters[channel_name].transfer_busy for channel_name in self.channel_names):
            await self.wait_clocks('i_clk', 1)

    def add_received_packets_to_scoreboard(self):
        """Add received packets from the output monitor to the scoreboard"""
        while self.monitor_e._recvQ:
            pkt = self.monitor_e._recvQ.popleft()
            self.scoreboard.add_output_packet(pkt)

    def check_scoreboard(self):
        """Check the scoreboard for errors"""
        errors = self.scoreboard.report()
        self.total_errors += errors
        if errors > 0:
            self.log.error(f"Scoreboard found {errors} errors{self.get_time_ns_str()}")
            self.log_error('scoreboard', f"Scoreboard reported {errors} errors")
        else:
            self.log.info(f"Scoreboard verification passed{self.get_time_ns_str()}")
        return errors

    def get_component_statistics(self):
        """Get statistics from all components"""
        stats = {
            'slave_e': self.slave_e.get_stats(),
            'monitor_e': self.monitor_e.get_stats(),
            'scoreboard': self.scoreboard.get_statistics(),
            'memory_models': {
                'output': self.output_memory_model.get_stats(),
            },
            'arbiter': self.get_arbiter_statistics(),
            'error_count': self.total_errors,
            'error_log_count': len(self.error_log)
        }

        # Add input channel statistics using loops
        for channel_name in self.channel_names:
            stats[f'master_{channel_name.lower()}'] = self.masters[channel_name].get_stats()
            stats[f'monitor_{channel_name.lower()}'] = self.monitors[channel_name].get_stats()
            stats['memory_models'][f'input_{channel_name}'] = self.input_memory_models[channel_name].get_stats()

        return stats

    async def run_simple_test(self, packets_per_channel=40, expected_outputs=10):
        """Run a simple test with equal packets on all channels"""
        self.log.info(f"Starting simple test with {packets_per_channel} packets per channel{self.get_time_ns_str()}")

        # Reset system
        await self.assert_reset()
        await self.wait_clocks('i_clk', 10)
        await self.deassert_reset()
        await self.wait_clocks('i_clk', 10)

        # Set equal weights for all channels
        self.set_arbiter_weights(8, 8, 8, 8)
        self.start_arbiter_monitoring()
        self.scoreboard.clear()

        # Set randomizers to moderate for stable test
        self.set_randomizers('moderate')

        # Send packets on all channels concurrently
        send_tasks = []
        for i, channel_name in enumerate(self.channel_names):
            base_data = 0x100 + i * 0x100  # Different base data per channel
            task = cocotb.start_soon(
                self.send_packets_on_channel(
                    channel_name, packets_per_channel,
                    id_value=self.channel_ids[i],
                    base_data=base_data
                )
            )
            send_tasks.append(task)

        # Wait for all sending tasks and add packets to scoreboard
        for task in send_tasks:
            sent_packets = await task
            for pkt in sent_packets:
                self.scoreboard.add_input_packet(pkt)

        # Wait for masters to finish transmitting
        await self.wait_for_all_masters_idle()
        self.log.info(f"All masters finished sending{self.get_time_ns_str()}")

        # Calculate expected outputs (use parameter if provided, otherwise calculate)
        if expected_outputs == 10:  # Default value, calculate based on packets
            total_expected_outputs = (packets_per_channel * len(self.channels)) // self.CHUNKS
        else:
            total_expected_outputs = expected_outputs

        # Wait for expected outputs
        await self.wait_for_expected_outputs(total_expected_outputs)
        self.add_received_packets_to_scoreboard()
        await self.wait_clocks('i_clk', 100)

        # Verify arbiter weight compliance
        weight_compliance = self.verify_arbiter_weight_compliance()
        if not weight_compliance:
            self.log.error(f"Arbiter weight compliance check failed{self.get_time_ns_str()}")
            self.total_errors += 1

        # Check scoreboard
        errors = self.check_scoreboard()

        # Get and report statistics
        stats = self.get_component_statistics()
        self.log.info(f"Test Statistics: {stats}")

        return errors == 0 and weight_compliance

    async def run_comprehensive_randomizer_sweep(self, packets_per_config=20):
        """Test all available randomizer configurations"""
        self.log.info('='*80)
        self.log.info(f'Running comprehensive data collection randomizer sweep with {packets_per_config} packets per config')
        
        # Get test level from environment for filtering
        test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
        
        # Filter configs based on test level
        if test_level == 'basic':
            test_configs = ['backtoback', 'fast', 'constrained', 'collect_realistic']
        elif test_level == 'medium':
            test_configs = [
                'backtoback', 'fast', 'constrained', 'bursty', 'moderate', 'balanced',
                'collect_stress', 'collect_realistic', 'collect_pipeline'
            ]
        else:  # full
            test_configs = list(self.randomizer_configs.keys())
        
        # Filter to only existing configs
        test_configs = [config for config in test_configs if config in self.randomizer_configs]
        
        total_configs = len(test_configs)
        for i, config_name in enumerate(test_configs):
            self.log.info(f'Testing data collection config {i+1}/{total_configs}: {config_name}')
            
            try:
                # Reset system
                await self.assert_reset()
                await self.wait_clocks('i_clk', 10)
                await self.deassert_reset()
                await self.wait_clocks('i_clk', 10)

                # Set equal weights for all channels
                self.set_arbiter_weights(8, 8, 8, 8)
                self.start_arbiter_monitoring()
                self.scoreboard.clear()

                # Set randomizers
                self.set_randomizers(config_name)

                # Send packets on all channels
                send_tasks = []
                for j, channel_name in enumerate(self.channel_names):
                    base_data = 0x100 + j * 0x100 + i * 0x1000
                    task = cocotb.start_soon(
                        self.send_packets_on_channel(
                            channel_name, packets_per_config,
                            id_value=self.channel_ids[j],
                            base_data=base_data
                        )
                    )
                    send_tasks.append(task)

                # Wait for sending to complete
                for task in send_tasks:
                    sent_packets = await task
                    for pkt in sent_packets:
                        self.scoreboard.add_input_packet(pkt)

                await self.wait_for_all_masters_idle()

                # Calculate expected outputs
                expected_outputs = (packets_per_config * len(self.channels)) // self.CHUNKS

                # Wait for outputs
                await self.wait_for_expected_outputs(expected_outputs)
                self.add_received_packets_to_scoreboard()
                await self.wait_clocks('i_clk', 50)

                # Check results
                weight_compliance = self.verify_arbiter_weight_compliance()
                errors = self.check_scoreboard()

                if errors > 0 or not weight_compliance:
                    self.log.error(f'✗ Data collection config {config_name} failed: {errors} errors, weight_compliance={weight_compliance}')
                    raise Exception(f"Config {config_name} failed")
                else:
                    self.log.info(f'✓ Data collection config {config_name} passed')
                    
            except Exception as e:
                self.log.error(f'✗ Data collection config {config_name} failed: {e}')
                raise

    async def run_weighted_arbiter_test(self, weights_list=None):
        """Run a test with different arbiter weight configurations"""
        if weights_list is None:
            # Get test level for configuration filtering
            test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
            
            if test_level == 'basic':
                weights_list = [
                    (8, 8, 8, 8),     # Equal weights
                    (15, 0, 0, 0),    # Channel A only
                    (8, 8, 0, 0),     # Equal A and B
                ]
            elif test_level == 'medium':
                weights_list = [
                    (8, 8, 8, 8),     # Equal weights
                    (15, 0, 0, 0),    # Channel A only
                    (0, 15, 0, 0),    # Channel B only
                    (8, 8, 0, 0),     # Equal A and B
                    (4, 8, 12, 0),    # Varied weights
                ]
            else:  # full
                weights_list = [
                    (15, 0, 0, 0),    # Channel A only
                    (0, 15, 0, 0),    # Channel B only
                    (0, 0, 15, 0),    # Channel C only
                    (0, 0, 0, 15),    # Channel D only
                    (8, 8, 0, 0),     # Equal A and B
                    (0, 8, 8, 0),     # Equal B and C
                    (0, 0, 8, 8),     # Equal C and D
                    (8, 0, 0, 8),     # Equal A and D
                    (4, 8, 12, 0),    # Varied weights
                    (1, 2, 4, 8),     # Increasing weights
                ]

        all_passed = True
        results = []

        for i, weights in enumerate(weights_list):
            self.log.info(f"Starting weighted test {i+1}/{len(weights_list)} with weights: {weights}{self.get_time_ns_str()}")

            # Reset system
            await self.assert_reset()
            await self.wait_clocks('i_clk', 10)
            await self.deassert_reset()
            await self.wait_clocks('i_clk', 10)

            # Set weights
            self.set_arbiter_weights(*weights)
            self.start_arbiter_monitoring()
            self.scoreboard.clear()

            # Set randomizers to fast for efficient testing
            self.set_randomizers('fast')

            # Calculate packets per channel based on weights
            base_count = 24  # Multiple of CHUNKS for clean testing
            packets_per_channel = []
            for weight in weights:
                if weight == 0:
                    packets_per_channel.append(0)
                else:
                    # Ensure multiples of CHUNKS for clean testing
                    count = (base_count * weight // self.CHUNKS) * self.CHUNKS
                    packets_per_channel.append(count)

            expected_outputs = sum(packets_per_channel) // self.CHUNKS

            # Send packets concurrently
            send_tasks = []
            for j, (channel_name, packet_count, weight) in enumerate(zip(self.channel_names, packets_per_channel, weights)):
                if packet_count > 0:
                    base_data = 0x100 + j * 0x100 + i * 0x1000
                    task = cocotb.start_soon(
                        self.send_packets_on_channel(
                            channel_name, packet_count,
                            id_value=self.channel_ids[j],
                            base_data=base_data,
                            expected_weight=weight
                        )
                    )
                    send_tasks.append(task)

            # Wait for sending to complete
            for task in send_tasks:
                sent_packets = await task
                for pkt in sent_packets:
                    self.scoreboard.add_input_packet(pkt)

            await self.wait_for_all_masters_idle()
            await self.wait_clocks('i_clk', 200)

            # Wait for expected outputs
            success = await self.wait_for_expected_outputs(expected_outputs)

            if not success:
                self.log.error(f"Test {i+1} failed: timeout waiting for outputs{self.get_time_ns_str()}")
                all_passed = False
                results.append(False)
            else:
                self.add_received_packets_to_scoreboard()
                await self.wait_clocks('i_clk', 100)

                # Verify arbiter weight compliance
                weight_compliance = self.verify_arbiter_weight_compliance(tolerance=0.3)
                errors = self.check_scoreboard()

                if errors > 0 or not weight_compliance:
                    self.log.error(f"Test {i+1} failed: {errors} errors, weight_compliance={weight_compliance}{self.get_time_ns_str()}")
                    all_passed = False
                    results.append(False)
                else:
                    self.log.info(f"Test {i+1} passed{self.get_time_ns_str()}")
                    results.append(True)

            # Get statistics
            stats = self.get_component_statistics()
            self.log.info(f"Test {i+1} Statistics: {stats}")

        self.log.info(f"Weighted arbiter test results: {results}")
        self.log.info(f"Overall result: {'Passed' if all_passed else 'Failed'}")
        return all_passed
