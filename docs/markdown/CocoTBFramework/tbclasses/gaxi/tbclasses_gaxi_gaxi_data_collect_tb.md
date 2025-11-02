# gaxi_data_collect_tb.py

Enhanced testbench for GAXI data collection modules using modern framework with FlexConfigGen. This testbench provides specialized testing capabilities for multi-channel data aggregation systems with weighted round-robin arbitration and sophisticated verification methodologies.

## Overview

The `GAXIDataCollectTB` class provides comprehensive testing for GAXI data collection components that aggregate data from multiple input channels with arbitration. It includes advanced scoreboard functionality, channel-specific validation, and enhanced field verification capabilities.

### Key Features
- **Multi-channel data validation** with channel-specific integrity checking
- **Weighted round-robin arbitration monitoring** for fairness verification
- **Enhanced field validation** with error detection and reporting
- **Sophisticated scoreboard** with data combining logic
- **FlexConfigGen integration** for advanced randomization
- **Channel ID mapping** and validation
- **Modern framework integration** using GAXIComponentBase

### Supported DUT Types
- `gaxi_data_collect`: Multi-channel data aggregation with weighted round-robin arbitration
- Custom data collection implementations with channel-based input

## Class Definition

```python
class GAXIDataCollectTB(TBBase):
    """
    Enhanced testbench for gaxi_data_collect module using modern framework with FlexConfigGen.
    Updated to use FlexConfigGen returning FlexRandomizer instances directly.
    """
    
    def __init__(self, dut, clk=None, rstn=None):
```

## Specialized Scoreboard

### GAXIDataCollectScoreboard

The testbench includes a sophisticated scoreboard designed specifically for data collection verification:

```python
class GAXIDataCollectScoreboard:
    """
    Specialized scoreboard for gaxi_data_collect module with enhanced field validation and error detection.
    Updated to use modern framework components with GAXI protocol.
    """
    
    def __init__(self, title, input_field_config, output_field_config, log=None):
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
```

### Channel Configuration

The scoreboard supports four channels (A, B, C, D) with configurable channel IDs:

```python
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
```

### Data Collection Logic

The scoreboard implements sophisticated data collection and combination logic:

```python
def add_input_packet(self, packet, channel=None):
    """
    Add input packet to appropriate channel queue
    
    Parameters:
    - packet: Input packet to add
    - channel: Channel identifier (auto-detected if None)
    """
    
    # Auto-detect channel from packet ID if not specified
    if channel is None:
        channel = self.detect_channel_from_packet(packet)
    
    if channel not in self.channels:
        self.log.error(f"Invalid channel: {channel}")
        return
    
    # Add to input queue
    self.input_queues[channel].append(packet)
    
    # Check if we can form a complete group
    if len(self.input_queues[channel]) >= 4:
        self.combine_packets(channel)
    
    self.log.debug(f"Added input packet to channel {channel}, queue length: {len(self.input_queues[channel])}")

def combine_packets(self, channel):
    """
    Combine 4 packets from input queue into combined packet
    
    Parameters:
    - channel: Channel to process
    """
    
    if len(self.input_queues[channel]) < 4:
        return
    
    # Take 4 packets from input queue
    input_packets = []
    for _ in range(4):
        if self.input_queues[channel]:
            input_packets.append(self.input_queues[channel].popleft())
    
    if len(input_packets) != 4:
        self.log.error(f"Failed to get 4 packets for combination in channel {channel}")
        return
    
    # Create combined packet
    combined_packet = self.create_combined_packet(input_packets, channel)
    self.combined_queues[channel].append(combined_packet)
    
    self.log.debug(f"Combined 4 packets for channel {channel}, combined queue length: {len(self.combined_queues[channel])}")

def create_combined_packet(self, input_packets, channel):
    """
    Create combined packet from 4 input packets
    
    Parameters:
    - input_packets: List of 4 input packets
    - channel: Source channel
    
    Returns: Combined packet
    """
    
    # Create combined packet using output field config
    combined_packet = GAXIPacket(self.output_field_config)
    
    # Combine data from input packets
    # Typically: concatenate or process the 4 input packets
    combined_data = 0
    for i, packet in enumerate(input_packets):
        if hasattr(packet, 'data'):
            # Pack data: each packet contributes 8 bits to 32-bit combined value
            packet_data = packet.data & 0xFF
            combined_data |= (packet_data << (i * 8))
    
    # Set combined packet fields
    combined_packet.data = combined_data
    combined_packet.channel = channel
    combined_packet.source_packets = input_packets.copy()
    combined_packet.combination_time = time.time()
    
    return combined_packet
```

## Arbitration Monitoring

### Weighted Round-Robin Arbitration

The testbench includes specialized monitoring for weighted round-robin arbitration:

```python
from CocoTBFramework.components.misc.arbiter_monitor import WeightedRoundRobinArbiterMonitor

# Create arbitration monitor
self.arbiter_monitor = WeightedRoundRobinArbiterMonitor(
    dut=self.dut,
    title="DataCollectArbiter",
    num_requesters=4,  # Four channels
    clock=self.clk,
    log=self.log
)

# Configure channel weights (if configurable)
channel_weights = {
    'A': 4,  # Highest priority
    'B': 3,
    'C': 2, 
    'D': 1   # Lowest priority
}
```

### Arbitration Verification

```python
def verify_arbitration_fairness(self, test_duration_cycles=1000):
    """
    Verify arbitration fairness over test duration
    
    Parameters:
    - test_duration_cycles: Duration to monitor arbitration
    
    Returns: Arbitration fairness report
    """
    
    # Monitor arbitration decisions
    arbitration_decisions = []
    channel_grants = {'A': 0, 'B': 0, 'C': 0, 'D': 0}
    
    for cycle in range(test_duration_cycles):
        # Check which channel is granted access
        granted_channel = self.detect_granted_channel()
        if granted_channel:
            arbitration_decisions.append(granted_channel)
            channel_grants[granted_channel] += 1
    
    # Calculate fairness metrics
    total_grants = sum(channel_grants.values())
    fairness_report = {
        'total_grants': total_grants,
        'channel_grants': channel_grants.copy(),
        'grant_percentages': {},
        'fairness_score': 0.0
    }
    
    if total_grants > 0:
        for channel, grants in channel_grants.items():
            fairness_report['grant_percentages'][channel] = (grants / total_grants) * 100
        
        # Calculate fairness score based on expected weights
        expected_weights = {'A': 0.4, 'B': 0.3, 'C': 0.2, 'D': 0.1}
        fairness_score = 0.0
        
        for channel, expected_weight in expected_weights.items():
            actual_percentage = fairness_report['grant_percentages'][channel] / 100.0
            deviation = abs(actual_percentage - expected_weight)
            fairness_score += (1.0 - deviation)
        
        fairness_report['fairness_score'] = fairness_score / len(expected_weights)
    
    self.log.info(f"Arbitration fairness: {fairness_report['fairness_score']:.3f}")
    return fairness_report

def detect_granted_channel(self):
    """Detect which channel is currently granted access"""
    
    # Check grant signals for each channel
    grant_signals = {
        'A': getattr(self.dut, 'grant_a', None),
        'B': getattr(self.dut, 'grant_b', None),
        'C': getattr(self.dut, 'grant_c', None),
        'D': getattr(self.dut, 'grant_d', None)
    }
    
    for channel, signal in grant_signals.items():
        if signal and signal.value == 1:
            return channel
    
    return None
```

## Core Testing Methods

### Multi-Channel Data Testing

```python
async def test_multi_channel_data_collection(self, packets_per_channel=20):
    """
    Test multi-channel data collection with arbitration
    
    Parameters:
    - packets_per_channel: Number of packets to send per channel
    """
    
    self.log.info(f"Testing multi-channel data collection: {packets_per_channel} packets per channel")
    
    # Generate test data for each channel
    channel_data = {}
    for channel in ['A', 'B', 'C', 'D']:
        channel_data[channel] = self.generate_channel_test_data(channel, packets_per_channel)
    
    # Send data concurrently on all channels
    async def send_channel_data(channel, packets):
        master = getattr(self, f'master_{channel.lower()}')
        for i, packet in enumerate(packets):
            await master.drive_packet(packet)
            # Add variable delay to create realistic conditions
            await Timer(random.randint(1, 5), units='ns')
            self.log.debug(f"Channel {channel} sent packet {i}")
    
    # Start all channels concurrently
    tasks = []
    for channel, packets in channel_data.items():
        task = cocotb.start(send_channel_data(channel, packets))
        tasks.append(task)
    
    # Wait for all channels to complete transmission
    for task in tasks:
        await task
    
    # Wait for data collection to complete
    expected_combined_packets = packets_per_channel // 4  # 4 packets combine to 1
    total_expected = expected_combined_packets * 4  # 4 channels
    
    await self.wait_for_data_collection_completion(total_expected)
    
    # Verify collected data
    verification_errors = self.verify_collected_data(channel_data)
    
    self.log.info(f"Multi-channel test completed with {verification_errors} verification errors")
    return verification_errors

def generate_channel_test_data(self, channel, num_packets):
    """
    Generate test data for specific channel
    
    Parameters:
    - channel: Channel identifier ('A', 'B', 'C', 'D')
    - num_packets: Number of packets to generate
    
    Returns: List of test packets for channel
    """
    
    packets = []
    channel_id = self.channel_ids[channel][0]  # Use primary channel ID
    
    for i in range(num_packets):
        packet = GAXIPacket(self.input_field_config)
        
        # Set channel-specific data
        packet.data = (channel_id << 24) | (i & 0xFFFFFF)
        packet.channel_id = channel_id
        packet.channel = channel
        packet.sequence_number = i
        
        # Add packet to scoreboard for tracking
        self.scoreboard.add_input_packet(packet, channel)
        
        packets.append(packet)
    
    self.log.debug(f"Generated {num_packets} test packets for channel {channel}")
    return packets

async def wait_for_data_collection_completion(self, expected_packets, timeout_cycles=2000):
    """
    Wait for data collection to complete
    
    Parameters:
    - expected_packets: Number of combined packets expected
    - timeout_cycles: Maximum cycles to wait
    """
    
    collected_count = 0
    
    for cycle in range(timeout_cycles):
        # Check collection progress
        current_count = self.get_collected_packet_count()
        
        if current_count >= expected_packets:
            self.log.info(f"Data collection completed at cycle {cycle}: {current_count}/{expected_packets}")
            return True
        
        await RisingEdge(self.clk)
        
        # Periodic progress reporting
        if cycle % 100 == 0:
            self.log.debug(f"Collection progress cycle {cycle}: {current_count}/{expected_packets}")
    
    self.log.error(f"Data collection timeout after {timeout_cycles} cycles: {current_count}/{expected_packets}")
    return False
```

### Channel-Specific Verification

```python
def verify_collected_data(self, original_channel_data):
    """
    Verify that collected data matches expected combined results
    
    Parameters:
    - original_channel_data: Dictionary of original data per channel
    
    Returns: Number of verification errors
    """
    
    verification_errors = 0
    
    # Get collected output packets
    collected_packets = self.get_all_collected_packets()
    
    # Verify each collected packet
    for packet in collected_packets:
        # Determine source channel
        source_channel = self.identify_packet_source_channel(packet)
        
        if source_channel not in original_channel_data:
            verification_errors += 1
            self.log.error(f"Unknown source channel for collected packet: {source_channel}")
            continue
        
        # Verify packet data integrity
        data_valid = self.verify_packet_data_integrity(packet, source_channel, original_channel_data[source_channel])
        if not data_valid:
            verification_errors += 1
    
    # Verify packet count per channel
    count_errors = self.verify_packet_counts(original_channel_data, collected_packets)
    verification_errors += count_errors
    
    if verification_errors == 0:
        self.log.info("Data collection verification PASSED")
    else:
        self.log.error(f"Data collection verification FAILED: {verification_errors} errors")
    
    return verification_errors

def verify_packet_data_integrity(self, collected_packet, source_channel, original_packets):
    """
    Verify data integrity of collected packet
    
    Parameters:
    - collected_packet: Packet from data collection output
    - source_channel: Source channel identifier
    - original_packets: Original packets from source channel
    
    Returns: True if data integrity verified
    """
    
    # Extract combined data
    collected_data = getattr(collected_packet, 'data', 0)
    
    # Find corresponding original packets (typically 4 packets combined into 1)
    packet_group_size = 4
    
    # Verify data combination logic
    # This depends on the specific combining algorithm used by the DUT
    expected_combined_data = self.calculate_expected_combined_data(original_packets, collected_packet)
    
    if collected_data != expected_combined_data:
        self.log.error(f"Data integrity failure for channel {source_channel}: "
                      f"collected=0x{collected_data:08X}, expected=0x{expected_combined_data:08X}")
        return False
    
    self.log.debug(f"Data integrity verified for channel {source_channel}")
    return True

def calculate_expected_combined_data(self, original_packets, collected_packet):
    """
    Calculate expected combined data based on combination algorithm
    
    Parameters:
    - original_packets: Original input packets
    - collected_packet: Collected output packet
    
    Returns: Expected combined data value
    """
    
    # Default combination: pack 4 bytes from 4 packets into 32-bit word
    # This should match the DUT's combination logic
    
    if hasattr(collected_packet, 'source_packets') and collected_packet.source_packets:
        # Use source packets if available
        source_packets = collected_packet.source_packets
    else:
        # Estimate based on timing and sequence
        packet_index = getattr(collected_packet, 'sequence_number', 0) * 4
        source_packets = original_packets[packet_index:packet_index+4]
    
    combined_data = 0
    for i, packet in enumerate(source_packets[:4]):  # Ensure max 4 packets
        packet_data = getattr(packet, 'data', 0) & 0xFF
        combined_data |= (packet_data << (i * 8))
    
    return combined_data
```

## Usage Examples

### Basic Data Collection Testing

```python
import cocotb
import os
from CocoTBFramework.tbclasses.gaxi.gaxi_data_collect_tb import GAXIDataCollectTB

@cocotb.test()
async def test_data_collection_basic(dut):
    # Configure test environment
    os.environ['TEST_CHANNELS'] = '4'
    os.environ['TEST_DATA_WIDTH'] = '8'
    os.environ['TEST_COMBINED_WIDTH'] = '32'
    
    # Create testbench
    tb = GAXIDataCollectTB(dut, clk=dut.clk, rstn=dut.rstn)
    await tb.initialize()
    
    # Run basic multi-channel test
    errors = await tb.test_multi_channel_data_collection(packets_per_channel=16)
    
    # Verify no errors
    assert errors == 0, f"Data collection test failed with {errors} errors"
```

### Advanced Data Collection with Arbitration

```python
@cocotb.test()
async def test_data_collection_with_arbitration(dut):
    # Advanced configuration
    os.environ['TEST_CHANNELS'] = '4'
    os.environ['TEST_ARBITRATION'] = 'weighted_round_robin'
    os.environ['TEST_CHANNEL_WEIGHTS'] = '4,3,2,1'  # A,B,C,D weights
    
    tb = GAXIDataCollectTB(dut, clk=dut.clk, rstn=dut.rstn)
    await tb.initialize()
    
    # Test with arbitration monitoring
    errors = await tb.test_multi_channel_data_collection(packets_per_channel=32)
    
    # Verify arbitration fairness
    fairness_report = tb.verify_arbitration_fairness(test_duration_cycles=1000)
    tb.log.info(f"Arbitration fairness score: {fairness_report['fairness_score']:.3f}")
    
    # Check fairness threshold
    assert fairness_report['fairness_score'] > 0.8, "Arbitration fairness below threshold"
    assert errors == 0, f"Data collection test failed with {errors} errors"
```

### Custom Channel Configuration

```python
@cocotb.test()
async def test_custom_channel_configuration(dut):
    # Custom channel IDs and configuration
    custom_channel_config = {
        'A': {'id': 0x10, 'weight': 5, 'data_pattern': 'incremental'},
        'B': {'id': 0x20, 'weight': 3, 'data_pattern': 'random'},
        'C': {'id': 0x30, 'weight': 2, 'data_pattern': 'alternating'},
        'D': {'id': 0x40, 'weight': 1, 'data_pattern': 'constant'}
    }
    
    tb = GAXIDataCollectTB(dut, clk=dut.clk, rstn=dut.rstn)
    
    # Configure custom channels
    tb.configure_custom_channels(custom_channel_config)
    await tb.initialize()
    
    # Test with custom configuration
    errors = await tb.test_multi_channel_data_collection(packets_per_channel=24)
    
    # Generate detailed report
    report = tb.generate_data_collection_report()
    tb.log.info(f"Custom channel test report:\n{report}")
    
    assert errors == 0, f"Custom channel test failed with {errors} errors"
```

## Advanced Features

### Performance Monitoring

```python
def monitor_collection_performance(self, monitoring_duration_cycles=1000):
    """
    Monitor data collection performance metrics
    
    Parameters:
    - monitoring_duration_cycles: Duration to monitor
    
    Returns: Performance metrics dictionary
    """
    
    start_time = time.time()
    start_cycle = self.get_current_cycle()
    
    metrics = {
        'throughput': {'input': 0, 'output': 0},
        'latency': {'min': float('inf'), 'max': 0, 'avg': 0},
        'channel_utilization': {'A': 0, 'B': 0, 'C': 0, 'D': 0},
        'arbitration_efficiency': 0.0
    }
    
    # Monitor for specified duration
    input_packets = 0
    output_packets = 0
    latency_samples = []
    
    for cycle in range(monitoring_duration_cycles):
        # Count input/output packets this cycle
        cycle_input = self.count_input_packets_this_cycle()
        cycle_output = self.count_output_packets_this_cycle()
        
        input_packets += cycle_input
        output_packets += cycle_output
        
        # Measure latency if packets available
        if cycle_output > 0:
            cycle_latency = self.measure_current_latency()
            if cycle_latency > 0:
                latency_samples.append(cycle_latency)
    
    end_time = time.time()
    duration_seconds = end_time - start_time
    
    # Calculate metrics
    if duration_seconds > 0:
        metrics['throughput']['input'] = input_packets / duration_seconds
        metrics['throughput']['output'] = output_packets / duration_seconds
    
    if latency_samples:
        metrics['latency']['min'] = min(latency_samples)
        metrics['latency']['max'] = max(latency_samples)
        metrics['latency']['avg'] = sum(latency_samples) / len(latency_samples)
    
    return metrics

def generate_data_collection_report(self):
    """Generate comprehensive data collection test report"""
    
    report = []
    report.append("=" * 80)
    report.append("GAXI Data Collection Test Report")
    report.append("=" * 80)
    
    # Test summary
    total_errors = getattr(self, 'total_errors', 0)
    total_packets = getattr(self, 'total_packets_processed', 0)
    
    report.append(f"Total Packets Processed: {total_packets}")
    report.append(f"Total Errors: {total_errors}")
    report.append(f"Success Rate: {((total_packets - total_errors) / max(1, total_packets) * 100):.1f}%")
    report.append("")
    
    # Channel statistics
    report.append("Channel Statistics:")
    report.append("-" * 40)
    
    if hasattr(self, 'scoreboard'):
        for channel in ['A', 'B', 'C', 'D']:
            input_count = len(self.scoreboard.input_queues.get(channel, []))
            combined_count = len(self.scoreboard.combined_queues.get(channel, []))
            report.append(f"Channel {channel}: {input_count:>3} input, {combined_count:>3} combined")
    
    report.append("")
    
    # Arbitration summary
    if hasattr(self, 'arbiter_monitor'):
        arb_stats = self.arbiter_monitor.get_statistics()
        report.append("Arbitration Statistics:")
        report.append("-" * 40)
        report.append(f"Total Grants: {arb_stats.get('total_grants', 0)}")
        
        grant_dist = arb_stats.get('grant_distribution', {})
        for channel, grants in grant_dist.items():
            percentage = grants / max(1, arb_stats.get('total_grants', 1)) * 100
            report.append(f"Channel {channel}: {grants:>3} grants ({percentage:5.1f}%)")
    
    return "\n".join(report)
```

The `gaxi_data_collect_tb.py` component provides comprehensive testing capabilities for multi-channel data collection systems with sophisticated arbitration monitoring, channel-specific validation, and advanced verification methodologies for thorough GAXI data aggregation component testing.