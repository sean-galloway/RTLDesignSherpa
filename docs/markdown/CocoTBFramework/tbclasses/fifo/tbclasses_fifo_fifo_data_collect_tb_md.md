# fifo_data_collect_tb.py

Enhanced testbench for data collection module with multiple input channels and arbitration. This specialized testbench handles complex data collection FIFOs with multiple input channels, weighted round-robin arbitration, and sophisticated data aggregation patterns.

## Overview

The `DataCollectTB` class provides comprehensive verification for data collection FIFOs that aggregate data from multiple input channels into a single output stream. This testbench is designed for complex data collection systems with arbitration logic, multi-channel input management, and sophisticated scoreboard verification.

## Key Features

- **Multi-Channel Input Support**: Independent input channels (A, B, C, D) with individual control
- **Weighted Round-Robin Arbitration**: Advanced arbitration testing with fairness verification
- **Data Aggregation Verification**: Complex data collection and output stream verification
- **Enhanced Scoreboard**: Specialized scoreboard for multi-source data validation
- **Channel Isolation Testing**: Independent channel behavior verification
- **Performance Analysis**: Multi-channel throughput and efficiency metrics

## Class Definition

```python
class DataCollectTB(TBBase):
    """Enhanced testbench for data_collect module using FlexConfigGen only for randomization"""
```

## Constructor Parameters

```python
def __init__(self, dut, clock=None, reset=None, super_debug=True):
```

### Parameters
- **dut**: Device Under Test (DUT) object
- **clock**: Main system clock (optional, auto-detected if None)
- **reset**: System reset signal (optional, auto-detected if None)
- **super_debug**: Enable enhanced debug logging (default: True)

## Environment Configuration

### Multi-Channel Parameters
- `CHUNKS`: Number of data chunks per channel (default: 4)
- `DATA_WIDTH`: Data width per chunk in bits (default: 16)
- `ID_WIDTH`: ID field width in bits (default: 8)

### FIFO Configuration
- `OUTPUT_FIFO_DEPTH`: Output FIFO depth (default: 16)

### Channel Configuration
- `CHANNELS`: Input channels ('a', 'b', 'c', 'd')
- `CHANNEL_NAMES`: Channel names ('Channel A', 'Channel B', etc.)

## Architecture Overview

### Multi-Channel Input Architecture

```
┌─────────────┐    ┌─────────────────────┐    ┌─────────────┐
│  Channel A  │───▶│                     │    │             │
│   Master    │    │                     │    │             │
├─────────────┤    │   Data Collection   │    │   Output    │
│  Channel B  │───▶│      Module         │───▶│    FIFO     │
│   Master    │    │    (DUT with        │    │             │
├─────────────┤    │   Arbitration)      │    │             │
│  Channel C  │───▶│                     │    │             │
│   Master    │    │                     │    │             │
├─────────────┤    │                     │    │             │
│  Channel D  │───▶│                     │    │             │
│   Master    │    └─────────────────────┘    └─────────────┘
└─────────────┘
```

### Field Configuration

#### Input Field Configuration
Each input channel uses the same field structure:

```python
self.input_field_config.add_field(FieldDefinition(
    name='data',
    bits=self.DATA_WIDTH,
    default=0,
    format='hex',
    description='Data value'
))
```

#### Output Field Configuration
Output aggregates multiple data chunks plus ID:

```python
# Multiple data fields (data0, data1, data2, data3)
for i in range(self.CHUNKS):
    self.output_field_config.add_field(FieldDefinition(
        name=f'data{i}',
        bits=self.DATA_WIDTH,
        default=0,
        format='hex',
        description=f'Data{i} value'
    ))

# ID field for channel identification
self.output_field_config.add_field(FieldDefinition(
    name='id',
    bits=self.ID_WIDTH,
    default=0,
    format='hex',
    description='Channel ID value'
))
```

## Component Architecture

### Multi-Channel Masters

Each input channel has its own FIFO master:

```python
for i, (channel, channel_name) in enumerate(zip(self.channels, self.channel_names)):
    self.masters[channel_name] = FIFOMaster(
        dut=dut,
        title=f'Master {channel_name}',
        clock=self.clock,
        field_config=self.input_field_config,
        multi_sig=True,
        bus_name=channel,  # 'a', 'b', 'c', 'd'
        timeout_cycles=1000,
        mode='fifo_mux',
        super_debug=self.super_debug
    )
```

### Multi-Channel Monitors

Each input channel has dedicated monitoring:

```python
self.monitors[channel_name] = FIFOMonitor(
    dut=dut,
    title=f'Monitor {channel_name}',
    clock=self.clock,
    field_config=self.input_field_config,
    is_slave=False,  # Monitor input side
    multi_sig=True,
    bus_name=channel,
    mode='fifo_mux',
    super_debug=self.super_debug
)
```

### Output Components

**Output Slave**: Handles output data collection
**Output Monitor**: Monitors aggregated output stream
**Arbiter Monitor**: Specialized monitor for arbitration behavior

```python
self.arbiter_monitor = WeightedRoundRobinArbiterMonitor(
    dut=dut,
    clock=self.clock,
    channel_names=self.channel_names,
    log=self.log
)
```

## Specialized Scoreboard

### DataCollectScoreboard Features

The specialized scoreboard provides comprehensive multi-channel verification:

- **Channel-Specific Tracking**: Independent tracking for each input channel
- **Data Aggregation Verification**: Verification of data collection and aggregation
- **Order Verification**: Proper ordering verification across channels
- **Arbitration Verification**: Fairness and correctness of arbitration decisions
- **Performance Metrics**: Multi-channel performance analysis

### Scoreboard Architecture

```python
class DataCollectScoreboard:
    """Specialized scoreboard for data_collect module with enhanced field validation"""
    
    def __init__(self, channels, chunks, data_width, id_width):
        self.channels = channels
        self.expected_packets = {channel: deque() for channel in channels}
        self.received_packets = deque()
        self.channel_stats = {channel: {...} for channel in channels}
```

## Test Methods

### Multi-Channel Functional Tests

#### `test_multi_channel_input(packets_per_channel=50)`
Tests basic multi-channel input functionality.

**Purpose**: Verify independent channel operation and basic data collection
**Pattern**: Simultaneous traffic on all channels
**Verification**: Proper data collection from multiple sources

```python
await tb.test_multi_channel_input(packets_per_channel=100)
```

#### `test_channel_isolation(packets_per_channel=75)`
Tests isolation between input channels.

**Purpose**: Verify channel independence and isolation
**Pattern**: Sequential channel activation
**Verification**: No cross-channel interference

### Arbitration Tests

#### `test_arbiter_fairness(total_packets=400)`
Tests weighted round-robin arbitration fairness.

**Purpose**: Verify fair arbitration across all channels
**Pattern**: Equal traffic load across channels
**Verification**: Fair arbitration distribution

```python
await tb.test_arbiter_fairness(total_packets=500)
```

#### `test_weighted_arbitration(weights=[1, 2, 3, 4])`
Tests weighted arbitration with specific channel weights.

**Purpose**: Verify weighted arbitration behavior
**Pattern**: Traffic proportional to weights
**Verification**: Arbitration matches specified weights

### Stress Tests

#### `test_high_throughput_collection(duration_cycles=10000)`
High-throughput data collection testing.

**Purpose**: Maximum rate multi-channel data collection
**Pattern**: Continuous high-rate traffic on all channels
**Verification**: Data integrity under maximum load

#### `test_burst_traffic_patterns(burst_sizes=[10, 20, 50])`
Tests various burst patterns across channels.

**Purpose**: Burst traffic handling verification
**Pattern**: Coordinated burst sequences
**Verification**: Proper burst handling and arbitration

### Advanced Multi-Channel Tests

#### `test_coordinated_channel_patterns(pattern_count=200)`
Tests coordinated patterns across multiple channels.

**Purpose**: Complex multi-channel coordination verification
**Pattern**: Synchronized and phased channel patterns
**Verification**: Proper coordination and data aggregation

## Usage Examples

### Basic Multi-Channel Testing

```python
import cocotb
import os
from CocoTBFramework.tbclasses.fifo.fifo_data_collect_tb import DataCollectTB

@cocotb.test()
async def test_data_collect(dut):
    # Configure data collection parameters
    os.environ['CHUNKS'] = '4'
    os.environ['DATA_WIDTH'] = '16'
    os.environ['ID_WIDTH'] = '8'
    os.environ['OUTPUT_FIFO_DEPTH'] = '32'
    
    tb = DataCollectTB(dut, super_debug=True)
    await tb.initialize()
    
    # Basic multi-channel testing
    await tb.test_multi_channel_input(packets_per_channel=50)
    await tb.test_channel_isolation(packets_per_channel=30)
    
    tb.verify_results()
```

### Advanced Arbitration Testing

```python
@cocotb.test()
async def test_advanced_arbitration(dut):
    # Configure for arbitration testing
    os.environ['CHUNKS'] = '8'
    os.environ['DATA_WIDTH'] = '32'
    os.environ['ID_WIDTH'] = '16'
    
    tb = DataCollectTB(dut, super_debug=True)
    await tb.initialize()
    
    # Comprehensive arbitration testing
    await tb.test_arbiter_fairness(total_packets=800)
    await tb.test_weighted_arbitration(weights=[1, 2, 4, 8])
    await tb.test_burst_traffic_patterns(burst_sizes=[5, 15, 25])
    
    tb.verify_results()
```

### High-Performance Data Collection

```python
@cocotb.test()
async def test_high_perf_collection(dut):
    # Configure for maximum performance
    os.environ['CHUNKS'] = '16'
    os.environ['DATA_WIDTH'] = '64'
    os.environ['ID_WIDTH'] = '8'
    os.environ['OUTPUT_FIFO_DEPTH'] = '256'
    
    tb = DataCollectTB(dut, super_debug=False)  # Disable debug for performance
    await tb.initialize()
    
    # High-performance testing
    await tb.test_high_throughput_collection(duration_cycles=50000)
    await tb.test_coordinated_channel_patterns(pattern_count=1000)
    
    tb.verify_results()
```

## Multi-Channel Verification Features

### Channel-Specific Verification

**Individual Channel Integrity**: Per-channel data integrity verification
**Channel Independence**: Verification of channel isolation
**Channel Performance**: Individual channel throughput metrics
**Channel Arbitration**: Per-channel arbitration behavior analysis

### Aggregation Verification

**Data Collection Accuracy**: Verification of proper data aggregation
**Order Preservation**: Verification of proper ordering in output stream
**ID Assignment**: Verification of correct channel ID assignment
**Aggregation Performance**: Overall data collection efficiency

### Arbitration Analysis

**Fairness Metrics**: Quantitative fairness analysis
**Weight Compliance**: Verification of weighted arbitration behavior
**Arbitration Latency**: Arbitration decision timing analysis
**Throughput Impact**: Impact of arbitration on overall throughput

## Advanced Features

### Dynamic Channel Configuration

```python
async def test_dynamic_channels(self):
    # Enable/disable channels dynamically
    await self.enable_channels(['A', 'B'])
    await self.test_traffic_subset()
    
    await self.enable_channels(['C', 'D'])
    await self.test_channel_switching()
```

### Channel Priority Testing

```python
async def test_priority_scenarios(self):
    # Test various priority scenarios
    priorities = [
        {'A': 'high', 'B': 'medium', 'C': 'low', 'D': 'low'},
        {'A': 'low', 'B': 'high', 'C': 'medium', 'D': 'high'}
    ]
    
    for priority_config in priorities:
        await self.test_with_priorities(priority_config)
```

### Performance Profiling

```python
def generate_performance_report(self):
    """Generate comprehensive performance analysis"""
    return {
        'aggregate_throughput': self.calculate_aggregate_throughput(),
        'per_channel_throughput': self.calculate_channel_throughput(),
        'arbitration_efficiency': self.calculate_arbitration_efficiency(),
        'latency_metrics': self.calculate_latency_metrics(),
        'fairness_analysis': self.analyze_arbitration_fairness()
    }
```

## Integration with System Verification

### System-Level Testing

The data collection testbench integrates well with larger system verification:

- **Multi-Module Integration**: Integration with upstream data producers
- **System Performance**: End-to-end system performance verification
- **Protocol Compliance**: Protocol-specific data collection verification
- **Real-World Scenarios**: Realistic traffic pattern simulation

### Scalability

**Channel Scaling**: Easy addition of more input channels
**Performance Scaling**: Optimization for high-channel-count systems
**Complexity Management**: Modular approach for complex aggregation scenarios
**Resource Optimization**: Efficient resource usage for large-scale testing

This specialized testbench provides comprehensive verification capabilities for complex data collection systems, enabling thorough testing of multi-channel arbitration, data aggregation, and system-level performance characteristics.