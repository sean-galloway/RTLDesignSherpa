<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# fifo_buffer_multi.py

Multi-signal FIFO buffer testbench for parallel data paths and complex signal interfaces. This testbench handles FIFOs with multiple parallel signals and enhanced signal management capabilities.

## Overview

The `FifoMultiBufferTB` class provides verification for FIFOs with multiple parallel signal interfaces. This testbench is designed for FIFOs that handle wide data buses, parallel processing paths, or complex signal structures that require simultaneous multi-signal operations.

## Key Features

- **Multi-Signal Interface Support**: Parallel signal path management
- **Enhanced Signal Monitoring**: Comprehensive multi-signal observation
- **Parallel Data Path Verification**: Simultaneous multi-path data integrity
- **Advanced Memory Modeling**: Multi-region memory management for parallel paths
- **Sophisticated Randomization**: Multi-signal coordinated randomization patterns

## Class Definition

```python
class FifoMultiBufferTB(TBBase):
    """Testbench for multi-signal FIFO components using FlexConfigGen only for randomization"""
```

## Constructor Parameters

```python
def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None, super_debug=True):
```

### Parameters
- **dut**: Device Under Test (DUT) object
- **wr_clk**: Write clock signal (optional, auto-detected if None)
- **wr_rstn**: Write reset signal (optional, auto-detected if None)
- **rd_clk**: Read clock signal (optional, auto-detected if None)
- **rd_rstn**: Read reset signal (optional, auto-detected if None)
- **super_debug**: Enable enhanced debug logging (default: True)

## Environment Configuration

Extended configuration for multi-signal operations:

### Multi-Signal Parameters
- `TEST_ADDR_WIDTH`: Address signal width in bits (required)
- `TEST_CTRL_WIDTH`: Control signal width in bits (required)
- `TEST_DATA_WIDTH`: Data signal width in bits (required)

### Core Parameters
- `TEST_DEPTH`: FIFO depth (required)
- `TEST_MODE`: Operation mode ('fifo_mux', 'fifo_simple') (default: 'fifo_mux')
- `TEST_KIND`: Clock domain type ('sync', 'async') (default: 'sync')

### Clock Configuration
- `TEST_CLK_WR`: Write clock period in ns (default: 10)
- `TEST_CLK_RD`: Read clock period in ns (default: 10)

### Test Control
- `SEED`: Random seed for reproducible tests (default: 12345)

## Multi-Signal Architecture

### Signal Interface Structure

The testbench manages multiple parallel signals simultaneously:

**Write Side Signals:**
- `write`: Write enable
- `addr`: Address signal bus
- `ctrl`: Control signal bus
- `data0`: First data signal bus
- `data1`: Second data signal bus
- `full`: FIFO full indication

**Read Side Signals:**
- `read`: Read enable
- `addr`: Address signal bus
- `ctrl`: Control signal bus
- `data0`: First data signal bus
- `data1`: Second data signal bus
- `empty`: FIFO empty indication

### Field Configuration

Multi-signal field configuration using `FIELD_CONFIGS['field']`:

```python
self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['field'])
self.field_config.update_field_width('addr', self.AW)
self.field_config.update_field_width('ctrl', self.CW)
self.field_config.update_field_width('data0', self.DW)
self.field_config.update_field_width('data1', self.DW)
```

## Memory Model Architecture

### Multi-Region Memory Management

The testbench creates specialized memory regions for parallel signal tracking:

```python
self.memory_model.define_region('addr_signals', 0, TEST_DEPTH // 4 - 1, 'Address signals')
self.memory_model.define_region('ctrl_signals', TEST_DEPTH // 4, TEST_DEPTH // 2 - 1, 'Control signals')
self.memory_model.define_region('data_signals', TEST_DEPTH // 2, TEST_DEPTH - 1, 'Data signals')
```

### Benefits
- **Parallel Tracking**: Independent tracking of each signal type
- **Performance Analysis**: Per-signal performance metrics
- **Debug Enhancement**: Signal-specific error detection
- **Memory Efficiency**: Optimized memory usage for multi-signal data

## Component Architecture

### Multi-Signal BFM Components

**Write Master with Multi-Signal Support:**
```python
self.write_master = FIFOMaster(
    dut=dut,
    clock=self.wr_clk,
    field_config=self.field_config,
    multi_sig=True,  # Enable multi-signal mode
    timeout_cycles=self.TIMEOUT_CYCLES,
    mode=self.TEST_MODE
)
```

**Read Slave with Multi-Signal Support:**
```python
self.read_slave = FIFOSlave(
    dut=dut,
    clock=self.rd_clk,
    field_config=self.field_config,
    multi_sig=True,  # Enable multi-signal mode
    timeout_cycles=self.TIMEOUT_CYCLES,
    mode=self.TEST_MODE
)
```

### Multi-Signal Monitoring

**Write Side Monitor:**
- Monitors all write-side signals simultaneously
- Captures multi-signal transactions
- Provides parallel signal analysis

**Read Side Monitor:**
- Monitors all read-side signals simultaneously
- Captures multi-signal transactions
- Provides parallel signal verification

## Test Methods

### Multi-Signal Functional Tests

#### `test_parallel_signals(packet_count=100)`
Tests parallel signal operation and coordination.

**Purpose**: Verify simultaneous multi-signal operation
**Pattern**: Coordinated multi-signal patterns
**Verification**: Parallel signal integrity and timing

```python
await tb.test_parallel_signals(packet_count=100)
```

#### `test_signal_independence(packet_count=200)`
Tests independence of parallel signal paths.

**Purpose**: Verify signal path isolation
**Pattern**: Independent signal variations
**Verification**: Cross-signal interference detection

### Signal Coordination Tests

#### `test_coordinated_traffic(packet_count=300)`
Tests coordinated multi-signal traffic patterns.

**Purpose**: Verify complex signal coordination
**Pattern**: Synchronized multi-signal sequences
**Verification**: Multi-signal timing and data integrity

#### `test_signal_burst_patterns(packet_count=500)`
Tests burst patterns across multiple signals.

**Purpose**: High-throughput multi-signal testing
**Pattern**: Burst sequences on parallel signals
**Verification**: Burst handling and data integrity

### Advanced Multi-Signal Tests

#### `test_randomized_multi_signals(packet_count=800, profile='balanced')`
Randomized testing across all signal paths.

**Purpose**: Comprehensive multi-signal randomization
**Randomization**: Coordinated random patterns across signals
**Verification**: Complex multi-signal pattern validation

```python
await tb.test_randomized_multi_signals(packet_count=500, profile='aggressive')
```

#### `test_signal_stress_patterns(packet_count=1000)`
Stress testing with intensive multi-signal patterns.

**Purpose**: Maximum load multi-signal testing
**Pattern**: High-frequency multi-signal operations
**Verification**: Stress condition signal integrity

## Usage Examples

### Basic Multi-Signal Testing

```python
import cocotb
import os
from CocoTBFramework.tbclasses.fifo.fifo_buffer_multi import FifoMultiBufferTB

@cocotb.test()
async def test_multi_signal_fifo(dut):
    # Configure multi-signal parameters
    os.environ['TEST_ADDR_WIDTH'] = '16'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_DEPTH'] = '64'
    
    tb = FifoMultiBufferTB(dut, super_debug=True)
    await tb.initialize()
    
    # Multi-signal testing
    await tb.test_parallel_signals(packet_count=100)
    await tb.test_signal_independence(packet_count=150)
    
    tb.verify_results()
```

### Advanced Multi-Signal Configuration

```python
@cocotb.test()
async def test_advanced_multi_signal(dut):
    # Configure for wide parallel interface
    os.environ['TEST_ADDR_WIDTH'] = '32'
    os.environ['TEST_CTRL_WIDTH'] = '16'
    os.environ['TEST_DATA_WIDTH'] = '128'
    os.environ['TEST_DEPTH'] = '256'
    os.environ['TEST_MODE'] = 'fifo_mux'
    
    tb = FifoMultiBufferTB(dut, super_debug=True)
    await tb.initialize()
    
    # Comprehensive multi-signal testing
    await tb.test_coordinated_traffic(packet_count=200)
    await tb.test_signal_burst_patterns(packet_count=300)
    await tb.test_randomized_multi_signals(packet_count=500, profile='balanced')
    await tb.test_signal_stress_patterns(packet_count=400)
    
    tb.verify_results()
```

### High-Performance Multi-Signal Testing

```python
@cocotb.test()
async def test_high_perf_multi_signal(dut):
    # Configure for maximum throughput
    os.environ['TEST_ADDR_WIDTH'] = '64'
    os.environ['TEST_CTRL_WIDTH'] = '32'
    os.environ['TEST_DATA_WIDTH'] = '512'
    os.environ['TEST_DEPTH'] = '1024'
    os.environ['TEST_CLK_WR'] = '5'   # 200 MHz
    os.environ['TEST_CLK_RD'] = '5'   # 200 MHz
    
    tb = FifoMultiBufferTB(dut, super_debug=False)  # Disable debug for performance
    await tb.initialize()
    
    # High-performance testing
    await tb.test_maximum_throughput_multi_signal()
    await tb.test_sustained_burst_traffic()
    await tb.test_parallel_bandwidth_utilization()
    
    tb.verify_results()
```

## Multi-Signal Verification Features

### Parallel Signal Verification

**Signal Coordination**: Verify proper signal timing relationships
**Data Coherency**: Ensure data consistency across parallel signals
**Signal Independence**: Verify isolation between signal paths
**Timing Verification**: Check setup/hold times for multi-signal operations

### Advanced Multi-Signal Analysis

**Parallel Bandwidth**: Calculate aggregate bandwidth across signals
**Signal Utilization**: Measure individual signal path efficiency
**Coordination Efficiency**: Analyze multi-signal coordination overhead
**Parallel Performance**: Overall multi-signal system performance

### Debug and Analysis Features

**Multi-Signal Tracing**: Complete trace of all parallel signals
**Signal Correlation**: Cross-signal timing and data analysis
**Parallel Error Detection**: Multi-signal error detection and isolation
**Performance Profiling**: Per-signal and aggregate performance metrics

## Multi-Signal Patterns

### Synchronized Pattern
All signals operate in perfect synchronization:

```python
for i in range(packet_count):
    packet = FIFOPacket(field_config)
    packet.addr = sync_addr_pattern[i]
    packet.ctrl = sync_ctrl_pattern[i]
    packet.data0 = sync_data0_pattern[i]
    packet.data1 = sync_data1_pattern[i]
    await master.send(packet)
```

### Independent Pattern
Each signal operates independently:

```python
async def drive_independent_signals():
    # Drive each signal independently
    await asyncio.gather(
        drive_addr_pattern(),
        drive_ctrl_pattern(),
        drive_data0_pattern(),
        drive_data1_pattern()
    )
```

### Coordinated Burst Pattern
Coordinated bursts across multiple signals:

```python
for burst in burst_sequences:
    for packet in burst:
        await master.send(packet)
    await wait_clocks(burst_gap)
```

## Performance Considerations

### Parallel Processing Benefits

**Increased Bandwidth**: Multiple signal paths provide higher aggregate bandwidth
**Parallel Operations**: Simultaneous processing across signal paths
**Scalability**: Easy scaling by adding more signal paths
**Efficiency**: Better resource utilization through parallelism

### Multi-Signal Challenges

**Synchronization Complexity**: Coordinating multiple signals requires careful timing
**Debug Complexity**: Multi-signal issues can be harder to isolate
**Resource Usage**: More signals require more verification resources
**Timing Closure**: Multiple signals may complicate timing analysis

## Integration with Other Testbenches

The multi-signal testbench serves as the foundation for:

- **fifo_buffer_multi_sigmap.py**: Adds signal mapping capabilities
- **High-bandwidth applications**: Multiple data stream processing
- **Parallel protocol handling**: Multiple protocol streams
- **Complex interface verification**: Multi-interface FIFO systems

This multi-signal approach enables verification of complex FIFO designs while providing the infrastructure for even more sophisticated multi-signal verification scenarios.