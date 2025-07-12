# gaxi_buffer.py

Basic GAXI buffer testbench component using FlexConfigGen-only randomization. This testbench provides fundamental testing capabilities for GAXI buffer components with simplified architecture and enhanced performance.

## Overview

The `GaxiBufferTB` class provides comprehensive testing for basic GAXI buffer components, focusing on single data field operations with robust randomization and verification capabilities.

### Key Features
- **FlexConfigGen-only randomization** - Eliminated manual FlexRandomizer instantiation
- **Simplified randomizer management** with direct profile access
- **Single data field testing** for basic buffer operations
- **Sync/async operation support** with configurable clock domains
- **Memory model integration** for verification
- **Timeout protection** preventing infinite waits
- **Comprehensive error handling** and reporting

### Supported DUT Types
- `gaxi_fifo_sync`: Synchronous FIFO buffer implementation
- `gaxi_skid_buffer`: Skid buffer with flow control

## Class Definition

```python
class GaxiBufferTB(TBBase):
    """Testbench for GAXI buffer components using FlexConfigGen only for randomization"""
    
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
```

## Configuration Parameters

The testbench uses environment variables for flexible configuration:

### Required Environment Variables
```bash
export TEST_DEPTH=16           # Buffer depth
export TEST_DATA_WIDTH=32      # Data width in bits
export TEST_MODE=skid          # Buffer mode ('skid', 'fifo')
export TEST_KIND=sync          # Clock mode ('sync', 'async')
export TEST_CLK_WR=10          # Write clock period
export TEST_CLK_RD=10          # Read clock period
```

### Configuration Properties
- `TEST_DEPTH`: Buffer depth (affects completion timing)
- `TEST_DATA_WIDTH`: Data bus width (1-128 bits typically)
- `TEST_MODE`: Buffer implementation type
- `TEST_KIND`: Clock domain configuration
- `DW`: Data width (derived from TEST_DATA_WIDTH)
- `MAX_DATA`: Maximum data value (2^TEST_DATA_WIDTH - 1)
- `TIMEOUT_CYCLES`: Maximum wait cycles (default: 1000)

## Component Architecture

### FlexConfigGen Integration

The testbench uses FlexConfigGen for all randomization needs:

```python
# Create FlexConfigGen with data constraints
self.flex_config_gen = FlexConfigGen()

# Configure data randomization profiles
data_constraints = {
    'uniform': (0, self.MAX_DATA),
    'weighted': ([(0, 100), (100, self.MAX_DATA)], [0.3, 0.7]),
    'corner': ([0, 1, self.MAX_DATA-1, self.MAX_DATA], [0.25, 0.25, 0.25, 0.25])
}
```

### Signal Configuration

Automatic signal resolution with fallback options:

```python
# Clock and reset signal setup
self.wr_clk = wr_clk or dut.clk
self.wr_rstn = wr_rstn or dut.rstn
self.rd_clk = self.wr_clk if self.TEST_KIND == 'sync' else (rd_clk or dut.rd_clk)
self.rd_rstn = self.wr_rstn if self.TEST_KIND == 'sync' else (rd_rstn or dut.rd_rstn)
```

### Memory Model Integration

Built-in memory models for verification:

```python
# Memory models for input/output tracking
self.memory_model = MemoryModel(
    num_lines=max(16, self.TEST_DEPTH),
    bytes_per_line=1,  # Single data field
    log=self.log
)
```

## Core Testing Methods

### Basic Functionality Testing

```python
async def basic_test(self, num_packets=10):
    """
    Basic read/write functionality test
    
    Parameters:
    - num_packets: Number of packets to test (default: 10)
    """
```

**Test Flow**:
1. Initialize DUT and components
2. Generate random data packets using FlexConfigGen
3. Send packets through write interface
4. Receive packets from read interface
5. Verify data integrity using memory model
6. Report results and statistics

### Burst Testing

```python
async def burst_test(self, burst_size=8, num_bursts=5):
    """
    Burst operation testing
    
    Parameters:
    - burst_size: Number of packets per burst
    - num_bursts: Number of burst sequences
    """
```

**Test Capabilities**:
- Back-to-back packet transmission
- Burst boundary testing
- Flow control verification during bursts
- Buffer overflow/underflow detection

### Randomized Testing

```python
async def random_test(self, num_packets=50, profile='uniform'):
    """
    Randomized data pattern testing
    
    Parameters:
    - num_packets: Number of random packets
    - profile: Randomization profile ('uniform', 'weighted', 'corner')
    """
```

**Randomization Features**:
- Multiple randomization profiles
- Configurable data distributions
- Corner case emphasis
- Constraint-based generation

## Verification Capabilities

### Data Integrity Verification

```python
def verify_packet(self, sent_packet, received_packet):
    """
    Verify packet data integrity
    
    Returns: (success: bool, details: str)
    """
    if sent_packet.data != received_packet.data:
        return False, f"Data mismatch: sent=0x{sent_packet.data:X}, received=0x{received_packet.data:X}"
    return True, "Packet verified successfully"
```

### Protocol Compliance Checking

- **Handshake Validation**: Valid/ready protocol compliance
- **Signal State Validation**: X/Z detection and reporting
- **Timing Validation**: Setup/hold requirements
- **Flow Control**: Backpressure handling verification

### Performance Monitoring

```python
def get_performance_stats(self):
    """Get comprehensive performance statistics"""
    return {
        'packets_sent': self.total_packets_sent,
        'packets_received': self.total_packets_received,
        'throughput': self.calculate_throughput(),
        'latency_avg': self.calculate_average_latency(),
        'errors': self.total_errors
    }
```

## Usage Examples

### Basic Test Setup

```python
import cocotb
import os
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer import GaxiBufferTB

@cocotb.test()
async def test_basic_buffer(dut):
    # Configure test environment
    os.environ['TEST_DEPTH'] = '16'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_MODE'] = 'skid'
    os.environ['TEST_KIND'] = 'sync'
    
    # Create and initialize testbench
    tb = GaxiBufferTB(dut, wr_clk=dut.clk, wr_rstn=dut.rstn)
    await tb.initialize()
    
    # Run basic functionality test
    await tb.basic_test(num_packets=50)
    
    # Get test results
    stats = tb.get_performance_stats()
    tb.log.info(f"Test completed: {stats}")
```

### Advanced Test Configuration

```python
@cocotb.test()
async def test_advanced_buffer(dut):
    # Advanced configuration
    os.environ['TEST_DEPTH'] = '32'
    os.environ['TEST_DATA_WIDTH'] = '64'
    os.environ['TEST_MODE'] = 'fifo'
    os.environ['TEST_KIND'] = 'async'
    os.environ['TEST_CLK_WR'] = '8'
    os.environ['TEST_CLK_RD'] = '12'
    
    # Create testbench with separate clocks
    tb = GaxiBufferTB(
        dut,
        wr_clk=dut.wr_clk,
        wr_rstn=dut.wr_rstn,
        rd_clk=dut.rd_clk,
        rd_rstn=dut.rd_rstn
    )
    await tb.initialize()
    
    # Run comprehensive test suite
    await tb.burst_test(burst_size=16, num_bursts=10)
    await tb.random_test(num_packets=100, profile='corner')
    
    # Verify final state
    assert tb.total_errors == 0, f"Test failed with {tb.total_errors} errors"
```

### Custom Randomization

```python
@cocotb.test()
async def test_custom_patterns(dut):
    os.environ['TEST_DEPTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '16'
    
    tb = GaxiBufferTB(dut, wr_clk=dut.clk, wr_rstn=dut.rstn)
    await tb.initialize()
    
    # Custom data patterns
    custom_patterns = [0x0000, 0xFFFF, 0x5555, 0xAAAA, 0x1234]
    
    # Send custom patterns
    for pattern in custom_patterns:
        packet = tb.create_packet(data=pattern)
        await tb.send_packet(packet)
        received = await tb.receive_packet()
        success, details = tb.verify_packet(packet, received)
        assert success, details
    
    tb.log.info("Custom pattern test completed successfully")
```

## Error Handling and Recovery

### Timeout Protection

```python
async def wait_for_condition(self, condition_func, timeout_cycles=None):
    """
    Wait for condition with timeout protection
    
    Parameters:
    - condition_func: Function returning True when condition met
    - timeout_cycles: Maximum wait cycles (default: self.TIMEOUT_CYCLES)
    """
    timeout = timeout_cycles or self.TIMEOUT_CYCLES
    for cycle in range(timeout):
        if condition_func():
            return True
        await RisingEdge(self.wr_clk)
    
    self.log.error(f"Timeout waiting for condition after {timeout} cycles")
    return False
```

### Error Recovery

- **Signal Cleanup**: Automatic reset of control signals after errors
- **State Recovery**: Return to known good state after failures
- **Graceful Degradation**: Continue testing after non-fatal errors
- **Comprehensive Reporting**: Detailed error context and statistics

## Performance Optimizations

### Key Improvements

- **40% faster data collection** through cached signal references
- **30% faster data driving** through optimized signal updates
- **Reduced memory overhead** with efficient data structures
- **FlexConfigGen integration** eliminates manual randomizer management

### Caching Mechanisms

```python
def _cache_signal_references(self):
    """Cache frequently accessed signal references"""
    self._cached_signals = {
        'valid': getattr(self.dut, f'{self.prefix}valid', None),
        'ready': getattr(self.dut, f'{self.prefix}ready', None),
        'data': getattr(self.dut, f'{self.prefix}data', None)
    }
```

## Integration Points

### Framework Integration

- **TBBase inheritance** for common testbench functionality
- **Component factory support** for automated setup
- **Statistics aggregation** with framework reporting
- **Utility integration** for path management and tool support

### External Tool Integration

- **Waveform capture** for debug visualization
- **Log file integration** for comprehensive debugging
- **Multiple simulator support** (VCS, Questasim, Xcelium)
- **Coverage integration** for metrics collection

## Best Practices

### Test Organization

1. **Environment Setup**: Configure all parameters before testbench creation
2. **Initialization**: Proper component initialization and signal setup
3. **Test Execution**: Run tests in logical progression (basic → advanced)
4. **Verification**: Comprehensive result checking and error handling
5. **Cleanup**: Proper resource cleanup and final reporting

### Performance Considerations

- Use appropriate buffer depths for testing requirements
- Configure timeout values based on system characteristics
- Monitor memory usage in long-running tests
- Leverage caching for frequently accessed signals

### Debug Strategies

- Enable detailed logging for complex issues
- Use waveform capture for timing analysis
- Implement custom verification callbacks for specific scenarios
- Monitor statistics for performance bottleneck identification

The `gaxi_buffer.py` component provides a solid foundation for GAXI buffer testing with modern framework integration, comprehensive verification capabilities, and optimized performance characteristics.