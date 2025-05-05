# FIFO Buffer Testbench

## Overview

The `FifoBufferTB` class provides a base testbench for verifying FIFO buffer implementations. It supports testing of standard FIFO interfaces with single-field data, focusing on data integrity, proper handshaking, and timing behavior. The testbench includes comprehensive error detection and reporting, statistics collection, and support for different timing variations.

## Class Definition

```python
class FifoBufferTB(TBBase):
    """
    Testbench for FIFO buffer components with enhanced signal handling and robust error detection.
    """

    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
        """
        Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
            wr_clk: Write clock signal
            wr_rstn: Write reset signal (active low)
            rd_clk: Read clock signal (same as wr_clk for sync FIFOs)
            rd_rstn: Read reset signal (same as wr_rstn for sync FIFOs)
        """
        super().__init__(dut)
        
        # Gather the settings from the Parameters
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'fifo_mux')
        self.TEST_KIND = os.environ.get('TEST_KIND', 'sync')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))
```

## Key Features

- Support for both synchronous and asynchronous FIFOs
- Parameterized data width and buffer depth
- Flexible timing controls via randomization profiles
- Comprehensive data pattern verification
- Detailed error reporting with binary pattern display
- Memory model integration for data validation
- Monitor integration for transaction tracking
- Component statistics collection and analysis

## Primary Methods

### clear_interface

Clears all interface signals to default values.

```python
async def clear_interface(self):
    """Clear the interface signals"""
    await self.write_master.reset_bus()
    await self.read_slave.reset_bus()
```

### assert_reset / deassert_reset

Controls reset signals for the testbench.

```python
async def assert_reset(self):
    """Assert reset"""
    self.wr_rstn.value = 0
    if self.rd_rstn != self.wr_rstn:
        self.rd_rstn.value = 0
    await self.clear_interface()

async def deassert_reset(self):
    """Deassert reset"""
    self.wr_rstn.value = 1
    if self.rd_rstn != self.wr_rstn:
        self.rd_rstn.value = 1
    self.log.info("Reset complete")
```

### compare_packets

Compares packets captured by monitors to verify data integrity.

```python
def compare_packets(self, msg, expected_count):
    """
    Compare packets captured by monitors.
    Logs any mismatches and updates self.total_errors.
    
    Args:
        msg: Message for error reporting
        expected_count: Expected number of packets
    """
    # Check packet counts
    wr_mon_count = len(self.wr_monitor.observed_queue)
    rd_mon_count = len(self.rd_monitor.observed_queue)

    # Verify packet counts match expected count
    # ...

    # Compare packets
    while self.wr_monitor.observed_queue and self.rd_monitor.observed_queue:
        wr_pkt = self.wr_monitor.observed_queue.popleft()
        rd_pkt = self.rd_monitor.observed_queue.popleft()

        # Compare the two packets
        if wr_pkt != rd_pkt:
            self.log.error(
                f"{msg}: Packet mismatch – WR: {wr_pkt.formatted(compact=True)} "
                f"vs RD: {rd_pkt.formatted(compact=True)}"
            )
            self.total_errors += 1
```

### get_component_statistics

Collects statistics from all components for analysis.

```python
def get_component_statistics(self):
    """Get statistics from all components for analysis"""
    stats = {
        'write_master': self.write_master.get_stats(),
        'read_slave': self.read_slave.get_stats() if hasattr(self.read_slave, 'get_stats') else {},
        'write_monitor': self.wr_monitor.get_stats() if hasattr(self.wr_monitor, 'get_stats') else {},
        'read_monitor': self.rd_monitor.get_stats() if hasattr(self.rd_monitor, 'get_stats') else {},
        'memory_model': self.memory_model.get_stats() if hasattr(self.memory_model, 'get_stats') else {}
    }
    return stats
```

### simple_incremental_loops

Tests FIFO with incrementing data patterns.

```python
async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
    """
    Run simple incremental tests with different packet sizes.
    
    Args:
        count: Number of packets to send
        delay_key: Key for timing configuration
        delay_clks_after: Clock cycles to wait after test
    """
    # Choose the type of randomizer
    self.log.info(f'simple_incremental_loops({count=}, {delay_key=}, {delay_clks_after=}')
    self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))
    self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))

    # Reset and prepare for test
    await self.assert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    await self.deassert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)

    # Send packets with incrementing data
    for i in range(count):
        # Create packet
        data = i & self.MAX_DATA  # Mask data to avoid overflow
        packet = FIFOPacket(self.field_config)
        packet.data = data

        # Queue the packet for transmission
        await self.write_master.send(packet)

    # Wait for all packets to be transmitted
    # Wait for all packets to be received
    # Compare the packets
    # ...
```

### stress_test_with_random_patterns

Tests FIFO with complex data patterns.

```python
async def stress_test_with_random_patterns(self, count=100, delay_key='constrained'):
    """
    Run a stress test with more complex patterns to test FIFO buffering.
    
    Args:
        count: Number of packets to send
        delay_key: Key for timing configuration
    """
    self.log.info(f'Running stress test with {count} packets and delay profile {delay_key}')
    
    # Set randomizers for both components
    self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))
    self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))
    
    # Reset the environment
    await self.assert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    await self.deassert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    
    # Create varied test patterns
    patterns = []
    
    # Pattern 1: Walking ones
    # Pattern 2: Walking zeros
    # Pattern 3: Alternating bits
    # Pattern 4: Random values
    # ...
    
    # Send all patterns
    # Wait for all packets to be received
    # Compare the packets
    # ...
```

## Test Patterns

The testbench implements various data patterns for comprehensive testing:

1. **Incremental**: Sequential values to test basic operation
   ```python
   data = i & self.MAX_DATA  # i increments for each packet
   ```

2. **Walking Ones**: Single bit set in each position
   ```python
   for bit in range(min(32, self.DW)):
       patterns.append(1 << bit)
   ```

3. **Walking Zeros**: Single bit cleared in each position
   ```python
   all_ones = (1 << self.DW) - 1
   for bit in range(min(32, self.DW)):
       patterns.append(all_ones & ~(1 << bit))
   ```

4. **Alternating Bits**: Common patterns to test bit adjacency
   ```python
   patterns.extend([
       0x55555555 & self.MAX_DATA,  # 0101...
       0xAAAAAAAA & self.MAX_DATA,  # 1010...
       0x33333333 & self.MAX_DATA,  # 0011...
       0xCCCCCCCC & self.MAX_DATA,  # 1100...
   ])
   ```

5. **Random Values**: Random patterns for general coverage
   ```python
   patterns.append(random.randint(0, self.MAX_DATA))
   ```

## Component Setup

The testbench creates a complete verification environment:

```python
# Create field configuration
self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['standard'])
self.field_config.update_field_width('data', self.DW)

# Create enhanced memory model
self.memory_model = EnhancedMemoryModel(
    num_lines=self.TEST_DEPTH,
    bytes_per_line=self.DW // 8 or 1,
    log=self.log
)

# Set up signal mappings
master_signal_map = {
    'm2s_valid': 'i_wr_valid',
    's2m_ready': 'o_wr_ready'
}
master_optional_map = {
    'm2s_pkt_data': 'i_wr_data'
}
# ... similar mappings for slave

# Create BFM components
self.write_master = FIFOMaster(...)
self.read_slave = FIFOSlave(...)

# Set up monitors
self.wr_monitor = FIFOMonitor(...)
self.rd_monitor = FIFOMonitor(...)
```

## Error Reporting

The testbench provides detailed error reporting:

```python
if (wr_mon_count != rd_mon_count):
    self.log.error(
        f"Packet count mismatch: "
        f"{wr_mon_count} sent vs "
        f"{rd_mon_count} received"
    )
    self.total_errors += 1

# ...

if wr_pkt != rd_pkt:
    self.log.error(
        f"{msg}: Packet mismatch – WR: {wr_pkt.formatted(compact=True)} "
        f"vs RD: {rd_pkt.formatted(compact=True)}"
    )
    self.total_errors += 1
```

## Example Usage

Basic usage of the FIFO buffer testbench:

```python
from CocoTBFramework.tbclasses.fifo.fifo_buffer import FifoBufferTB

@cocotb.test()
async def test_fifo_buffer(dut):
    # Set environment variables
    os.environ['TEST_DEPTH'] = '16'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_MODE'] = 'fifo_mux'
    os.environ['TEST_KIND'] = 'sync'
    
    # Create testbench
    tb = FifoBufferTB(
        dut,
        wr_clk=dut.i_clk,
        wr_rstn=dut.i_rst_n,
        rd_clk=dut.i_clk,
        rd_rstn=dut.i_rst_n
    )
    
    # Run simple test
    await tb.simple_incremental_loops(
        count=32,
        delay_key='constrained',
        delay_clks_after=10
    )
    
    # Run stress test
    await tb.stress_test_with_random_patterns(
        count=100,
        delay_key='constrained'
    )
    
    # Check results
    assert tb.total_errors == 0, f"Test failed with {tb.total_errors} errors"
```

Using different timing profiles:

```python
# Test with fast back-to-back transfers
await tb.simple_incremental_loops(
    count=32,
    delay_key='backtoback',
    delay_clks_after=10
)

# Test with bursty traffic
await tb.simple_incremental_loops(
    count=32,
    delay_key='burst_pause',
    delay_clks_after=10
)

# Test with slow consumer
await tb.simple_incremental_loops(
    count=32,
    delay_key='slow_consumer',
    delay_clks_after=10
)
```

## Implementation Notes

- The testbench is configurable via environment variables
- Default signal mappings follow standard naming conventions
- Comprehensive error checking with detailed reporting
- Support for different delay profiles via randomization
- Complete verification environment with master, slave, and monitors
- Memory model integration for data validation
- Statistics collection for performance analysis
- Binary comparison for data mismatch debugging

## Environment Variables

The testbench configuration is controlled by these variables:

- **TEST_DEPTH**: FIFO buffer depth
- **TEST_DATA_WIDTH**: Width of data bus in bits
- **TEST_MODE**: FIFO read mode ('fifo_mux' or 'fifo_flop')
- **TEST_KIND**: FIFO synchronization ('sync' or 'async')
- **TEST_CLK_WR**: Write clock period
- **TEST_CLK_RD**: Read clock period

## See Also

- [FIFO Buffer Configs](fifo_buffer_configs.md) - Configuration definitions
- [FIFO Buffer Field](fifo_buffer_field.md) - Field-based FIFO testbench
- [FIFO Buffer Multi](fifo_buffer_multi.md) - Multi-signal FIFO testbench

## Navigation

[↑ FIFO Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
