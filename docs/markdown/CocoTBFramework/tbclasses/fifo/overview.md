# FIFO Testbenches Overview

## Introduction

The FIFO testbench classes provide comprehensive verification environments for First-In-First-Out buffer designs. These testbenches leverage the FIFO components to create structured test environments for different types of FIFO implementations, including synchronous FIFOs, skid buffers, field-based FIFOs, and multi-signal FIFOs. They enable systematic testing of FIFO functionality across various operational modes and configurations.

## Architecture

The FIFO testbenches follow a layered architecture:

1. **Base Layer**: Common test infrastructure (TBBase)
2. **Component Layer**: FIFO-specific components (Master, Slave, Monitor)
3. **Configuration Layer**: Field and randomization configuration
4. **Test Layer**: Specific test sequences and verification methods
5. **Reporting Layer**: Error detection and statistics collection

### Testbench Hierarchy

```
┌───────────────────┐
│    TBBase         │
└───────┬───────────┘
        │
┌───────▼───────────┐
│  FifoBufferTB     │◄─────┐
└───────┬───────────┘      │
        │                  │
┌───────▼───────────┐      │ Derived Classes
│FifoFieldBufferTB  │      │
└───────┬───────────┘      │
        │                  │
┌───────▼───────────┐      │
│FifoMultiBufferTB  │◄─────┘
└───────────────────┘
```

## Core Testbench Classes

### FifoBufferTB

The `FifoBufferTB` class provides a base testbench for standard FIFO buffers. Key features:

- Support for both synchronous and asynchronous FIFOs
- Parameterized data width and buffer depth
- Standard data path testing with single field
- Incremental data pattern testing
- Stress testing with varied data patterns

```python
class FifoBufferTB(TBBase):
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
        # Initialization with clock and reset signals
        # Setup based on environment variables
        # Component creation (master, slave, monitors)
```

### FifoFieldBufferTB

The `FifoFieldBufferTB` class extends the base testbench for field-based FIFOs. Key features:

- Support for multi-field data paths (addr, ctrl, data, etc.)
- Field configuration based testing
- Field-specific data integrity verification
- Dependency testing between fields
- Enhanced field validation and error reporting

```python
class FifoFieldBufferTB(TBBase):
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
        # Initialization with multi-field support
        # Field-specific components and configurations
```

### FifoMultiBufferTB

The `FifoMultiBufferTB` class provides testing for FIFOs with separate signals for different fields. Key features:

- Support for multi-signal interfaces (separate signals per field)
- Protocol error testing and detection
- Buffer state tracking and verification
- Enhanced error reporting with field comparison
- Dynamic test sequence generation

```python
class FifoMultiBufferTB(TBBase):
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
        # Initialization with multi-signal support
        # Signal mapping for separate field signals
```

## Common Test Methods

All FIFO testbenches implement these core test methods:

### simple_incremental_loops

Tests the FIFO with simple incremental data patterns.

```python
async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
    """
    Run simple incremental tests with different packet sizes.
    
    Args:
        count: Number of packets to send
        delay_key: Key for delay configuration
        delay_clks_after: Clock cycles to wait after test
    """
    # Set randomizers for timing control
    # Reset the FIFO
    # Send incremental data packets
    # Verify received data matches sent data
```

### stress_test_with_random_patterns

Tests the FIFO with complex random data patterns.

```python
async def stress_test_with_random_patterns(self, count=100, delay_key='constrained'):
    """
    Run a stress test with complex patterns to test FIFO buffering.
    
    Args:
        count: Number of packets to send
        delay_key: Key for delay configuration
    """
    # Generate various data patterns (walking ones, etc.)
    # Test with alternating bit patterns
    # Test with random values
    # Verify data integrity across all patterns
```

### compare_packets

Compares packets on write and read sides for verification.

```python
def compare_packets(self, msg, expected_count):
    """
    Compare packets captured by monitors.
    Logs any mismatches and updates self.total_errors.
    
    Args:
        msg: Message for error reporting
        expected_count: Expected number of packets
    """
    # Check packet counts match expectations
    # Compare each packet for field-by-field equality
    # Detailed error reporting for any mismatches
```

## Configuration Approaches

### Environment Variables

FIFO testbenches use environment variables for configuration:

```python
# Parse environment variables
self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '0'))
self.TEST_MODE = os.environ.get('TEST_MODE', 'fifo_mux')
self.TEST_KIND = os.environ.get('TEST_KIND', 'sync')
self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))
```

### Field Configurations

Field configurations define the packet structure:

```python
# Create field configuration
self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['field'])
self.field_config.update_field_width('addr', self.AW)
self.field_config.update_field_width('ctrl', self.CW)
self.field_config.update_field_width('data0', self.DW)
self.field_config.update_field_width('data1', self.DW)
```

### Randomization Configurations

Randomization configurations control timing behavior:

```python
RANDOMIZER_CONFIGS = {
    'fixed': {
        'write': {'valid_delay': ([[2, 2]], [1])},
        'read': {'ready_delay': ([[2, 2]], [1])}
    },
    'constrained': {
        'write': {'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])},
        'read': {'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])}
    },
    # Other configurations...
}
```

## Implementation Patterns

### Component Initialization Pattern

```python
# Create BFM components
self.write_master = FIFOMaster(
    dut, 'write_master', '', self.wr_clk,
    field_config=self.field_config,
    memory_model=self.memory_model,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=master_signal_map,
    optional_signal_map=master_optional_map,
    log=self.log
)

self.read_slave = FIFOSlave(
    dut, 'read_slave', '', self.rd_clk,
    mode=self.TEST_MODE,
    field_config=self.field_config,
    memory_model=self.memory_model,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=slave_signal_map,
    optional_signal_map=slave_optional_map,
    log=self.log
)

# Set up monitors
self.wr_monitor = FIFOMonitor(
    dut, 'Write monitor', '', self.wr_clk,
    field_config=self.field_config,
    is_slave=False,
    signal_map=master_signal_map,
    optional_signal_map=master_optional_map,
    log=self.log
)

self.rd_monitor = FIFOMonitor(
    dut, 'Read monitor', '', self.rd_clk,
    mode=self.TEST_MODE,
    field_config=self.field_config,
    is_slave=True,
    signal_map=slave_signal_map,
    optional_signal_map=slave_optional_map,
    log=self.log
)
```

### Reset Pattern

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

### Statistics Pattern

```python
def get_component_statistics(self):
    """Get statistics from all components for analysis"""
    stats = {
        'write_master': self.write_master.get_stats(),
        'read_slave': self.read_slave.get_stats(),
        'write_monitor': self.wr_monitor.get_stats(),
        'read_monitor': self.rd_monitor.get_stats(),
        'memory_model': self.memory_model.get_stats()
    }
    return stats
```

## Creating a New FIFO Testbench

To create a new FIFO testbench:

1. **Extend the Appropriate Base Class**:
   ```python
   class MyCustomFifoTB(FifoBufferTB):
       def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
           super().__init__(dut, wr_clk, wr_rstn, rd_clk, rd_rstn)
           # Custom initialization
   ```

2. **Add Custom Test Methods**:
   ```python
   async def my_custom_test(self, params):
       """Custom test for specific FIFO behavior"""
       # Reset and prepare
       await self.assert_reset()
       await self.wait_clocks(self.wr_clk_name, 10)
       await self.deassert_reset()
       
       # Custom test implementation
       # ...
       
       # Verify results
       self.compare_packets("Custom Test", expected_count)
   ```

3. **Implement Signal Mapping**:
   ```python
   # Map signals based on your DUT's interface
   master_signal_map = {
       'm2s_valid': 'your_valid_signal',
       's2m_ready': 'your_ready_signal'
   }
   
   master_optional_map = {
       'm2s_pkt_data': 'your_data_signal'
   }
   ```

4. **Configure Field Structure**:
   ```python
   # Define your packet structure
   field_config = FieldConfig()
   field_config.add_field_dict('your_field', {
       'bits': width,
       'default': 0,
       'format': 'hex'
   })
   ```

## Best Practices

1. **Clear Error Reporting**: Provide detailed error information for debugging
2. **Test Isolation**: Reset between tests to ensure clean state
3. **Statistics Collection**: Track and analyze component performance
4. **Memory Model Integration**: Use memory models for data verification
5. **Parameterization**: Make testbenches configurable via environment variables
6. **Randomization**: Use appropriate randomization for realistic testing
7. **Binary Representation**: Include binary representations in error messages
8. **Component Integration**: Leverage the FIFO component framework

## Example Usage

```python
# Configure environment variables
os.environ['TEST_DEPTH'] = '16'
os.environ['TEST_DATA_WIDTH'] = '32'
os.environ['TEST_MODE'] = 'fifo_mux'

@cocotb.test()
async def test_fifo(dut):
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
    
    # Check component statistics
    stats = tb.get_component_statistics()
    print(f"Test Statistics: {stats}")
```

## See Also

- [FIFO Components](../../components/fifo/index.md) - FIFO component building blocks
- [TBBase](../tbbase.md) - Base class for all testbench components
- [Field Config](../../components/field_config.md) - Field configuration for packets

## Navigation

[↑ FIFO Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
