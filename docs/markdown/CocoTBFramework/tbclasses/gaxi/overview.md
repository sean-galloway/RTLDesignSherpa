# GAXI Testbenches Overview

## Introduction

The GAXI (Generic AXI) testbench classes provide comprehensive verification environments for AXI-style interfaces and buffer designs. These testbenches leverage the GAXI components to create structured testing frameworks for different implementations, including standard buffers, skid buffers, field-based components, and multi-signal architectures. They enable systematic verification of data integrity, timing behavior, and protocol compliance across different operational modes and configurations.

## Architecture

The GAXI testbenches follow a layered architecture:

1. **Base Layer**: Common test infrastructure (TBBase)
2. **Component Layer**: GAXI-specific components (Master, Slave, Monitor)
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
│   GaxiBufferTB    │◄─────┐
└───────┬───────────┘      │
        │                  │
┌───────▼───────────┐      │
│GaxiFieldBufferTB  │      │ Derived Classes
└───────┬───────────┘      │
        │                  │
┌───────▼───────────┐      │
│GaxiMultiBufferTB  │◄─────┘
└───────────────────┘
```

## Core Testbench Classes

### GaxiBufferTB

The `GaxiBufferTB` class provides a base testbench for standard GAXI buffers. Key features:

- Support for both synchronous and asynchronous buffer designs
- Parameterized data width and buffer depth
- Standard data path testing with single field
- Incremental data pattern testing
- Comparison between write and read interfaces

```python
class GaxiBufferTB(TBBase):
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
        # Initialization with clock and reset signals
        # Setup based on environment variables
        # Component creation (master, slave, monitors)
```

### GaxiFieldBufferTB

The `GaxiFieldBufferTB` class extends the base testbench for field-based GAXI buffers. Key features:

- Support for multi-field data paths (addr, ctrl, data0, data1, etc.)
- Field configuration based testing
- Field-specific data integrity verification
- Sequence-based test pattern generation
- Enhanced field validation and error reporting

```python
class GaxiFieldBufferTB(TBBase):
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
        # Initialization with multi-field support
        # Field-specific components and configurations
```

### GaxiMultiBufferTB

The `GaxiMultiBufferTB` class provides testing for GAXI buffers with separate signals for different fields. Key features:

- Support for multi-signal interfaces (separate signals per field)
- Signal mapping for complex interfaces
- Enhanced error reporting with field comparison
- Support for various test sequences
- Comprehensive timing tests

```python
class GaxiMultiBufferTB(TBBase):
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
        # Initialization with multi-signal support
        # Signal mapping for separate field signals
```

### CDCHandshakeTB

The `CDCHandshakeTB` class provides specialized testing for Clock Domain Crossing (CDC) handshake designs. Key features:

- Support for dual clock domain testing
- Verification of CDC handshake protocols
- Memory model integration for data verification
- Transaction monitoring and timing validation
- Support for different test scenarios (basic, burst, random)

```python
class CDCHandshakeTB(TBBase):
    def __init__(self, dut):
        # Initialization with dual clock domains
        # Setup for CDC handshake verification
        # Transaction monitoring and timing validation
```

## Common Test Methods

All GAXI testbenches implement these core test methods:

### simple_incremental_loops

Tests the buffer with simple incremental data patterns.

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
    # Reset the buffer
    # Send incremental data packets
    # Verify received data matches sent data
```

### run_sequence_test

Tests the buffer with predefined sequences of test patterns.

```python
async def run_sequence_test(self, sequence, delay_key='fixed', delay_clks_after=5):
    """
    Run a test with the specified sequence.
    
    Args:
        sequence: GAXIBufferSequence to use for the test
        delay_key: Key for randomizer configuration
        delay_clks_after: Additional delay clocks after test
    """
    # Apply randomizer configurations
    # Reset and prepare for test
    # Generate and send sequence packets
    # Verify all packets are correctly received
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

## Sequence Generation

The `GAXIBufferSequence` class provides sophisticated test sequence generation:

```python
class GAXIBufferSequence:
    def __init__(self, name, field_config, packet_class=GAXIPacket):
        # Sequence initialization
    
    def add_walking_ones_pattern(self, delay=0):
        # Add walking ones bit pattern
        
    def add_alternating_patterns(self, count, delay=0):
        # Add alternating bit patterns
        
    def add_random_data_pattern(self, count, delay=0):
        # Add random data pattern
        
    def add_boundary_values(self, delay=0):
        # Add boundary value tests
```

## Configuration Approaches

### Environment Variables

GAXI testbenches use environment variables for configuration:

```python
# Parse environment variables
self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
self.TEST_WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '0'))
self.TEST_MODE = os.environ.get('TEST_MODE', 'skid')
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
self.write_master = GAXIMaster(
    dut, 'write_master', '', self.wr_clk,
    field_config=self.field_config,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=master_signal_map,
    optional_signal_map=master_optional_map,
    log=self.log
)

self.read_slave = GAXISlave(
    dut, 'read_slave', '', self.rd_clk,
    mode=self.TEST_MODE,
    field_config=self.field_config,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=slave_signal_map,
    optional_signal_map=slave_optional_map,
    log=self.log
)

# Set up monitors
self.wr_monitor = GAXIMonitor(
    dut, 'Write monitor', '', self.wr_clk,
    field_config=self.field_config,
    is_slave=False,
    signal_map=master_signal_map,
    optional_signal_map=master_optional_map,
    log=self.log
)

self.rd_monitor = GAXIMonitor(
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

### Data Verification Pattern

```python
# Compare packets for equality
if wr_pkt != rd_pkt:
    self.log.error(
        f"{msg}: Packet mismatch – WR: {wr_pkt.formatted(compact=True)} "
        f"vs RD: {rd_pkt.formatted(compact=True)}"
    )
    self.total_errors += 1
```

## Creating a New GAXI Testbench

To create a new GAXI testbench:

1. **Extend the Appropriate Base Class**:
   ```python
   class MyCustomGaxiTB(GaxiBufferTB):
       def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
           super().__init__(dut, wr_clk, wr_rstn, rd_clk, rd_rstn)
           # Custom initialization
   ```

2. **Add Custom Test Methods**:
   ```python
   async def my_custom_test(self, params):
       """Custom test for specific GAXI behavior"""
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
7. **Component Integration**: Leverage the GAXI component framework
8. **Sequence Generation**: Use predefined sequences for thorough testing
9. **Clock Domain Awareness**: For CDC testing, carefully manage clock domains

## Example Usage

```python
# Configure environment variables
os.environ['TEST_DEPTH'] = '16'
os.environ['TEST_WIDTH'] = '32'
os.environ['TEST_MODE'] = 'skid'

@cocotb.test()
async def test_gaxi_buffer(dut):
    # Create testbench
    tb = GaxiBufferTB(
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
```

## See Also

- [GAXI Components](../../components/gaxi/index.md) - GAXI component building blocks
- [TBBase](../tbbase.md) - Base class for all testbench components
- [Field Config](../../components/field_config.md) - Field configuration for packets

## Navigation

[↑ GAXI Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
