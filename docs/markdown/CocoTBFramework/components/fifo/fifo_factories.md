# FIFO Factories Documentation

## Overview

`fifo_factories.py` provides a comprehensive set of factory functions for creating and configuring FIFO components with consistent settings. These factories simplify test bench setup by providing standardized ways to create various FIFO components, ensuring proper signal mapping, memory integration, and component relationships.

## Key Factory Functions

### Component Creation

- **get_default_field_config(data_width=32, addr_width=0, ctrl_width=0)**:
  Get default field configuration for FIFO packets.
  
- **create_fifo_master(dut, title, prefix, clock, ...)**:
  Create a FIFO Master component with configuration.
  
- **create_fifo_slave(dut, title, prefix, clock, ...)**:
  Create a FIFO Slave component with configuration.
  
- **create_fifo_monitor(dut, title, prefix, clock, ...)**:
  Create a FIFO Monitor component with configuration.
  
- **create_fifo_scoreboard(name, field_config=None, log=None)**:
  Create a FIFO Scoreboard with configuration.
  
- **create_fifo_command_handler(master, slave, memory_model=None, log=None, fifo_capacity=8)**:
  Create a FIFO Command Handler for managing transactions.
  
- **create_enhanced_memory_model(num_lines, bytes_per_line=4, log=None, preset_values=None, debug=False)**:
  Create an enhanced memory model with improved diagnostics and boundary checking.

### Complete System Creation

- **create_fifo_components(dut, clock, title_prefix="", ...)**:
  Create a complete set of FIFO components (master, slave, monitors, scoreboard, command handler).

## Default Configurations

### Field Configuration

```python
DEFAULT_FIELD_CONFIG = {
    'data': {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data value'
    }
}
```

### Signal Maps

```python
# Master signal maps
DEFAULT_MASTER_SIGNAL_MAP = {
    'i_write': 'i_write',
    'o_wr_full': 'o_wr_full'
}

DEFAULT_MASTER_OPTIONAL_SIGNAL_MAP = {
    'i_wr_data': 'i_wr_data'
}

# Slave signal maps
DEFAULT_SLAVE_SIGNAL_MAP = {
    'o_rd_empty': 'o_rd_empty',
    'i_read': 'i_read'
}

DEFAULT_SLAVE_OPTIONAL_SIGNAL_MAP = {
    'o_rd_data': 'o_rd_data'
}

DEFAULT_SLAVE_MUX_OPTIONAL_SIGNAL_MAP = {
    'o_rd_data': 'ow_rd_data'
}
```

## Detailed Function Descriptions

### get_default_field_config()

```python
def get_default_field_config(data_width=32, addr_width=0, ctrl_width=0):
    """
    Get default field configuration for FIFO packets.

    Args:
        data_width: Data width in bits
        addr_width: Address width in bits (0 to exclude)
        ctrl_width: Control width in bits (0 to exclude)

    Returns:
        Field configuration dictionary or FieldConfig object
    """
```

This function creates a default field configuration object with specified field widths. It generates a configuration that includes:
- A `data` field with the specified width
- An optional `addr` field if addr_width > 0
- An optional `ctrl` field if ctrl_width > 0

### create_fifo_master()

```python
def create_fifo_master(dut, title, prefix, clock, field_config=None, field_mode=False,
                      randomizer=None, memory_model=None,
                      memory_fields=None, log=None, signal_map=None,
                      optional_signal_map=None, multi_sig=False):
    """
    Create a FIFO Master component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets
        field_mode: Whether to use field mode for data interpretation
        randomizer: Timing randomizer
        memory_model: Memory model for data storage
        memory_fields: Field mapping for memory operations
        log: Logger instance
        signal_map: Signal mapping for FIFO signals
        optional_signal_map: Optional signal mapping
        multi_sig: Whether to use multi-signal mode

    Returns:
        FIFOMaster instance
    """
```

This function creates and configures a FIFOMaster component with comprehensive options for signal mapping, field handling, and memory integration.

### create_fifo_slave()

```python
def create_fifo_slave(dut, title, prefix, clock, field_config=None, field_mode=False,
                     randomizer=None, memory_model=None,
                     memory_fields=None, log=None, mode='fifo_mux',
                     signal_map=None, optional_signal_map=None, multi_sig=False):
    """
    Create a FIFO Slave component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets
        field_mode: Whether to use field mode for data interpretation
        randomizer: Timing randomizer
        memory_model: Memory model for data storage
        memory_fields: Field mapping for memory operations
        log: Logger instance
        mode: Operating mode ('fifo_mux', 'fifo_flop')
        signal_map: Signal mapping for FIFO signals
        optional_signal_map: Optional signal mapping
        multi_sig: Whether to use multi-signal mode

    Returns:
        FIFOSlave instance
    """
```

This function creates and configures a FIFOSlave component with options for operating mode, signal mapping, and memory integration.

### create_fifo_monitor()

```python
def create_fifo_monitor(dut, title, prefix, clock, field_config=None, field_mode=False,
                       is_slave=False, log=None, mode='fifo_mux',
                       signal_map=None, optional_signal_map=None, multi_sig=False):
    """
    Create a FIFO Monitor component with configuration.

    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        field_config: Field configuration for packets
        field_mode: Whether to use field mode for data interpretation
        is_slave: If True, monitor read side; if False, monitor write side
        log: Logger instance
        mode: Operating mode ('fifo_mux', 'fifo_flop')
        signal_map: Signal mapping for FIFO signals
        optional_signal_map: Optional signal mapping
        multi_sig: Whether to use multi-signal mode

    Returns:
        FIFOMonitor instance
    """
```

This function creates a FIFOMonitor component that can monitor either the read (is_slave=True) or write (is_slave=False) side of a FIFO interface.

### create_fifo_scoreboard()

```python
def create_fifo_scoreboard(name, field_config=None, log=None):
    """
    Create a FIFO Scoreboard with configuration.

    Args:
        name: Scoreboard name
        field_config: Field configuration for packets
        log: Logger instance

    Returns:
        FIFOScoreboard instance
    """
```

This function creates a scoreboard component for validating FIFO transactions by comparing expected and actual values.

### create_fifo_command_handler()

```python
def create_fifo_command_handler(master, slave, memory_model=None, log=None, fifo_capacity=8):
    """
    Create a FIFO Command Handler for managing transactions between master and slave.
    
    Args:
        master: FIFOMaster instance
        slave: FIFOSlave instance
        memory_model: Optional memory model
        log: Logger instance
        fifo_capacity: FIFO capacity in entries for modeling
        
    Returns:
        FIFOCommandHandler instance
    """
```

This function creates a command handler to coordinate transactions between master and slave components with optional memory model integration.

### create_enhanced_memory_model()

```python
def create_enhanced_memory_model(num_lines, bytes_per_line=4, log=None, preset_values=None, debug=False):
    """
    Create an enhanced memory model with improved diagnostics and boundary checking.
    
    Args:
        num_lines: Number of memory lines
        bytes_per_line: Bytes per memory line
        log: Logger instance
        preset_values: Optional initial values for memory
        debug: Enable detailed debug logging
        
    Returns:
        EnhancedMemoryModel instance
    """
```

This function creates an enhanced memory model with robust error handling, boundary checking, and improved diagnostics.

### create_fifo_components()

```python
def create_fifo_components(dut, clock, title_prefix="", field_config=None, field_mode=False,
                         memory_model=None, log=None, mode='fifo_mux',
                         master_signal_map=None, master_optional_signal_map=None,
                         slave_signal_map=None, slave_optional_signal_map=None,
                         multi_sig=False, fifo_capacity=8):
    """
    Create a complete set of FIFO components (master, slave, monitors, scoreboard, command handler).

    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component titles
        field_config: Field configuration
        field_mode: Whether to use field mode
        memory_model: Memory model for data storage
        log: Logger instance
        mode: Operating mode for slave/monitor
        master_signal_map: Signal mapping for master port
        master_optional_signal_map: Optional signal mapping for master port
        slave_signal_map: Signal mapping for slave port
        slave_optional_signal_map: Optional signal mapping for slave port
        multi_sig: Whether to use multi-signal mode
        fifo_capacity: FIFO capacity in entries for modeling

    Returns:
        Dictionary containing all created components
    """
```

This function creates a complete set of FIFO components with consistent configuration, including:
- Master
- Slave
- Master monitor
- Slave monitor
- Scoreboard
- Command handler
- Memory model

## Usage Examples

### Basic Component Creation

```python
# Create a basic field configuration
field_config = get_default_field_config(data_width=32)

# Create a master component
master = create_fifo_master(
    dut, "FIFO1_Master", "", clock,
    field_config=field_config
)

# Create a slave component
slave = create_fifo_slave(
    dut, "FIFO1_Slave", "", clock,
    field_config=field_config,
    mode='fifo_mux'
)

# Create a command handler
handler = create_fifo_command_handler(
    master, slave, fifo_capacity=8
)
```

### Creating a Complete FIFO System

```python
# Create all components with a single call
components = create_fifo_components(
    dut, clock, "FIFO1_",
    field_config=field_config,
    mode='fifo_mux',
    fifo_capacity=8
)

# Access individual components
master = components['master']
slave = components['slave']
master_monitor = components['master_monitor']
slave_monitor = components['slave_monitor']
scoreboard = components['scoreboard']
command_handler = components['command_handler']
memory_model = components['memory_model']

# Start command handler
await command_handler.start()
```

### Creating Components with Custom Signal Mapping

```python
# Define custom signal maps
master_signal_map = {
    'i_write': 'my_write_sig',
    'o_wr_full': 'my_full_sig'
}

master_optional_signal_map = {
    'i_wr_data': 'my_wr_data'
}

slave_signal_map = {
    'o_rd_empty': 'my_empty_sig',
    'i_read': 'my_read_sig'
}

slave_optional_signal_map = {
    'o_rd_data': 'my_rd_data'
}

# Create components with custom signal mapping
components = create_fifo_components(
    dut, clock, "Custom_",
    field_config=field_config,
    master_signal_map=master_signal_map,
    master_optional_signal_map=master_optional_signal_map,
    slave_signal_map=slave_signal_map,
    slave_optional_signal_map=slave_optional_signal_map
)
```

### Creating Components with Memory Model

```python
# Create a memory model
memory_model = create_enhanced_memory_model(
    num_lines=8,
    bytes_per_line=4,
    debug=True
)

# Create components with shared memory
components = create_fifo_components(
    dut, clock, "Memory_",
    field_config=field_config,
    memory_model=memory_model
)

# Initialize memory with data
for i in range(8):
    addr = i * 4
    data = bytearray([i, i+1, i+2, i+3])
    memory_model.write(addr, data, 0xF)
```

### Creating Complex Field Configurations

```python
# Create a complex field configuration
field_config = get_default_field_config(
    data_width=32,
    addr_width=16,
    ctrl_width=8
)

# Create components with the complex configuration
components = create_fifo_components(
    dut, clock, "Complex_",
    field_config=field_config,
    multi_sig=True  # Use separate signals for each field
)
```

## Integration with Test Environments

The factory functions are designed to be used in CocoTB test environments:

```python
@cocotb.test()
async def test_fifo_basic(dut):
    """Test basic FIFO operation."""
    # Create clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Create FIFO components
    components = create_fifo_components(
        dut, dut.clk, "FIFO_Test_"
    )
    
    # Start command handler
    await components['command_handler'].start()
    
    # Send test transactions
    master = components['master']
    packet = FIFOPacket(components['master'].field_config)
    packet.data = 0x12345678
    await master.send(packet)
    
    # Wait for completion
    await ClockCycles(dut.clk, 10)
    
    # Check results
    stats = components['command_handler'].get_stats()
    assert stats['completed_transactions'] == 1
```

## Best Practices

1. **Use Factory Functions**: Always use the factory functions to ensure consistent component configuration
2. **Share Memory Models**: Use a single memory model for all components when appropriate
3. **Use Appropriate Defaults**: Leverage default configurations when possible
4. **Create Complete Systems**: Use `create_fifo_components()` for a complete test setup
5. **Customize Signal Maps**: Define custom signal maps to match your DUT
6. **Match Configurations**: Ensure field configurations match between components
7. **Use Appropriate Modes**: Select the correct mode ('fifo_mux', 'fifo_flop') for your FIFO implementation

## Navigation

[↑ FIFO Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
