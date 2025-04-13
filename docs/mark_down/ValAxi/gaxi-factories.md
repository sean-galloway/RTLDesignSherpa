# GAXI Factories

## Overview

The `gaxi_factories.py` module provides a collection of factory functions that simplify the creation and configuration of GAXI components. These factories abstract away the complexity of component instantiation, providing a standardized way to create and connect GAXI components with consistent configuration.

## Key Features

- Simplified creation of GAXI masters, slaves, monitors, and scoreboards
- Consistent handling of field configurations
- Automatic memory model integration
- Signal mapping support for different interface types
- Creation of complete GAXI component sets with a single function call
- Default configurations for common use cases

## Factory Functions

### Field Configuration Factory

```python
def get_default_field_config(data_width=32):
    """
    Get field configuration for command-response protocol.

    Args:
        data_width: Data width in bits

    Returns:
        FieldConfig object for command-response protocol
    """
```

### Component Factories

```python
def create_gaxi_master(dut, title, prefix, clock, field_config=None,
                      randomizer=None, memory_model=None,
                      memory_fields=None, log=None, signal_map=None,
                      optional_signal_map=None, field_mode=False, multi_sig=False):
    """Create a GAXI Master component with configuration"""
    
def create_gaxi_slave(dut, title, prefix, clock, field_config=None, field_mode=False,
                     randomizer=None, memory_model=None,
                     memory_fields=None, log=None, mode='skid',
                     signal_map=None, optional_signal_map=None, multi_sig=False):
    """Create a GAXI Slave component with configuration"""
    
def create_gaxi_monitor(dut, title, prefix, clock, field_config=None, field_mode=False,
                       is_slave=False, log=None, mode='skid',
                       signal_map=None, optional_signal_map=None, multi_sig=False):
    """Create a GAXI Monitor component with configuration"""
    
def create_gaxi_scoreboard(name, field_config=None, log=None):
    """Create a GAXI Scoreboard with configuration"""
```

### Complete System Factory

```python
def create_gaxi_components(dut, clock, title_prefix="", field_config=None, field_mode=False,
                          memory_model=None, log=None,
                          mode='skid', signal_map=None, optional_signal_map=None, multi_sig=False):
    """
    Create a complete set of GAXI components (master, slave, monitors, scoreboard).
    
    Returns:
        Dictionary containing all created components
    """
```

## Usage Examples

### Basic Component Creation

```python
# Create a default field configuration
field_config = get_default_field_config(data_width=32)

# Create a master component
master = create_gaxi_master(
    dut, 'Master', '', dut.clk,
    field_config=field_config
)

# Create a slave component
slave = create_gaxi_slave(
    dut, 'Slave', '', dut.clk,
    field_config=field_config,
    mode='skid'
)

# Create monitors for master and slave sides
master_monitor = create_gaxi_monitor(
    dut, 'MasterMonitor', '', dut.clk,
    field_config=field_config,
    is_slave=False
)

slave_monitor = create_gaxi_monitor(
    dut, 'SlaveMonitor', '', dut.clk,
    field_config=field_config,
    is_slave=True
)

# Create a scoreboard
scoreboard = create_gaxi_scoreboard(
    'TestScoreboard',
    field_config=field_config
)
```

### Complete System Creation

```python
# Create all components in one call
components = create_gaxi_components(
    dut, dut.clk,
    title_prefix="Test",
    field_config=field_config,
    mode='skid'
)

# Access the created components
master = components['master']
slave = components['slave']
master_monitor = components['master_monitor']
slave_monitor = components['slave_monitor']
scoreboard = components['scoreboard']
memory_model = components['memory_model']

# Use the components
packet = GAXIPacket(field_config)
packet.data = 0x12345678
await master.send(packet)
```

### Custom Field Configuration

```python
# Create a custom field configuration
field_config = FieldConfig()
field_config.add_field_dict('addr', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Address value'
})
field_config.add_field_dict('data', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Data value'
})

# Create components with the custom field configuration
components = create_gaxi_components(
    dut, dut.clk,
    title_prefix="Custom",
    field_config=field_config
)
```

### Multi-Signal Mode

```python
# Create signal mappings for multi-signal mode
signal_map = {
    'm2s_valid': 'i_wr_valid',
    's2m_ready': 'o_wr_ready'
}
optional_signal_map = {
    'm2s_pkt_addr': 'i_wr_addr',
    'm2s_pkt_data': 'i_wr_data'
}

# Create components in multi-signal mode
components = create_gaxi_components(
    dut, dut.clk,
    title_prefix="MultiSig",
    field_config=field_config,
    multi_sig=True,
    signal_map=signal_map,
    optional_signal_map=optional_signal_map
)
```

### Memory Model Integration

```python
# Create a memory model
memory_model = MemoryModel(
    num_lines=1024,
    bytes_per_line=4
)

# Create components with memory integration
components = create_gaxi_components(
    dut, dut.clk,
    title_prefix="MemoryInteg",
    field_config=field_config,
    memory_model=memory_model
)

# Use the components with automatic memory handling
master = components['master']
packet = GAXIPacket(field_config)
packet.addr = 0x1000
packet.data = 0xABCDEF01
await master.send(packet)
```

### Different Operating Modes

```python
# Create components in fifo_flop mode
fifo_flop_components = create_gaxi_components(
    dut, dut.clk,
    title_prefix="FifoFlop",
    field_config=field_config,
    mode='fifo_flop'
)

# Create components in fifo_mux mode
fifo_mux_components = create_gaxi_components(
    dut, dut.clk,
    title_prefix="FifoMux",
    field_config=field_config,
    mode='fifo_mux'
)
```

### Custom Randomizers

```python
# Create a master randomizer
master_randomizer = FlexRandomizer({
    'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
})

# Create a slave randomizer
slave_randomizer = FlexRandomizer({
    'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
})

# Create master and slave with custom randomizers
master = create_gaxi_master(
    dut, 'MasterRand', '', dut.clk,
    field_config=field_config,
    randomizer=master_randomizer
)

slave = create_gaxi_slave(
    dut, 'SlaveRand', '', dut.clk,
    field_config=field_config,
    randomizer=slave_randomizer
)
```

## Creating a Complete Testbench

```python
# Create all components
components = create_gaxi_components(
    dut, dut.clk,
    title_prefix="TB",
    field_config=field_config
)

# Create a command handler
command_handler = GAXICommandHandler(
    components['master'],
    components['slave'],
    components['memory_model']
)

# Create a sequence
sequence = GAXISequence("test_sequence", field_config)
sequence.add_data_incrementing(count=10, data_start=0, data_step=1, delay=0)
sequence.add_walking_ones(data_width=32, delay=1)

# Start the command handler
await command_handler.start()

# Process the sequence
await command_handler.process_sequence(sequence)

# Add callbacks to the monitors
def master_callback(transaction):
    components['scoreboard'].add_expected(transaction)

def slave_callback(transaction):
    components['scoreboard'].add_actual(transaction)

components['master_monitor'].add_callback(master_callback)
components['slave_monitor'].add_callback(slave_callback)

# Check scoreboard results
result = components['scoreboard'].check_complete()
print(f"Scoreboard result: {'PASS' if result else 'FAIL'}")

# Stop the command handler
await command_handler.stop()
```

## Tips and Best Practices

1. **Factory Functions**: Use factory functions for consistent component creation
2. **Field Configurations**: Define field configurations once and reuse across components
3. **Memory Models**: Share the same memory model instance among components
4. **Signal Mapping**: Provide explicit signal mappings for clarity
5. **Component Sets**: Use create_gaxi_components for creating complete component sets
6. **Default Configurations**: Use get_default_field_config for simple cases
7. **Component Access**: Access components by key when using create_gaxi_components
8. **Mode Selection**: Choose the appropriate mode for your DUT implementation
9. **Random Generators**: Customize randomization behavior for specific test cases
10. **Component Prefixes**: Use title_prefix for clear component identification
