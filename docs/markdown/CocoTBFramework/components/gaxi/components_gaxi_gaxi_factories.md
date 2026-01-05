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

# gaxi_factories.py

Updated GAXI factories with fixed parameter handling to match TB instantiation patterns. This module provides simplified factory functions for creating GAXI components with proper defaults and consistent parameter handling across all factory methods.

## Overview

The `gaxi_factories.py` module provides factory functions for creating GAXI components (Master, Slave, Monitor, Scoreboard) with simplified configuration and proper parameter defaults. All existing APIs are preserved and parameters are passed through exactly as before, with enhanced defaults for signal prefixes and naming.

### Key Features
- **Simplified component creation** with sensible defaults
- **Consistent parameter handling** across all factories
- **Backward compatibility** - all existing parameters preserved
- **Enhanced defaults** for signal prefixes (empty strings work for most cases)
- **Memory model integration** using base MemoryModel directly
- **Complete system creation** with factory methods for full environments

## Field Configuration

### `get_default_field_config(data_width=32)`

Get standard field configuration for GAXI protocol.

**Parameters:**
- `data_width`: Data width in bits (default: 32)

**Returns:** FieldConfig object for standard data field

```python
# Get default 32-bit data configuration
config = get_default_field_config()

# Get 64-bit data configuration
config_64 = get_default_field_config(data_width=64)
```

## Component Factories

### `create_gaxi_master()`

Create a GAXI Master component with simplified configuration.

```python
create_gaxi_master(dut, title, prefix, clock, field_config=None, packet_class=None,
                   randomizer=None, memory_model=None, memory_fields=None, log=None,
                   signal_map=None, optional_signal_map=None, field_mode=False,
                   multi_sig=False, mode='skid', bus_name='', pkt_prefix='',
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title
- `prefix`: Signal prefix
- `clock`: Clock signal
- `field_config`: Field configuration (default: standard data field)
- `packet_class`: Packet class to use
- `randomizer`: Timing randomizer (default: standard master constraints)
- `memory_model`: Memory model for transactions (optional)
- `memory_fields`: Field mapping for memory operations (unused - kept for compatibility)
- `log`: Logger instance (default: dut's logger)
- `signal_map`: Signal mapping (unused - kept for compatibility)
- `optional_signal_map`: Optional signal mapping (unused - kept for compatibility)
- `field_mode`: Field mode (unused - kept for compatibility)
- `multi_sig`: Whether using multi-signal mode
- `mode`: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `**kwargs`: Additional arguments

**Returns:** GAXIMaster instance

```python
# Basic master creation
master = create_gaxi_master(
    dut=dut,
    title="TestMaster",
    prefix="master_",
    clock=dut.clk
)

# Advanced master with custom configuration
master = create_gaxi_master(
    dut=dut,
    title="AdvancedMaster",
    prefix="",
    clock=dut.clk,
    field_config=custom_field_config,
    memory_model=shared_memory,
    multi_sig=True,
    mode='fifo_flop',
    log=custom_logger
)
```

### `create_gaxi_slave()`

Create a GAXI Slave component with simplified configuration.

```python
create_gaxi_slave(dut, title, prefix, clock, field_config=None, field_mode=False,
                  packet_class=None, randomizer=None, memory_model=None,
                  memory_fields=None, log=None, mode='skid', signal_map=None,
                  optional_signal_map=None, multi_sig=False, bus_name='',
```

**Parameters:** Same as `create_gaxi_master()` with slave-specific defaults

**Returns:** GAXISlave instance

```python
# Basic slave creation
slave = create_gaxi_slave(
    dut=dut,
    title="TestSlave",
    prefix="slave_",
    clock=dut.clk
)

# Slave with shared memory model
slave = create_gaxi_slave(
    dut=dut,
    title="MemorySlave",
    prefix="",
    clock=dut.clk,
    memory_model=shared_memory,
    mode='skid'
)
```

### `create_gaxi_monitor()`

Create a GAXI Monitor component with simplified configuration.

```python
create_gaxi_monitor(dut, title, prefix, clock, field_config=None, is_slave=False,
                    log=None, mode='skid', multi_sig=False, bus_name='',
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title
- `prefix`: Signal prefix
- `clock`: Clock signal
- `field_config`: Field configuration (default: standard data field)
- `is_slave`: If True, monitor slave side; if False, monitor master side
- `log`: Logger instance (default: dut's logger)
- `mode`: Operating mode ('skid', 'fifo_mux', 'fifo_flop')
- `multi_sig`: Whether using multi-signal mode
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `**kwargs`: Additional arguments

**Returns:** GAXIMonitor instance

```python
# Master-side monitor
master_monitor = create_gaxi_monitor(
    dut=dut,
    title="MasterMonitor",
    prefix="",
    clock=dut.clk,
    is_slave=False
)

# Slave-side monitor
slave_monitor = create_gaxi_monitor(
    dut=dut,
    title="SlaveMonitor",
    prefix="",
    clock=dut.clk,
    is_slave=True,
    mode='fifo_flop'
)
```

### `create_gaxi_scoreboard()`

Create a GAXI Scoreboard with simplified configuration.

```python
create_gaxi_scoreboard(name, field_config=None, log=None)
```

**Parameters:**
- `name`: Scoreboard name
- `field_config`: Field configuration (default: standard data field)
- `log`: Logger instance

**Returns:** GAXIScoreboard instance

```python
# Basic scoreboard
scoreboard = create_gaxi_scoreboard("TestScoreboard")

# Scoreboard with custom configuration
scoreboard = create_gaxi_scoreboard(
    name="CustomScoreboard",
    field_config=custom_field_config,
    log=custom_logger
)
```

## System Creation Factories

### `create_gaxi_components()`

Create a complete set of GAXI components (master, slave, monitors, scoreboard).

```python
create_gaxi_components(dut, clock, title_prefix="", field_config=None,
                       field_mode=False, packet_class=None, memory_model=None,
                       log=None, mode='skid', signal_map=None, optional_signal_map=None,
                       multi_sig=False, bus_name='', pkt_prefix='',
```

**Parameters:**
- `dut`: Device under test
- `clock`: Clock signal
- `title_prefix`: Prefix for component titles
- `field_config`: Field configuration (default: standard data field)
- `field_mode`: Field mode (unused - kept for compatibility)
- `packet_class`: Packet class to use
- `memory_model`: Memory model for components (auto-created if None)
- `log`: Logger instance
- `mode`: Operating mode for slave/monitor
- `signal_map`: Signal mapping (unused - kept for compatibility)
- `optional_signal_map`: Optional signal mapping (unused - kept for compatibility)
- `multi_sig`: Whether using multi-signal mode
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `**kwargs`: Additional configuration passed to all components

**Returns:** Dictionary containing all created components

```python
# Create complete GAXI system
components = create_gaxi_components(
    dut=dut,
    clock=dut.clk,
    title_prefix="GAXI_"
)

# Access components
master = components['master']
slave = components['slave']
master_monitor = components['master_monitor']
slave_monitor = components['slave_monitor']
scoreboard = components['scoreboard']
memory_model = components['memory_model']
```

### `create_gaxi_system()`

Create a complete GAXI system with all components - alias for `create_gaxi_components()`.

```python
create_gaxi_system(dut, clock, title_prefix="", field_config=None,
                   memory_model=None, log=None, bus_name='', pkt_prefix='',
```

**Parameters:** Simplified version of `create_gaxi_components()` parameters

**Returns:** Dictionary containing all created components and shared resources

```python
# Create GAXI system with clean API
system = create_gaxi_system(
    dut=dut,
    clock=dut.clk,
    title_prefix="System_",
    field_config=custom_config
)
```

### `create_gaxi_test_environment()`

Create a complete GAXI test environment ready for immediate use.

```python
create_gaxi_test_environment(dut, clock, bus_name='', pkt_prefix='',
```

**Parameters:**
- `dut`: Device under test
- `clock`: Clock signal
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `**kwargs`: Configuration overrides including:
  - `title_prefix`: Component title prefix (default: 'GAXI_')
  - `field_config`: Field configuration
  - `data_width`: Data width (default: 32)
  - `memory_size`: Memory size in lines (default: 1024)
  - `log`: Logger instance

**Returns:** Dictionary with complete test environment including convenience functions

```python
# Create ready-to-use test environment
env = create_gaxi_test_environment(
    dut=dut,
    clock=dut.clk,
    data_width=64,
    memory_size=2048
)

# Use convenience functions
await env['send_data'](0xDEADBEEF)
data = env['read_memory'](0x1000)
env['write_memory'](0x1000, 0x12345678)
all_stats = env['get_all_stats']()
```

## Usage Patterns

### Basic Component Creation

```python
@cocotb.test()
async def test_basic_gaxi(dut):
    """Basic GAXI test with factory-created components"""
    
    # Create individual components
    master = create_gaxi_master(
        dut=dut,
        title="TestMaster",
        prefix="",
        clock=dut.clk
    )
    
    slave = create_gaxi_slave(
        dut=dut,
        title="TestSlave", 
        prefix="",
        clock=dut.clk
    )
    
    # Test basic functionality
    await master.reset_bus()
    await slave.reset_bus()
    
    # Send test transaction
    packet = master.create_packet(data=0xDEADBEEF)
    await master.send(packet)
    
    # Verify reception
    await Timer(100, units='ns')
    received = slave.get_observed_packets()
    assert len(received) > 0
```

### Complete System Creation

```python
@cocotb.test()
async def test_complete_system(dut):
    """Test with complete GAXI system"""
    
    # Create complete system
    system = create_gaxi_system(
        dut=dut,
        clock=dut.clk,
        title_prefix="Test_",
        data_width=32,
        memory_size=1024
    )
    
    # Extract components
    master = system['master']
    slave = system['slave']
    master_monitor = system['master_monitor']
    slave_monitor = system['slave_monitor']
    scoreboard = system['scoreboard']
    memory = system['memory_model']
    
    # Connect monitors to scoreboard
    master_monitor.add_callback(scoreboard.master_transaction)
    slave_monitor.add_callback(scoreboard.slave_transaction)
    
    # Run test sequence
    await run_test_sequence(master, slave)
    
    # Check results
    stats = {
        'master': master.get_stats(),
        'slave': slave.get_stats(),
        'master_monitor': master_monitor.get_stats(),
        'slave_monitor': slave_monitor.get_stats(),
        'memory': memory.get_stats()
    }
    
    log.info(f"Test completed: {stats}")
```

### Test Environment Creation

```python
@cocotb.test()
async def test_with_environment(dut):
    """Test using complete test environment"""
    
    # Create test environment with convenience functions
    env = create_gaxi_test_environment(
        dut=dut,
        clock=dut.clk,
        title_prefix="ENV_",
        data_width=64,
        memory_size=2048
    )
    
    # Use convenience functions for testing
    test_data = [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0x87654321]
    
    for i, data in enumerate(test_data):
        # Send data using convenience function
        await env['send_data'](data)
        
        # Write to memory using convenience function
        env['write_memory'](0x1000 + i*4, data)
    
    # Read back and verify
    for i, expected_data in enumerate(test_data):
        addr = 0x1000 + i*4
        read_data = env['read_memory'](addr)
        
        # Convert bytearray to integer for comparison
        if isinstance(read_data, bytearray):
            read_value = int.from_bytes(read_data, byteorder='little')
        else:
            read_value = read_data
            
        assert read_value == expected_data, f"Memory mismatch at 0x{addr:X}"
    
    # Get comprehensive statistics
    all_stats = env['get_all_stats']()
    log.info(f"Environment test completed: {all_stats}")
```

### Advanced Configuration

```python
async def create_advanced_gaxi_system(dut, clock):
    """Create advanced GAXI system with custom configuration"""
    
    # Create custom field configuration
    field_config = FieldConfig()
    field_config.add_field(FieldDefinition("addr", 32, format="hex"))
    field_config.add_field(FieldDefinition("data", 64, format="hex"))
    field_config.add_field(FieldDefinition("cmd", 4, format="hex", encoding={
        0x0: "NOP", 0x1: "READ", 0x2: "WRITE", 0x3: "BURST"
    }))
    
    # Create shared memory model
    memory = MemoryModel(
        num_lines=4096,
        bytes_per_line=8,  # 64-bit data
        log=dut._log
    )
    
    # Create components with advanced configuration
    master = create_gaxi_master(
        dut=dut,
        title="AdvancedMaster",
        prefix="m_",
        clock=clock,
        field_config=field_config,
        memory_model=memory,
        multi_sig=True,
        mode='fifo_flop',
    )
    
    slave = create_gaxi_slave(
        dut=dut,
        title="AdvancedSlave",
        prefix="s_",
        clock=clock,
        field_config=field_config,
        memory_model=memory,
        multi_sig=True,
        mode='fifo_flop',
    )
    
    # Create monitors for both sides
    master_monitor = create_gaxi_monitor(
        dut=dut,
        title="MasterSideMonitor",
        prefix="m_",
        clock=clock,
        field_config=field_config,
        is_slave=False,
        multi_sig=True
    )
    
    slave_monitor = create_gaxi_monitor(
        dut=dut,
        title="SlaveSideMonitor",
        prefix="s_",
        clock=clock,
        field_config=field_config,
        is_slave=True,
        multi_sig=True,
        mode='fifo_flop'
    )
    
    # Create scoreboard
    scoreboard = create_gaxi_scoreboard(
        name="AdvancedScoreboard",
        field_config=field_config,
        log=dut._log
    )
    
    return {
        'master': master,
        'slave': slave,
        'master_monitor': master_monitor,
        'slave_monitor': slave_monitor,
        'scoreboard': scoreboard,
        'memory_model': memory,
        'field_config': field_config
    }
```

### Multi-Instance Systems

```python
async def create_multi_master_system(dut, clock):
    """Create system with multiple masters and one slave"""
    
    # Shared resources
    shared_memory = MemoryModel(num_lines=2048, bytes_per_line=4)
    shared_config = get_default_field_config(data_width=32)
    
    # Create multiple masters
    masters = {}
    for i in range(4):
        masters[f'master_{i}'] = create_gaxi_master(
            dut=dut,
            title=f"Master{i}",
            prefix=f"m{i}_",
            clock=clock,
            field_config=shared_config,
            memory_model=shared_memory
        )
    
    # Create single slave
    slave = create_gaxi_slave(
        dut=dut,
        title="SharedSlave",
        prefix="s_",
        clock=clock,
        field_config=shared_config,
        memory_model=shared_memory
    )
    
    # Create monitors for each master
    monitors = {}
    for i in range(4):
        monitors[f'master_{i}_monitor'] = create_gaxi_monitor(
            dut=dut,
            title=f"Master{i}Monitor",
            prefix=f"m{i}_",
            clock=clock,
            field_config=shared_config,
            is_slave=False
        )
    
    # Slave monitor
    monitors['slave_monitor'] = create_gaxi_monitor(
        dut=dut,
        title="SlaveMonitor",
        prefix="s_",
        clock=clock,
        field_config=shared_config,
        is_slave=True
    )
    
    # Scoreboard for transaction checking
    scoreboard = create_gaxi_scoreboard(
        name="MultiMasterScoreboard",
        field_config=shared_config
    )
    
    return {
        'masters': masters,
        'slave': slave,
        'monitors': monitors,
        'scoreboard': scoreboard,
        'shared_memory': shared_memory
    }
```

### Factory Pattern Integration

```python
class GAXITestFactory:
    """Factory class for creating GAXI test environments"""
    
    def __init__(self, dut, clock):
        self.dut = dut
        self.clock = clock
        self.default_config = get_default_field_config()
        
    def create_basic_system(self, prefix=""):
        """Create basic GAXI system"""
        return create_gaxi_system(
            dut=self.dut,
            clock=self.clock,
            title_prefix=prefix
        )
        
    def create_performance_test_system(self, data_width=32, memory_size=4096):
        """Create system optimized for performance testing"""
        return create_gaxi_test_environment(
            dut=self.dut,
            clock=self.clock,
            title_prefix="PERF_",
            data_width=data_width,
            memory_size=memory_size
        )
        
    def create_protocol_test_system(self, multi_sig=True, mode='skid'):
        """Create system for protocol compliance testing"""
        field_config = FieldConfig()
        field_config.add_field(FieldDefinition("addr", 32))
        field_config.add_field(FieldDefinition("data", 32))
        field_config.add_field(FieldDefinition("prot", 3))
        field_config.add_field(FieldDefinition("user", 4))
        
        return create_gaxi_components(
            dut=self.dut,
            clock=self.clock,
            title_prefix="PROT_",
            field_config=field_config,
            multi_sig=multi_sig,
            mode=mode
        )
        
    def create_stress_test_system(self):
        """Create system for stress testing"""
        return create_gaxi_test_environment(
            dut=self.dut,
            clock=self.clock,
            title_prefix="STRESS_",
            data_width=64,
            memory_size=8192
        )

# Usage
@cocotb.test()
async def test_with_factory(dut):
    factory = GAXITestFactory(dut, dut.clk)
    
    # Create different systems for different test phases
    basic_system = factory.create_basic_system("BASIC_")
    perf_system = factory.create_performance_test_system(64, 2048)
    stress_system = factory.create_stress_test_system()
    
    # Run tests with different systems...
```

## Error Handling and Validation

### Parameter Validation

```python
# Factories automatically handle parameter validation
try:
    master = create_gaxi_master(
        dut=dut,
        title="TestMaster",
        prefix="",
        clock=dut.clk,
        field_config=invalid_config  # Will be validated and corrected
    )
except Exception as e:
    log.error(f"Factory creation failed: {e}")
```

### Default Fallbacks

```python
# Factories provide sensible defaults for all parameters
master = create_gaxi_master(dut, "Master", "", dut.clk)
# Uses: default field config, dut's logger, empty prefixes, etc.
```

### Memory Model Auto-Creation

```python
# Memory model is automatically created if not provided
system = create_gaxi_components(dut, dut.clk)
# Automatically creates MemoryModel(1024, 4) with proper configuration
```

## Best Practices

### 1. **Use Empty String Prefixes for Most Cases**
```python
# Empty prefixes work for most DUT configurations
```

### 2. **Create Complete Systems for Full Testing**
```python
# Use create_gaxi_test_environment for comprehensive testing
env = create_gaxi_test_environment(dut, dut.clk)
# Includes all components plus convenience functions
```

### 3. **Share Memory Models Across Components**
```python
# Share memory for consistent state
memory = MemoryModel(1024, 4, log=log)
master = create_gaxi_master(dut, "Master", "", dut.clk, memory_model=memory)
slave = create_gaxi_slave(dut, "Slave", "", dut.clk, memory_model=memory)
```

### 4. **Use Multi-Signal Mode for Complex Protocols**
```python
# Enable multi-signal mode for protocols with many fields
components = create_gaxi_components(dut, dut.clk, multi_sig=True)
```

### 5. **Leverage Factory Patterns for Complex Tests**
```python
# Create factory class for standardized test setups
factory = GAXITestFactory(dut, dut.clk)
system = factory.create_protocol_test_system()
```

## Backward Compatibility

All factory functions maintain complete backward compatibility:

- **All existing parameters are preserved** and passed through exactly as before
- **Parameter order is maintained** for positional arguments
- **Default values are enhanced** but don't break existing code
- **New parameters have sensible defaults** that work with existing configurations
- **Legacy parameter names are supported** (e.g., `field_mode`, `signal_map`) even when unused

```python
# Legacy code continues to work unchanged
components = create_gaxi_components(
    dut, clock, title_prefix="Legacy_", field_mode=True,
    signal_map=old_signal_map, optional_signal_map=old_optional_map
)
```

The GAXI factories provide a robust, simplified interface for creating GAXI components while maintaining full backward compatibility and supporting advanced configuration scenarios.
