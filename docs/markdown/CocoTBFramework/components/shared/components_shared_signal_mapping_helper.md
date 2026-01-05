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

# signal_mapping_helper.py

Simplified GAXI/FIFO Signal Mapping with pattern matching against top-level ports. This module uses pattern matching against actual DUT ports with parameter combinations to find the correct signal mappings automatically, with support for manual signal mapping override.

## Overview

The `signal_mapping_helper.py` module provides automatic signal discovery and mapping for GAXI and FIFO protocols. It can automatically discover signals using pattern matching or accept manual signal mappings. The module handles prefix management for cocotb compatibility and provides comprehensive error reporting.

### Key Features
- **Automatic signal discovery** using pattern matching against DUT ports
- **Manual signal mapping override** with comprehensive validation
- **Prefix handling** for cocotb Bus compatibility
- **Protocol support** for GAXI and FIFO (master/slave variants)
- **Multi-signal and single-signal modes** for different DUT configurations
- **Rich error reporting** with detailed diagnostics
- **Thread-safe operation** for parallel testing environments

## Constants and Patterns

### Protocol Modes

```python
# Standard FIFO modes (for parameter passing to RTL)
FIFO_VALID_MODES = ['fifo_mux', 'fifo_flop']

# Standard GAXI modes (for parameter passing to RTL)
GAXI_VALID_MODES = ['skid', 'fifo_mux', 'fifo_flop']
```

### Signal Patterns

The module includes comprehensive signal patterns for different protocols:

#### GAXI Patterns
- **Master-side patterns**: For masters and write monitors
- **Slave-side patterns**: For slaves and read monitors

#### FIFO Patterns  
- **Write-side patterns**: For masters and write monitors
- **Read-side patterns**: For slaves and read monitors

### Protocol Signal Configurations

```python
PROTOCOL_SIGNAL_CONFIGS = {
    'fifo_master': {
        'signal_map': {
            'i_write':   FIFO_BASE_PATTERNS['write_base'],
            'o_wr_full': FIFO_BASE_PATTERNS['full_base']
        },
        'optional_signal_map': {
            'multi_sig_false': FIFO_BASE_PATTERNS['wr_data_base'],
            'multi_sig_true':  FIFO_BASE_PATTERNS['wr_field_base']
        }
    },
    # ... other protocol configurations
}
```

## Core Class

### SignalResolver

Signal resolver using pattern matching against actual top-level DUT ports with support for manual signal mapping.

#### Constructor

```python
SignalResolver(protocol_type: str, dut, bus, log, component_name: str,
               prefix='', field_config=None, multi_sig: bool = False,
               bus_name: str = '', pkt_prefix: str = '', mode: str = None,
               super_debug: bool = False, signal_map: Optional[Dict[str, str]] = None)
```

**Parameters:**
- `protocol_type`: Protocol type ('fifo_master', 'fifo_slave', 'gaxi_master', 'gaxi_slave')
- `dut`: Device under test
- `bus`: Bus object from BusDriver/BusMonitor (can be None initially)
- `log`: Logger instance (can be None)
- `component_name`: Component name for error messages
- `prefix`: Prefix that cocotb will prepend to signal names
- `field_config`: Field configuration (required for multi_sig=True)
- `multi_sig`: Whether using multi-signal mode
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `mode`: Protocol mode (kept for RTL parameter)
- `super_debug`: Enable detailed signal resolution debugging
- `signal_map`: Optional manual signal mapping (bypasses automatic discovery)

#### Signal Map Format

When using manual `signal_map`, the keys vary by protocol:

**GAXI Protocols:**
- `'valid'`: Valid signal name
- `'ready'`: Ready signal name  
- `'data'`: Data signal name (single-signal mode)
- Field names: Individual field signal names (multi-signal mode)

**FIFO Master:**
- `'write'`: Write signal name
- `'full'`: Full signal name
- `'data'`: Data signal name (single-signal mode)
- Field names: Individual field signal names (multi-signal mode)

**FIFO Slave:**
- `'read'`: Read signal name
- `'empty'`: Empty signal name
- `'data'`: Data signal name (single-signal mode)
- Field names: Individual field signal names (multi-signal mode)

```python
# Automatic signal discovery
resolver = SignalResolver(
    protocol_type='gaxi_master',
    dut=dut,
    bus=bus,
    log=log,
    component_name='TestMaster',
    prefix='test_',
    multi_sig=False
)

# Manual signal mapping
signal_map = {
    'valid': 'master_valid',
    'ready': 'slave_ready', 
    'data': 'transfer_data'
}
resolver = SignalResolver(
    protocol_type='gaxi_master',
    dut=dut,
    bus=bus,
    log=log,
    component_name='TestMaster',
    signal_map=signal_map
)
```

#### Methods

##### `apply_to_component(component)`

Apply resolved signals to component as attributes with comprehensive validation.

**Parameters:**
- `component`: Component to apply signals to

**Raises:**
- `RuntimeError`: If signal linkage fails with detailed diagnostic information

```python
# Apply signals to component
try:
    resolver.apply_to_component(self)
    log.info("Signal mapping successful")
except RuntimeError as e:
    log.error(f"Signal mapping failed: {e}")
    raise
```

##### `get_signal(logical_name: str)`

Get a resolved signal by logical name.

**Parameters:**
- `logical_name`: Logical signal name from SignalResolver

**Returns:** Signal object or None

```python
# Get specific signals
valid_signal = resolver.get_signal('o_valid')
data_signal = resolver.get_signal('data_sig')
```

##### `has_signal(logical_name: str) -> bool`

Check if a signal was found and is not None.

```python
if resolver.has_signal('data_sig'):
    # Data signal is available
    pass
```

##### `get_signal_lists()`

Get the _signals and _optional_signals lists for cocotb Bus initialization.

**Returns:** Tuple of (_signals, _optional_signals)

```python
signals, optional_signals = resolver.get_signal_lists()
```

##### `get_stats() -> Dict[str, Any]`

Get statistics about signal resolution.

**Returns:** Dictionary with comprehensive resolution statistics

```python
stats = resolver.get_stats()
print(f"Resolution rate: {stats['resolution_rate']:.1f}%")
print(f"Signal mapping source: {stats['signal_mapping_source']}")
print(f"Protocol: {stats['protocol_type']}")
```

## Usage Patterns

### Automatic Signal Discovery

```python
class GAXIMaster:
    def __init__(self, dut, field_config, log):
        self.dut = dut
        self.log = log
        
        # Create bus for signal access
        self.bus = GAXIBus(dut, "test_", log)
        
        # Automatic signal discovery
        self.resolver = SignalResolver(
            protocol_type='gaxi_master',
            dut=dut,
            bus=self.bus,
            log=log,
            component_name='GAXIMaster',
            prefix='test_',           # Prefix cocotb will add
            field_config=field_config,
            multi_sig=True,          # Use individual field signals
            super_debug=False        # Enable for debugging
        )
        
        # Apply signals to component
        self.resolver.apply_to_component(self)
        
        # Now we can access signals as attributes
        # self.valid_sig, self.ready_sig, self.field_addr_sig, etc.
    
    @cocotb.coroutine
    def send_transaction(self, packet):
        """Send transaction using resolved signals"""
        # Drive valid
        self.valid_sig.value = 1
        
        # Drive field signals
        if hasattr(self, 'field_addr_sig'):
            self.field_addr_sig.value = packet.addr
        if hasattr(self, 'field_data_sig'):
            self.field_data_sig.value = packet.data
        
        # Wait for ready
        while self.ready_sig.value != 1:
            yield RisingEdge(self.dut.clk)
        
        yield RisingEdge(self.dut.clk)
        
        # Deassert valid
        self.valid_sig.value = 0
```

### Manual Signal Mapping

```python
class FIFOMaster:
    def __init__(self, dut, field_config, log):
        self.dut = dut
        self.log = log
        
        # Create bus
        self.bus = FIFOBus(dut, "fifo_", log)
        
        # Manual signal mapping (when automatic discovery fails)
        signal_map = {
            'write': 'wr_en',      # Write enable signal
            'full': 'fifo_full',   # FIFO full signal
            'data': 'wr_data'      # Write data signal
        }
        
        self.resolver = SignalResolver(
            protocol_type='fifo_master',
            dut=dut,
            bus=self.bus,
            log=log,
            component_name='FIFOMaster',
            signal_map=signal_map
        )
        
        # Apply signals
        self.resolver.apply_to_component(self)
        
        # Access signals: self.write_sig, self.full_sig, self.data_sig
    
    @cocotb.coroutine
    def write_data(self, data):
        """Write data to FIFO"""
        # Check if FIFO is full
        if self.full_sig.value == 1:
            self.log.warning("FIFO is full, cannot write")
            return False
        
        # Write data
        self.data_sig.value = data
        self.write_sig.value = 1
        
        yield RisingEdge(self.dut.clk)
        
        self.write_sig.value = 0
        return True
```

### Multi-Signal Mode

```python
class MultiSignalGAXISlave:
    def __init__(self, dut, field_config, log):
        # Field configuration with multiple fields
        self.field_config = field_config  # Contains addr, data, cmd fields
        
        # Multi-signal mode - each field has its own signal
        self.resolver = SignalResolver(
            protocol_type='gaxi_slave',
            dut=dut,
            bus=None,  # Will be set later
            log=log,
            component_name='MultiSignalSlave',
            field_config=field_config,
            multi_sig=True,           # Enable multi-signal mode
            prefix='slave_'
        )
        
        # Create bus after resolver is configured
        signals, optional_signals = self.resolver.get_signal_lists()
        self.bus = GAXIBus(dut, "slave_", log, signals, optional_signals)
        self.resolver.bus = self.bus
        
        # Apply signals
        self.resolver.apply_to_component(self)
        
        # Now we have: self.valid_sig, self.ready_sig, 
        # self.field_addr_sig, self.field_data_sig, self.field_cmd_sig
    
    @cocotb.coroutine
    def monitor_transactions(self):
        """Monitor incoming transactions"""
        while True:
            yield RisingEdge(self.dut.clk)
            
            if self.valid_sig.value == 1 and self.ready_sig.value == 1:
                # Capture transaction
                transaction = {}
                transaction['addr'] = int(self.field_addr_sig.value)
                transaction['data'] = int(self.field_data_sig.value)
                transaction['cmd'] = int(self.field_cmd_sig.value)
                
                self.process_transaction(transaction)
```

### Error Handling and Debugging

```python
class DebugSignalResolver:
    def __init__(self, dut, log):
        self.dut = dut
        self.log = log
        
        try:
            # Attempt automatic discovery with debug enabled
            self.resolver = SignalResolver(
                protocol_type='gaxi_master',
                dut=dut,
                bus=None,
                log=log,
                component_name='DebugMaster',
                super_debug=True,     # Enable detailed debugging
                prefix='debug_'
            )
            
            # Check resolution statistics
            stats = self.resolver.get_stats()
            self.log.info(f"Signal resolution: {stats}")
            
            if stats['missing_required'] > 0:
                self.log.error("Missing required signals, trying manual mapping")
                self._try_manual_mapping()
            
        except ValueError as e:
            self.log.error(f"Signal resolution failed: {e}")
            self._try_manual_mapping()
    
    def _try_manual_mapping(self):
        """Try manual signal mapping as fallback"""
        # Inspect available signals
        available_signals = self._get_available_signals()
        self.log.info(f"Available signals: {available_signals}")
        
        # Create manual mapping based on available signals
        signal_map = self._create_manual_mapping(available_signals)
        
        if signal_map:
            self.resolver = SignalResolver(
                protocol_type='gaxi_master',
                dut=self.dut,
                bus=None,
                log=self.log,
                component_name='DebugMaster',
                signal_map=signal_map
            )
        else:
            raise RuntimeError("Unable to create signal mapping")
    
    def _get_available_signals(self):
        """Get list of available signals on DUT"""
        signals = []
        for attr_name in dir(self.dut):
            if not attr_name.startswith('_'):
                try:
                    attr = getattr(self.dut, attr_name)
                    if hasattr(attr, 'value'):
                        signals.append(attr_name)
                except:
                    pass
        return signals
    
    def _create_manual_mapping(self, available_signals):
        """Create manual mapping from available signals"""
        signal_map = {}
        
        # Look for common signal patterns
        for signal in available_signals:
            if 'valid' in signal.lower():
                signal_map['valid'] = signal
            elif 'ready' in signal.lower():
                signal_map['ready'] = signal
            elif 'data' in signal.lower():
                signal_map['data'] = signal
        
        # Return mapping if we found required signals
        if 'valid' in signal_map and 'ready' in signal_map:
            return signal_map
        else:
            return None
```

### Advanced Configuration

```python
class AdvancedSignalMapping:
    def __init__(self, dut, config):
        self.dut = dut
        self.config = config
        self.resolvers = {}
        
        # Create multiple resolvers for different interfaces
        self._setup_multiple_interfaces()
    
    def _setup_multiple_interfaces(self):
        """Set up multiple protocol interfaces"""
        
        # Master interface
        master_map = {
            'valid': 'master_valid',
            'ready': 'master_ready',
            'data': 'master_data'
        }
        
        self.resolvers['master'] = SignalResolver(
            protocol_type='gaxi_master',
            dut=self.dut,
            bus=None,
            log=self.log,
            component_name='AdvancedMaster',
            signal_map=master_map,
            prefix='m_'
        )
        
        # Slave interface
        slave_map = {
            'valid': 'slave_valid',
            'ready': 'slave_ready',
            'data': 'slave_data'
        }
        
        self.resolvers['slave'] = SignalResolver(
            protocol_type='gaxi_slave',
            dut=self.dut,
            bus=None,
            log=self.log,
            component_name='AdvancedSlave',
            signal_map=slave_map,
            prefix='s_'
        )
        
        # Apply all resolvers
        for name, resolver in self.resolvers.items():
            resolver.apply_to_component(self)
            self.log.info(f"Applied {name} interface signals")
    
    def get_interface_stats(self):
        """Get statistics for all interfaces"""
        stats = {}
        for name, resolver in self.resolvers.items():
            stats[name] = resolver.get_stats()
        return stats
```

### Protocol-Specific Usage

```python
class ProtocolSpecificExample:
    """Examples for different protocol configurations"""
    
    def setup_gaxi_write_channel(self, dut, log):
        """Set up GAXI write channel signals"""
        
        # Write address channel
        aw_resolver = SignalResolver(
            protocol_type='gaxi_master',
            dut=dut,
            bus=None,
            log=log,
            component_name='AW_Channel',
            signal_map={
                'valid': 'awvalid',
                'ready': 'awready',
                'awid': 'awid',
                'awaddr': 'awaddr',
                'awlen': 'awlen'
            },
            multi_sig=True
        )
        
        return aw_resolver
    
    def setup_fifo_interface(self, dut, log):
        """Set up FIFO interface signals"""
        
        # FIFO write interface
        fifo_resolver = SignalResolver(
            protocol_type='fifo_master',
            dut=dut,
            bus=None,
            log=log,
            component_name='FIFO_Write',
            signal_map={
                'write': 'wr_en',
                'full': 'full',
                'data': 'din'
            }
        )
        
        return fifo_resolver
    
    def setup_custom_protocol(self, dut, log):
        """Set up custom protocol using manual mapping"""
        
        # Custom protocol with specific signal names
        custom_map = {
            'valid': 'req_valid',
            'ready': 'req_ready',
            'cmd': 'command',
            'addr': 'address',
            'data': 'payload'
        }
        
        custom_resolver = SignalResolver(
            protocol_type='gaxi_master',  # Use closest matching protocol
            dut=dut,
            bus=None,
            log=log,
            component_name='CustomProtocol',
            signal_map=custom_map,
            multi_sig=True
        )
        
        return custom_resolver
```

### Test Framework Integration

```python
@cocotb.test()
def signal_mapping_test(dut):
    """Test with automatic signal mapping"""
    
    # Create field configuration
    field_config = FieldConfig()
    field_config.add_field(FieldDefinition("addr", 32))
    field_config.add_field(FieldDefinition("data", 32))
    
    # Set up signal resolver
    resolver = SignalResolver(
        protocol_type='gaxi_master',
        dut=dut,
        bus=None,
        log=cocotb.log,
        component_name='TestMaster',
        field_config=field_config,
        multi_sig=True,
        super_debug=True
    )
    
    # Create and configure bus
    signals, optional_signals = resolver.get_signal_lists()
    bus = GAXIBus(dut, "", cocotb.log, signals, optional_signals)
    resolver.bus = bus
    
    # Apply to test master
    master = TestMaster(dut, resolver)
    
    # Verify signal mapping
    assert hasattr(master, 'valid_sig'), "Valid signal not mapped"
    assert hasattr(master, 'ready_sig'), "Ready signal not mapped"
    
    # Run test with mapped signals
    yield master.run_test_sequence()
    
    # Check mapping statistics
    stats = resolver.get_stats()
    cocotb.log.info(f"Signal mapping stats: {stats}")
    
    assert stats['resolved_signals'] >= 2, "Insufficient signals resolved"
    assert stats['conflicts'] == 0, "Signal conflicts detected"

class TestMaster:
    def __init__(self, dut, resolver):
        self.dut = dut
        resolver.apply_to_component(self)
    
    @cocotb.coroutine
    def run_test_sequence(self):
        """Run test using mapped signals"""
        for i in range(10):
            # Use resolved signals
            self.valid_sig.value = 1
            self.field_addr_sig.value = 0x1000 + i*4
            self.field_data_sig.value = i * 0x100
            
            yield RisingEdge(self.dut.clk)
            self.valid_sig.value = 0
```

## Error Handling and Diagnostics

### Comprehensive Error Reporting

The SignalResolver provides detailed error reporting when signal mapping fails:

```python
try:
    resolver.apply_to_component(component)
except RuntimeError as e:
    # Error message includes:
    # - Failed signal details (DUT signal name, cocotb signal name, target attribute)
    # - Signal type (REQUIRED vs DATA/OPTIONAL)
    # - Successful linkages (for comparison)
    # - Bus diagnostic information
    # - Prefix handling details
    # - Signal lists passed to Bus
    # - Manual signal map info (if used)
    
    log.error(f"Detailed signal mapping failure: {e}")
```

### Debugging Support

```python
# Enable super debug for detailed tracing
resolver = SignalResolver(
    protocol_type='gaxi_master',
    dut=dut,
    bus=bus,
    log=log,
    component_name='DebugComponent',
    super_debug=True  # Enables detailed logging
)

# Check resolution statistics
stats = resolver.get_stats()
print(f"Total ports found: {stats['total_ports_found']}")
print(f"Parameter combinations: {stats['parameter_combinations']}")
print(f"Resolution rate: {stats['resolution_rate']:.1f}%")

# Dump log messages if logger not available
if not log:
    resolver.dump_log_messages()
```

## Best Practices

### 1. **Start with Automatic Discovery**
```python
# Try automatic discovery first
try:
    resolver = SignalResolver('gaxi_master', dut, bus, log, 'Component')
    resolver.apply_to_component(self)
except RuntimeError:
    # Fall back to manual mapping
    signal_map = create_manual_mapping()
    resolver = SignalResolver('gaxi_master', dut, bus, log, 'Component', signal_map=signal_map)
```

### 2. **Use Manual Mapping for Non-Standard Signals**
```python
# For custom or non-standard signal names
signal_map = {
    'valid': 'my_custom_valid',
    'ready': 'my_custom_ready',
    'data': 'my_custom_data'
}
resolver = SignalResolver(protocol_type, dut, bus, log, name, signal_map=signal_map)
```

### 3. **Handle Prefix Correctly**
```python
# Prefix should match what cocotb Bus will add
resolver = SignalResolver(
    protocol_type='gaxi_master',
    dut=dut,
    bus=bus,
    log=log,
    component_name='Master',
    prefix='master_'  # This should match Bus prefix
)
```

### 4. **Validate Signal Mapping**
```python
# Always check mapping was successful
resolver.apply_to_component(self)

# Verify expected signals exist
required_signals = ['valid_sig', 'ready_sig', 'data_sig']
for signal_name in required_signals:
    assert hasattr(self, signal_name), f"Missing signal: {signal_name}"
```

### 5. **Use Statistics for Debugging**
```python
# Check resolution statistics for debugging
stats = resolver.get_stats()
if stats['resolution_rate'] < 100:
    log.warning(f"Incomplete signal resolution: {stats}")
    
if stats['conflicts'] > 0:
    log.error(f"Signal conflicts detected: {stats['conflict_details']}")
```

The SignalResolver provides a robust foundation for signal mapping across different protocols, with comprehensive error handling, flexible configuration options, and extensive debugging support for verification environments.
