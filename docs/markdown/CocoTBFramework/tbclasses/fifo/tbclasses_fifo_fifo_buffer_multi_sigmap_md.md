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

# fifo_buffer_multi_sigmap.py

Multi-signal FIFO buffer testbench with signal mapping capabilities. This testbench extends multi-signal support with configurable signal name mapping for non-standard or custom signal naming conventions.

## Overview

The `FifoMultiSigMapBufferTB` class provides verification for FIFOs with multiple parallel signals and configurable signal mapping. This testbench is essential for testing FIFOs with custom signal names, legacy interfaces, or non-standard naming conventions while maintaining full multi-signal verification capabilities.

## Key Features

- **Configurable Signal Mapping**: Custom signal name mapping for DUT interfaces
- **Multi-Signal Interface Support**: All capabilities of multi-signal testbench
- **Legacy Design Support**: Adaptation for existing designs with custom naming
- **Flexible Signal Routing**: Dynamic signal name resolution
- **Enhanced Debug Support**: Signal mapping aware debugging and analysis

## Class Definition

```python
class FifoMultiSigMapBufferTB(TBBase):
    """Testbench for multi-signal FIFO components with signal mapping using FlexConfigGen only"""
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

## Signal Mapping Configuration

### Master Signal Mapping (Write Side)

```python
self.master_signal_map = {
    'write' : 'wr_en',      # Standard 'write' maps to custom 'wr_en'
    'full'  : 'wr_full',    # Standard 'full' maps to custom 'wr_full'
    'addr'  : 'wr_siga',    # Standard 'addr' maps to custom 'wr_siga'
    'ctrl'  : 'wr_sigb',    # Standard 'ctrl' maps to custom 'wr_sigb'
    'data0' : 'wr_sigc',    # Standard 'data0' maps to custom 'wr_sigc'
    'data1' : 'wr_sigd'     # Standard 'data1' maps to custom 'wr_sigd'
}
```

### Slave Signal Mapping (Read Side)

```python
self.slave_signal_map = {
    'read'  : 'read',       # Standard 'read' maps to custom 'read'
    'empty' : 'rd_empty',   # Standard 'empty' maps to custom 'rd_empty'
    'addr'  : 'rd_sige',    # Standard 'addr' maps to custom 'rd_sige'
    'ctrl'  : 'rd_sigf',    # Standard 'ctrl' maps to custom 'rd_sigf'
    'data0' : 'rd_sigg',    # Standard 'data0' maps to custom 'rd_sigg'
    'data1' : 'rd_sigh'     # Standard 'data1' maps to custom 'rd_sigh'
}
```

## Environment Configuration

Same configuration as multi-signal testbench:

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

## Signal Mapping Architecture

### How Signal Mapping Works

The testbench uses signal mapping dictionaries to translate between standard signal names used by the framework and custom signal names in the DUT:

1. **Framework Interface**: Uses standard names (write, read, addr, ctrl, data0, data1)
2. **Signal Translation**: Maps standard names to DUT-specific names
3. **DUT Interface**: Connects to actual DUT signals with custom names

### Example Signal Translation

```python
# Framework wants to access 'write' signal
# Signal mapping translates 'write' -> 'wr_en'
# Testbench connects to dut.wr_en

# Framework wants to access 'data0' signal  
# Signal mapping translates 'data0' -> 'wr_sigc'
# Testbench connects to dut.wr_sigc
```

## Component Architecture with Signal Mapping

### Master with Signal Mapping

```python
self.write_master = FIFOMaster(
    dut=dut,
    title='write_master',
    clock=self.wr_clk,
    field_config=self.field_config,
    multi_sig=True,                        # Enable multi-signal mode
    signal_map=self.master_signal_map,     # Apply signal mapping
    timeout_cycles=self.TIMEOUT_CYCLES,
    mode=self.TEST_MODE,
    super_debug=self.super_debug
)
```

### Slave with Signal Mapping

```python
self.read_slave = FIFOSlave(
    dut=dut,
    title='read_slave',
    clock=self.rd_clk,
    field_config=self.field_config,
    multi_sig=True,                        # Enable multi-signal mode
    signal_map=self.slave_signal_map,      # Apply signal mapping
    timeout_cycles=self.TIMEOUT_CYCLES,
    mode=self.TEST_MODE,
    super_debug=self.super_debug
)
```

### Monitors with Signal Mapping

Both write and read monitors also use signal mapping to properly observe the custom-named signals while maintaining standard framework interfaces.

## Test Methods

### Signal Mapping Verification Tests

#### `test_signal_mapping_integrity(packet_count=100)`
Verifies that signal mapping works correctly for all mapped signals.

**Purpose**: Verify signal mapping translation accuracy
**Pattern**: Test each mapped signal individually
**Verification**: Correct signal routing and data integrity

```python
await tb.test_signal_mapping_integrity(packet_count=100)
```

#### `test_mapped_signal_isolation(packet_count=200)`
Tests isolation between different mapped signal groups.

**Purpose**: Verify signal isolation with custom mapping
**Pattern**: Independent variation of mapped signal groups
**Verification**: No cross-talk between mapped signals

### Enhanced Multi-Signal Tests with Mapping

#### `test_coordinated_mapped_signals(packet_count=300)`
Tests coordination between mapped signals.

**Purpose**: Verify complex coordination with signal mapping
**Pattern**: Coordinated patterns across all mapped signals
**Verification**: Proper timing and data integrity with mapping

#### `test_mapped_signal_stress(packet_count=500)`
Stress testing with signal mapping active.

**Purpose**: High-load testing with signal mapping overhead
**Pattern**: Intensive traffic with signal name translation
**Verification**: Performance and integrity under mapping stress

### Signal Mapping Specific Tests

#### `test_isolation_patterns(packet_count=400)`
Advanced isolation testing with field-specific patterns.

**Purpose**: Comprehensive field isolation with signal mapping
**Test Patterns**:
- **Address Isolation**: Only address field varies across mapped signals
- **Control Isolation**: Only control field varies across mapped signals  
- **Data0 Isolation**: Only data0 field varies across mapped signals
- **Data1 Isolation**: Only data1 field varies across mapped signals
- **Address/Control Combo**: Combined address and control variations
- **Data Combo**: Combined data0 and data1 variations

```python
await tb.test_isolation_patterns(packet_count=300)
```

## Usage Examples

### Basic Signal Mapping Testing

```python
import cocotb
import os
from CocoTBFramework.tbclasses.fifo.fifo_buffer_multi_sigmap import FifoMultiSigMapBufferTB

@cocotb.test()
async def test_sigmap_fifo(dut):
    # Configure signal mapping parameters
    os.environ['TEST_ADDR_WIDTH'] = '16'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_DEPTH'] = '64'
    
    tb = FifoMultiSigMapBufferTB(dut, super_debug=True)
    await tb.initialize()
    
    # Signal mapping specific tests
    await tb.test_signal_mapping_integrity(packet_count=100)
    await tb.test_mapped_signal_isolation(packet_count=150)
    
    tb.verify_results()
```

### Custom Signal Mapping Configuration

```python
@cocotb.test()
async def test_custom_sigmap_fifo(dut):
    # Configure for custom interface
    os.environ['TEST_ADDR_WIDTH'] = '20'
    os.environ['TEST_CTRL_WIDTH'] = '12'
    os.environ['TEST_DATA_WIDTH'] = '64'
    os.environ['TEST_DEPTH'] = '128'
    
    tb = FifoMultiSigMapBufferTB(dut, super_debug=True)
    
    # Customize signal mapping for specific DUT
    tb.master_signal_map.update({
        'write': 'custom_wr_enable',
        'full': 'custom_wr_full_flag',
        'addr': 'custom_address_bus',
        'ctrl': 'custom_control_bus'
    })
    
    tb.slave_signal_map.update({
        'read': 'custom_rd_enable',
        'empty': 'custom_rd_empty_flag',
        'addr': 'custom_out_address',
        'ctrl': 'custom_out_control'
    })
    
    await tb.initialize()
    
    # Test with custom signal mapping
    await tb.test_coordinated_mapped_signals(packet_count=200)
    await tb.test_isolation_patterns(packet_count=300)
    
    tb.verify_results()
```

### Legacy Interface Adaptation

```python
@cocotb.test()
async def test_legacy_interface(dut):
    # Configure for legacy interface adaptation
    tb = FifoMultiSigMapBufferTB(dut, super_debug=True)
    
    # Map to legacy signal names
    tb.master_signal_map = {
        'write': 'legacy_write_strobe',
        'full': 'legacy_fifo_full',
        'addr': 'legacy_addr_bus',
        'ctrl': 'legacy_cmd_bus',
        'data0': 'legacy_data_low',
        'data1': 'legacy_data_high'
    }
    
    tb.slave_signal_map = {
        'read': 'legacy_read_strobe', 
        'empty': 'legacy_fifo_empty',
        'addr': 'legacy_out_addr',
        'ctrl': 'legacy_out_cmd',
        'data0': 'legacy_out_data_low',
        'data1': 'legacy_out_data_high'
    }
    
    await tb.initialize()
    
    # Legacy interface verification
    await tb.test_legacy_compatibility()
    await tb.test_mapped_signal_stress(packet_count=400)
    
    tb.verify_results()
```

## Signal Mapping Debug Features

### Enhanced Debug with Signal Mapping

**Mapped Signal Tracing**: Shows both framework names and actual DUT signal names
**Signal Translation Logging**: Logs signal name translations
**Mapping Verification**: Automatic verification of signal mapping correctness
**Debug Signal Names**: Debug output shows both standard and mapped names

### Signal Mapping Verification

The testbench automatically verifies signal mapping:

```python
# Automatic verification during initialization
for standard_name, mapped_name in signal_map.items():
    if not hasattr(dut, mapped_name):
        raise ValueError(f"Mapped signal '{mapped_name}' not found in DUT")
```

### Signal Mapping Analysis

**Mapping Coverage**: Ensures all required signals are mapped
**Mapping Consistency**: Verifies mapping consistency across components
**Performance Impact**: Measures signal mapping overhead
**Debug Correlation**: Correlates framework signals with DUT signals

## Common Signal Mapping Patterns

### Standard to Custom Mapping
```python
signal_map = {
    'write': 'wr_en',
    'read': 'rd_en', 
    'full': 'almost_full',
    'empty': 'almost_empty'
}
```

### Protocol-Specific Mapping
```python
axi_signal_map = {
    'write': 'axi_awvalid',
    'addr': 'axi_awaddr',
    'data0': 'axi_wdata',
    'ctrl': 'axi_awprot'
}
```

### Legacy Interface Mapping
```python
legacy_map = {
    'write': 'WR_STROBE',
    'read': 'RD_STROBE',
    'full': 'FULL_FLAG',
    'empty': 'EMPTY_FLAG'
}
```

## Performance Considerations

### Signal Mapping Overhead

**Translation Cost**: Minimal overhead for signal name translation
**Debug Impact**: Enhanced debug may increase simulation time
**Memory Usage**: Signal mapping adds minimal memory overhead
**Flexibility Benefit**: Significant flexibility gain for adaptation

### Optimization Strategies

**Disable Debug**: Turn off super_debug for performance-critical tests
**Optimize Mapping**: Use direct signal connections where possible
**Batch Operations**: Group signal operations to reduce mapping overhead
**Profile Performance**: Monitor impact of signal mapping on test execution

## Integration Benefits

### Design Flexibility

**Interface Adaptation**: Easily adapt testbench to any signal naming convention
**Legacy Support**: Seamlessly integrate with existing designs
**Protocol Mapping**: Map framework signals to protocol-specific names
**Custom Interfaces**: Support non-standard or proprietary interfaces

### Verification Efficiency

**Reuse Framework**: Use standard framework with any DUT interface
**Reduce Development**: No need to modify framework for custom signals
**Maintain Standards**: Keep verification methodology consistent
**Easy Migration**: Simple migration between different DUT versions

## Common Use Cases

### Multi-Vendor IP Integration
When integrating IP from different vendors with varying signal naming conventions:

```python
# Vendor A mapping
vendor_a_map = {
    'write': 'push',
    'read': 'pop',
    'full': 'fifo_full',
    'empty': 'fifo_empty'
}

# Vendor B mapping  
vendor_b_map = {
    'write': 'wr_en',
    'read': 'rd_en',
    'full': 'almost_full',
    'empty': 'almost_empty'
}
```

### Protocol-Specific Interfaces
Adapting to protocol-specific signal names:

```python
# AXI4-Stream mapping
axi_stream_map = {
    'write': 'tvalid',
    'data0': 'tdata',
    'ctrl': 'tuser',
    'full': 'tready'  # Note: inverted logic handled by framework
}

# Avalon-ST mapping
avalon_st_map = {
    'write': 'valid',
    'data0': 'data',
    'read': 'ready',
    'empty': 'startofpacket'
}
```

### Legacy Design Migration
Supporting legacy designs during modernization:

```python
# Legacy FIFO interface
legacy_fifo_map = {
    'write': 'WR_REQ',
    'read': 'RD_REQ', 
    'full': 'FULL_N',     # Active low
    'empty': 'EMPTY_N',   # Active low
    'data0': 'WR_DATA',
    'data1': 'RD_DATA'
}
```

## Advanced Signal Mapping Features

### Conditional Mapping
Signal mapping can be conditional based on test configuration:

```python
def setup_conditional_mapping(self, interface_type):
    if interface_type == 'axi':
        self.master_signal_map = self.axi_signal_map
    elif interface_type == 'avalon':
        self.master_signal_map = self.avalon_signal_map
    else:
        self.master_signal_map = self.default_signal_map
```

### Dynamic Signal Mapping
Signal mapping can be modified during test execution:

```python
async def test_dynamic_mapping(self):
    # Start with one mapping
    await self.test_with_mapping(self.mapping_v1)
    
    # Switch to different mapping
    self.update_signal_mapping(self.mapping_v2)
    await self.test_with_mapping(self.mapping_v2)
```

### Hierarchical Signal Mapping
Support for hierarchical signal structures:

```python
hierarchical_map = {
    'write': 'interface.control.write_enable',
    'addr': 'interface.address.addr_bus',
    'data0': 'interface.data.payload_0',
    'data1': 'interface.data.payload_1'
}
```

## Error Handling and Validation

### Signal Mapping Validation
The testbench includes comprehensive signal mapping validation:

```python
def validate_signal_mapping(self, signal_map, dut):
    """Validate that all mapped signals exist in DUT"""
    for framework_name, dut_signal_name in signal_map.items():
        if not self.signal_exists(dut, dut_signal_name):
            raise SignalMappingError(
                f"Mapped signal '{dut_signal_name}' for '{framework_name}' not found in DUT"
            )
```

### Error Recovery
Graceful handling of signal mapping errors:

```python
try:
    await self.test_with_signal_mapping()
except SignalMappingError as e:
    self.log.error(f"Signal mapping error: {e}")
    self.suggest_alternative_mapping()
    raise
```

### Mapping Diagnostics
Comprehensive diagnostics for signal mapping issues:

```python
def diagnose_signal_mapping(self):
    """Provide diagnostic information for signal mapping issues"""
    available_signals = self.get_available_dut_signals()
    missing_signals = self.find_missing_mapped_signals()
    suggested_mappings = self.suggest_signal_mappings(available_signals)
    
    return {
        'available': available_signals,
        'missing': missing_signals,
        'suggestions': suggested_mappings
    }
```

## Best Practices

### Signal Mapping Design Guidelines

1. **Use Descriptive Names**: Choose signal mapping names that clearly indicate their purpose
2. **Maintain Consistency**: Use consistent naming patterns across similar interfaces
3. **Document Mappings**: Clearly document signal mapping rationale and conventions
4. **Validate Early**: Validate signal mappings during testbench initialization
5. **Handle Errors Gracefully**: Provide clear error messages for mapping failures

### Performance Optimization

1. **Cache Mappings**: Cache signal mapping results to avoid repeated lookups
2. **Minimize Debug**: Disable verbose debug for performance-critical tests
3. **Batch Operations**: Group signal operations to reduce mapping overhead
4. **Profile Impact**: Regularly profile signal mapping performance impact

### Maintenance Strategies

1. **Version Control**: Track signal mapping changes alongside DUT changes
2. **Automated Validation**: Include mapping validation in automated test suites
3. **Documentation**: Maintain clear documentation of mapping conventions
4. **Migration Plans**: Plan signal mapping updates for DUT evolution

This signal mapping capability makes the FIFO testbench framework extremely flexible and adaptable to virtually any FIFO interface design, enabling reuse of verification infrastructure across diverse projects and design styles.