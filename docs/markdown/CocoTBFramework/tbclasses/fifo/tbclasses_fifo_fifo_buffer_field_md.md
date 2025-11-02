# fifo_buffer_field.py

Multi-field FIFO buffer testbench for complex data structures. This testbench handles FIFOs with structured packets containing multiple fields such as address, control, and data fields.

## Overview

The `FifoFieldBufferTB` class provides comprehensive verification for FIFOs that handle complex, structured data packets. Instead of simple data values, this testbench works with packets containing multiple fields (addr, ctrl, data0, data1), making it ideal for protocol-specific FIFOs and complex data processing applications.

## Key Features

- **Multi-Field Packet Support**: Address, control, and multiple data fields
- **Field-Specific Testing**: Individual field isolation and validation
- **Advanced Memory Modeling**: Memory regions for different field types
- **Field Configuration Management**: Dynamic field width and format control
- **Enhanced Randomization**: Field-specific randomization patterns

## Class Definition

```python
class FifoFieldBufferTB(TBBase):
    """Testbench for multi-field FIFO components using FlexConfigGen only for randomization"""
```

## Constructor Parameters

```python
def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None, super_debug=False):
```

### Parameters
- **dut**: Device Under Test (DUT) object
- **wr_clk**: Write clock signal (optional, auto-detected if None)
- **wr_rstn**: Write reset signal (optional, auto-detected if None)
- **rd_clk**: Read clock signal (optional, auto-detected if None)
- **rd_rstn**: Read reset signal (optional, auto-detected if None)
- **super_debug**: Enable enhanced debug logging (default: False)

## Environment Configuration

Extended configuration for multi-field operations:

### Field Width Parameters
- `TEST_ADDR_WIDTH`: Address field width in bits (required)
- `TEST_CTRL_WIDTH`: Control field width in bits (required)
- `TEST_DATA_WIDTH`: Data field width in bits (required)

### Core Parameters
- `TEST_DEPTH`: FIFO depth (required)
- `TEST_MODE`: Operation mode ('fifo_mux', 'fifo_simple') (default: 'fifo_mux')
- `TEST_KIND`: Clock domain type ('sync', 'async') (default: 'sync')

### Clock Configuration
- `TEST_CLK_WR`: Write clock period in ns (default: 10)
- `TEST_CLK_RD`: Read clock period in ns (default: 10)

### Test Control
- `SEED`: Random seed for reproducible tests (default: 12345)

## Field Configuration

The testbench uses `FieldConfig` from `FIELD_CONFIGS['field']` and dynamically adjusts field widths:

### Supported Fields
- **addr**: Address field with configurable width
- **ctrl**: Control field with configurable width  
- **data0**: First data field with configurable width
- **data1**: Second data field with configurable width

### Field Properties
Each field includes:
- Bit width configuration
- Display format (hex, decimal, binary)
- Default values
- Active bit ranges
- Field descriptions

## Memory Model Architecture

### Memory Regions

The testbench creates specialized memory regions:

```python
self.memory_model.define_region('addr_fields', 0, TEST_DEPTH // 4 - 1, 'Address fields')
self.memory_model.define_region('ctrl_fields', TEST_DEPTH // 4, TEST_DEPTH // 2 - 1, 'Control fields')  
self.memory_model.define_region('data_fields', TEST_DEPTH // 2, TEST_DEPTH - 1, 'Data fields')
```

This segmentation provides:
- **Targeted Analysis**: Field-specific memory analysis
- **Enhanced Debugging**: Region-based error detection
- **Performance Metrics**: Per-field performance tracking

## Component Architecture

### Packet Structure

```python
packet = FIFOPacket(field_config)
packet.addr = address_value
packet.ctrl = control_value  
packet.data0 = first_data_value
packet.data1 = second_data_value
```

### Signal Interface

Multi-field interface with structured signals:
- Write side: `write`, `addr`, `ctrl`, `data0`, `data1`, `full`
- Read side: `read`, `addr`, `ctrl`, `data0`, `data1`, `empty`

## Test Methods

### Field-Specific Tests

#### `test_field_isolation(packet_count=100)`
Tests each field independently to verify field isolation.

**Purpose**: Verify individual field behavior and independence
**Pattern**: Vary one field while keeping others constant
**Verification**: Field-specific data integrity

```python
await tb.test_field_isolation(packet_count=100)
```

**Test Patterns:**
- **Address Isolation**: Only address field varies
- **Control Isolation**: Only control field varies
- **Data0 Isolation**: Only first data field varies
- **Data1 Isolation**: Only second data field varies

#### `test_field_combinations(packet_count=200)`
Tests various field combinations to verify field interactions.

**Purpose**: Verify field combination handling
**Pattern**: Multiple field variations in structured patterns
**Verification**: Complex field interaction validation

### Advanced Randomization Tests

#### `test_randomized_fields(packet_count=500, profile='balanced')`
Field-specific randomization with configurable profiles.

**Purpose**: Comprehensive field randomization testing
**Randomization**: Independent field randomization with correlations
**Verification**: Complex random pattern validation

```python
await tb.test_randomized_fields(packet_count=300, profile='aggressive')
```

### Stress Tests

#### `test_field_stress(packet_count=1000)`
High-stress testing with rapid field changes.

**Purpose**: Maximum rate field variation testing
**Pattern**: Rapid-fire field changes with back-to-back operations
**Verification**: High-speed field integrity

#### `test_mixed_field_traffic(packet_count=800)`
Mixed traffic with varying field patterns.

**Purpose**: Realistic field usage pattern testing
**Pattern**: Mixed field patterns with random timing
**Verification**: Complex traffic field handling

## Usage Examples

### Basic Field Testing

```python
import cocotb
import os
from CocoTBFramework.tbclasses.fifo.fifo_buffer_field import FifoFieldBufferTB

@cocotb.test()
async def test_field_fifo(dut):
    # Configure field widths
    os.environ['TEST_ADDR_WIDTH'] = '16'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_DEPTH'] = '32'
    
    tb = FifoFieldBufferTB(dut, super_debug=True)
    await tb.initialize()
    
    # Field-specific tests
    await tb.test_field_isolation(packet_count=50)
    await tb.test_field_combinations(packet_count=100)
    
    tb.verify_results()
```

### Advanced Field Configuration

```python
@cocotb.test()
async def test_advanced_field_fifo(dut):
    # Configure for complex fields
    os.environ['TEST_ADDR_WIDTH'] = '20'
    os.environ['TEST_CTRL_WIDTH'] = '12'
    os.environ['TEST_DATA_WIDTH'] = '64'
    os.environ['TEST_DEPTH'] = '64'
    os.environ['TEST_MODE'] = 'fifo_mux'
    
    tb = FifoFieldBufferTB(dut, super_debug=True)
    await tb.initialize()
    
    # Comprehensive field testing
    await tb.test_field_isolation(packet_count=100)
    await tb.test_randomized_fields(packet_count=400, profile='balanced')
    await tb.test_field_stress(packet_count=200)
    await tb.test_mixed_field_traffic(packet_count=300)
    
    tb.verify_results()
```

### Protocol-Specific Testing

```python
@cocotb.test()
async def test_protocol_fifo(dut):
    # Configure for specific protocol
    os.environ['TEST_ADDR_WIDTH'] = '32'  # Memory address
    os.environ['TEST_CTRL_WIDTH'] = '16'  # Command/status
    os.environ['TEST_DATA_WIDTH'] = '256' # Payload data
    os.environ['TEST_DEPTH'] = '128'
    
    tb = FifoFieldBufferTB(dut)
    await tb.initialize()
    
    # Protocol-specific patterns
    await tb.test_protocol_commands()
    await tb.test_address_sequencing()
    await tb.test_data_payload_integrity()
    
    tb.verify_results()
```

## Field Randomization Profiles

### Conservative Field Profile
- Minimal field value changes
- Predictable field patterns
- Address/control stability focus

### Moderate Field Profile
- Balanced field randomization
- Mixed predictable and random patterns
- Good for general field testing

### Aggressive Field Profile
- Maximum field variation
- Rapid field value changes
- Stress testing focus

### Balanced Field Profile
- Optimized field variation mix
- Comprehensive field coverage
- Recommended for thorough testing

## Verification Features

### Field-Specific Verification

**Field Integrity**: Individual field value verification
**Field Ordering**: Proper field sequencing verification  
**Field Independence**: Cross-field interference detection
**Field Boundaries**: Field width and value range verification

### Advanced Analysis

**Field Statistics**: Per-field performance metrics
**Field Patterns**: Field usage pattern analysis
**Field Correlation**: Inter-field relationship analysis
**Field Efficiency**: Field utilization metrics

### Debug Capabilities

**Field Tracing**: Complete field-level transaction traces
**Field Comparison**: Reference model field comparison
**Field Error Analysis**: Field-specific error detection and reporting
**Field Memory Mapping**: Memory region analysis for field data

## Common Field Patterns

### Address Sequencing
Testing sequential address patterns for memory-like operations:

```python
for i in range(packet_count):
    packet = FIFOPacket(field_config)
    packet.addr = base_addr + (i * stride)
    packet.ctrl = operation_type
    packet.data0 = payload_data
    await master.send(packet)
```

### Command/Response Patterns
Testing command/status field patterns:

```python
commands = ['READ', 'WRITE', 'STATUS', 'CONFIG']
for cmd in commands:
    packet = FIFOPacket(field_config)
    packet.addr = target_addr
    packet.ctrl = encode_command(cmd)
    packet.data0 = command_data
    await master.send(packet)
```

### Data Payload Patterns
Testing large data payload patterns:

```python
for chunk in data_chunks:
    packet = FIFOPacket(field_config)
    packet.addr = chunk_addr
    packet.ctrl = chunk_info
    packet.data0 = chunk[:width]
    packet.data1 = chunk[width:]
    await master.send(packet)
```

## Integration with Protocol Stacks

This field-based testbench integrates well with protocol verification:

- **AXI Protocols**: Address, control, and data field mapping
- **PCIe TLPs**: Header and payload field structures
- **Network Protocols**: Header and payload separation
- **Custom Protocols**: Flexible field configuration for any protocol

The structured field approach enables protocol-aware testing while maintaining the flexibility to adapt to various field configurations and requirements.