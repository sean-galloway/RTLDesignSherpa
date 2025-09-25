# AXIL4 Components Overview

The CocoTBFramework AXIL4 components provide comprehensive support for AXI4-Lite protocol verification and transaction generation. Built on the proven GAXI infrastructure, these components offer a simplified yet powerful interface for memory-mapped register protocol testing with advanced features optimized for single-transaction, lightweight AXI implementations.

## Framework Integration

### GAXI Infrastructure Foundation

The AXIL4 components inherit from the robust GAXI framework, providing:

**Unified Field Configuration**: Complete integration with the CocoTBFramework field configuration system for flexible register transaction structures
**Memory Model Support**: Seamless integration with memory models and register models for data verification
**Statistics Integration**: Comprehensive performance metrics and transaction tracking
**Signal Resolution**: Automatic signal detection and mapping across different naming conventions
**Advanced Debugging**: Multi-level debugging capabilities with detailed transaction logging

### AXI4-Lite Protocol Specialization

While inheriting GAXI's power, AXIL4 components are specifically optimized for lightweight memory-mapped protocols:

**Simplified Five Channel Architecture**: Complete support for AR, R, AW, W, and B channels without burst complexity
**Single Transaction Model**: No burst support, single outstanding transaction architecture
**Register-Oriented Design**: Optimized for control/status register access patterns
**Reduced Signaling**: No ID, USER, QoS, or REGION signals for simplified implementation
**Protocol Compliance**: Integrated compliance checking for AXI4-Lite specification adherence

## Core Components Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                   AXIL4 Component Ecosystem                    │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ │
│  │AXIL4MstrRd  │ │AXIL4MstrWr  │ │AXIL4SlvRd   │ │AXIL4SlvWr   │ │
│  │ (AR/R)      │ │ (AW/W/B)    │ │ (AR/R)      │ │ (AW/W/B)    │ │
│  │ Single Txn  │ │ Single Txn  │ │ Single Txn  │ │ Single Txn  │ │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────────┘ │
│         │               │               │               │       │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │           AXIL4 Field Configurations (Simplified)          │ │
│  │     AR Config │ R Config │ AW Config │ W Config │ B Config │ │
│  │   (No ID/User)│(No ID/User)│(No ID/User)│(No User)│(No ID/User)│ │
│  └─────────────────────────────────────────────────────────────┘ │
│         │               │               │               │       │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │            AXIL4 Specific Features                         │ │
│  │  • Register API    • Single Outstanding  • Compliance     │ │
│  │  • Packet Utils    • Simplified Timing   • Factories      │ │
│  └─────────────────────────────────────────────────────────────┘ │
│         │               │               │               │       │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │                GAXI Infrastructure                         │ │
│  │  • Signal Resolution  • Memory Models  • Statistics       │ │
│  │  • Field Handling     • Debug Support  • Configuration    │ │
│  └─────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

## Component Capabilities

### AXIL4MasterRead - Register Read Operations

The `AXIL4MasterRead` component drives AXI4-Lite read transactions as a master:

**Address Request Management**:
- **AR Channel Control**: ARADDR, ARPROT management (no ARID, ARLEN, ARSIZE, ARBURST)
- **Single Transaction**: One outstanding transaction model for simplified timing
- **Address Alignment**: Automatic word/byte address alignment
- **Protection Attributes**: ARPROT signal support for access control

**Read Data Reception**:
- **R Channel Monitoring**: RDATA, RRESP processing (no RID, RLAST)
- **Error Handling**: Complete RRESP error detection and reporting (SLVERR, DECERR)
- **Flow Control**: RREADY signal management for backpressure
- **Data Width Handling**: Support for 32-bit and 64-bit data widths

**Register-Oriented API**:
```python
# Register access methods
data = await master_read.read_register(address=0x100)
data = await master_read.single_read(address=0x200)  # API consistency
values = await master_read.read_transaction(address=0x300)  # Generic method
```

### AXIL4MasterWrite - Register Write Operations

The `AXIL4MasterWrite` component drives AXI4-Lite write transactions as a master:

**Address and Data Management**:
- **AW Channel Control**: AWADDR, AWPROT management (no AWID, AWLEN, etc.)
- **W Channel Control**: WDATA, WSTRB coordination (no WID, WLAST)
- **Byte Lane Control**: WSTRB-based byte-level write enable
- **Address/Data Synchronization**: Proper ordering of address and data phases

**Write Response Handling**:
- **B Channel Processing**: BRESP response verification (no BID)
- **Error Detection**: Complete write response error handling
- **Transaction Completion**: Proper write transaction lifecycle management

**Register-Oriented API**:
```python
# Register write methods
await master_write.write_register(address=0x100, data=0x12345678)
await master_write.write_register(address=0x100, data=0xFF, strobe=0x1)  # Byte write
await master_write.single_write(address=0x200, data=0xDEADBEEF)  # API consistency
```

### AXIL4SlaveRead - Register Read Response

The `AXIL4SlaveRead` component responds to AXI4-Lite read transactions as a slave:

**Address Processing**:
- **AR Channel Monitoring**: Read address request detection and decode
- **Address Range Checking**: Configurable address space definition
- **Protection Processing**: ARPROT attribute handling
- **Address Decode Logic**: Simplified decode without burst considerations

**Data Response Generation**:
- **R Channel Control**: RDATA, RRESP generation based on address decode
- **Register Model Integration**: Direct connection to register models
- **Error Response**: Configurable SLVERR, DECERR response generation
- **Response Timing**: Configurable RVALID timing and latency modeling

**Register Model Features**:
```python
# Connect register model
register_model = {
    0x000: RegisterDef("CTRL", 32, reset=0x00000000),
    0x004: RegisterDef("STATUS", 32, reset=0x00000001, readonly=True),
    0x008: RegisterDef("DATA", 32, reset=0x00000000)
}
slave_read.connect_registers(register_model)
```

### AXIL4SlaveWrite - Register Write Response

The `AXIL4SlaveWrite` component responds to AXI4-Lite write transactions as a slave:

**Write Transaction Processing**:
- **AW/W Channel Coordination**: Address and data phase synchronization
- **Write Strobe Processing**: WSTRB-based byte-level write processing
- **Register Update**: Direct register model updates based on address decode
- **Write Protection**: Address-based write protection and access control

**Write Response Generation**:
- **B Channel Control**: BRESP response generation based on write result
- **Error Conditions**: Configurable error response for invalid addresses
- **Response Timing**: Realistic write response latency modeling

**Advanced Features**:
```python
# Write callback registration
def register_write_callback(address, data, strobe):
    print(f"Register 0x{address:03X} = 0x{data:08X} (strobe=0x{strobe:X})")
    # Custom write logic here

slave_write.register_write_callback(register_write_callback)
```

## Field Configuration System

### AXIL4FieldConfigs - Simplified Channel Configuration

The AXIL4 field configuration system provides simplified configurations optimized for AXI4-Lite:

**Simplified Channel Configurations**:
```python
# AR Channel Configuration (no ID, LEN, SIZE, BURST)
ar_config = AXIL4FieldConfigHelper.create_ar_field_config(
    addr_width=32
)

# AW Channel Configuration (no ID, LEN, SIZE, BURST)
aw_config = AXIL4FieldConfigHelper.create_aw_field_config(
    addr_width=32
)

# R Channel Configuration (no ID, LAST)
r_config = AXIL4FieldConfigHelper.create_r_field_config(
    data_width=32
)

# W Channel Configuration (no ID, LAST)
w_config = AXIL4FieldConfigHelper.create_w_field_config(
    data_width=32
)

# B Channel Configuration (no ID)
b_config = AXIL4FieldConfigHelper.create_b_field_config()
```

**Key Simplifications**:
- **No ID Fields**: Single outstanding transaction removes ID requirements
- **No Burst Fields**: AWLEN, ARLEN, AWSIZE, ARSIZE, AWBURST, ARBURST omitted
- **No USER Fields**: Simplified sideband signaling
- **No LAST Fields**: Single transfer per transaction removes WLAST, RLAST

## Advanced Features

### AXIL4ComplianceChecker - Simplified Protocol Verification

The AXIL4 compliance checker focuses on AXI4-Lite specific requirements:

**Protocol Compliance Checking**:
- **Handshake Protocol**: VALID/READY signal timing verification
- **Single Transaction**: Verification of no outstanding transaction violations
- **Address Alignment**: Word/byte alignment requirement checking
- **Response Consistency**: BRESP/RRESP consistency verification

**Simplified Monitoring**:
- **No Burst Checking**: Simplified verification without burst complexity
- **No ID Tracking**: No transaction ID consistency requirements
- **Single Outstanding**: Simple outstanding transaction limit enforcement

### Register Model Integration

AXIL4 components provide extensive register model support:

**Register Definition**:
```python
class RegisterDef:
    def __init__(self, name, width, reset=0, readonly=False, writeonly=False):
        self.name = name
        self.width = width
        self.reset = reset
        self.readonly = readonly
        self.writeonly = writeonly
        self.current_value = reset

# Create register map
register_map = {
    0x000: RegisterDef("DEVICE_ID", 32, reset=0x12345678, readonly=True),
    0x004: RegisterDef("CONTROL", 32, reset=0x00000000),
    0x008: RegisterDef("STATUS", 32, reset=0x00000001, readonly=True),
    0x00C: RegisterDef("DATA_IN", 32, reset=0x00000000, writeonly=True),
    0x010: RegisterDef("DATA_OUT", 32, reset=0x00000000, readonly=True)
}
```

**Register Access Monitoring**:
```python
def register_access_monitor(address, data, is_write, strobe=None):
    reg_name = register_map[address].name if address in register_map else "UNKNOWN"
    operation = "WRITE" if is_write else "READ"
    strobe_info = f" (strobe=0x{strobe:X})" if is_write and strobe is not None else ""
    print(f"Register {operation}: {reg_name} @ 0x{address:03X} = 0x{data:08X}{strobe_info}")
```

## Usage Patterns and Integration

### Basic Register Access

```python
# Create AXIL4 master interfaces
master_read = AXIL4MasterRead(dut, clk, "m_axil_", data_width=32, addr_width=32)
master_write = AXIL4MasterWrite(dut, clk, "m_axil_", data_width=32, addr_width=32)

# Basic register operations
await master_write.write_register(0x100, 0x12345678)  # Write control register
status = await master_read.read_register(0x104)       # Read status register

# Byte-level operations
await master_write.write_register(0x108, 0xFF, strobe=0x1)  # Write byte 0 only
await master_write.write_register(0x108, 0xFF00, strobe=0x2)  # Write byte 1 only
```

### Configuration Space Testing

```python
async def test_configuration_space():
    """Test PCIe-style configuration space access."""

    # Test device identification
    device_id = await master_read.read_register(0x000)
    vendor_id = await master_read.read_register(0x002)

    # Test configuration registers
    await master_write.write_register(0x004, 0x00000006)  # Enable bus master
    command = await master_read.read_register(0x004)
    assert (command & 0x6) == 0x6, "Bus master not enabled"

    # Test BAR configuration
    await master_write.write_register(0x010, 0xFFFFFFFF)  # Write all 1s
    bar0_size = await master_read.read_register(0x010)    # Read back
    size = (~bar0_size + 1) & 0xFFFFFFFF
    print(f"BAR0 size: {size} bytes")
```

### Peripheral Control Interface

```python
async def test_peripheral_control():
    """Test typical peripheral control interface."""

    # Configure peripheral
    await master_write.write_register(0x000, 0x00000001)  # Enable peripheral
    await master_write.write_register(0x004, 0x12345678)  # Set data value
    await master_write.write_register(0x008, 0x00000080)  # Start operation

    # Wait for completion
    while True:
        status = await master_read.read_register(0x00C)
        if status & 0x1:  # Done bit
            break
        await Timer(100, units='ns')

    # Read results
    result = await master_read.read_register(0x010)
    error_status = await master_read.read_register(0x014)

    assert error_status == 0, f"Operation failed with error: {error_status}"
    return result
```

### Memory-Mapped FIFO Testing

```python
async def test_memory_mapped_fifo():
    """Test memory-mapped FIFO interface."""

    # Check FIFO status
    status = await master_read.read_register(0x100)  # FIFO status
    empty = (status >> 0) & 1
    full = (status >> 1) & 1
    count = (status >> 8) & 0xFF

    print(f"FIFO: empty={empty}, full={full}, count={count}")

    # Write data to FIFO
    test_data = [0x11111111, 0x22222222, 0x33333333, 0x44444444]
    for data in test_data:
        await master_write.write_register(0x104, data)  # FIFO data register

    # Read data from FIFO
    read_data = []
    for _ in range(len(test_data)):
        data = await master_read.read_register(0x108)  # FIFO read register
        read_data.append(data)

    assert read_data == test_data, "FIFO data mismatch"
```

## Performance Optimization

### Single Transaction Benefits

**Simplified State Machines**:
- **No Outstanding Tracking**: Single transaction simplifies state management
- **Reduced Latency**: Immediate response without queueing complexity
- **Lower Resource Usage**: Minimal buffering requirements

**Register Access Optimization**:
- **Direct Mapping**: Address directly maps to register without burst decode
- **Immediate Response**: Single-cycle register access patterns
- **Simplified Arbitration**: No complex outstanding transaction arbitration

### Timing Optimization

**Minimal Protocol Overhead**:
```python
# Configure for fastest response
axil_master.configure_timing(
    ar_setup_cycles=0,    # Minimum setup time
    r_response_cycles=1,  # Single cycle response
    aw_setup_cycles=0,    # Minimum setup time
    b_response_cycles=1   # Single cycle write response
)
```

## Debug and Analysis

### Register Access Logging

**Transaction-Level Tracing**:
```python
# Enable comprehensive register access logging
master_read.enable_debug_logging(level='TRACE')
master_write.enable_debug_logging(level='TRACE')

# All register accesses automatically logged with:
# - Address and data values
# - Timing information
# - Strobe patterns for writes
# - Response codes
```

**Register Map Visualization**:
```python
def generate_register_access_report():
    """Generate register access pattern report."""

    access_log = master_read.get_access_log()

    print("Register Access Summary:")
    print("=" * 50)

    for address in sorted(access_log.keys()):
        accesses = access_log[address]
        reg_name = register_map.get(address, {}).get('name', 'UNKNOWN')

        reads = sum(1 for a in accesses if a.is_read)
        writes = sum(1 for a in accesses if not a.is_read)

        print(f"0x{address:03X}: {reg_name:15} - {reads:3} reads, {writes:3} writes")
```

### Performance Analysis

**AXIL4-Specific Metrics**:
- **Register Access Frequency**: Per-register access statistics
- **Response Latency**: Read and write response timing analysis
- **Bus Utilization**: Percentage of time bus is active
- **Error Rate**: SLVERR/DECERR response frequency

## Configuration Examples

### Standard 32-bit Configuration

```python
# Typical 32-bit AXIL4 configuration
axil_config = {
    'data_width': 32,
    'addr_width': 32,
    'strobe_width': 4,    # 32/8 = 4 bytes
    'compliance_check': True,
    'register_model': standard_register_map
}

master_read = AXIL4MasterRead(dut, clk, "m_axil_", **axil_config)
master_write = AXIL4MasterWrite(dut, clk, "m_axil_", **axil_config)
```

### 64-bit AXIL4 Configuration

```python
# 64-bit wide AXIL4 configuration for high-performance applications
axil_64_config = {
    'data_width': 64,
    'addr_width': 64,     # Extended addressing
    'strobe_width': 8,    # 64/8 = 8 bytes
    'register_model': extended_register_map
}

master_read = AXIL4MasterRead(dut, clk, "m_axil_", **axil_64_config)
```

The AXIL4 components provide a comprehensive, efficient, and simplified solution for AXI4-Lite protocol verification, combining the power of the GAXI infrastructure with AXI4-Lite-specific optimizations and advanced features for complete register-oriented interface testing.