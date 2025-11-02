# apb_packet.py

APB Packet and Transaction classes providing object-oriented transaction handling with randomization support. This module extends the base Packet class with APB-specific functionality and includes transaction generators for test stimulus.

## Overview

The `apb_packet.py` module provides two main classes:
- **APBPacket**: Protocol-specific packet extending the base Packet class
- **APBTransaction**: Randomized transaction generator for test stimulus

### Key Features
- **Object-oriented transaction handling** with field validation
- **Built-in randomization** with configurable constraints
- **Protocol compliance checking** for APB specification
- **Flexible field configuration** with default APB layout
- **Integration with base framework** components

## Constants and Mappings

```python
# PWRITE direction mapping
PWRITE_MAP = ['READ', 'WRITE']
```

## Core Classes

### APBPacket

APB-specific packet class that extends the base Packet with APB protocol fields and functionality.

#### Constructor

```python
APBPacket(field_config=None, skip_compare_fields=None, data_width=32, addr_width=32, strb_width=4, **kwargs)
```

**Parameters:**
- `field_config`: Field configuration (default: auto-generated APB config)
- `skip_compare_fields`: Fields to skip during equality comparison
- `data_width`: Width of data fields in bits (default: 32)
- `addr_width`: Width of address field in bits (default: 32)
- `strb_width`: Width of strobe field in bits (default: 4)
- `**kwargs`: Initial field values (e.g., paddr=0x123, pwrite=1)

```python
# Create APB packet with default configuration
packet = APBPacket(
    pwrite=1,           # Write transaction
    paddr=0x1000,       # Address
    pwdata=0xDEADBEEF,  # Write data
    pstrb=0xF           # All strobes active
)

# Create with custom configuration
custom_packet = APBPacket(
    data_width=64,
    addr_width=16,
    strb_width=8,
    pwrite=0,           # Read transaction
    paddr=0x200
)
```

#### Properties

- `direction`: String representation of transaction direction ('READ' or 'WRITE')
- `data_width`: Data field width in bits
- `addr_width`: Address field width in bits  
- `strb_width`: Strobe field width in bits
- `count`: Transaction counter for identification

#### APB Field Configuration

The default APB field configuration includes:

| Field    | Bits | Format | Description |
|----------|------|--------|-------------|
| pwrite   | 1    | dec    | Write Enable (0=Read, 1=Write) |
| paddr    | 32   | hex    | Address |
| pwdata   | 32   | hex    | Write Data |
| prdata   | 32   | hex    | Read Data |
| pstrb    | 4    | bin    | Write Strobes |
| pprot    | 3    | hex    | Protection Control |
| pslverr  | 1    | dec    | Slave Error |

#### Methods

##### `create_apb_field_config(addr_width, data_width, strb_width)` [Static]

Create default field configuration for APB packets.

**Parameters:**
- `addr_width`: Address field width in bits
- `data_width`: Data field width in bits
- `strb_width`: Strobe field width in bits

**Returns:** FieldConfig object with APB fields

```python
# Create custom field configuration
config = APBPacket.create_apb_field_config(
    addr_width=16,
    data_width=64,
    strb_width=8
)

# Use in packet creation
packet = APBPacket(field_config=config)
```

##### `__str__() -> str`

Detailed string representation showing all packet fields.

```python
print(packet)
# Output:
# APB Packet:
#   Direction:  WRITE
#   Address:    0x00001000
#   Write Data: 0xDEADBEEF
#   Strobes:    1111
#   Protection: 0x0
#   Slave Err:  0
#   Start Time: 1000 ns
#   End Time:   2000 ns
#   Duration:   1000 ns
#   Count:      1
```

##### `formatted(compact=False) -> str`

Return formatted string representation.

**Parameters:**
- `compact`: If True, return compact one-line format

```python
# Detailed format
print(packet.formatted())

# Compact format
print(packet.formatted(compact=True))
# Output: APBPacket(time=1000, dir=WRITE, addr=0x00001000, wdata=0xDEADBEEF, strb=1111, prot=0x0)
```

##### `__eq__(other) -> bool`

Compare packets for equality with APB-specific logic.

```python
packet1 = APBPacket(pwrite=1, paddr=0x100, pwdata=0x123)
packet2 = APBPacket(pwrite=1, paddr=0x100, pwdata=0x123)
assert packet1 == packet2  # True

# Direction-aware data comparison
read_packet = APBPacket(pwrite=0, paddr=0x100, prdata=0x456)
write_packet = APBPacket(pwrite=1, paddr=0x100, pwdata=0x123)
assert read_packet != write_packet  # Different directions and data
```

### APBTransaction

Randomized transaction generator that extends the Randomized base class for constraint-based stimulus generation.

#### Constructor

```python
APBTransaction(data_width=32, addr_width=32, strb_width=4, randomizer=None, **kwargs)
```

**Parameters:**
- `data_width`: Data width in bits (default: 32)
- `addr_width`: Address width in bits (default: 32)
- `strb_width`: Strobe width in bits (default: 4)
- `randomizer`: FlexRandomizer instance or constraint dictionary
- `**kwargs`: Initial field values

```python
# Create with default randomization
transaction = APBTransaction()

# Create with custom randomization
custom_randomizer = FlexRandomizer({
    'pwrite': ([(0, 0), (1, 1)], [1, 2]),  # 2:1 write bias
    'paddr': ([(0x1000, 0x1FFF)], [1]),    # Limited address range
    'pstrb': ([(0xF, 0xF)], [1])           # Always full strobes
})

transaction = APBTransaction(
    randomizer=custom_randomizer,
    data_width=64
)
```

#### Default Randomization

The default randomizer provides realistic APB traffic patterns:

```python
# Default randomization constraints
{
    'pwrite': ([(0, 0), (1, 1)], [1, 1]),           # Equal read/write
    'paddr': ([(0, addr_min), (addr_max_lo, addr_max_hi)], [4, 1]),  # Address distribution
    'pstrb': ([(15, 15), (0, 14)], [4, 1]),         # Mostly full strobes
    'pprot': ([(0, 0), (1, 7)], [4, 1])             # Mostly normal protection
}
```

#### Methods

##### `next() -> APBPacket`

Generate the next randomized transaction packet.

**Returns:** APBPacket with randomized field values

```python
# Generate random transactions
for i in range(10):
    packet = transaction.next()
    print(f"Transaction {i}: {packet.formatted(compact=True)}")
```

##### `set_constrained_random() -> 'APBTransaction'`

Set fields using constrained randomization.

**Returns:** Self for method chaining

```python
# Generate and return randomized transaction
packet = transaction.set_constrained_random()
```

##### `formatted(compact=False) -> str`

Return formatted representation of the transaction.

```python
print(transaction.formatted())
print(transaction.formatted(compact=True))
```

## Usage Patterns

### Basic Packet Creation

```python
from CocoTBFramework.components.apb.apb_packet import APBPacket

# Create write packet
write_packet = APBPacket(
    pwrite=1,
    paddr=0x2000,
    pwdata=0x12345678,
    pstrb=0xF,
    pprot=0
)

# Create read packet
read_packet = APBPacket(
    pwrite=0,
    paddr=0x2000,
    pprot=0
)

print(f"Write: {write_packet.formatted(compact=True)}")
print(f"Read: {read_packet.formatted(compact=True)}")
```

### Custom Field Configuration

```python
# Create 64-bit APB configuration
config = APBPacket.create_apb_field_config(
    addr_width=32,
    data_width=64,
    strb_width=8
)

# Create packet with custom configuration
packet = APBPacket(
    field_config=config,
    pwrite=1,
    paddr=0x8000,
    pwdata=0x123456789ABCDEF0,
    pstrb=0xFF  # All 8 strobes active
)
```

### Transaction Generation

```python
from CocoTBFramework.components.apb.apb_packet import APBTransaction

# Create transaction generator
transaction = APBTransaction(
    data_width=32,
    addr_width=16
)

# Generate test sequence
packets = []
for i in range(100):
    packet = transaction.next()
    packets.append(packet)

# Analyze generated patterns
write_count = sum(1 for p in packets if p.direction == 'WRITE')
read_count = len(packets) - write_count
print(f"Generated {write_count} writes, {read_count} reads")
```

### Constrained Randomization

```python
# Create address-constrained randomizer
address_randomizer = FlexRandomizer({
    'pwrite': ([(0, 0), (1, 1)], [1, 1]),
    'paddr': ([(0x1000, 0x1FFF), (0x8000, 0x8FFF)], [3, 1]),  # Prefer low addresses
    'pstrb': ([(0xF, 0xF), (0x3, 0x3), (0xC, 0xC)], [6, 1, 1]),  # Various strobe patterns
    'pprot': ([(0, 0)], [1])  # Always normal protection
})

# Create constrained transaction generator
constrained_transaction = APBTransaction(randomizer=address_randomizer)

# Generate constrained sequence
for i in range(20):
    packet = constrained_transaction.next()
    print(f"Addr: 0x{packet.paddr:04X}, Strb: 0b{packet.pstrb:04b}, Dir: {packet.direction}")
```

### Register Access Patterns

```python
def create_register_access_sequence(base_addr, num_regs):
    """Create sequence for register testing"""
    packets = []
    
    # Write pattern to all registers
    for i in range(num_regs):
        addr = base_addr + (i * 4)
        data = 0xA0000000 + i
        
        write_packet = APBPacket(
            pwrite=1,
            paddr=addr,
            pwdata=data,
            pstrb=0xF,
            count=len(packets)
        )
        packets.append(write_packet)
    
    # Read back all registers
    for i in range(num_regs):
        addr = base_addr + (i * 4)
        
        read_packet = APBPacket(
            pwrite=0,
            paddr=addr,
            count=len(packets)
        )
        packets.append(read_packet)
    
    return packets

# Generate register test sequence
reg_packets = create_register_access_sequence(0x1000, 16)
```

### Error Testing Patterns

```python
def create_error_test_packets():
    """Create packets for error testing"""
    packets = []
    
    # Valid transaction
    valid_packet = APBPacket(
        pwrite=1,
        paddr=0x100,
        pwdata=0x12345678,
        pstrb=0xF,
        pslverr=0
    )
    packets.append(valid_packet)
    
    # Transaction that should cause slave error
    error_packet = APBPacket(
        pwrite=1,
        paddr=0xDEAD,  # Invalid address
        pwdata=0xBAADF00D,
        pstrb=0xF,
        pslverr=0  # Will be set by slave
    )
    packets.append(error_packet)
    
    return packets
```

### Strobe Pattern Testing

```python
def create_strobe_test_packets(base_addr):
    """Create packets testing different strobe patterns"""
    packets = []
    test_data = 0x12345678
    
    # Test individual byte strobes
    for byte_pos in range(4):
        strobe = 1 << byte_pos
        packet = APBPacket(
            pwrite=1,
            paddr=base_addr,
            pwdata=test_data,
            pstrb=strobe,
            count=len(packets)
        )
        packets.append(packet)
    
    # Test combinations
    strobe_patterns = [0x3, 0xC, 0x5, 0xA, 0x7, 0xE, 0xF]
    for pattern in strobe_patterns:
        packet = APBPacket(
            pwrite=1,
            paddr=base_addr + 4,
            pwdata=test_data,
            pstrb=pattern,
            count=len(packets)
        )
        packets.append(packet)
    
    return packets
```

### Performance Testing

```python
def create_performance_test_sequence(num_transactions):
    """Create high-performance test sequence"""
    # Use transaction generator for variety
    transaction = APBTransaction()
    
    # Override randomizer for performance testing
    perf_randomizer = FlexRandomizer({
        'pwrite': ([(1, 1)], [1]),  # All writes for performance
        'paddr': ([(0x1000, 0x2000)], [1]),  # Sequential addresses
        'pstrb': ([(0xF, 0xF)], [1]),  # Always full strobes
        'pprot': ([(0, 0)], [1])  # Normal protection
    })
    
    transaction.randomizer = perf_randomizer
    
    # Generate performance sequence
    packets = []
    for i in range(num_transactions):
        packet = transaction.next()
        packet.count = i
        packets.append(packet)
    
    return packets
```

### Packet Validation

```python
def validate_apb_packet(packet):
    """Validate APB packet for protocol compliance"""
    errors = []
    
    # Check required fields
    if packet.pwrite not in [0, 1]:
        errors.append("Invalid PWRITE value")
    
    # Address alignment check (assuming 32-bit data)
    if packet.paddr % 4 != 0:
        errors.append("Address not word-aligned")
    
    # Strobe validation for writes
    if packet.direction == 'WRITE':
        if packet.pstrb == 0:
            errors.append("No strobes active for write")
        
        # Check strobe-data consistency
        if packet.pstrb > 0xF:
            errors.append("Invalid strobe pattern")
    
    # Protection field validation
    if packet.pprot > 7:
        errors.append("Invalid protection value")
    
    return errors

# Validate packet
packet = APBPacket(pwrite=1, paddr=0x103, pwdata=0x123, pstrb=0xF)
validation_errors = validate_apb_packet(packet)
if validation_errors:
    print(f"Validation errors: {validation_errors}")
```

## Integration with Test Framework

### Testbench Integration

```python
import cocotb
from cocotb.triggers import RisingEdge
from CocoTBFramework.components.apb import APBMaster, APBPacket

@cocotb.test()
async def packet_driven_test(dut):
    # Create master
    master = APBMaster(dut, "Master", "apb_", dut.clk)
    
    # Create test packets
    packets = [
        APBPacket(pwrite=1, paddr=0x100, pwdata=0x11111111),
        APBPacket(pwrite=1, paddr=0x104, pwdata=0x22222222),
        APBPacket(pwrite=0, paddr=0x100),
        APBPacket(pwrite=0, paddr=0x104)
    ]
    
    # Send packets
    for packet in packets:
        await master.send(packet)
        print(f"Sent: {packet.formatted(compact=True)}")
    
    # Wait for completion
    while master.transfer_busy:
        await RisingEdge(dut.clk)
```

### Scoreboard Integration

```python
class APBScoreboard:
    def __init__(self):
        self.expected_packets = []
        self.actual_packets = []
    
    def add_expected(self, packet):
        self.expected_packets.append(packet)
    
    def add_actual(self, packet):
        self.actual_packets.append(packet)
        self.check_transaction()
    
    def check_transaction(self):
        if len(self.actual_packets) <= len(self.expected_packets):
            expected = self.expected_packets[len(self.actual_packets) - 1]
            actual = self.actual_packets[-1]
            
            if expected == actual:
                print("✓ Transaction match")
            else:
                print(f"✗ Transaction mismatch:")
                print(f"  Expected: {expected.formatted(compact=True)}")
                print(f"  Actual:   {actual.formatted(compact=True)}")
```

## Best Practices

### 1. **Use Appropriate Field Widths**
```python
# Match your DUT configuration
packet = APBPacket(
    data_width=32,     # Match DUT data width
    addr_width=16,     # Match DUT address width
    strb_width=4       # data_width / 8
)
```

### 2. **Validate Packets Before Use**
```python
# Always validate critical fields
assert packet.direction in ['READ', 'WRITE']
assert packet.paddr % 4 == 0  # Word alignment
if packet.direction == 'WRITE':
    assert packet.pstrb > 0  # At least one strobe
```

### 3. **Use Transactions for Random Testing**
```python
# Use transaction generators for stimulus
transaction = APBTransaction(randomizer=custom_randomizer)
for _ in range(1000):
    packet = transaction.next()
    # Send to DUT
```

### 4. **Handle Timing Information**
```python
# Set timing for performance analysis
import cocotb
packet.start_time = cocotb.utils.get_sim_time('ns')
# ... send packet ...
packet.end_time = cocotb.utils.get_sim_time('ns')
duration = packet.end_time - packet.start_time
```

### 5. **Use Compact Format for Logging**
```python
# Use compact format in loops
for packet in packet_sequence:
    print(f"Processing: {packet.formatted(compact=True)}")
```

The APB packet classes provide a robust foundation for APB transaction handling, from simple directed tests to complex randomized stimulus generation, with full integration into the verification framework.