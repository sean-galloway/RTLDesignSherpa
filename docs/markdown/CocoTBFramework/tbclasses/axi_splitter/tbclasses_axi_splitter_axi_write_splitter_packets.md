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

# axi_write_splitter_packets.py

This module provides common AXI Write Splitter packet definitions that create shared packet classes based on field configurations. These packets are specifically designed for AXI write operations and extend the read splitter concept to handle the three-channel write flow (AW → W → B).

## Purpose

The packet classes extend GAXIPacket and provide:
- Write-specific packet structures for AW, W, and B channels
- Consistent packet handling across write testbench components
- Type-safe write transaction management
- Write data distribution and strobe pattern support
- Response consolidation tracking for write operations

## Key Components

### Field Configuration Functions

#### `create_axi_write_address_field_config(id_width=8, addr_width=32, user_width=1)`

Creates field configuration for AXI write address channel (AW) packets.

**Parameters:**
- `id_width`: Transaction ID width (default: 8 bits)
- `addr_width`: Address width (default: 32 bits)
- `user_width`: User signal width (default: 1 bit)

**Returns:** FieldConfig object with AXI write address channel fields

**Generated Fields:**
- `id`: Transaction ID (hex format)
- `addr`: Write address (hex format)
- `len`: Burst length - transfers minus 1 (decimal)
- `size`: Burst size - bytes per transfer (decimal)
- `burst`: Burst type (FIXED=0, INCR=1, WRAP=2)
- `lock`: Lock type (decimal)
- `cache`: Cache control (hex)
- `prot`: Protection attributes (hex)
- `qos`: Quality of Service (decimal)
- `region`: Region identifier (decimal)
- `user`: User-defined attributes (hex, if user_width > 0)

#### `create_axi_write_data_field_config(data_width=32, user_width=1)`

Creates field configuration for AXI write data channel (W) packets.

**Parameters:**
- `data_width`: Data width (default: 32 bits)
- `user_width`: User signal width (default: 1 bit)

**Returns:** FieldConfig object with AXI write data channel fields

**Generated Fields:**
- `data`: Write data (hex format)
- `strb`: Write strobes/byte enables (hex format, width = data_width/8)
- `last`: Last transfer in burst indicator (WLAST)
- `user`: User-defined attributes (hex, if user_width > 0)

#### `create_axi_write_response_field_config(id_width=8, user_width=1)`

Creates field configuration for AXI write response channel (B) packets.

**Parameters:**
- `id_width`: Transaction ID width (default: 8 bits)
- `user_width`: User signal width (default: 1 bit)

**Returns:** FieldConfig object with AXI write response channel fields

**Generated Fields:**
- `id`: Transaction ID (hex format)
- `resp`: Response status with encoding (OKAY=0, EXOKAY=1, SLVERR=2, DECERR=3)
- `user`: User-defined attributes (hex, if user_width > 0)

#### `create_write_split_info_field_config(id_width=8, addr_width=32)`

Creates field configuration for write split information tracking.

**Parameters:**
- `id_width`: Transaction ID width (default: 8 bits)
- `addr_width`: Address width (default: 32 bits)

**Returns:** FieldConfig object with write split information fields

**Generated Fields:**
- `addr`: Original write address (hex format)
- `id`: Original transaction ID (hex format)
- `cnt`: Number of split transactions (decimal)

### Packet Classes

#### `AXIWriteAddressPacket`

Represents AXI Write Address Channel (AW) packets using field configuration. Replaces custom AWTransaction class with field-config-based implementation.

**Key Methods:**
- `from_dict(data, field_config)`: Create packet from dictionary data
- `to_dict()`: Convert packet to dictionary
- `get_burst_type_name()`: Get burst type as string
- `calculate_total_bytes()`: Calculate total bytes in write burst
- `will_cross_boundary(boundary_size)`: Check if write transaction crosses boundary
- `calculate_write_beats()`: Calculate number of write beats required

**Usage:**
```python
# Create write address packet
aw_config = create_axi_write_address_field_config()
aw_packet = AXIWriteAddressPacket(aw_config)
aw_packet.id = 0x42
aw_packet.addr = 0x1000
aw_packet.len = 7  # 8 transfers
aw_packet.size = 2  # 4 bytes per transfer

# Check boundary crossing for write
crosses = aw_packet.will_cross_boundary(0x1000)  # 4KB boundary
total_bytes = aw_packet.calculate_total_bytes()  # 32 bytes
write_beats = aw_packet.calculate_write_beats()  # 8 beats
```

#### `AXIWriteDataPacket`

Represents AXI Write Data Channel (W) packets using field configuration.

**Key Methods:**
- `from_dict(data, field_config)`: Create packet from dictionary data
- `to_dict()`: Convert packet to dictionary
- `get_strobe_pattern()`: Get write strobe pattern as string
- `is_last_transfer()`: Check if this is the last transfer (WLAST)
- `calculate_valid_bytes()`: Calculate number of valid bytes based on strobes
- `generate_strobe_pattern(byte_count, data_width)`: Generate appropriate strobe pattern

**Usage:**
```python
# Create write data packet
w_config = create_axi_write_data_field_config(data_width=64)
w_packet = AXIWriteDataPacket(w_config)
w_packet.data = 0xDEADBEEFCAFEBABE
w_packet.strb = 0xFF  # All bytes valid
w_packet.last = 1     # Last transfer

# Analyze strobe pattern
valid_bytes = w_packet.calculate_valid_bytes()  # 8 bytes
strobe_pattern = w_packet.get_strobe_pattern()  # "11111111"
```

#### `AXIWriteResponsePacket`

Represents AXI Write Response Channel (B) packets using field configuration.

**Key Methods:**
- `from_dict(data, field_config)`: Create packet from dictionary data
- `to_dict()`: Convert packet to dictionary
- `get_response_name()`: Get response status as string
- `is_error_response()`: Check if response indicates error
- `is_okay_response()`: Check if response is OKAY

**Usage:**
```python
# Create write response packet
b_config = create_axi_write_response_field_config()
b_packet = AXIWriteResponsePacket(b_config)
b_packet.id = 0x42
b_packet.resp = 0  # OKAY

# Check response status
resp_name = b_packet.get_response_name()  # "OKAY"
is_error = b_packet.is_error_response()   # False
is_okay = b_packet.is_okay_response()     # True
```

#### `WriteSplitInfoPacket`

Represents write split information for tracking write transaction splitting.

**Key Methods:**
- `from_dict(data, field_config)`: Create packet from dictionary data
- `to_dict()`: Convert packet to dictionary
- `calculate_expected_data_beats()`: Calculate expected write data beats
- `calculate_split_boundaries()`: Calculate split boundary information

**Usage:**
```python
# Create write split info packet
split_config = create_write_split_info_field_config()
split_packet = WriteSplitInfoPacket(split_config)
split_packet.addr = 0x1000
split_packet.id = 0x42
split_packet.cnt = 3  # Split into 3 transactions

# Calculate write-specific information
data_beats = split_packet.calculate_expected_data_beats()
boundaries = split_packet.calculate_split_boundaries()
```

### Write Transaction State Management

#### `SplitWriteTransactionState`

Enumeration for tracking split write transaction states:
- `PENDING`: Transaction submitted, waiting for address phase
- `ADDRESS_SENT`: AW sent, waiting for data phase
- `DATA_PARTIAL`: Some data sent, more data expected
- `DATA_COMPLETE`: All data sent, waiting for response
- `COMPLETE`: Response received, transaction complete
- `ERROR`: Error occurred during processing

#### `SplitWriteTransaction`

Dataclass for comprehensive split write transaction tracking.

**Attributes:**
- `original_aw`: Original AXI write address packet
- `split_info`: Write split information packet (optional)
- `split_aws`: List of split write address packets
- `expected_data_beats`: Expected number of write data beats
- `received_data_beats`: List of received write data packets
- `expected_responses`: Expected number of write responses
- `received_responses`: List of received write response packets
- `state`: Current write transaction state
- `start_time`: Transaction start timestamp
- `completion_time`: Transaction completion timestamp (optional)
- `errors`: List of error messages

**Key Methods:**
- `add_split_aw(aw_packet)`: Add a split AW transaction
- `add_data_beat(w_packet)`: Add a write data beat
- `add_response(b_packet)`: Add a write response
- `add_error(error)`: Add an error message
- `is_address_complete()`: Check if address phase is complete
- `is_data_complete()`: Check if data phase is complete
- `is_complete()`: Check if entire transaction is complete
- `has_errors()`: Check if transaction has errors
- `get_duration()`: Get transaction duration
- `calculate_data_integrity()`: Verify data integrity across splits

**Usage:**
```python
# Create split write transaction tracker
split_write_txn = SplitWriteTransaction(
    original_aw=original_aw_packet,
    split_info=None,
    split_aws=[],
    expected_data_beats=8,
    received_data_beats=[],
    expected_responses=1,
    received_responses=[],
    state=SplitWriteTransactionState.PENDING,
    start_time=time.time()
)

# Track write progress through phases
split_write_txn.add_split_aw(split_aw_packet_1)  # Address phase
split_write_txn.add_data_beat(w_packet_1)        # Data phase
split_write_txn.add_response(b_packet)           # Response phase

# Check completion status
if split_write_txn.is_complete():
    duration = split_write_txn.get_duration()
    integrity = split_write_txn.calculate_data_integrity()
```

### Conversion Utilities

#### `convert_gaxi_packet_to_axi_write_address(gaxi_packet, field_config)`

Converts a GAXI packet to an AXI write address packet.

**Parameters:**
- `gaxi_packet`: Source GAXI packet
- `field_config`: Target field configuration (optional)

**Returns:** AXIWriteAddressPacket with converted data

#### `convert_gaxi_packet_to_axi_write_data(gaxi_packet, field_config)`

Converts a GAXI packet to an AXI write data packet.

**Parameters:**
- `gaxi_packet`: Source GAXI packet
- `field_config`: Target field configuration (optional)

**Returns:** AXIWriteDataPacket with converted data

#### `convert_gaxi_packet_to_axi_write_response(gaxi_packet, field_config)`

Converts a GAXI packet to an AXI write response packet.

**Parameters:**
- `gaxi_packet`: Source GAXI packet
- `field_config`: Target field configuration (optional)

**Returns:** AXIWriteResponsePacket with converted data

## Write-Specific Features

### Write Strobe Handling

```python
# Generate appropriate strobe patterns
def generate_write_strobes(data_width, valid_bytes, start_offset=0):
    """Generate write strobe pattern for partial writes"""
    strobe_width = data_width // 8
    strobe_mask = 0
    
    for i in range(valid_bytes):
        byte_pos = (start_offset + i) % strobe_width
        strobe_mask |= (1 << byte_pos)
    
    return strobe_mask
```

### Write Data Distribution

```python
# Distribute write data across split transactions
def distribute_write_data(original_data, split_info):
    """Distribute original write data across split transactions"""
    split_data = []
    bytes_per_split = split_info.bytes_per_split
    
    for split_idx in range(split_info.cnt):
        start_byte = split_idx * bytes_per_split
        end_byte = min(start_byte + bytes_per_split, len(original_data))
        split_data.append(original_data[start_byte:end_byte])
    
    return split_data
```

## Integration with Write Testbench Components

### With Write Scoreboard

```python
from .axi_write_splitter_packets import *

# In write scoreboard initialization
self.write_addr_field_config = create_axi_write_address_field_config(
    id_width=8, addr_width=32, user_width=1
)
self.write_data_field_config = create_axi_write_data_field_config(
    data_width=64, user_width=1
)
self.write_resp_field_config = create_axi_write_response_field_config(
    id_width=8, user_width=1
)

# Convert and track write packets
aw_packet = convert_gaxi_packet_to_axi_write_address(gaxi_packet, self.write_addr_field_config)
w_packet = convert_gaxi_packet_to_axi_write_data(gaxi_packet, self.write_data_field_config)
b_packet = convert_gaxi_packet_to_axi_write_response(gaxi_packet, self.write_resp_field_config)
```

### With Write Testbench

```python
from .axi_write_splitter_packets import *

# Create write test transactions
aw_config = create_axi_write_address_field_config()
test_aw_packet = AXIWriteAddressPacket(aw_config)
test_aw_packet.addr = boundary_crossing_address
test_aw_packet.len = 15  # 16 transfers

# Generate corresponding write data
w_config = create_axi_write_data_field_config(data_width=64)
for beat in range(16):
    w_packet = AXIWriteDataPacket(w_config)
    w_packet.data = generate_write_data_pattern(beat)
    w_packet.strb = 0xFF  # All bytes valid
    w_packet.last = 1 if beat == 15 else 0
```

## Benefits

**Write-Specific Design**: Tailored for AXI write operations with three-channel flow support.

**Strobe Pattern Support**: Comprehensive write strobe handling for partial writes.

**Data Distribution**: Built-in support for distributing write data across split transactions.

**Response Consolidation**: Proper tracking of write response consolidation.

**Consistency**: Ensures consistent packet handling across all write testbench components.

**Type Safety**: Strong typing with field validation prevents write-specific errors.

**Flexibility**: Configurable field configurations for different write scenarios.

This packet framework provides the foundation for robust AXI write splitter verification by ensuring consistent, type-safe write transaction handling across all testbench components.