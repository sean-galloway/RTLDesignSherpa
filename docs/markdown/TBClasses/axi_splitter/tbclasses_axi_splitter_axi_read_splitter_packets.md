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

# axi_read_splitter_packets.py

This module provides common AXI Read Splitter packet definitions that create shared packet classes based on field configurations. These packets can be used by both the testbench and scoreboard, ensuring consistency and eliminating duplicate transaction definitions.

## Purpose

The packet classes extend GAXIPacket and use field configurations to provide:
- Consistent packet structure across testbench components
- Type-safe transaction handling
- Automatic field validation and encoding
- Conversion utilities between different packet formats

## Key Components

### Field Configuration Functions

#### `create_axi_address_field_config(id_width=8, addr_width=32, user_width=1)`

Creates field configuration for AXI address channel (AR) packets.

**Parameters:**
- `id_width`: Transaction ID width (default: 8 bits)
- `addr_width`: Address width (default: 32 bits)  
- `user_width`: User signal width (default: 1 bit)

**Returns:** FieldConfig object with AXI address channel fields

**Generated Fields:**
- `id`: Transaction ID (hex format)
- `addr`: Address (hex format)
- `len`: Burst length - transfers minus 1 (decimal)
- `size`: Burst size - bytes per transfer (decimal)
- `burst`: Burst type (FIXED=0, INCR=1, WRAP=2)
- `lock`: Lock type (decimal)
- `cache`: Cache control (hex)
- `prot`: Protection attributes (hex)
- `qos`: Quality of Service (decimal)
- `region`: Region identifier (decimal)
- `user`: User-defined attributes (hex, if user_width > 0)

#### `create_axi_data_field_config(id_width=8, data_width=32, user_width=1)`

Creates field configuration for AXI data channel (R) packets.

**Parameters:**
- `id_width`: Transaction ID width (default: 8 bits)
- `data_width`: Data width (default: 32 bits)
- `user_width`: User signal width (default: 1 bit)

**Returns:** FieldConfig object with AXI data channel fields

**Generated Fields:**
- `id`: Transaction ID (hex format)
- `data`: Read data (hex format)
- `resp`: Response status with encoding (OKAY=0, EXOKAY=1, SLVERR=2, DECERR=3)
- `last`: Last transfer in burst indicator (decimal)
- `user`: User-defined attributes (hex, if user_width > 0)

#### `create_split_info_field_config(id_width=8, addr_width=32)`

Creates field configuration for split information tracking.

**Parameters:**
- `id_width`: Transaction ID width (default: 8 bits)
- `addr_width`: Address width (default: 32 bits)

**Returns:** FieldConfig object with split information fields

**Generated Fields:**
- `addr`: Original address (hex format)
- `id`: Original transaction ID (hex format)
- `cnt`: Number of split transactions (decimal)

### Packet Classes

#### `AXIAddressPacket`

Represents AXI Address Channel packets using field configuration. Replaces custom ARTransaction class with field-config-based implementation.

**Key Methods:**
- `from_dict(data, field_config)`: Create packet from dictionary data
- `to_dict()`: Convert packet to dictionary
- `get_burst_type_name()`: Get burst type as string
- `calculate_total_bytes()`: Calculate total bytes in burst
- `will_cross_boundary(boundary_size)`: Check if transaction crosses boundary

**Usage:**
```python
# Create address packet
addr_config = create_axi_address_field_config()
ar_packet = AXIAddressPacket(addr_config)
ar_packet.id = 0x42
ar_packet.addr = 0x1000
ar_packet.len = 7  # 8 transfers
ar_packet.size = 2  # 4 bytes per transfer

# Check boundary crossing
crosses = ar_packet.will_cross_boundary(0x1000)  # 4KB boundary
total_bytes = ar_packet.calculate_total_bytes()  # 32 bytes
```

#### `AXIDataPacket`

Represents AXI Data Channel packets using field configuration. Replaces custom RTransaction class with field-config-based implementation.

**Key Methods:**
- `from_dict(data, field_config)`: Create packet from dictionary data  
- `to_dict()`: Convert packet to dictionary
- `get_response_name()`: Get response status as string
- `is_error_response()`: Check if response indicates error

**Usage:**
```python
# Create data packet
data_config = create_axi_data_field_config()
r_packet = AXIDataPacket(data_config)
r_packet.id = 0x42
r_packet.data = 0xDEADBEEF
r_packet.resp = 0  # OKAY
r_packet.last = 1  # Last transfer

# Check response
resp_name = r_packet.get_response_name()  # "OKAY"
is_error = r_packet.is_error_response()   # False
```

#### `SplitInfoPacket`

Represents split information for tracking transaction splitting.

**Key Methods:**
- `from_dict(data, field_config)`: Create packet from dictionary data
- `to_dict()`: Convert packet to dictionary

**Usage:**
```python
# Create split info packet
split_config = create_split_info_field_config()
split_packet = SplitInfoPacket(split_config)
split_packet.addr = 0x1000
split_packet.id = 0x42
split_packet.cnt = 3  # Split into 3 transactions
```

### Transaction State Management

#### `SplitTransactionState`

Enumeration for tracking split transaction states:
- `PENDING`: Transaction submitted, waiting for splits
- `PARTIAL`: Some responses received
- `COMPLETE`: All responses received
- `ERROR`: Error occurred during processing

#### `SplitTransaction`

Dataclass for comprehensive split transaction tracking. Replaces custom SplitTransaction class.

**Attributes:**
- `original_ar`: Original AXI address packet
- `split_info`: Split information packet (optional)
- `split_ars`: List of split address packets
- `expected_responses`: Expected number of responses
- `received_responses`: List of received data packets
- `state`: Current transaction state
- `start_time`: Transaction start timestamp
- `completion_time`: Transaction completion timestamp (optional)
- `errors`: List of error messages

**Key Methods:**
- `add_split_ar(ar_packet)`: Add a split AR transaction
- `add_response(r_packet)`: Add a response data packet
- `add_error(error)`: Add an error message
- `is_complete()`: Check if transaction is complete
- `has_errors()`: Check if transaction has errors
- `get_duration()`: Get transaction duration

**Usage:**
```python
# Create split transaction tracker
split_txn = SplitTransaction(
    original_ar=original_ar_packet,
    split_info=None,
    split_ars=[],
    expected_responses=3,
    received_responses=[],
    state=SplitTransactionState.PENDING,
    start_time=time.time()
)

# Track split progress
split_txn.add_split_ar(split_ar_packet_1)
split_txn.add_response(response_packet_1)

# Check completion
if split_txn.is_complete():
    duration = split_txn.get_duration()
```

### Conversion Utilities

#### `convert_gaxi_packet_to_axi_address(gaxi_packet, field_config)`

Converts a GAXI packet to an AXI address packet.

**Parameters:**
- `gaxi_packet`: Source GAXI packet
- `field_config`: Target field configuration (optional)

**Returns:** AXIAddressPacket with converted data

#### `convert_gaxi_packet_to_axi_data(gaxi_packet, field_config)`

Converts a GAXI packet to an AXI data packet.

**Parameters:**
- `gaxi_packet`: Source GAXI packet  
- `field_config`: Target field configuration (optional)

**Returns:** AXIDataPacket with converted data

## Integration with Testbench Components

### With Scoreboard

```python
from .axi_read_splitter_packets import *

# In scoreboard initialization
self.addr_field_config = create_axi_address_field_config(
    id_width=8, addr_width=32, user_width=1
)
self.data_field_config = create_axi_data_field_config(
    id_width=8, data_width=64, user_width=1
)

# Convert and track packets
ar_packet = convert_gaxi_packet_to_axi_address(gaxi_packet, self.addr_field_config)
self.record_upstream_transaction(ar_packet)
```

### With Testbench

```python
from .axi_read_splitter_packets import *

# Create test transactions
addr_config = create_axi_address_field_config()
test_packet = AXIAddressPacket(addr_config)
test_packet.addr = boundary_crossing_address
test_packet.len = 15  # 16 transfers

# Check if split is expected
if test_packet.will_cross_boundary(self.BOUNDARY_SIZE):
    await self.send_transaction_expecting_split(test_packet)
```

## Benefits

**Consistency**: All components use the same packet definitions and field configurations, ensuring consistent behavior across the testbench.

**Type Safety**: Strong typing with field validation prevents common errors in packet handling.

**Flexibility**: Field configurations can be customized for different data widths and protocol variants.

**Maintainability**: Centralized packet definitions make it easy to modify or extend packet structures.

**Debugging**: Built-in methods for packet inspection and conversion simplify debugging and analysis.

This packet framework provides the foundation for robust AXI read splitter verification by ensuring consistent, type-safe transaction handling across all testbench components.