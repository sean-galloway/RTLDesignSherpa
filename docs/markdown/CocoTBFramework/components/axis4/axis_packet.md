# AXISPacket

The `AXISPacket` class provides comprehensive data structure management for AXI4-Stream protocol transactions. Built on the GAXI packet infrastructure, it offers convenient field access, byte-level manipulation, and automatic data validation for stream protocol verification.

## Class Overview

```python
class AXISPacket(GAXIPacket):
    """
    AXIS Packet class for AXI4-Stream protocol.

    Inherits all functionality from GAXIPacket while providing
    AXIS-specific convenience methods and field access.

    AXIS protocol uses a single T channel with:
    - data: Stream data payload
    - strb: Byte enables
    - last: End of packet/frame indicator
    - id: Stream identifier (optional)
    - dest: Destination routing (optional)
    - user: User-defined sideband data (optional)
    """
```

## Constructor

### `__init__(*args, **kwargs)`

Initialize an AXIS packet with optional field configuration.

**Parameters:**
- **`field_config`** (AXISFieldConfigs) - Field configuration defining signal widths
- **`timestamp`** - Optional timestamp for packet creation
- Additional parameters inherited from GAXIPacket

**Example:**
```python
# Create packet with field configuration
config = AXISFieldConfigs.create_default_axis_config()
packet = AXISPacket(field_config=config)

# Create packet with timestamp
packet = AXISPacket(field_config=config, timestamp=get_sim_time())
```

## Field Properties

All AXIS packet fields are accessible through convenient properties with automatic type handling.

### Core Data Fields

#### `data` (property)

Stream data payload - the primary data being transmitted.

```python
# Get data value
data_value = packet.data

# Set data value
packet.data = 0x12345678
packet.data = 0xDEADBEEF
```

#### `strb` (property)

Byte strobe/enable signals indicating which data bytes are valid.

```python
# Get strobe value
strb_value = packet.strb

# Set strobe - bit 0 = byte 0 valid, bit 1 = byte 1 valid, etc.
packet.strb = 0xF    # All 4 bytes valid
packet.strb = 0x3    # Only lower 2 bytes valid
packet.strb = 0xC    # Only upper 2 bytes valid
```

#### `last` (property)

End of packet/frame indicator (TLAST signal).

```python
# Get last indicator
is_last = packet.last

# Set last indicator
packet.last = 1      # End of packet/frame
packet.last = 0      # More data follows
```

### Optional Sideband Fields

#### `id` (property)

Stream identifier for routing and stream demultiplexing.

```python
# Get stream ID
stream_id = packet.id

# Set stream ID
packet.id = 5        # Stream 5
packet.id = 0xAB     # Stream 0xAB
```

#### `dest` (property)

Destination identifier for packet routing.

```python
# Get destination
destination = packet.dest

# Set destination
packet.dest = 2      # Route to destination 2
packet.dest = 0x1F   # Route to destination 0x1F
```

#### `user` (property)

User-defined sideband data for custom protocol extensions.

```python
# Get user data
user_data = packet.user

# Set user data
packet.user = 0x1234     # Custom user data
packet.user = 0xABCDEF   # Extended user data
```

## Utility Methods

### Packet State Queries

#### `is_last()`

Check if this is the last transfer in a packet/frame.

**Returns:** `bool` - True if TLAST is asserted

```python
if packet.is_last():
    print("End of packet reached")
    process_complete_packet()
```

#### `is_first()`

Check if this is the first transfer in a packet/frame.

**Returns:** `bool` - True if this is a first transfer (always True for single-beat packets)

```python
if packet.is_first():
    print("Start of new packet")
    initialize_packet_processing()
```

### Byte-Level Operations

#### `get_byte_count()`

Get number of valid bytes based on strobe signal.

**Returns:** `int` - Count of asserted bits in strobe

```python
# Example with different strobe patterns
packet.strb = 0xF      # 4 bytes valid
print(packet.get_byte_count())  # Outputs: 4

packet.strb = 0x3      # 2 bytes valid
print(packet.get_byte_count())  # Outputs: 2

packet.strb = 0x5      # 2 bytes valid (bits 0 and 2)
print(packet.get_byte_count())  # Outputs: 2
```

#### `get_data_bytes()`

Extract data as list of valid bytes based on strobe pattern.

**Returns:** `list` - List of valid byte values

```python
# Extract bytes from data word
packet.data = 0x12345678
packet.strb = 0xF           # All bytes valid

bytes_list = packet.get_data_bytes()
# Returns: [0x78, 0x56, 0x34, 0x12]  (little-endian order)

# Partial byte extraction
packet.strb = 0x3           # Only lower 2 bytes valid
bytes_list = packet.get_data_bytes()
# Returns: [0x78, 0x56]
```

#### `set_data_bytes(byte_list)`

Set data and strobe from list of bytes.

**Parameters:**
- **`byte_list`** (list) - List of byte values to pack

```python
# Pack bytes into data word
bytes_to_pack = [0xAB, 0xCD, 0xEF, 0x12]
packet.set_data_bytes(bytes_to_pack)

# Results in:
# packet.data = 0x12EFCDAB
# packet.strb = 0xF
```

## String Representation

### `__str__()`

Concise string representation showing key fields.

```python
packet.data = 0x12345678
packet.strb = 0xF
packet.last = 1
packet.id = 5

print(str(packet))
# Output: AXISPacket(data=0x12345678, strb=0b1111, last=1, id=0x5)
```

### `__repr__()`

Detailed representation including timestamp and computed values.

```python
print(repr(packet))
# Output: AXISPacket(time=1250000, data=0x12345678, strb=0b1111, last=1, bytes=4)
```

## Factory Function

### `create_axis_packet(**kwargs)`

Factory function for convenient packet creation with field initialization.

**Parameters:**
- **`data`** (int) - Stream data value (default: 0)
- **`strb`** (int) - Strobe value (auto-generated if None)
- **`last`** (int) - Last indicator (default: 0)
- **`id`** (int) - Stream ID (default: 0)
- **`dest`** (int) - Destination (default: 0)
- **`user`** (int) - User signal (default: 0)
- **`field_config`** - Field configuration
- **`**kwargs`** - Additional packet parameters

**Returns:** `AXISPacket` - Configured packet instance

**Example:**
```python
# Create packet with all fields
packet = create_axis_packet(
    data=0xDEADBEEF,
    strb=0xF,
    last=1,
    id=3,
    dest=2,
    user=0x1234,
    field_config=config
)

# Create packet with auto-generated strobe
packet = create_axis_packet(
    data=0x12345678,
    last=1,
    field_config=config  # strobe auto-generated from config
)
```

## Usage Examples

### Basic Packet Creation and Manipulation

```python
# Create packet
packet = AXISPacket(field_config=axis_config)

# Set basic fields
packet.data = 0xCAFEBABE
packet.last = 1
packet.id = 7

# Auto-generate full strobe
if 'strb' in axis_config:
    strb_bits = axis_config['strb'].bits
    packet.strb = (1 << strb_bits) - 1

print(f"Created packet: {packet}")
print(f"Byte count: {packet.get_byte_count()}")
```

### Byte-Level Data Handling

```python
# Create packet from byte array
data_bytes = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
packet = AXISPacket(field_config=config)

# Pack first 4 bytes
packet.set_data_bytes(data_bytes[:4])
packet.last = 0  # More data follows

print(f"First packet: {packet}")
print(f"Data bytes: {packet.get_data_bytes()}")

# Pack remaining bytes
packet2 = AXISPacket(field_config=config)
packet2.set_data_bytes(data_bytes[4:])
packet2.last = 1  # End of data

print(f"Second packet: {packet2}")
```

### Multi-Stream Packet Creation

```python
# Create packets for different streams
packets = []

for stream_id in range(4):
    for seq_num in range(8):
        packet = create_axis_packet(
            data=0x1000 + (stream_id << 8) + seq_num,
            strb=0xF,
            last=1 if seq_num == 7 else 0,  # Last packet in sequence
            id=stream_id,
            dest=stream_id % 2,
            user=0x5000 + seq_num,
            field_config=config
        )
        packets.append(packet)

print(f"Created {len(packets)} packets for {4} streams")
```

### Packet Analysis and Validation

```python
def analyze_packet(packet):
    """Analyze packet contents and validity."""
    analysis = {
        'data_value': f"0x{packet.data:08x}",
        'valid_bytes': packet.get_byte_count(),
        'is_end_of_frame': packet.is_last(),
        'stream_id': packet.id,
        'destination': packet.dest,
        'user_data': f"0x{packet.user:x}" if packet.user else "None"
    }

    # Validate strobe pattern
    byte_count = packet.get_byte_count()
    if byte_count == 0:
        analysis['warning'] = "No valid bytes (strobe = 0)"
    elif packet.strb != ((1 << byte_count) - 1):
        analysis['warning'] = "Non-contiguous strobe pattern"

    return analysis

# Analyze received packet
packet = create_axis_packet(data=0x12345678, strb=0xF, last=1, id=5)
analysis = analyze_packet(packet)

for key, value in analysis.items():
    print(f"{key}: {value}")
```

### Frame Assembly from Packets

```python
def assemble_frame(packets):
    """Assemble frame data from packet sequence."""
    if not packets:
        return []

    frame_data = []
    frame_id = packets[0].id

    for i, packet in enumerate(packets):
        # Verify stream consistency
        assert packet.id == frame_id, f"Stream ID mismatch at packet {i}"

        # Extract valid bytes
        valid_bytes = packet.get_data_bytes()
        frame_data.extend(valid_bytes)

        # Check frame completion
        if packet.is_last():
            break

    return frame_data

# Example frame assembly
frame_packets = [
    create_axis_packet(data=0x03020100, strb=0xF, last=0, id=1),
    create_axis_packet(data=0x07060504, strb=0xF, last=0, id=1),
    create_axis_packet(data=0x0B0A0908, strb=0xF, last=1, id=1),
]

frame_data = assemble_frame(frame_packets)
print(f"Frame data: {[hex(b) for b in frame_data]}")
```

## Integration with Components

### Master Component Usage

```python
# Create packet for transmission
packet = create_axis_packet(
    data=0xDEADBEEF,
    strb=0xF,
    last=1,
    id=stream_id,
    dest=destination,
    field_config=master.field_config
)

# Send via master
success = await master.send_packet(packet)
```

### Slave Component Usage

```python
# Packets are automatically created by slave during reception
# Access through slave's internal mechanisms or callbacks

def packet_received_callback(packet):
    print(f"Received: {packet}")

    if packet.is_last():
        print("Frame complete")
        process_frame_data(packet.get_data_bytes())
```

The AXISPacket class provides a complete data structure solution for AXI4-Stream verification, offering both low-level field access and high-level convenience methods for efficient packet manipulation and analysis.