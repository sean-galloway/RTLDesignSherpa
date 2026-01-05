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

# AXISMaster

The `AXISMaster` class provides comprehensive AXI4-Stream protocol master (source) functionality. Built on the GAXI infrastructure, it offers advanced stream data generation, flow control management, and packet-based transmission with complete sideband signal support.

## Class Overview

```python
class AXISMaster(GAXIMaster):
    """
    AXIS Master component for driving AXI4-Stream protocol.

    Inherits common functionality from GAXIComponentBase:
    - Signal resolution and data driving setup
    - Unified field configuration handling
    - Memory model integration
    - Statistics and logging patterns

    AXIS-specific features:
    - Stream data transmission
    - Flow control with backpressure
    - Packet/frame boundary handling with TLAST
    - Optional ID and destination routing
    """
```

## Constructor

### `__init__(dut, title, prefix, clock, **kwargs)`

Initialize the AXIS Master component.

**Parameters:**
- **`dut`** - Device under test instance
- **`title`** (str) - Component title/name for identification and logging
- **`prefix`** (str) - Signal prefix (e.g., "m_axis_", "fub_axis_")
- **`clock`** - Clock signal reference

**Optional Parameters:**
- **`field_config`** (AXISFieldConfigs) - Field configuration (creates default if None)
- **`timeout_cycles`** (int) - Maximum cycles to wait for ready (default: 1000)
- **`mode`** (str) - Protocol mode ('skid', 'blocking', etc.)
- **`bus_name`** (str) - Bus/channel name for identification
- **`pkt_prefix`** (str) - Packet field prefix
- **`multi_sig`** (bool) - Whether using multi-signal mode
- **`randomizer`** - Optional randomizer for timing variations
- **`memory_model`** - Optional memory model integration
- **`log`** - Logger instance for debug output
- **`super_debug`** (bool) - Enable detailed debugging
- **`pipeline_debug`** (bool) - Enable pipeline debugging
- **`signal_map`** (dict) - Optional manual signal mapping

**Example:**
```python
master = AXISMaster(
    dut=dut,
    title="StreamSource",
    prefix="m_axis_",
    clock=clk,
    timeout_cycles=2000,
    super_debug=True
)
```

## Core Methods

### Stream Data Transmission

#### `send_stream_data(data_list, **kwargs)` (async)

Send multiple data values as a stream with automatic packet management.

**Parameters:**
- **`data_list`** (list) - List of data values to send
- **`id`** (int) - Stream ID for all transfers (default: 0)
- **`dest`** (int) - Destination for all transfers (default: 0)
- **`user`** (int) - User signal for all transfers (default: 0)
- **`auto_last`** (bool) - Automatically set TLAST on final transfer (default: True)
- **`strb_list`** (list) - Optional list of strobe values

**Returns:** `bool` - True if successful, False if timeout

**Example:**
```python
# Send a stream of data with automatic TLAST
data = [0x11111111, 0x22222222, 0x33333333, 0x44444444]
success = await master.send_stream_data(
    data_list=data,
    id=5,
    dest=2,
    user=0xABCD
)
```

#### `send_packet(packet)` (async)

Send a single AXIS packet with complete control over all fields.

**Parameters:**
- **`packet`** (AXISPacket) - Configured packet to send

**Returns:** `bool` - True if successful, False if timeout

**Example:**
```python
# Create and send a custom packet
packet = AXISPacket(field_config=master.field_config)
packet.data = 0x12345678
packet.last = 1
packet.id = 3
packet.dest = 1
packet.user = 0x1000

success = await master.send_packet(packet)
```

#### `send_frame(frame_data, **kwargs)` (async)

Send a complete frame (multiple transfers with TLAST on final).

**Parameters:**
- **`frame_data`** (list) - List of data values for the frame
- **`frame_id`** (int) - Frame ID (default: 0)
- **`dest`** (int) - Destination (default: 0)
- **`user`** (int) - User signal (default: 0)

**Returns:** `bool` - True if successful

**Example:**
```python
# Send a complete frame
frame = [0xDEADBEEF, 0xCAFEBABE, 0x12345678]
success = await master.send_frame(
    frame_data=frame,
    frame_id=7,
    dest=3
)
```

#### `send_single_beat(data, **kwargs)` (async)

Send a single beat/transfer with full field control.

**Parameters:**
- **`data`** - Data value to send
- **`last`** (int) - TLAST value (default: 1)
- **`id`** (int) - Stream ID (default: 0)
- **`dest`** (int) - Destination (default: 0)
- **`user`** (int) - User signal (default: 0)
- **`strb`** (int) - Strobe value (auto-generated if None)

**Returns:** `bool` - True if successful

**Example:**
```python
# Send single beat with custom fields
success = await master.send_single_beat(
    data=0xABCDEF01,
    last=0,  # Not end of packet
    id=2,
    dest=1,
    user=0x5555,
    strb=0xF  # All bytes valid
)
```

## Status and Control Methods

### `is_busy()`

Check if master is currently busy sending data.

**Returns:** `bool` - True if transactions are queued or active

### `get_queue_depth()`

Get current send queue depth.

**Returns:** `int` - Number of packets waiting to be sent

### `get_stats()`

Get comprehensive transmission statistics.

**Returns:** `dict` - Statistics dictionary containing:
- `packets_sent` - Total packets transmitted
- `frames_sent` - Total frames transmitted
- `total_data_bytes` - Total bytes transferred
- `timeouts` - Number of timeout events
- `errors` - Number of failed transactions
- `queue_depth` - Current queue depth
- `is_busy` - Current busy status

**Example:**
```python
stats = master.get_stats()
print(f"Sent {stats['packets_sent']} packets, {stats['frames_sent']} frames")
print(f"Queue depth: {stats['queue_depth']}, Busy: {stats['is_busy']}")
```

## Advanced Features

### Flow Control and Timing

The AXISMaster automatically handles:
- **TREADY Backpressure**: Waits for slave readiness before transmission
- **Timeout Protection**: Configurable timeout to prevent deadlocks
- **Pipeline Control**: Efficient pipeline management for maximum throughput
- **Timing Randomization**: Optional randomizer integration for realistic test scenarios

### Memory Model Integration

```python
# Connect memory model for automatic data generation
memory = create_memory_model(size=1024, data_width=32)
master.memory_model = memory

# Memory is automatically updated with sent data
await master.send_stream_data([0x1000, 0x2000, 0x3000])
```

### Statistics and Monitoring

The component provides comprehensive statistics:
- Packet and frame counters
- Byte transfer tracking
- Timeout and error monitoring
- Queue depth monitoring
- Performance metrics

### Debug and Logging

```python
# Enable detailed debugging
master = AXISMaster(
    dut=dut,
    title="DebugMaster",
    prefix="m_axis_",
    clock=clk,
    super_debug=True,
    pipeline_debug=True
)

# All transactions are logged with detailed information
```

## Integration Examples

### Basic Stream Generation

```python
async def test_stream_generation():
    # Create master
    master = AXISMaster(dut, "Generator", "m_axis_", clk)

    # Generate test data
    test_data = [i * 0x11111111 for i in range(1, 17)]

    # Send as stream
    success = await master.send_stream_data(
        data_list=test_data,
        id=1,
        dest=0
    )

    assert success, "Stream transmission failed"

    # Verify statistics
    stats = master.get_stats()
    assert stats['packets_sent'] == 16
    assert stats['frames_sent'] == 1
```

### Multi-Stream Scenario

```python
async def test_multi_stream():
    master = AXISMaster(dut, "MultiStream", "m_axis_", clk)

    # Send multiple concurrent streams
    for stream_id in range(4):
        stream_data = [0x1000 + stream_id + i for i in range(8)]
        await master.send_stream_data(
            data_list=stream_data,
            id=stream_id,
            dest=stream_id % 2
        )

    # Wait for completion
    while master.is_busy():
        await RisingEdge(clk)
```

### Custom Packet Construction

```python
async def test_custom_packets():
    master = AXISMaster(dut, "CustomSender", "m_axis_", clk)

    # Create packet with specific strobe pattern
    packet = AXISPacket(field_config=master.field_config)
    packet.data = 0x12345678
    packet.strb = 0xC  # Only upper 2 bytes valid
    packet.last = 1
    packet.id = 10
    packet.user = 0xABCD

    success = await master.send_packet(packet)
    assert success
```

## Error Handling

The AXISMaster provides robust error handling:
- Timeout detection and reporting
- Exception catching and logging
- Transaction failure tracking
- Automatic recovery mechanisms

**Common error scenarios:**
- TREADY timeout (slave not accepting data)
- Invalid packet configuration
- Memory model write failures
- Clock domain issues

## Performance Considerations

- **Queue Management**: Efficient deque-based packet queuing
- **Pipeline Optimization**: Minimal cycle overhead for back-to-back transfers
- **Memory Efficiency**: Optimized data structures for high-throughput scenarios
- **Statistics Overhead**: Minimal performance impact from statistics collection

The AXISMaster component provides a complete solution for AXI4-Stream data generation, combining ease of use with advanced features for comprehensive verification scenarios.