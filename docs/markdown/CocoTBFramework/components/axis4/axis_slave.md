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

# AXISSlave

The `AXISSlave` class provides comprehensive AXI4-Stream protocol slave (sink) functionality. Built on the GAXI infrastructure, it offers advanced stream data reception, backpressure control, and automatic frame assembly with complete protocol monitoring capabilities.

## Class Overview

```python
class AXISSlave(GAXIMonitorBase):
    """
    AXIS Slave component for receiving AXI4-Stream protocol.

    Inherits common functionality from GAXIMonitorBase:
    - Signal resolution and data collection setup
    - Clean _get_data_dict() with automatic field unpacking
    - Unified _finish_packet() without conditional mess
    - Packet creation and statistics
    - Memory model integration

    AXIS-specific features:
    - Stream data reception with backpressure control
    - Frame boundary detection with TLAST
    - Ready signal timing control
    - Packet and frame statistics
    """
```

## Constructor

### `__init__(dut, title, prefix, clock, **kwargs)`

Initialize the AXIS Slave component.

**Parameters:**
- **`dut`** - Device under test instance
- **`title`** (str) - Component title/name for identification and logging
- **`prefix`** (str) - Signal prefix (e.g., "s_axis_", "axis_")
- **`clock`** - Clock signal reference

**Optional Parameters:**
- **`field_config`** (AXISFieldConfigs) - Field configuration (creates default if None)
- **`timeout_cycles`** (int) - Maximum cycles for operations (default: 1000)
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
slave = AXISSlave(
    dut=dut,
    title="StreamSink",
    prefix="s_axis_",
    clock=clk,
    timeout_cycles=2000,
    super_debug=True
)
```

## Core Methods

### Flow Control and Ready Management

#### `set_ready_always(ready=True)`

Set ready signal to always be ready or never ready.

**Parameters:**
- **`ready`** (bool) - True for always ready, False for never ready

**Example:**
```python
# Always accept data
slave.set_ready_always(True)

# Never accept data (create backpressure)
slave.set_ready_always(False)
```

#### `apply_backpressure(probability=0.2, min_cycles=1, max_cycles=5)`

Apply random backpressure by controlling ready signal timing.

**Parameters:**
- **`probability`** (float) - Probability of applying backpressure (0.0 to 1.0)
- **`min_cycles`** (int) - Minimum cycles to hold ready low
- **`max_cycles`** (int) - Maximum cycles to hold ready low

**Example:**
```python
# Apply 30% chance of 1-3 cycle backpressure
slave.apply_backpressure(
    probability=0.3,
    min_cycles=1,
    max_cycles=3
)
```

### Frame Monitoring and Reception

#### `wait_for_frame(timeout_cycles=None)` (async)

Wait for a complete frame to be received (packet sequence ending with TLAST).

**Parameters:**
- **`timeout_cycles`** (int) - Maximum cycles to wait (uses instance default if None)

**Returns:** `bool` - True if frame completed, False if timeout

**Example:**
```python
# Wait for next frame with default timeout
frame_received = await slave.wait_for_frame()

# Wait with custom timeout
frame_received = await slave.wait_for_frame(timeout_cycles=5000)

if frame_received:
    stats = slave.get_stats()
    print(f"Frame received! Total frames: {stats['frames_received']}")
```

#### `get_current_frame_info()`

Get information about the currently receiving frame.

**Returns:** `dict` - Frame information containing:
- `packets_in_frame` - Number of packets received in current frame
- `frame_id` - ID of the current frame (from first packet)
- `total_bytes` - Total bytes received in current frame
- `is_receiving` - Whether currently receiving a frame

**Example:**
```python
frame_info = slave.get_current_frame_info()
print(f"Current frame: {frame_info['packets_in_frame']} packets, "
      f"{frame_info['total_bytes']} bytes, ID={frame_info['frame_id']}")
```

## Status and Statistics Methods

### `get_stats()`

Get comprehensive reception statistics.

**Returns:** `dict` - Statistics dictionary containing:
- `packets_received` - Total packets received
- `frames_received` - Total frames received (sequences ending with TLAST)
- `total_data_bytes` - Total bytes received
- `errors` - Number of error events
- `current_frame_info` - Information about current frame being received

**Example:**
```python
stats = slave.get_stats()
print(f"Received {stats['packets_received']} packets in {stats['frames_received']} frames")
print(f"Total data: {stats['total_data_bytes']} bytes")
print(f"Current frame: {stats['current_frame_info']['packets_in_frame']} packets")
```

## Automatic Monitoring Features

### Stream Reception Monitoring

The AXISSlave automatically monitors the bus and:
- **Handshake Detection**: Monitors TVALID/TREADY handshakes
- **Packet Capture**: Automatically captures valid transfers
- **Frame Assembly**: Groups packets by TLAST boundaries
- **Statistics Tracking**: Updates counters and performance metrics

### Frame Boundary Processing

- **Automatic TLAST Detection**: Identifies frame boundaries
- **Frame Statistics**: Tracks complete frame reception
- **Multi-Frame Support**: Handles concurrent or sequential frames
- **Frame ID Tracking**: Associates packets with frame IDs

### Memory Model Integration

```python
# Connect memory model for automatic data storage
memory = create_memory_model(size=1024, data_width=32)
slave.memory_model = memory

# All received data is automatically written to memory
# Memory addresses are calculated based on packet fields
```

## Advanced Features

### Protocol Compliance Monitoring

The component automatically:
- Validates TVALID/TREADY handshake timing
- Checks protocol specification compliance
- Detects and reports protocol violations
- Monitors sideband signal consistency

### Timing Randomization

```python
# Create randomizer for realistic timing
from cocotb_framework.randomizers import StreamRandomizer

randomizer = StreamRandomizer()
slave = AXISSlave(
    dut=dut,
    title="RealisticSink",
    prefix="s_axis_",
    clock=clk,
    randomizer=randomizer
)

# Randomizer automatically applies ready timing variations
```

### Debug and Analysis

```python
# Enable comprehensive debugging
slave = AXISSlave(
    dut=dut,
    title="DebugSlave",
    prefix="s_axis_",
    clock=clk,
    super_debug=True,
    pipeline_debug=True
)

# All received packets are logged with detailed information
```

## Integration Examples

### Basic Stream Reception

```python
async def test_stream_reception():
    # Create slave
    slave = AXISSlave(dut, "Receiver", "s_axis_", clk)

    # Set to always ready
    slave.set_ready_always(True)

    # Wait for data
    await slave.wait_for_frame(timeout_cycles=1000)

    # Check results
    stats = slave.get_stats()
    assert stats['frames_received'] > 0, "No frames received"
    print(f"Successfully received {stats['packets_received']} packets")
```

### Backpressure Testing

```python
async def test_backpressure():
    slave = AXISSlave(dut, "BackpressureSink", "s_axis_", clk)

    # Apply moderate backpressure
    slave.apply_backpressure(
        probability=0.4,  # 40% chance
        min_cycles=1,
        max_cycles=4
    )

    # Monitor reception with backpressure
    initial_time = get_sim_time()
    await slave.wait_for_frame(timeout_cycles=5000)
    reception_time = get_sim_time() - initial_time

    print(f"Reception time with backpressure: {reception_time}")
```

### Multi-Stream Monitoring

```python
async def test_multi_stream():
    slave = AXISSlave(dut, "MultiStreamSink", "s_axis_", clk)
    slave.set_ready_always(True)

    # Monitor multiple frames
    frame_count = 0
    target_frames = 4

    while frame_count < target_frames:
        if await slave.wait_for_frame(timeout_cycles=2000):
            frame_count += 1
            frame_info = slave.get_current_frame_info()
            print(f"Frame {frame_count}: ID={frame_info['frame_id']}")
        else:
            break

    stats = slave.get_stats()
    assert stats['frames_received'] == target_frames
```

### Memory Verification

```python
async def test_memory_verification():
    # Create memory model
    memory = create_memory_model(size=2048, data_width=32)

    # Create slave with memory integration
    slave = AXISSlave(
        dut, "MemorySink", "s_axis_", clk,
        memory_model=memory
    )

    # Receive data (automatically written to memory)
    await slave.wait_for_frame()

    # Verify memory contents
    received_data = memory.read_range(0x0, 64)  # Read first 64 bytes
    expected_data = generate_expected_pattern()

    assert received_data == expected_data, "Memory verification failed"
```

## Error Handling and Recovery

The AXISSlave provides robust error handling:
- **Timeout Detection**: Configurable timeout for operations
- **Exception Recovery**: Graceful handling of simulation exceptions
- **Protocol Error Detection**: Identification of protocol violations
- **Logging Integration**: Comprehensive error reporting

**Common error scenarios:**
- TVALID timeout (no data received)
- Protocol violations (invalid handshake)
- Memory model write failures
- Clock domain issues

## Performance Monitoring

### Reception Statistics

The component tracks:
- **Throughput**: Packets and bytes per time unit
- **Frame Statistics**: Frame completion rates and sizes
- **Backpressure Impact**: Ready signal timing analysis
- **Protocol Efficiency**: Handshake success rates

### Real-time Analysis

```python
# Monitor real-time performance
stats = slave.get_stats()
frame_info = slave.get_current_frame_info()

print(f"Throughput: {stats['total_data_bytes'] / simulation_time} MB/s")
print(f"Frame completion rate: {stats['frames_received'] / elapsed_frames}")
print(f"Current frame progress: {frame_info['packets_in_frame']} packets")
```

## Integration with Other Components

### Master-Slave Pairs

```python
# Create matched master-slave pair
master = AXISMaster(dut, "Source", "m_axis_", clk)
slave = AXISSlave(dut, "Sink", "s_axis_", clk)

# Configure matching parameters
config = AXISFieldConfigs.create_default_axis_config()
master.field_config = config
slave.field_config = config
```

### Monitor Integration

```python
# Add monitor for comprehensive analysis
monitor = AXISMonitor(dut, "StreamMonitor", "s_axis_", clk)
slave = AXISSlave(dut, "StreamSink", "s_axis_", clk)

# Both components monitor the same signals
# Monitor provides protocol analysis
# Slave provides reception functionality
```

The AXISSlave component provides a complete solution for AXI4-Stream data reception, combining automatic monitoring with flexible flow control and comprehensive statistics for verification scenarios.