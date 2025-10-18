### Sink SRAM Control

#### Overview

The Sink SRAM Control provides sophisticated buffering and flow control for incoming data streams from the Network network. The module implements single-writer architecture with multi-channel read capabilities, comprehensive stream boundary management, and precise chunk forwarding for optimal AXI write performance.

#### Key Features

- **Single Write Interface**: Simplified architecture with Network Slave as sole writer
- **Multi-Channel Read**: Parallel read interfaces for maximum AXI engine throughput  
- **Stream Boundary Management**: Complete EOS lifecycle tracking and completion signaling
- **Chunk Forwarding**: Precise chunk enables storage and forwarding for AXI write strobes
- **SRAM Storage**: 530-bit entries with complete packet metadata
- **Buffer Flow Control**: Stream-aware backpressure and overflow prevention
- **Credit Return**: Consumption notification for proper Network flow control
- **Monitor Integration**: Rich monitor events for system visibility

#### Interface Specification

##### Configuration Parameters

| Parameter | Default Value | Description |
|-----------|---------------|-------------|
| `CHANNELS` | 32 | Number of virtual channels |
| `LINES_PER_CHANNEL` | 256 | SRAM depth per channel |
| `DATA_WIDTH` | 512 | Data width in bits |
| `PTR_BITS` | `$clog2(LINES_PER_CHANNEL) + 1` | Pointer width (+1 for wrap bit) |
| `CHAN_BITS` | `$clog2(CHANNELS)` | Channel address width |
| `COUNT_BITS` | `$clog2(LINES_PER_CHANNEL)` | Counter width |
| `NUM_CHUNKS` | 16 | Number of 32-bit chunks (512/32) |
| `OVERFLOW_MARGIN` | 8 | Safety margin for overflow prevention |
| `USED_THRESHOLD` | 4 | Minimum entries for read operation |

##### Clock and Reset Signals

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **clk** | logic | 1 | Input | Yes | System clock |
| **rst_n** | logic | 1 | Input | Yes | Active-low asynchronous reset |

##### Write Interface (From Network Slave FUB)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **wr_valid** | logic | 1 | Input | Yes | Write request valid |
| **wr_ready** | logic | 1 | Output | Yes | Write request ready |
| **wr_data** | logic | DATA_WIDTH | Input | Yes | Write data |
| **wr_channel** | logic | CHAN_BITS | Input | Yes | Target channel |
| **wr_type** | logic | 2 | Input | Yes | Packet type |
| **wr_eos** | logic | 1 | Input | Yes | End of Stream |
| **wr_chunk_en** | logic | NUM_CHUNKS | Input | Yes | Chunk enable mask |

##### Multi-Channel Read Interface (To AXI Engines)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **rd_valid** | logic | CHANNELS | Output | Yes | Read data valid per channel |
| **rd_ready** | logic | CHANNELS | Input | Yes | Read data ready per channel |
| **rd_data** | logic | DATA_WIDTH × CHANNELS | Output | Yes | Read data per channel |
| **rd_type** | logic | 2 × CHANNELS | Output | Yes | Packet type per channel |
| **rd_eos** | logic | CHANNELS | Output | Yes | End of Stream per channel |
| **rd_chunk_valid** | logic | NUM_CHUNKS × CHANNELS | Output | Yes | Chunk enables per channel |
| **rd_used_count** | logic | 8 × CHANNELS | Output | Yes | Used entries per channel |
| **rd_lines_for_transfer** | logic | 8 × CHANNELS | Output | Yes | Lines available for transfer per channel |

##### Data Consumption Notification

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **data_consumed_valid** | logic | 1 | Output | Yes | Consumption notification valid |
| **data_consumed_ready** | logic | 1 | Input | Yes | Consumption notification ready |
| **data_consumed_channel** | logic | CHAN_BITS | Output | Yes | Channel that consumed data |

##### EOS Completion Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **eos_completion_valid** | logic | 1 | Output | Yes | EOS completion notification valid |
| **eos_completion_ready** | logic | 1 | Input | Yes | EOS completion notification ready |
| **eos_completion_channel** | logic | CHAN_BITS | Output | Yes | Channel with EOS completion |

##### Control and Status

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **drain_enable** | logic | 1 | Input | Yes | Enable buffer draining mode |
| **channel_full** | logic | CHANNELS | Output | Yes | Per-channel full status |
| **channel_overflow** | logic | CHANNELS | Output | Yes | Per-channel overflow status |
| **backpressure_warning** | logic | CHANNELS | Output | Yes | Per-channel backpressure warning |
| **eos_pending** | logic | CHANNELS | Output | Yes | EOS pending per channel |

##### Monitor Bus Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **mon_valid** | logic | 1 | Output | Yes | Monitor packet valid |
| **mon_ready** | logic | 1 | Input | Yes | Monitor ready to accept packet |
| **mon_packet** | logic | 64 | Output | Yes | Monitor packet data |

#### SRAM Architecture

#### Sink SRAM Control FSM

The Sink SRAM Control operates through a sophisticated flow control and arbitration state machine that manages multi-channel buffer operations with stream-aware priority scheduling and comprehensive boundary processing. The FSM coordinates single-writer operations from the Network slave interface with multi-channel read arbitration for AXI write engines, implementing priority-based scheduling that favors channels with pending stream boundaries over threshold-based normal operations.

![Sink SRAM FSM](/mnt/data/github/tsunami/design/rapids/markdown/rapids_spec/ch02_blocks/puml/sink_sram_control_fsm.png)

**Key Operations:**
- **Write State Management**: Single-writer flow control with overflow prevention and metadata embedding for 530-bit SRAM entries
- **Read Arbitration**: Multi-level priority arbitration favoring EOS/EOL/EOD pending channels, then threshold-based scheduling, then round-robin fairness
- **Stream Boundary Processing**: Complete EOS lifecycle tracking with dedicated completion signaling and consumption notification coordination
- **Buffer Management**: Per-channel pointer management with wrap detection, used count tracking, and configurable threshold monitoring
- **Flow Control Coordination**: Backpressure generation, overflow warning, and credit return triggering for proper Network flow control

The FSM implements stream-aware buffer management where EOS boundaries receive highest priority processing to ensure timely descriptor completion signaling, while sophisticated pointer arithmetic and buffer status tracking prevent overflow conditions and coordinate with upstream Network credit management. The architecture eliminates traditional multi-writer arbitration complexity through the single-writer design while maintaining optimal multi-channel read performance through priority-based scheduling algorithms.

##### Storage Format (530 bits total)

The SRAM stores complete packet metadata alongside data for precise forwarding:

```systemverilog
// SRAM entry format:
// {TYPE[1:0], CHUNK_VALID[15:0], DATA[511:0]} = 530 bits total
localparam int EXTENDED_SRAM_WIDTH = 2 + NUM_CHUNKS + DATA_WIDTH;

// Write data composition
assign w_sram_wr_data = {
    wr_type,                         // Bits 529:528: Packet type
    wr_chunk_en,                     // Bits 527:512: Chunk enables
    wr_data                          // Bits 511:0: Data payload
};
```

##### EOS Flow Management

**Critical Design Decision**: EOS is NOT stored in SRAM but used for completion signaling:

1. **EOS Detection**: Network packets arrive with EOS bit in packet structure
2. **EOS Processing**: EOS triggers descriptor completion logic (control only)
3. **EOS Storage**: EOS is NOT stored in SRAM - only payload data is stored
4. **EOS Control**: EOS used for completion signaling to scheduler
5. **EOS Completion**: Dedicated FIFO interface for EOS completion notifications

##### Multi-Channel Buffer Management

Each channel maintains independent:
- **Write Pointer**: Binary pointer with wrap detection
- **Read Pointer**: Binary pointer with wrap detection  
- **Used Count**: Number of valid entries available for reading
- **Open Count**: Number of available entries for writing
- **EOS Pending**: Flag indicating EOS completion pending

#### Buffer Flow Control

##### Write Acceptance Logic

```systemverilog
// Write acceptance based on buffer availability and barriers
assign wr_ready = !w_channel_full[wr_channel] && 
                  (r_used_count[wr_channel] < (LINES_PER_CHANNEL - OVERFLOW_MARGIN));
```

##### Read Arbitration

The module implements sophisticated read arbitration:

```systemverilog
// Priority levels for read arbitration
// 1. Channels with EOS pending (highest priority)
// 2. Channels meeting used threshold
// 3. Round-robin fairness among eligible channels
// 4. Drain mode considerations

assign w_eos_priority = r_eos_pending;
assign w_threshold_priority = (r_used_count[i] >= USED_THRESHOLD);
assign w_drain_priority = drain_enable && (r_used_count[i] > 0);
```

##### Stream Boundary Processing

EOS boundaries trigger special processing:

```systemverilog
// EOS completion signaling
always_ff @(posedge clk) begin
    if (!rst_n) begin
        r_eos_pending <= '0;
    end else begin
        // Set EOS pending when EOS packet written
        if (wr_valid && wr_ready && wr_eos) begin
            r_eos_pending[wr_channel] <= 1'b1;
        end
        // Clear EOS pending when completion signaled
        if (eos_completion_valid && eos_completion_ready) begin
            r_eos_pending[eos_completion_channel] <= 1'b0;
        end
    end
end
```

#### Data Flow Architecture

```
FC/TS Packets: Network Slave FUB → Sink SRAM Control → AXI Write Engine
                    ↓              ↓                    ↓
               Single Write    530-bit Storage    Multi-Channel Read
               Interface       + Packet Metadata  + Chunk Forwarding

EOS Flow:      EOS Detection → Completion Signaling → Scheduler Notification
                    ↓              ↓                    ↓
               Packet-Level    Control-Only         Descriptor-Level
               EOS in Network     Processing           Completion
```

#### Network 2.0 Support

The sink SRAM control fully supports the Network 2.0 protocol specification, using chunk enables instead of the older start/len approach for indicating valid data chunks within each 512-bit packet. This provides more flexible and precise control over partial data transfers.

#### Monitor Bus Events

The module generates comprehensive monitor events:

##### Error Events
- **Buffer Overflow**: When channel buffer exceeds capacity
- **Invalid Channel**: When write targets invalid channel
- **Pointer Corruption**: When pointer consistency checks fail

##### Completion Events  
- **Write Completion**: Successful data write to buffer
- **Read Completion**: Successful data read from buffer
- **EOS Completion**: End of stream processing complete

##### Threshold Events
- **Backpressure Warning**: When buffer usage exceeds warning threshold
- **Buffer Full**: When channel buffer reaches capacity
- **Credit Exhausted**: When no buffer space available

#### Performance Characteristics

##### Throughput Metrics
- **Write Throughput**: 1 write per cycle when space available
- **Read Throughput**: 1 read per cycle per channel with proper SRAM implementation
- **Metadata Overhead**: 3.5% (18 metadata bits / 530 total bits)
- **Buffer Efficiency**: 95%+ utilization with stream-aware flow control

##### Latency Characteristics
- **Write Latency**: 1 cycle for data acceptance
- **Read Arbitration**: 1-3 cycles depending on priority and contention
- **EOS Processing**: 1 cycle for EOS completion signaling
- **Credit Return**: 2-4 cycles from consumption to credit notification

#### Implementation Notes

##### Multi-Channel Read Support

The current implementation provides a foundation for multi-channel reads but requires additional infrastructure for optimal concurrent operation:

1. **Multiple SRAM instances** (one per channel) - Highest performance
2. **Multi-port SRAM** with read arbitration - Good performance  
3. **Time-multiplexed single-port** with scheduling - Acceptable performance

##### Buffer Management

Each channel operates independently with:
- **Independent Pointer Management**: Separate read/write pointers per channel
- **Per-Channel Flow Control**: Individual full/empty status tracking
- **EOS State Management**: Per-channel EOS pending tracking
- **Credit Return Coordination**: Channel-specific consumption notifications

#### Usage Guidelines

##### Performance Optimization

- Configure `USED_THRESHOLD` based on AXI engine requirements
- Set `OVERFLOW_MARGIN` to prevent buffer overflow under burst conditions
- Use EOS completion interface for proper stream boundary coordination
- Monitor backpressure warnings to optimize buffer utilization

##### Error Handling

The module provides comprehensive error detection:
- Monitor channel overflow conditions
- Check buffer pointer consistency
- Verify EOS completion flow
- Track per-channel error statistics through monitor events
