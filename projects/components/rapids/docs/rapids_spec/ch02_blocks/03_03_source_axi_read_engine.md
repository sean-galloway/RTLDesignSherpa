### Source AXI Read Engine

#### Overview

The Source AXI Read Engine orchestrates read transactions from external memory with sophisticated chunk enable generation for precise validity control and comprehensive stream boundary support. The module implements dynamic chunk enable calculation based on alignment transfers, preallocation-based deadlock prevention, and chunk-aware burst optimization for optimal memory utilization.

#### Key Features

- **Dynamic Chunk Enable Generation**: Precise chunk_enables[15:0] for memory efficiency
- **Address Alignment Intelligence**: Uses pre-calculated alignment information from scheduler
- **Stream Boundary Support**: Complete EOS processing with sequence completion tracking
- **Preallocation Coordination**: Deadlock prevention with chunk density analysis
- **Burst Optimization**: Chunk-aware burst patterns for optimal AXI performance
- **Multi-Channel Operation**: Independent processing across up to 32 channels
- **Error Recovery**: Comprehensive error detection with stream boundary validation
- **Monitor Integration**: Rich monitor events for system visibility

#### Interface Specification

##### Configuration Parameters

| Parameter | Default Value | Description |
|-----------|---------------|-------------|
| `NUM_CHANNELS` | 32 | Total number of channels in system |
| `CHAN_WIDTH` | `$clog2(NUM_CHANNELS)` | Width of channel address fields |
| `ADDR_WIDTH` | 64 | Address width for AXI transactions |
| `DATA_WIDTH` | 512 | Data width for AXI and internal interfaces |
| `NUM_CHUNKS` | 16 | Number of 32-bit chunks (512/32) |
| `AXI_ID_WIDTH` | 8 | AXI transaction ID width |
| `MAX_BURST_LEN` | 64 | Maximum AXI burst length (4KB) |
| `TIMEOUT_CYCLES` | 1000 | Timeout threshold for stuck transfers |
| `TRACKING_FIFO_DEPTH` | 32 | Transaction tracking FIFO depth |
| `COUNT_BITS` | 8 | Counter width for buffer management |

##### Clock and Reset Signals

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **clk** | logic | 1 | Input | Yes | System clock |
| **rst_n** | logic | 1 | Input | Yes | Active-low asynchronous reset |

##### Configuration Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **cfg_transfer_size** | logic | 2 | Input | Yes | Transfer size configuration |
| **cfg_streaming_enable** | logic | 1 | Input | Yes | Streaming mode enable |

##### Multi-Channel Scheduler Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **data_valid** | logic | NUM_CHANNELS | Input | Yes | Data transfer request per channel |
| **data_ready** | logic | NUM_CHANNELS | Output | Yes | Data engine ready per channel |
| **data_address** | logic | ADDR_WIDTH x NUM_CHANNELS | Input | Yes | Transfer address per channel |
| **data_length** | logic | 32 x NUM_CHANNELS | Input | Yes | Transfer length per channel (4-byte chunks) |
| **data_type** | logic | 2 x NUM_CHANNELS | Input | Yes | Packet type per channel |
| **data_eos** | logic | NUM_CHANNELS | Input | Yes | End of Stream per channel |
| **data_transfer_length** | logic | 32 x NUM_CHANNELS | Output | Yes | Actual transfer length per channel |
| **data_error** | logic | NUM_CHANNELS | Output | Yes | Data transfer error per channel |
| **data_done_strobe** | logic | NUM_CHANNELS | Output | Yes | Transfer completed pulse per channel |

##### Address Alignment Bus Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **data_alignment_info** | alignment_info_t | NUM_CHANNELS | Input | Yes | Pre-calculated alignment information per channel |
| **data_alignment_valid** | logic | NUM_CHANNELS | Input | Yes | Alignment information valid per channel |
| **data_alignment_ready** | logic | NUM_CHANNELS | Output | Yes | Alignment information ready per channel |
| **data_alignment_next** | logic | NUM_CHANNELS | Output | Yes | Request next alignment per channel |
| **data_transfer_phase** | transfer_phase_t | NUM_CHANNELS | Input | Yes | Transfer phase per channel |
| **data_sequence_complete** | logic | NUM_CHANNELS | Input | Yes | Transfer sequence complete per channel |

##### Channel Availability Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **available_lines** | logic | COUNT_BITS x NUM_CHANNELS | Input | Yes | Available SRAM lines per channel |
| **channel_ready_for_prealloc** | logic | NUM_CHANNELS | Input | Yes | Channel ready for preallocation |

##### SRAM Preallocation Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **prealloc_valid** | logic | 1 | Output | Yes | Preallocation request valid |
| **prealloc_ready** | logic | 1 | Input | Yes | Preallocation request ready |
| **prealloc_beats** | logic | 8 | Output | Yes | Requested preallocation beats |
| **prealloc_type** | logic | 2 | Output | Yes | Packet type for preallocation |
| **prealloc_channel** | logic | CHAN_WIDTH | Output | Yes | Channel for preallocation |

##### SRAM Write Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **wr_valid** | logic | 1 | Output | Yes | Write request valid |
| **wr_ready** | logic | 1 | Input | Yes | Write request ready |
| **wr_data** | logic | DATA_WIDTH | Output | Yes | Write data |
| **wr_type** | logic | 2 | Output | Yes | Packet type |
| **wr_eos** | logic | 1 | Output | Yes | End of Stream |
| **wr_chunk_valid** | logic | NUM_CHUNKS | Output | Yes | Chunk enables |
| **wr_channel** | logic | CHAN_WIDTH | Output | Yes | Target channel |

##### AXI4 Master Read Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **ar_valid** | logic | 1 | Output | Yes | Read address valid |
| **ar_ready** | logic | 1 | Input | Yes | Read address ready |
| **ar_addr** | logic | ADDR_WIDTH | Output | Yes | Read address |
| **ar_len** | logic | 8 | Output | Yes | Burst length |
| **ar_size** | logic | 3 | Output | Yes | Burst size |
| **ar_burst** | logic | 2 | Output | Yes | Burst type |
| **ar_id** | logic | AXI_ID_WIDTH | Output | Yes | Read ID |
| **ar_lock** | logic | 1 | Output | Yes | Lock type |
| **ar_cache** | logic | 4 | Output | Yes | Cache attributes |
| **ar_prot** | logic | 3 | Output | Yes | Protection attributes |
| **ar_qos** | logic | 4 | Output | Yes | QoS identifier |
| **ar_region** | logic | 4 | Output | Yes | Region identifier |
| **r_valid** | logic | 1 | Input | Yes | Read data valid |
| **r_ready** | logic | 1 | Output | Yes | Read data ready |
| **r_data** | logic | DATA_WIDTH | Input | Yes | Read data |
| **r_resp** | logic | 2 | Input | Yes | Read response |
| **r_last** | logic | 1 | Input | Yes | Read last |
| **r_id** | logic | AXI_ID_WIDTH | Input | Yes | Read ID |

##### Status Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **engine_idle** | logic | 1 | Output | Yes | Engine idle status |
| **engine_busy** | logic | 1 | Output | Yes | Engine busy status |

##### Monitor Bus Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **mon_valid** | logic | 1 | Output | Yes | Monitor packet valid |
| **mon_ready** | logic | 1 | Input | Yes | Monitor ready to accept packet |
| **mon_packet** | logic | 64 | Output | Yes | Monitor packet data |

#### Pure Pipeline Architecture

##### Zero-FSM Design

The source AXI read engine implements a revolutionary pure pipeline architecture without traditional FSM overhead:

```
Channel Selection -> Preallocation -> AXI Address -> Data Reception -> SRAM Write
        ↓               ↓              ↓              ↓               ↓
   Multi-Channel    Deadlock        Alignment      Chunk Enable    Stream 
   Arbitration      Prevention      Optimized      Generation      Boundary
```

##### Pipeline Benefits

1. **No FSM Overhead**: Eliminates state machine latency in critical path
2. **Continuous Operation**: Overlapped operations across pipeline stages
3. **Optimal Throughput**: Maximum bandwidth utilization with minimal latency
4. **Natural Backpressure**: Clean flow control through ready/valid handshakes

#### Address Alignment Integration

##### Pre-Calculated Optimization

The engine leverages the scheduler's address alignment FSM for optimal AXI performance:

```systemverilog
// Use pre-calculated alignment information
if (data_alignment_valid[channel]) begin
    case (data_transfer_phase[channel])
        PHASE_ALIGNMENT: begin
            ar_addr <= data_alignment_info[channel].aligned_addr;
            ar_len <= data_alignment_info[channel].first_burst_len;
            expected_chunks <= data_alignment_info[channel].first_chunk_enables;
        end
        PHASE_STREAMING: begin
            ar_addr <= streaming_base_addr + stream_offset;
            ar_len <= data_alignment_info[channel].optimal_burst_len;
            expected_chunks <= 16'hFFFF;  // All chunks valid
        end
        PHASE_FINAL: begin
            ar_addr <= final_transfer_addr;
            ar_len <= data_alignment_info[channel].final_burst_len;
            expected_chunks <= data_alignment_info[channel].final_chunk_enables;
        end
    endcase
end
```

##### Performance Benefits

1. **Hidden Alignment Latency**: No alignment calculation in critical AXI path
2. **Optimal Burst Planning**: Pre-calculated burst lengths and patterns
3. **Precise Chunk Generation**: Pre-calculated chunk enable patterns
4. **Transfer Sequence Coordination**: Complete sequence planned in advance

#### Dynamic Chunk Enable Generation

##### Network 2.0 Chunk Processing

```systemverilog
// Generate chunk enables based on transfer parameters
function logic [NUM_CHUNKS-1:0] generate_chunk_enables(
    input logic [ADDR_WIDTH-1:0] addr,
    input logic [31:0] length_chunks,
    input logic [7:0] burst_len
);
    logic [5:0] addr_offset = addr[5:0];  // Offset within 64-byte boundary
    logic [3:0] start_chunk = addr_offset[5:2];  // Starting chunk index
    logic [3:0] num_chunks = (length_chunks > 16) ? 4'd16 : length_chunks[3:0];
    logic [15:0] chunk_mask = (16'h1 << num_chunks) - 1;  // Create mask
    
    return chunk_mask << start_chunk;  // Shift to correct position
endfunction
```

##### Chunk Enable Applications

1. **Memory Efficiency**: Only read required data bytes
2. **SRAM Optimization**: Precise chunk forwarding to SRAM
3. **Network Efficiency**: Optimal Network 2.0 packet generation
4. **Bandwidth Utilization**: Eliminate unnecessary data transfers

#### Preallocation-Based Deadlock Prevention

##### Deadlock Prevention Strategy

```systemverilog
// Preallocation logic prevents deadlock
logic [NUM_CHANNELS-1:0] w_needs_prealloc;
logic [7:0] w_prealloc_beats [NUM_CHANNELS];

// Calculate preallocation requirements
generate
    for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_prealloc
        assign w_needs_prealloc[i] = data_valid[i] && 
                                   (available_lines[i] < w_prealloc_beats[i]) &&
                                   channel_ready_for_prealloc[i];
        
        // Calculate required beats based on transfer length
        assign w_prealloc_beats[i] = (data_length[i] + 15) >> 4;  // Convert chunks to beats
    end
endgenerate

// Preallocation request generation
assign prealloc_valid = |w_needs_prealloc;
assign prealloc_channel = priority_encoder(w_needs_prealloc);
assign prealloc_beats = w_prealloc_beats[prealloc_channel];
```

##### Benefits of Preallocation

1. **Deadlock Prevention**: Ensures SRAM space before AXI read
2. **Flow Control**: Coordinates with SRAM buffer management
3. **Performance Optimization**: Prevents pipeline stalls
4. **Resource Management**: Efficient SRAM space utilization

#### Multi-Channel Operation

##### Channel Arbitration

```systemverilog
// Multi-channel round-robin arbitration
logic [NUM_CHANNELS-1:0] w_channel_eligible;
logic [CHAN_WIDTH-1:0] w_selected_channel;

// Channel eligibility criteria
generate
    for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_eligibility
        assign w_channel_eligible[i] = data_valid[i] &&
                                     data_alignment_valid[i] &&
                                     (available_lines[i] >= w_prealloc_beats[i]) &&
                                     !w_channel_busy[i];
    end
endgenerate

// Round-robin arbiter
round_robin_arbiter #(
    .NUM_CHANNELS(NUM_CHANNELS)
) u_channel_arbiter (
    .clk(clk),
    .rst_n(rst_n),
    .request(w_channel_eligible),
    .grant_valid(w_grant_valid),
    .grant_id(w_selected_channel)
);
```

##### Independent Channel Processing

Each channel operates independently with:
- **Separate Transfer Tracking**: Independent transfer state per channel
- **Individual Alignment**: Per-channel alignment information processing
- **Buffer Coordination**: Channel-specific SRAM buffer management
- **Error Isolation**: Per-channel error detection and reporting

#### Stream Boundary Processing

##### EOS Handling

```systemverilog
// EOS detection and processing
logic [NUM_CHANNELS-1:0] w_eos_detected;
logic [NUM_CHANNELS-1:0] w_sequence_complete;

// EOS detection from scheduler interface
assign w_eos_detected = data_eos & data_valid;

// Sequence completion coordination
always_ff @(posedge clk) begin
    if (!rst_n) begin
        data_done_strobe <= '0;
    end else begin
        data_done_strobe <= w_eos_detected & w_transfer_complete;
    end
end

// Forward EOS to SRAM
assign wr_eos = w_current_eos && wr_valid;
```

#### AXI Transaction Management

##### Burst Optimization

```systemverilog
// Dynamic AXI burst configuration
always_comb begin
    case (cfg_transfer_size)
        2'b00: ar_len = 8'h00;      // Single beat
        2'b01: ar_len = 8'h0F;      // 1KB (16 beats)
        2'b10: ar_len = 8'h1F;      // 2KB (32 beats)
        2'b11: ar_len = 8'h3F;      // 4KB (64 beats)
    endcase
    
    // Override with alignment information if available
    if (data_alignment_valid[selected_channel]) begin
        ar_len = data_alignment_info[selected_channel].optimal_burst_len - 1;
    end
end

// AXI attributes for optimal performance
assign ar_size = 3'b110;        // 64 bytes (512 bits)
assign ar_burst = 2'b01;        // INCR burst type
assign ar_cache = 4'b0011;      // Normal, non-cacheable, bufferable
assign ar_prot = 3'b000;        // Data, non-secure, unprivileged
```

##### Transaction Tracking

```systemverilog
// Track outstanding transactions per channel
logic [7:0] outstanding_count [NUM_CHANNELS];
logic [NUM_CHANNELS-1:0] w_transaction_start;
logic [NUM_CHANNELS-1:0] w_transaction_complete;

// Transaction lifecycle tracking
assign w_transaction_start = data_valid & data_ready;
assign w_transaction_complete = r_valid & r_ready & r_last;

// Update outstanding counters
generate
    for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_tracking
        always_ff @(posedge clk) begin
            if (!rst_n) begin
                outstanding_count[i] <= 8'h0;
            end else begin
                case ({w_transaction_start[i], w_transaction_complete[i]})
                    2'b10: outstanding_count[i] <= outstanding_count[i] + 1;
                    2'b01: outstanding_count[i] <= outstanding_count[i] - 1;
                    default: outstanding_count[i] <= outstanding_count[i];
                endcase
            end
        end
    end
endgenerate
```

#### Error Detection and Recovery

##### Comprehensive Error Monitoring

```systemverilog
// Multi-layer error detection
logic [NUM_CHANNELS-1:0] w_axi_error;
logic [NUM_CHANNELS-1:0] w_timeout_error;
logic [NUM_CHANNELS-1:0] w_alignment_error;

// AXI response error detection
assign w_axi_error[channel] = r_valid && (r_id == channel) && (r_resp != 2'b00);

// Timeout detection per channel
generate
    for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_timeout
        timeout_detector #(
            .TIMEOUT_CYCLES(TIMEOUT_CYCLES)
        ) u_timeout (
            .clk(clk),
            .rst_n(rst_n),
            .start(w_transaction_start[i]),
            .stop(w_transaction_complete[i]),
            .timeout(w_timeout_error[i])
        );
    end
endgenerate

// Combined error reporting
assign data_error = w_axi_error | w_timeout_error | w_alignment_error;
```

#### Performance Characteristics

##### Throughput Analysis
- **Peak Bandwidth**: 512 bits x 1 GHz = 512 Gbps theoretical maximum
- **Sustained Rate**: >90% efficiency with optimal alignment and buffering
- **Multi-Channel**: Concurrent operation across active channels
- **Pipeline Efficiency**: Zero FSM overhead in critical path

##### Latency Characteristics
- **Address Issue**: 1-2 cycles from channel selection
- **First Data**: AXI read latency + pipeline traversal
- **Completion**: <5 cycles from last AXI data to SRAM write
- **Channel Switching**: 1 cycle arbitration overhead

##### Memory Efficiency
- **Chunk Precision**: Only required bytes transferred
- **Alignment Optimization**: Optimal burst patterns reduce overhead
- **Preallocation**: Prevents wasted AXI bandwidth from buffer overflow
- **Stream Awareness**: Proper boundary handling eliminates extra transfers

#### Monitor Bus Events

The source AXI read engine generates comprehensive monitor events:

##### Performance Events
- **Channel Selection**: Arbitration and channel grant timing
- **AXI Transaction**: Address issue, data reception, completion timing
- **Preallocation**: Space reservation and deadlock prevention
- **Chunk Generation**: Chunk enable calculation and optimization
- **Alignment Usage**: Address alignment effectiveness metrics

##### Error Events
- **AXI Error**: Read response error conditions
- **Timeout**: Transaction timeout detection
- **Alignment Error**: Address alignment validation failure
- **Buffer Error**: SRAM buffer overflow or underflow
- **Preallocation Error**: Space reservation failure

##### Completion Events
- **Transfer Complete**: AXI read transfer completion
- **Sequence Complete**: Multi-transfer sequence completion
- **EOS Processing**: End of Stream boundary completion
- **Channel Done**: Per-channel operation completion
- **Pipeline Flush**: Pipeline cleanup operations

#### Usage Guidelines

##### Performance Optimization

- Use address alignment bus for optimal AXI transfer planning
- Configure preallocation thresholds to prevent deadlock while minimizing overhead
- Monitor channel utilization and adjust arbitration priorities
- Use streaming mode for sustained high-bandwidth transfers

##### Buffer Management

Optimal buffer coordination requires:
1. Configure available_lines signals based on SRAM status
2. Set preallocation thresholds to prevent buffer overflow
3. Monitor channel_ready_for_prealloc for flow control
4. Balance preallocation overhead vs. deadlock prevention

##### Alignment Integration

The engine leverages scheduler alignment for optimal performance:
```systemverilog
// Example alignment-aware operation
if (data_alignment_valid[channel] && 
    (data_transfer_phase[channel] == PHASE_ALIGNMENT)) begin
    // Use pre-calculated alignment parameters
    ar_addr <= data_alignment_info[channel].aligned_addr;
    ar_len <= data_alignment_info[channel].first_burst_len;
    expected_chunk_pattern <= data_alignment_info[channel].first_chunk_enables;
end
```

This pure pipeline architecture with address alignment integration provides optimal AXI read performance while maintaining comprehensive error detection and multi-channel fairness.
