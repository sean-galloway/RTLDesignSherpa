### Source Data Path

#### Overview

The Source Data Path provides a complete integrated data transmission pipeline that combines multi-channel scheduler interfaces, AXI memory read operations, SRAM buffering, AXIS packet transmission, and comprehensive monitor bus aggregation. This wrapper manages the complete data flow from scheduler requests through final AXIS stream transmission.

**RTL Module:** `rtl/amba/axis/axis_master.sv` (AXIS interface) + RAPIDS source components

The wrapper implements sophisticated address alignment processing and stream boundary management to ensure optimal AXI read performance and reliable AXIS packet delivery with zero packet loss guarantees.

![source data path](draw.io/png/source_data_path.png)

#### Key Features

- **Complete Data Transmission Pipeline**: From scheduler requests to AXIS packet transmission
- **Standard AXIS Interface**: Industry-standard AXI-Stream protocol (no custom credits)
- **Multi-Channel Scheduler Interface**: Enhanced interface with address alignment bus support
- **AXI Read Engine**: Optimized multi-channel AXI read operations with tracking
- **SRAM Buffering**: Multi-channel buffering with preallocation and flow control
- **AXIS Master**: Multi-channel arbitration with standard AXIS backpressure
- **Monitor Bus Aggregation**: Unified monitoring from AXI engine, SRAM control, and AXIS master
- **Address Alignment Integration**: Pre-calculated alignment information for optimal performance

#### Interface Specification

##### Clock and Reset

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **clk** | logic | 1 | Input | Yes | System clock |
| **rst_n** | logic | 1 | Input | Yes | Active-low asynchronous reset |

##### Configuration Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **cfg_transfer_size** | logic | 2 | Input | Yes | Transfer size configuration (00=1Beat, 01=1KB, 10=2KB, 11=4KB) |
| **cfg_streaming_enable** | logic | 1 | Input | Yes | Streaming mode enable |
| **cfg_sram_enable** | logic | 1 | Input | Yes | SRAM buffering enable |
| **cfg_channel_enable** | logic | NUM_CHANNELS | Input | Yes | Per-channel enable control |

##### Multi-Channel Scheduler Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **data_valid** | logic | NUM_CHANNELS | Input | Yes | Data transfer request per channel |
| **data_ready** | logic | NUM_CHANNELS | Output | Yes | Data transfer ready per channel |
| **data_address** | logic | ADDR_WIDTH x NUM_CHANNELS | Input | Yes | Data address per channel |
| **data_length** | logic | 32 x NUM_CHANNELS | Input | Yes | Data length per channel |
| **data_type** | logic | 2 x NUM_CHANNELS | Input | Yes | Data type per channel |
| **data_eos** | logic | NUM_CHANNELS | Input | Yes | End of Stream per channel |
| **data_transfer_length** | logic | 32 x NUM_CHANNELS | Output | Yes | Actual transfer length per channel |
| **data_done_strobe** | logic | NUM_CHANNELS | Output | Yes | Transfer completion per channel |
| **data_error** | logic | NUM_CHANNELS | Output | Yes | Transfer error per channel |

##### Address Alignment Bus Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **data_alignment_info** | alignment_info_t | NUM_CHANNELS | Input | Yes | Pre-calculated alignment information per channel |
| **data_alignment_valid** | logic | NUM_CHANNELS | Input | Yes | Alignment information valid per channel |
| **data_alignment_ready** | logic | NUM_CHANNELS | Output | Yes | Alignment information ready per channel |
| **data_alignment_next** | logic | NUM_CHANNELS | Output | Yes | Request next alignment per channel |
| **data_transfer_phase** | transfer_phase_t | NUM_CHANNELS | Input | Yes | Current transfer phase per channel |
| **data_sequence_complete** | logic | NUM_CHANNELS | Output | Yes | Transfer sequence complete per channel |

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
| **ar_cache** | logic | 4 | Output | Yes | Cache type |
| **ar_prot** | logic | 3 | Output | Yes | Protection type |
| **ar_qos** | logic | 4 | Output | Yes | QoS identifier |
| **ar_region** | logic | 4 | Output | Yes | Region identifier |
| **r_valid** | logic | 1 | Input | Yes | Read data valid |
| **r_ready** | logic | 1 | Output | Yes | Read data ready |
| **r_data** | logic | DATA_WIDTH | Input | Yes | Read data |
| **r_resp** | logic | 2 | Input | Yes | Read response |
| **r_last** | logic | 1 | Input | Yes | Read last |
| **r_id** | logic | AXI_ID_WIDTH | Input | Yes | Read ID |

##### AXI-Stream Master Interface (TX)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **axis_src_tx_tdata** | logic | DATA_WIDTH | Output | Yes | Stream data payload |
| **axis_src_tx_tstrb** | logic | DATA_WIDTH/8 | Output | Yes | Byte strobes (write enables) |
| **axis_src_tx_tlast** | logic | 1 | Output | Yes | Last transfer in packet |
| **axis_src_tx_tvalid** | logic | 1 | Output | Yes | Stream data valid |
| **axis_src_tx_tready** | logic | 1 | Input | Yes | Stream ready (backpressure) |
| **axis_src_tx_tuser** | logic | 16 | Output | Yes | User sideband (packet metadata) |

**TUSER Encoding (Source TX):**
```
[15:8] - Channel ID
[7:0]  - Packet type/flags
```

**Note:** AXIS uses standard `tvalid/tready` backpressure. No credit channels or custom flow control mechanisms.

##### Monitor Bus Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **mon_valid** | logic | 1 | Output | Yes | Monitor packet valid |
| **mon_ready** | logic | 1 | Input | Yes | Monitor ready to accept packet |
| **mon_packet** | logic | 64 | Output | Yes | Monitor packet data |

##### Status and Control

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **engine_idle** | logic | NUM_CHANNELS | Output | Yes | Engine idle status per channel |
| **engine_busy** | logic | NUM_CHANNELS | Output | Yes | Engine busy status per channel |
| **sram_space_available** | logic | NUM_CHANNELS | Output | Yes | SRAM space available per channel |
| **axis_backpressure_active** | logic | 1 | Output | Yes | AXIS backpressure status |
| **error_axi_timeout** | logic | 1 | Output | Yes | AXI timeout error |
| **error_axis_protocol** | logic | 1 | Output | Yes | AXIS protocol error |
| **error_buffer_underflow** | logic | 1 | Output | Yes | Buffer underflow error |
| **error_channel_id** | logic | CHAN_WIDTH | Output | Yes | Channel with error |

#### Architecture

##### Internal Components

- **Source AXI Read Engine**: Multi-channel AXI read operations with address tracking
- **Source SRAM Control**: Multi-channel buffering with preallocation and flow control
- **AXIS Master**: Multi-channel arbitration with standard AXIS backpressure handling
- **Monitor Bus Aggregator**: Round-robin aggregation from all three components

##### Data Flow Pipeline

1. **Scheduler Request**: Multi-channel scheduler provides data requests with alignment information
2. **AXI Read Operations**: AXI engine performs optimized read operations using pre-calculated alignment
3. **SRAM Buffering**: SRAM control provides multi-channel buffering with flow control
4. **AXIS Transmission**: AXIS master transmits packets with standard backpressure handling
5. **Flow Control**: Standard AXIS backpressure propagates through pipeline

##### Address Alignment Integration

The wrapper integrates with the scheduler's address alignment bus:
- **Pre-Calculated Alignment**: Scheduler provides complete alignment information
- **Optimal AXI Planning**: Address offset, burst planning, and chunk enables pre-calculated
- **Transfer Phase Management**: Alignment/streaming/final transfer phases coordinated
- **Performance Benefits**: Eliminates alignment calculation overhead from AXI critical path

##### Multi-Channel Operation

Each channel operates independently with:
- **Independent Credit Tracking**: Separate SRAM and Network credit management
- **Channel-Aware Arbitration**: Fair arbitration across active channels
- **Per-Channel Status**: Individual idle/busy and error reporting
- **Configurable Operation**: Per-channel enable and configuration control

##### Standard AXIS Flow Control

The wrapper implements standard AXIS backpressure:
- **SRAM Buffering**: Prevent SRAM buffer overflow
- **AXIS Backpressure**: Standard `tvalid/tready` flow control
- **Upstream Coordination**: Backpressure propagates from AXIS to SRAM to AXI
- **Buffer Management**: Deep buffering absorbs backpressure transients

#### AXIS Integration

The source data path uses standard AXI-Stream (AXIS4) protocol for packet transmission:

**Key Benefits:**
1. **Industry Standard**: AXIS is widely supported, well-documented protocol
2. **Simplified Flow Control**: Standard `tvalid/tready` backpressure (no custom credits)
3. **Cleaner Byte Qualification**: Standard `tstrb` from chunk enables
4. **Packet Framing**: Standard `tlast` from internal EOS markers
5. **Better Tool Support**: Standard protocol enables better IP integration and verification

**TSTRB from Chunk Enables:**
- Chunk enables (16-bit for 512-bit data) -> TSTRB (64-bit byte strobes)
- Each chunk enable bit controls 4 bytes (32 bits)
- TSTRB provides byte-level granularity for precise data handling

#### Usage Guidelines

##### Performance Optimization

- Use address alignment bus for optimal AXI read planning
- Configure SRAM preallocation thresholds based on workload
- Adjust buffer depths based on downstream AXIS sink latency
- Monitor channel utilization and arbitration efficiency

##### Address Alignment Usage

The wrapper leverages pre-calculated alignment information:
```systemverilog
// Alignment information provided by scheduler
alignment_info_t alignment_info = data_alignment_info[channel];
if (data_alignment_valid[channel]) begin
    // Use pre-calculated alignment for optimal AXI reads
    ar_addr <= alignment_info.aligned_addr;
    ar_len <= alignment_info.optimal_burst_len;
    // Chunk enables already calculated for TSTRB conversion
    chunk_enables <= alignment_info.chunk_enables;
end
```

##### Flow Control Management

Proper AXIS backpressure handling requires:
1. Monitor SRAM buffer availability and utilization
2. Respect AXIS `tready` signal for downstream backpressure
3. Use deep buffering to absorb transient backpressure
4. Handle buffer underflow and timeout conditions

##### Error Handling

The wrapper provides comprehensive error detection:
- Monitor AXI and AXIS timeout conditions
- Check buffer underflow situations
- Verify AXIS protocol compliance
- Track per-channel error statistics

##### Stream Boundary Processing

The wrapper handles stream boundaries correctly:
- EOS propagation through the pipeline
- Proper packet boundary management
- Credit return on stream completion
- Coordination with downstream processors
