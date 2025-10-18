### Source Data Path

#### Overview

The Source Data Path provides a complete integrated data transmission pipeline that combines multi-channel scheduler interfaces, AXI memory read operations, SRAM buffering, Network packet transmission, and comprehensive monitor bus aggregation. This wrapper manages the complete data flow from scheduler requests through final Network network transmission.

The wrapper implements sophisticated address alignment processing, credit-based flow control, and stream boundary management to ensure optimal AXI read performance and reliable Network packet delivery with zero packet loss guarantees.

![source data path](/mnt/data/github/tsunami/design/rapids/markdown/rapids_spec/draw.io/png/source_data_path.png)

#### Key Features

- **Complete Data Transmission Pipeline**: From scheduler requests to Network packet transmission
- **Multi-Channel Scheduler Interface**: Enhanced interface with address alignment bus support
- **AXI Read Engine**: Optimized multi-channel AXI read operations with tracking
- **SRAM Buffering**: Multi-channel buffering with preallocation and flow control
- **Network Master**: Four-stage pipeline with credit-based flow control
- **Monitor Bus Aggregation**: Unified monitoring from AXI engine, SRAM control, and Network master
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
| **data_address** | logic | ADDR_WIDTH × NUM_CHANNELS | Input | Yes | Data address per channel |
| **data_length** | logic | 32 × NUM_CHANNELS | Input | Yes | Data length per channel |
| **data_type** | logic | 2 × NUM_CHANNELS | Input | Yes | Data type per channel |
| **data_eos** | logic | NUM_CHANNELS | Input | Yes | End of Stream per channel |
| **data_transfer_length** | logic | 32 × NUM_CHANNELS | Output | Yes | Actual transfer length per channel |
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

##### Network Packet Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **m_network_pkt_addr** | logic | 16 | Output | Yes | Network packet address |
| **m_network_pkt_addr_par** | logic | 1 | Output | Yes | Network packet address parity |
| **m_network_pkt_data** | logic | DATA_WIDTH | Output | Yes | Network packet data |
| **m_network_pkt_type** | logic | 2 | Output | Yes | Network packet type |
| **m_network_pkt_chunk_enables** | logic | NUM_CHUNKS | Output | Yes | Network packet chunk enables |
| **m_network_pkt_eos** | logic | 1 | Output | Yes | Network packet End of Stream |
| **m_network_pkt_par** | logic | 1 | Output | Yes | Network packet data parity |
| **m_network_pkt_valid** | logic | 1 | Output | Yes | Network packet valid |
| **m_network_pkt_ready** | logic | 1 | Input | Yes | Network packet ready |

##### Network Credit Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **s_network_credit_addr** | logic | 16 | Input | Yes | Network credit address |
| **s_network_credit_addr_par** | logic | 1 | Input | Yes | Network credit address parity |
| **s_network_credit_count** | logic | 8 | Input | Yes | Network credit count |
| **s_network_credit_par** | logic | 1 | Input | Yes | Network credit parity |
| **s_network_credit_valid** | logic | 1 | Input | Yes | Network credit valid |
| **s_network_credit_ready** | logic | 1 | Output | Yes | Network credit ready |

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
| **sram_credit_available** | logic | NUM_CHANNELS | Output | Yes | SRAM credit available per channel |
| **network_credits_available** | logic | NUM_CHANNELS | Output | Yes | Network credit available per channel |
| **error_axi_timeout** | logic | 1 | Output | Yes | AXI timeout error |
| **error_network_timeout** | logic | 1 | Output | Yes | Network timeout error |
| **error_credit_underflow** | logic | 1 | Output | Yes | Credit underflow error |
| **error_channel_id** | logic | CHAN_WIDTH | Output | Yes | Channel with error |

#### Architecture

##### Internal Components

- **Source AXI Read Engine**: Multi-channel AXI read operations with address tracking
- **Source SRAM Control**: Multi-channel buffering with preallocation and credit management
- **Network Master**: Four-stage pipeline with credit-based flow control and packet transmission
- **Monitor Bus Aggregator**: Round-robin aggregation from all three components

##### Data Flow Pipeline

1. **Scheduler Request**: Multi-channel scheduler provides data requests with alignment information
2. **AXI Read Operations**: AXI engine performs optimized read operations using pre-calculated alignment
3. **SRAM Buffering**: SRAM control provides multi-channel buffering with flow control
4. **Network Transmission**: Network master transmits packets with credit-based flow control
5. **Credit Management**: End-to-end credit tracking ensures flow control and prevents overflow

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

##### Credit-Based Flow Control

The wrapper implements comprehensive credit management:
- **SRAM Credits**: Prevent SRAM buffer overflow
- **Network Credits**: Ensure network-level flow control
- **Credit Return**: Automatic credit return on packet consumption
- **Deadlock Prevention**: Credit thresholds and timeout detection

#### Network 2.0 Support

The source data path fully supports the Network 2.0 protocol specification, using chunk enables instead of the older start/len approach for indicating valid data chunks within each 512-bit packet. This provides more flexible and precise control over partial data transfers.

#### Usage Guidelines

##### Performance Optimization

- Use address alignment bus for optimal AXI read planning
- Configure SRAM preallocation thresholds based on workload
- Adjust credit limits based on network and memory latency
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
    // Chunk enables already calculated
    chunk_enables <= alignment_info.chunk_enables;
end
```

##### Credit Management

Proper credit management requires:
1. Monitor SRAM and Network credit availability
2. Respect credit limits to prevent overflow
3. Track credit return on packet consumption
4. Handle credit underflow and timeout conditions

##### Error Handling

The wrapper provides comprehensive error detection:
- Monitor AXI and Network timeout conditions
- Check credit underflow situations
- Verify packet delivery and acknowledgment
- Track per-channel error statistics

##### Stream Boundary Processing

The wrapper handles stream boundaries correctly:
- EOS propagation through the pipeline
- Proper packet boundary management
- Credit return on stream completion
- Coordination with downstream processors
