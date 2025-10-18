### Sink Data Path

#### Overview

The Sink Data Path provides a complete integrated data reception and processing pipeline that combines Network packet reception, multi-channel SRAM buffering, multi-channel AXI write arbitration, and comprehensive monitor bus aggregation. This wrapper manages the complete data flow from Network network reception through final AXI memory writes.

The wrapper implements sophisticated EOS (End of Stream) flow control where packet-level EOS is managed by SRAM control and descriptor-level EOS completion is coordinated with the scheduler, ensuring proper stream boundary handling throughout the pipeline.

![sink data path](/mnt/data/github/tsunami/design/rapids/markdown/rapids_spec/draw.io/png/sink_data_path.png)

#### Key Features

- **Complete Data Reception Pipeline**: From Network packets to AXI memory writes
- **Multi-Channel SRAM Buffering**: Independent buffering for up to 32 channels
- **Advanced AXI Write Engine**: Multi-channel arbitration with transfer strategy optimization
- **EOS Flow Management**: Packet-level and descriptor-level EOS coordination
- **RDA Packet Routing**: Direct RDA packet interfaces bypassing SRAM buffering
- **Monitor Bus Aggregation**: Unified monitoring from Network slave, SRAM control, and AXI engine
- **Enhanced Scheduler Interface**: Address alignment bus support for optimal AXI performance

#### Interface Specification

##### Clock and Reset

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **clk** | logic | 1 | Input | Yes | System clock |
| **rst_n** | logic | 1 | Input | Yes | Active-low asynchronous reset |

##### Network Network Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **s_network_pkt_addr** | logic | ADDR_WIDTH | Input | Yes | Network packet address |
| **s_network_pkt_addr_par** | logic | 1 | Input | Yes | Network packet address parity |
| **s_network_pkt_data** | logic | DATA_WIDTH | Input | Yes | Network packet data |
| **s_network_pkt_type** | logic | 2 | Input | Yes | Network packet type |
| **s_network_pkt_chunk_enables** | logic | NUM_CHUNKS | Input | Yes | Network packet chunk enables |
| **s_network_pkt_eos** | logic | 1 | Input | Yes | Network packet End of Stream |
| **s_network_pkt_par** | logic | 1 | Input | Yes | Network packet data parity |
| **s_network_pkt_valid** | logic | 1 | Input | Yes | Network packet valid |
| **s_network_pkt_ready** | logic | 1 | Output | Yes | Network packet ready |

##### Network ACK Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **m_network_ack_addr** | logic | ADDR_WIDTH | Output | Yes | Network ACK address |
| **m_network_ack_addr_par** | logic | 1 | Output | Yes | Network ACK address parity |
| **m_network_ack_ack** | logic | 2 | Output | Yes | Network ACK type |
| **m_network_ack_par** | logic | 1 | Output | Yes | Network ACK parity |
| **m_network_ack_valid** | logic | 1 | Output | Yes | Network ACK valid |
| **m_network_ack_ready** | logic | 1 | Input | Yes | Network ACK ready |

##### RDA Interfaces (Direct Bypass)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **rda_src_valid** | logic | 1 | Output | Yes | RDA source packet valid |
| **rda_src_ready** | logic | 1 | Input | Yes | RDA source packet ready |
| **rda_src_packet** | logic | DATA_WIDTH | Output | Yes | RDA source packet data |
| **rda_src_channel** | logic | CHAN_WIDTH | Output | Yes | RDA source channel |
| **rda_src_eos** | logic | 1 | Output | Yes | RDA source End of Stream |
| **rda_snk_valid** | logic | 1 | Output | Yes | RDA sink packet valid |
| **rda_snk_ready** | logic | 1 | Input | Yes | RDA sink packet ready |
| **rda_snk_packet** | logic | DATA_WIDTH | Output | Yes | RDA sink packet data |
| **rda_snk_channel** | logic | CHAN_WIDTH | Output | Yes | RDA sink channel |
| **rda_snk_eos** | logic | 1 | Output | Yes | RDA sink End of Stream |

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
| **data_alignment_info** | alignment_info_t | NUM_CHANNELS | Input | Yes | Alignment information per channel |
| **data_alignment_valid** | logic | NUM_CHANNELS | Input | Yes | Alignment information valid per channel |
| **data_alignment_ready** | logic | NUM_CHANNELS | Output | Yes | Alignment information ready per channel |
| **data_alignment_next** | logic | NUM_CHANNELS | Output | Yes | Request next alignment per channel |
| **data_transfer_phase** | transfer_phase_t | NUM_CHANNELS | Input | Yes | Transfer phase per channel |
| **data_sequence_complete** | logic | NUM_CHANNELS | Output | Yes | Transfer sequence complete per channel |

##### EOS Completion Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **eos_completion_valid** | logic | 1 | Output | Yes | EOS completion notification valid |
| **eos_completion_ready** | logic | 1 | Input | Yes | EOS completion notification ready |
| **eos_completion_channel** | logic | CHAN_WIDTH | Output | Yes | Channel with EOS completion |

##### AXI4 Master Write Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **m_axi_awvalid** | logic | 1 | Output | Yes | Write address valid |
| **m_axi_awready** | logic | 1 | Input | Yes | Write address ready |
| **m_axi_awaddr** | logic | AXI_ADDR_WIDTH | Output | Yes | Write address |
| **m_axi_awlen** | logic | 8 | Output | Yes | Burst length |
| **m_axi_awsize** | logic | 3 | Output | Yes | Burst size |
| **m_axi_awburst** | logic | 2 | Output | Yes | Burst type |
| **m_axi_awid** | logic | AXI_ID_WIDTH | Output | Yes | Write ID |
| **m_axi_awlock** | logic | 1 | Output | Yes | Lock type |
| **m_axi_awcache** | logic | 4 | Output | Yes | Cache type |
| **m_axi_awprot** | logic | 3 | Output | Yes | Protection type |
| **m_axi_awqos** | logic | 4 | Output | Yes | QoS identifier |
| **m_axi_awregion** | logic | 4 | Output | Yes | Region identifier |
| **m_axi_wvalid** | logic | 1 | Output | Yes | Write data valid |
| **m_axi_wready** | logic | 1 | Input | Yes | Write data ready |
| **m_axi_wdata** | logic | DATA_WIDTH | Output | Yes | Write data |
| **m_axi_wstrb** | logic | DATA_WIDTH/8 | Output | Yes | Write strobes |
| **m_axi_wlast** | logic | 1 | Output | Yes | Write last |
| **m_axi_bvalid** | logic | 1 | Input | Yes | Write response valid |
| **m_axi_bready** | logic | 1 | Output | Yes | Write response ready |
| **m_axi_bresp** | logic | 2 | Input | Yes | Write response |
| **m_axi_bid** | logic | AXI_ID_WIDTH | Input | Yes | Write ID |

##### Monitor Bus Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **mon_valid** | logic | 1 | Output | Yes | Monitor packet valid |
| **mon_ready** | logic | 1 | Input | Yes | Monitor ready to accept packet |
| **mon_packet** | logic | 64 | Output | Yes | Monitor packet data |

##### Status and Error Reporting

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **channel_eos_pending** | logic | NUM_CHANNELS | Output | Yes | EOS pending per channel |
| **error_header_parity** | logic | 1 | Output | Yes | Header parity error |
| **error_body_parity** | logic | 1 | Output | Yes | Body parity error |
| **error_buffer_overflow** | logic | 1 | Output | Yes | Buffer overflow error |
| **error_ack_lost** | logic | 1 | Output | Yes | ACK lost error |
| **error_channel_id** | logic | CHAN_WIDTH | Output | Yes | Channel with error |
| **packet_count** | logic | 32 | Output | Yes | Total packet count |
| **error_count** | logic | 16 | Output | Yes | Total error count |

#### Architecture

##### Internal Components

- **Network Slave**: Packet reception, validation, and routing with bulletproof ACK generation
- **Sink SRAM Control**: Multi-channel buffering with EOS completion signaling
- **Sink AXI Write Engine**: Multi-channel arbitration and AXI write operations
- **Monitor Bus Aggregator**: Round-robin aggregation from all three components

##### Data Flow Pipeline

1. **Network Packet Reception**: Network slave receives and validates incoming packets
2. **Packet Classification**: Packets routed to SRAM (FC/TS/RAW) or RDA bypass (RDA packets)
3. **Multi-Channel Buffering**: SRAM control provides independent per-channel buffering
4. **AXI Write Arbitration**: AXI engine arbitrates between channels using scheduler inputs
5. **EOS Completion**: Packet-level EOS triggers descriptor completion notification

##### EOS Flow Management

The sink data path implements sophisticated EOS handling:
- **Packet-Level EOS**: Detected by Network slave, managed by SRAM control
- **EOS Completion Interface**: SRAM control notifies scheduler of descriptor completion
- **Stream Boundaries**: EOS triggers proper completion signaling and credit return

##### Address Alignment Integration

The wrapper supports the scheduler's address alignment bus, enabling:
- **Pre-calculated Alignment**: Scheduler provides alignment information before transfers
- **Optimal AXI Performance**: No alignment calculation overhead in AXI critical path
- **Transfer Strategy Selection**: Alignment information drives AXI burst optimization

##### Multi-Channel AXI Arbitration

The AXI write engine implements sophisticated arbitration:
- **Round-Robin Base**: Fair arbitration across active channels
- **Transfer Strategy**: Precision/aligned/forced/single transfer modes
- **Buffer-Aware**: Considers SRAM buffer status for optimal performance
- **Chunk-Aware Strobes**: Precise write strobes based on chunk enables

#### Network 2.0 Support

The sink data path fully supports the Network 2.0 protocol specification, using chunk enables instead of the older start/len approach for indicating valid data chunks within each 512-bit packet. This provides more flexible and precise control over partial data transfers.

#### Usage Guidelines

##### Performance Optimization

- Configure SRAM depths based on expected buffering requirements
- Use address alignment bus for optimal AXI transfer planning
- Monitor buffer status and arbitration efficiency
- Adjust transfer strategies based on workload characteristics

##### Error Handling

The wrapper provides comprehensive error reporting:
- Monitor parity errors for data integrity
- Check buffer overflow conditions
- Verify ACK generation and delivery
- Track per-channel error statistics

##### EOS Processing

Proper EOS handling requires:
1. Monitor packet-level EOS from Network slave
2. Track EOS completion notifications to scheduler
3. Coordinate descriptor completion with stream boundaries
4. Ensure proper credit return for flow control
