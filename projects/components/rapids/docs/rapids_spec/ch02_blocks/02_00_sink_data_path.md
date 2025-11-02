### Sink Data Path

#### Overview

The Sink Data Path provides a complete integrated data reception and processing pipeline that combines AXI-Stream packet reception, multi-channel SRAM buffering, multi-channel AXI write arbitration, and comprehensive monitor bus aggregation. This wrapper manages the complete data flow from AXIS interface reception through final AXI memory writes.

**RTL Module:** `rtl/amba/axis/axis_slave.sv` (AXIS interface) + RAPIDS sink components

The wrapper implements sophisticated TLAST (End of Stream) flow control where packet-level TLAST is managed by SRAM control and descriptor-level EOS completion is coordinated with the scheduler, ensuring proper stream boundary handling throughout the pipeline.

![sink data path](draw.io/png/sink_data_path.png)

#### Key Features

- **Complete Data Reception Pipeline**: From AXIS packets to AXI memory writes
- **Standard AXIS Interface**: Industry-standard AXI-Stream protocol (no custom credits/ACKs)
- **Multi-Channel SRAM Buffering**: Independent buffering for up to 32 channels
- **Advanced AXI Write Engine**: Multi-channel arbitration with transfer strategy optimization
- **TLAST Flow Management**: Packet-level and descriptor-level boundary coordination
- **RDA Packet Routing**: Direct RDA packet interfaces bypassing SRAM buffering
- **Monitor Bus Aggregation**: Unified monitoring from AXIS slave, SRAM control, and AXI engine
- **Enhanced Scheduler Interface**: Address alignment bus support for optimal AXI performance

#### Interface Specification

##### Clock and Reset

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **clk** | logic | 1 | Input | Yes | System clock |
| **rst_n** | logic | 1 | Input | Yes | Active-low asynchronous reset |

##### AXI-Stream Slave Interface (RX)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **axis_snk_rx_tdata** | logic | DATA_WIDTH | Input | Yes | Stream data payload |
| **axis_snk_rx_tstrb** | logic | DATA_WIDTH/8 | Input | Yes | Byte strobes (write enables) |
| **axis_snk_rx_tlast** | logic | 1 | Input | Yes | Last transfer in packet |
| **axis_snk_rx_tvalid** | logic | 1 | Input | Yes | Stream data valid |
| **axis_snk_rx_tready** | logic | 1 | Output | Yes | Stream ready (backpressure) |
| **axis_snk_rx_tuser** | logic | 16 | Input | Yes | User sideband (packet metadata) |

**TUSER Encoding (Sink RX):**
```
[15:8] - Channel ID
[7:0]  - Packet type/flags
```

**Note:** AXIS uses standard `tvalid/tready` backpressure. No ACK channels or custom credit mechanisms.

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

- **AXIS Slave**: Packet reception, validation, and routing with standard AXIS flow control
- **Sink SRAM Control**: Multi-channel buffering with TLAST/EOS completion signaling
- **Sink AXI Write Engine**: Multi-channel arbitration and AXI write operations
- **Monitor Bus Aggregator**: Round-robin aggregation from all three components

##### Data Flow Pipeline

1. **AXIS Packet Reception**: AXIS slave receives and validates incoming packets
2. **Packet Classification**: Packets routed to SRAM (FC/TS/RAW) or RDA bypass (RDA packets)
3. **Multi-Channel Buffering**: SRAM control provides independent per-channel buffering
4. **AXI Write Arbitration**: AXI engine arbitrates between channels using scheduler inputs
5. **TLAST Completion**: Packet-level TLAST triggers descriptor completion notification

##### TLAST Flow Management

The sink data path implements sophisticated stream boundary handling:
- **Packet-Level TLAST**: Detected by AXIS slave, managed by SRAM control
- **EOS Completion Interface**: SRAM control notifies scheduler of descriptor completion
- **Stream Boundaries**: TLAST triggers proper completion signaling (maps to internal EOS)

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
- **TSTRB-Based Strobes**: Precise write strobes based on AXIS byte strobes

#### AXIS Integration

The sink data path uses standard AXI-Stream (AXIS4) protocol for packet reception:

**Key Benefits:**
1. **Industry Standard**: AXIS is widely supported, well-documented protocol
2. **Simplified Flow Control**: Standard `tvalid/tready` backpressure (no custom ACK channels)
3. **Cleaner Byte Qualification**: Standard `tstrb` replaces custom chunk enables
4. **Packet Framing**: Standard `tlast` replaces custom EOS markers
5. **Better Tool Support**: Standard protocol enables better IP integration and verification

**TSTRB vs Legacy Chunk Enables:**
- AXIS: 64-bit byte strobes for 512-bit data (byte-level granularity)
- Legacy: 16-bit chunk enables (32-bit chunk granularity)
- TSTRB provides finer control and maps directly to AXI4 `wstrb`

#### Usage Guidelines

##### Performance Optimization

- Configure SRAM depths based on expected buffering requirements
- Use address alignment bus for optimal AXI transfer planning
- Monitor buffer status and arbitration efficiency
- Adjust transfer strategies based on workload characteristics

##### Error Handling

The wrapper provides comprehensive error reporting:
- Monitor TSTRB errors for data integrity
- Check buffer overflow conditions
- Verify AXIS protocol compliance
- Track per-channel error statistics

##### TLAST Processing

Proper stream boundary handling requires:
1. Monitor packet-level TLAST from AXIS slave
2. Track EOS completion notifications to scheduler (TLAST -> EOS mapping)
3. Coordinate descriptor completion with stream boundaries
4. Use standard AXIS backpressure (`tready`) for flow control
