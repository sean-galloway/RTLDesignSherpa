### Scheduler Group Array

#### Overview

The Scheduler Group Array is the top-level integration module that instantiates multiple `scheduler_group` instances and provides shared AXI master interfaces with round-robin arbitration. This module enables efficient multi-channel operation by allowing multiple channels to share common AXI infrastructure while maintaining isolation between channel operations.

**Architecture Highlights:**

- **Multi-Channel Array**: Instantiates `CHANNEL_COUNT` (default 32) independent `scheduler_group` instances
- **3 Shared AXI4 Masters**: Provides arbitrated access to external AXI infrastructure
  1. **Descriptor Engine** (read-only, 512-bit data width)
  2. **Control Read Engine** (read-only, 32-bit data width)
  3. **Control Write Engine** (write-only, 32-bit data width)
- **NOTE**: Program engine **removed** from scheduler_group and replaced with control engines
- **Round-Robin Arbitration**: Fair arbitration across all channels for each AXI master
- **ID-Based Response Routing**: Channel ID encoded in lower bits of AXI ID field for efficient demultiplexing
- **Unified MonBus Aggregation**: Combines monitor output from all channels and AXI masters (35 total sources)
- **Per-Channel Isolation**: Each channel operates independently with dedicated configuration and status

#### Key Features

- **Scalable Multi-Channel Design**: Configurable channel count (default 32 channels)
- **Efficient AXI Sharing**: 3 shared AXI masters eliminate per-channel master overhead
- **Fair Arbitration**: Round-robin arbitration ensures no channel starvation
- **Consistent ID Encoding**: Lower CHAN_WIDTH bits = channel ID, upper bits = 0 (same across all 3 AXI masters)
- **Response Routing**: AXI ID-based demultiplexing routes responses back to originating channel
- **MonBus Integration**: Each AXI master includes integrated monitoring with configurable packet filtering
- **Skid Buffers**: Configurable skid buffer depths for all AXI channels (AR, R, AW, W, B)
- **Clock Gating Support**: Integrated clock gating for power optimization
- **Array-Level Status**: Aggregated status for active channels, error counts, transaction counts

#### Interface Specification

##### Clock and Reset

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **clk** | logic | 1 | Input | Yes | System clock |
| **rst_n** | logic | 1 | Input | Yes | Active-low asynchronous reset |

##### Per-Channel Interfaces (Array of CHANNEL_COUNT)

###### APB Programming Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **apb_valid** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | APB descriptor fetch request valid (per channel) |
| **apb_ready** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | APB descriptor fetch request ready (per channel) |
| **apb_addr** | logic | ADDR_WIDTH [CHANNEL_COUNT] | Input | Yes | APB descriptor address (per channel) |

###### RDA Packet Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **rda_valid** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | RDA packet valid (per channel) |
| **rda_ready** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | RDA packet ready (per channel) |
| **rda_packet** | logic | DATA_WIDTH [CHANNEL_COUNT] | Input | Yes | RDA packet data (per channel) |
| **rda_channel** | logic | CHAN_WIDTH [CHANNEL_COUNT] | Input | Yes | RDA target channel (per channel) |

###### EOS Completion Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **eos_completion_valid** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | EOS completion notification valid (per channel) |
| **eos_completion_ready** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | EOS completion notification ready (per channel) |
| **eos_completion_channel** | logic | CHAN_WIDTH [CHANNEL_COUNT] | Input | Yes | Channel with EOS completion (per channel) |

###### Configuration Interface (Per Channel)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **cfg_idle_mode** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Global idle mode control (per channel) |
| **cfg_channel_wait** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Channel wait control (per channel) |
| **cfg_channel_enable** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Channel enable control (per channel) |
| **cfg_use_credit** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Credit mode enable (per channel) |
| **cfg_initial_credit** | logic | 4 [CHANNEL_COUNT] | Input | Yes | Initial credit values - exponential encoding (per channel) |
| **credit_increment** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Credit increment request (per channel) |
| **cfg_prefetch_enable** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Descriptor prefetch enable (per channel) |
| **cfg_fifo_threshold** | logic | 4 [CHANNEL_COUNT] | Input | Yes | Descriptor FIFO threshold (per channel) |
| **cfg_addr0_base** | logic | ADDR_WIDTH [CHANNEL_COUNT] | Input | Yes | Address range 0 base (per channel) |
| **cfg_addr0_limit** | logic | ADDR_WIDTH [CHANNEL_COUNT] | Input | Yes | Address range 0 limit (per channel) |
| **cfg_addr1_base** | logic | ADDR_WIDTH [CHANNEL_COUNT] | Input | Yes | Address range 1 base (per channel) |
| **cfg_addr1_limit** | logic | ADDR_WIDTH [CHANNEL_COUNT] | Input | Yes | Address range 1 limit (per channel) |
| **cfg_channel_reset** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Dynamic channel reset request (per channel) |
| **cfg_ctrlrd_max_try** | logic | 8 [CHANNEL_COUNT] | Input | Yes | Control read max retry count (per channel) |

###### Status Interface (Per Channel)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **descriptor_engine_idle** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | Descriptor engine idle status (per channel) |
| **program_engine_idle** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | Program engine idle (tied to 1'b1 - removed) (per channel) |
| **scheduler_idle** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | Scheduler idle status (per channel) |
| **descriptor_credit_counter** | logic | 32 [CHANNEL_COUNT] | Output | Yes | Current credit counter value (per channel) |
| **fsm_state** | logic | 6 [CHANNEL_COUNT] | Output | Yes | Current scheduler FSM state (per channel) |
| **scheduler_error** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | Scheduler error flag (per channel) |
| **backpressure_warning** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | Backpressure warning flag (per channel) |

###### Data Mover Interface (Per Channel)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **data_valid** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | Data transfer request active (per channel) |
| **data_ready** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Data engine ready for transfer (per channel) |
| **data_address** | logic | 64 [CHANNEL_COUNT] | Output | Yes | Current data address (per channel) |
| **data_length** | logic | 32 [CHANNEL_COUNT] | Output | Yes | Remaining data length (per channel) |
| **data_type** | logic | 2 [CHANNEL_COUNT] | Output | Yes | Packet type from descriptor (per channel) |
| **data_eos** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | End of Stream indicator (per channel) |
| **data_transfer_length** | logic | 32 [CHANNEL_COUNT] | Input | Yes | Actual transfer length completed (per channel) |
| **data_error** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Data transfer error (per channel) |
| **data_done_strobe** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Data transfer completed (per channel) |

###### Address Alignment Bus Interface (Per Channel)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **data_alignment_info** | alignment_info_t | struct [CHANNEL_COUNT] | Output | Yes | Pre-calculated alignment information (RAPIDS package type) (per channel) |
| **data_alignment_valid** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | Alignment information valid (per channel) |
| **data_alignment_ready** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Alignment information ready (per channel) |
| **data_alignment_next** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | Request next alignment calculation (per channel) |
| **data_transfer_phase** | transfer_phase_t | enum [CHANNEL_COUNT] | Output | Yes | Current transfer phase (RAPIDS package type) (per channel) |
| **data_sequence_complete** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | Transfer sequence complete (per channel) |

###### RDA Credit Return Interface (Per Channel)

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **rda_complete_valid** | logic | [CHANNEL_COUNT-1:0] | Output | Yes | RDA completion notification (per channel) |
| **rda_complete_ready** | logic | [CHANNEL_COUNT-1:0] | Input | Yes | RDA completion ready (per channel) |
| **rda_complete_channel** | logic | CHAN_WIDTH [CHANNEL_COUNT] | Output | Yes | Channel with RDA completion (per channel) |

##### Shared AXI4 Master Interfaces

###### Descriptor Engine AXI4 Master Read Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **m_axi_desc_arid** | logic | AXI_ID_WIDTH | Output | Yes | Read address ID (lower bits = channel ID) |
| **m_axi_desc_araddr** | logic | ADDR_WIDTH | Output | Yes | Read address |
| **m_axi_desc_arlen** | logic | 8 | Output | Yes | Burst length |
| **m_axi_desc_arsize** | logic | 3 | Output | Yes | Burst size |
| **m_axi_desc_arburst** | logic | 2 | Output | Yes | Burst type |
| **m_axi_desc_arlock** | logic | 1 | Output | Yes | Lock type |
| **m_axi_desc_arcache** | logic | 4 | Output | Yes | Cache type |
| **m_axi_desc_arprot** | logic | 3 | Output | Yes | Protection type |
| **m_axi_desc_arqos** | logic | 4 | Output | Yes | QoS identifier |
| **m_axi_desc_arregion** | logic | 4 | Output | Yes | Region identifier |
| **m_axi_desc_arvalid** | logic | 1 | Output | Yes | Read address valid |
| **m_axi_desc_arready** | logic | 1 | Input | Yes | Read address ready |
| **m_axi_desc_rid** | logic | AXI_ID_WIDTH | Input | Yes | Read data ID (lower bits = channel ID) |
| **m_axi_desc_rdata** | logic | DATA_WIDTH | Input | Yes | Read data (512-bit) |
| **m_axi_desc_rresp** | logic | 2 | Input | Yes | Read response |
| **m_axi_desc_rlast** | logic | 1 | Input | Yes | Read last |
| **m_axi_desc_rvalid** | logic | 1 | Input | Yes | Read data valid |
| **m_axi_desc_rready** | logic | 1 | Output | Yes | Read data ready |

###### Control Read Engine AXI4 Master Read Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **m_axi_ctrlrd_arid** | logic | AXI_ID_WIDTH | Output | Yes | Read address ID (lower bits = channel ID) |
| **m_axi_ctrlrd_araddr** | logic | ADDR_WIDTH | Output | Yes | Read address |
| **m_axi_ctrlrd_arlen** | logic | 8 | Output | Yes | Burst length (always 0 - single transfer) |
| **m_axi_ctrlrd_arsize** | logic | 3 | Output | Yes | Burst size (always 3'b010 - 4 bytes) |
| **m_axi_ctrlrd_arburst** | logic | 2 | Output | Yes | Burst type (always 2'b01 - INCR) |
| **m_axi_ctrlrd_arlock** | logic | 1 | Output | Yes | Lock type (always 0) |
| **m_axi_ctrlrd_arcache** | logic | 4 | Output | Yes | Cache type (always 0) |
| **m_axi_ctrlrd_arprot** | logic | 3 | Output | Yes | Protection type (always 0) |
| **m_axi_ctrlrd_arqos** | logic | 4 | Output | Yes | QoS identifier (always 0) |
| **m_axi_ctrlrd_arregion** | logic | 4 | Output | Yes | Region identifier (always 0) |
| **m_axi_ctrlrd_arvalid** | logic | 1 | Output | Yes | Read address valid |
| **m_axi_ctrlrd_arready** | logic | 1 | Input | Yes | Read address ready |
| **m_axi_ctrlrd_rid** | logic | AXI_ID_WIDTH | Input | Yes | Read data ID (lower bits = channel ID) |
| **m_axi_ctrlrd_rdata** | logic | 32 | Input | Yes | Read data (32-bit) |
| **m_axi_ctrlrd_rresp** | logic | 2 | Input | Yes | Read response |
| **m_axi_ctrlrd_rlast** | logic | 1 | Input | Yes | Read last |
| **m_axi_ctrlrd_rvalid** | logic | 1 | Input | Yes | Read data valid |
| **m_axi_ctrlrd_rready** | logic | 1 | Output | Yes | Read data ready (always 1'b1) |

###### Control Write Engine AXI4 Master Write Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **m_axi_ctrlwr_awid** | logic | AXI_ID_WIDTH | Output | Yes | Write address ID (lower bits = channel ID) |
| **m_axi_ctrlwr_awaddr** | logic | ADDR_WIDTH | Output | Yes | Write address |
| **m_axi_ctrlwr_awlen** | logic | 8 | Output | Yes | Burst length (always 0 - single transfer) |
| **m_axi_ctrlwr_awsize** | logic | 3 | Output | Yes | Burst size (always 3'b010 - 4 bytes) |
| **m_axi_ctrlwr_awburst** | logic | 2 | Output | Yes | Burst type (always 2'b01 - INCR) |
| **m_axi_ctrlwr_awlock** | logic | 1 | Output | Yes | Lock type (always 0) |
| **m_axi_ctrlwr_awcache** | logic | 4 | Output | Yes | Cache type (always 0) |
| **m_axi_ctrlwr_awprot** | logic | 3 | Output | Yes | Protection type (always 0) |
| **m_axi_ctrlwr_awqos** | logic | 4 | Output | Yes | QoS identifier (always 0) |
| **m_axi_ctrlwr_awregion** | logic | 4 | Output | Yes | Region identifier (always 0) |
| **m_axi_ctrlwr_awvalid** | logic | 1 | Output | Yes | Write address valid |
| **m_axi_ctrlwr_awready** | logic | 1 | Input | Yes | Write address ready |
| **m_axi_ctrlwr_wdata** | logic | 32 | Output | Yes | Write data (32-bit) |
| **m_axi_ctrlwr_wstrb** | logic | 4 | Output | Yes | Write strobes (always 4'b1111) |
| **m_axi_ctrlwr_wlast** | logic | 1 | Output | Yes | Write last (always 1'b1) |
| **m_axi_ctrlwr_wvalid** | logic | 1 | Output | Yes | Write data valid |
| **m_axi_ctrlwr_wready** | logic | 1 | Input | Yes | Write data ready |
| **m_axi_ctrlwr_bid** | logic | AXI_ID_WIDTH | Input | Yes | Write response ID (lower bits = channel ID) |
| **m_axi_ctrlwr_bresp** | logic | 2 | Input | Yes | Write response |
| **m_axi_ctrlwr_bvalid** | logic | 1 | Input | Yes | Write response valid |
| **m_axi_ctrlwr_bready** | logic | 1 | Output | Yes | Write response ready (always 1'b1) |

##### AXI Monitor Configuration

**NOTE:** These configuration signals apply to all 3 AXI master monitors (descriptor, control read, control write).

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **cfg_axi_monitor_enable** | logic | 1 | Input | Yes | Enable AXI monitoring |
| **cfg_axi_error_enable** | logic | 1 | Input | Yes | Enable error packet generation |
| **cfg_axi_timeout_enable** | logic | 1 | Input | Yes | Enable timeout detection |
| **cfg_axi_perf_enable** | logic | 1 | Input | Yes | Enable performance monitoring |
| **cfg_axi_timeout_cycles** | logic | 16 | Input | Yes | Timeout threshold in cycles |
| **cfg_axi_latency_threshold** | logic | 32 | Input | Yes | Latency warning threshold |
| **cfg_axi_pkt_mask** | logic | 16 | Input | Yes | Packet type filter mask |
| **cfg_axi_err_select** | logic | 16 | Input | Yes | Error type selection |
| **cfg_axi_error_mask** | logic | 16 | Input | Yes | Error packet filter mask |
| **cfg_axi_timeout_mask** | logic | 16 | Input | Yes | Timeout packet filter mask |
| **cfg_axi_compl_mask** | logic | 16 | Input | Yes | Completion packet filter mask |
| **cfg_axi_thresh_mask** | logic | 16 | Input | Yes | Threshold packet filter mask |
| **cfg_axi_perf_mask** | logic | 16 | Input | Yes | Performance packet filter mask |
| **cfg_axi_addr_mask** | logic | 16 | Input | Yes | Address packet filter mask |
| **cfg_axi_debug_mask** | logic | 16 | Input | Yes | Debug packet filter mask |

##### Clock Gating Configuration

**NOTE:** These configuration signals apply to all 3 AXI master monitors.

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **cfg_cg_enable** | logic | 1 | Input | Yes | Enable clock gating |
| **cfg_cg_idle_threshold** | logic | 8 | Input | Yes | Idle cycles before clock gate |
| **cfg_cg_force_on** | logic | 1 | Input | Yes | Force clocks on (disable gating) |
| **cfg_cg_gate_monitor** | logic | 1 | Input | Yes | Allow monitor clock gating |
| **cfg_cg_gate_reporter** | logic | 1 | Input | Yes | Allow reporter clock gating |
| **cfg_cg_gate_timers** | logic | 1 | Input | Yes | Allow timer clock gating |

##### Aggregated Monitor Bus Output

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **mon_valid** | logic | 1 | Output | Yes | Aggregated monitor packet valid |
| **mon_ready** | logic | 1 | Input | Yes | Monitor ready to accept packet |
| **mon_packet** | logic | 64 | Output | Yes | Aggregated monitor packet data |

##### Array-Level Status and Debug

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **active_channels** | logic | 8 | Output | Yes | Number of active (non-idle) channels |
| **total_error_count** | logic | 16 | Output | Yes | Aggregated error count from all 3 AXI masters |
| **total_transaction_count** | logic | 32 | Output | Yes | Aggregated transaction count from all 3 AXI masters |

#### Architecture

##### Internal Components

The scheduler_group_array instantiates and connects the following components:

1. **Scheduler Group Instances** (CHANNEL_COUNT)
   - Each channel gets independent scheduler_group instance
   - Per-channel configuration, status, and interfaces
   - Channel ID parameter sets unique identifier

2. **AXI Arbitration Logic** (3 arbiters)
   - **Descriptor AR Arbiter**: Round-robin for descriptor read requests
   - **Control Read AR Arbiter**: Round-robin for control read requests
   - **Control Write AW Arbiter**: Round-robin for control write requests

3. **AXI Master Monitors with MonBus** (3 instances)
   - **Descriptor Read Monitor** (`axi4_master_rd_mon_cg`) - 512-bit data width, agent ID 0x0A
   - **Control Read Monitor** (`axi4_master_rd_mon_cg`) - 32-bit data width, agent ID 0x0C
   - **Control Write Monitor** (`axi4_master_wr_mon_cg`) - 32-bit data width, agent ID 0x0D

4. **MonBus Arbiter**
   - Aggregates monitor packets from CHANNEL_COUNT scheduler_groups + 3 AXI masters
   - Total sources: CHANNEL_COUNT + 3 (typically 35 sources for 32 channels)
   - Round-robin arbitration with configurable input/output skid buffers

##### AXI ID Encoding Strategy

**Critical Design Detail:** All three AXI masters use **consistent ID encoding** for response routing:

```
AXI ID Field Encoding:
+--------------------+----------------------+
| Upper Bits (0)     | Lower Bits (Ch ID)   |
| [AXI_ID_WIDTH-1:   | [CHAN_WIDTH-1:0]     |
|  CHAN_WIDTH]       |                      |
+--------------------+----------------------+
```

**Encoding Formula:**
```systemverilog
axi_id = {{(AXI_ID_WIDTH-CHAN_WIDTH){1'b0}}, channel_id};
```

**Example (AXI_ID_WIDTH=8, CHAN_WIDTH=5, Channel 3):**
```
channel_id = 5'b00011 (3)
axi_id = 8'b000_00011
         ^^^   ^^^^^
       zeros  channel ID
```

**Decoding Formula:**
```systemverilog
channel_id = axi_id[CHAN_WIDTH-1:0];
```

**Why This Encoding?**
- **Consistency**: Same encoding for all 3 AXI masters (desc, ctrlrd, ctrlwr)
- **Easy Debugging**: Channel ID visible in lower bits makes waveform debugging simple
- **Future Expansion**: Upper bits available for transaction tracking if needed
- **Simple Routing**: Direct bit extraction for demultiplexing

##### Arbitration and Routing Flow

###### Descriptor Engine (Read)

**AR Channel Flow:**
1. All channels assert `desc_ar_valid` when descriptor read needed
2. Round-robin arbiter selects one channel per cycle
3. Granted channel's signals multiplexed to internal AXI interface
4. **Channel ID encoded** in lower bits of `desc_axi_int_arid`
5. Monitor wrapper adds skid buffers and monitoring
6. Request forwarded to external `m_axi_desc_ar*` interface

**R Channel Flow:**
1. External `m_axi_desc_r*` response received
2. Monitor wrapper extracts performance/error data
3. **Channel ID extracted** from lower bits of `desc_axi_int_rid`
4. R response demultiplexed to correct channel based on ID
5. Only target channel receives `desc_r_valid` assertion

###### Control Read Engine (Read)

**AR Channel Flow:**
1. Channels assert `ctrlrd_valid` when control read needed
2. Round-robin arbiter selects one channel
3. Custom ctrlrd interface converted to AXI AR channel:
   - `ctrlrd_addr` -> `araddr`
   - Fixed `arlen=0` (single transfer)
   - Fixed `arsize=3'b010` (4 bytes, 32-bit)
   - **Channel ID encoded in lower bits** of `arid`

**R Channel Flow:**
1. AXI R response received
2. **Channel ID extracted from lower bits** of `rid`
3. R channel converted back to custom ctrlrd interface:
   - `rdata` -> `ctrlrd_result`
   - `rresp != OKAY` -> `ctrlrd_error`
4. Response routed to correct channel

###### Control Write Engine (Write)

**AW/W Channel Flow:**
1. Channels assert `ctrlwr_valid` when control write needed
2. Round-robin arbiter selects one channel
3. Custom ctrlwr interface converted to AXI AW/W channels:
   - `ctrlwr_addr` -> `awaddr`
   - `ctrlwr_data` -> `wdata`
   - Fixed `awlen=0`, `wlast=1` (single transfer)
   - Fixed `wstrb=4'b1111` (all bytes valid)
   - **Channel ID encoded in lower bits** of `awid`

**B Channel Flow:**
1. AXI B response received
2. **Channel ID extracted from lower bits** of `bid`
3. B channel converted to custom ctrlwr interface:
   - `bresp != OKAY` -> `ctrlwr_error`
4. Error routed to correct channel

##### MonBus Aggregation Architecture

```
MonBus Source Organization (35 total sources for 32 channels):

Source Index  | Component               | Agent ID     | Description
--------------+-------------------------+--------------+--------------------
0-31          | Scheduler Groups        | Variable*    | Per-channel monitor packets
32            | Desc AXI Master Monitor | 0x0A         | Descriptor read monitoring
33            | Ctrl Read AXI Monitor   | 0x0C         | Control read monitoring
34            | Ctrl Write AXI Monitor  | 0x0D         | Control write monitoring

* Each scheduler_group internally aggregates 3 sources:
  - Descriptor Engine (agent ID: DESC_MON_AGENT_BASE + ch)
  - Scheduler (agent ID: SCHED_MON_AGENT_BASE + ch)
  - Program Engine monitor (tied off - prog engine removed)
```

**MonBus Arbiter Configuration:**
- **Arbitration**: Round-robin across all sources
- **Input Skid Buffers**: Optional per-source buffering (default depth 2)
- **Output Skid Buffer**: Optional output buffering (default depth 4)
- **Fairness**: Each source gets equal arbitration opportunity

##### Channel Reset Coordination

Each scheduler_group supports independent channel reset via `cfg_channel_reset[ch]`:

```systemverilog
// Per-channel reset sequence
if (!scheduler_idle[ch] && cfg_channel_reset[ch]) begin
    // Wait for channel to complete current operations
    // descriptor_engine_idle, scheduler_idle, program_engine_idle all assert
    // Then reset applied
end
```

**Reset Completion Detection:**
```systemverilog
logic channel_fully_idle = descriptor_engine_idle[ch] &
                            program_engine_idle[ch] &  // Always 1'b1 (removed)
                            scheduler_idle[ch];
```

#### Parameter Configuration

##### Channel Configuration Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| **CHANNEL_COUNT** | int | 32 | Number of scheduler_group instances |
| **CHAN_WIDTH** | int | $clog2(CHANNEL_COUNT) | Channel ID width (auto-calculated) |

##### Data and Address Width Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| **ADDR_WIDTH** | int | 64 | AXI address width |
| **DATA_WIDTH** | int | 512 | Descriptor data width |
| **AXI_ID_WIDTH** | int | 8 | AXI ID field width |
| **CREDIT_WIDTH** | int | 8 | Credit counter width |

##### Timing Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| **TIMEOUT_CYCLES** | int | 1000 | Timeout threshold for operations |
| **EARLY_WARNING_THRESHOLD** | int | 4 | Early warning threshold for backpressure |

##### AXI Skid Buffer Depth Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| **AXI_SKID_DEPTH_AR** | int | 2 | AR channel skid buffer depth |
| **AXI_SKID_DEPTH_R** | int | 4 | R channel skid buffer depth |
| **AXI_SKID_DEPTH_AW** | int | 2 | AW channel skid buffer depth |
| **AXI_SKID_DEPTH_W** | int | 2 | W channel skid buffer depth |
| **AXI_SKID_DEPTH_B** | int | 2 | B channel skid buffer depth |

##### AXI Monitor Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| **AXI_MAX_TRANSACTIONS** | int | 16 | Maximum concurrent transactions per monitor |
| **AXI_ENABLE_FILTERING** | bit | 1 | Enable packet filtering |
| **AXI_ADD_PIPELINE_STAGE** | bit | 0 | Add pipeline stage in monitor |

##### AXI Clock Gating Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| **AXI_ENABLE_CLOCK_GATING** | bit | 1 | Enable clock gating in monitors |
| **AXI_CG_IDLE_CYCLES** | int | 8 | Idle cycles before clock gate |

##### MonBus Agent ID Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| **DESC_MON_AGENT_BASE** | int | 16 | Base agent ID for descriptor engines (0x10) |
| **PROG_MON_AGENT_BASE** | int | 32 | Base agent ID for program engines (0x20) - tied off |
| **SCHED_MON_AGENT_BASE** | int | 48 | Base agent ID for schedulers (0x30) |
| **AXI_RD_MON_AGENT_ID** | int | 10 | Agent ID for descriptor AXI read master (0x0A) |
| **AXI_WR_MON_AGENT_ID** | int | 11 | Agent ID for legacy prog write master (0x0B) - removed |
| **CTRLRD_MON_AGENT_ID** | int | 12 | Agent ID for control read master (0x0C) |
| **CTRLWR_MON_AGENT_ID** | int | 13 | Agent ID for control write master (0x0D) |
| **MON_UNIT_ID** | int | 1 | Unit ID for all monitors (0x1) |

##### MonBus Arbiter Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| **MONBUS_INPUT_SKID_ENABLE** | int | 1 | Enable input skid buffers |
| **MONBUS_OUTPUT_SKID_ENABLE** | int | 1 | Enable output skid buffer |
| **MONBUS_INPUT_SKID_DEPTH** | int | 2 | Input skid buffer depth |
| **MONBUS_OUTPUT_SKID_DEPTH** | int | 4 | Output skid buffer depth |

#### Usage Guidelines

##### Basic Instantiation

```systemverilog
scheduler_group_array #(
    .CHANNEL_COUNT          (32),
    .ADDR_WIDTH             (64),
    .DATA_WIDTH             (512),
    .AXI_ID_WIDTH           (8),
    .CREDIT_WIDTH           (8),
    .TIMEOUT_CYCLES         (1000),
    .EARLY_WARNING_THRESHOLD(4)
) u_scheduler_group_array (
    // Clock and Reset
    .clk                    (clk),
    .rst_n                  (rst_n),

    // Per-Channel APB Interfaces
    .apb_valid              (apb_valid),      // [31:0]
    .apb_ready              (apb_ready),      // [31:0]
    .apb_addr               (apb_addr),       // [63:0][31:0]

    // Per-Channel RDA Interfaces
    .rda_valid              (rda_valid),      // [31:0]
    .rda_ready              (rda_ready),      // [31:0]
    .rda_packet             (rda_packet),     // [511:0][31:0]
    .rda_channel            (rda_channel),    // [4:0][31:0]

    // Per-Channel Configuration
    .cfg_idle_mode          (cfg_idle_mode),        // [31:0]
    .cfg_channel_enable     (cfg_channel_enable),   // [31:0]
    .cfg_use_credit         (cfg_use_credit),       // [31:0]
    .cfg_initial_credit     (cfg_initial_credit),   // [3:0][31:0]
    // ... additional per-channel config ...

    // Shared Descriptor AXI Master
    .m_axi_desc_arid        (m_axi_desc_arid),
    .m_axi_desc_araddr      (m_axi_desc_araddr),
    .m_axi_desc_arvalid     (m_axi_desc_arvalid),
    .m_axi_desc_arready     (m_axi_desc_arready),
    .m_axi_desc_rid         (m_axi_desc_rid),
    .m_axi_desc_rdata       (m_axi_desc_rdata),
    .m_axi_desc_rvalid      (m_axi_desc_rvalid),
    .m_axi_desc_rready      (m_axi_desc_rready),
    // ... additional AXI descriptor signals ...

    // Shared Control Read AXI Master
    .m_axi_ctrlrd_arid      (m_axi_ctrlrd_arid),
    .m_axi_ctrlrd_araddr    (m_axi_ctrlrd_araddr),
    .m_axi_ctrlrd_arvalid   (m_axi_ctrlrd_arvalid),
    .m_axi_ctrlrd_arready   (m_axi_ctrlrd_arready),
    // ... additional AXI ctrlrd signals ...

    // Shared Control Write AXI Master
    .m_axi_ctrlwr_awid      (m_axi_ctrlwr_awid),
    .m_axi_ctrlwr_awaddr    (m_axi_ctrlwr_awaddr),
    .m_axi_ctrlwr_awvalid   (m_axi_ctrlwr_awvalid),
    .m_axi_ctrlwr_awready   (m_axi_ctrlwr_awready),
    // ... additional AXI ctrlwr signals ...

    // AXI Monitor Configuration
    .cfg_axi_monitor_enable (cfg_axi_monitor_enable),
    .cfg_axi_error_enable   (cfg_axi_error_enable),
    // ... additional monitor config ...

    // Aggregated MonBus Output
    .mon_valid              (mon_valid),
    .mon_ready              (mon_ready),
    .mon_packet             (mon_packet),

    // Array-Level Status
    .active_channels        (active_channels),
    .total_error_count      (total_error_count),
    .total_transaction_count(total_transaction_count)
);
```

##### Channel-Specific Configuration

```systemverilog
// Configure channel 0 for high-priority operation
always_comb begin
    cfg_channel_enable[0]   = 1'b1;
    cfg_use_credit[0]       = 1'b1;
    cfg_initial_credit[0]   = 4'd8;    // 256 credits (2^8, exponential encoding)
    cfg_prefetch_enable[0]  = 1'b1;
    cfg_fifo_threshold[0]   = 4'd4;
    cfg_ctrlrd_max_try[0]   = 8'd10;
end

// Configure channel 1 for normal operation
always_comb begin
    cfg_channel_enable[1]   = 1'b1;
    cfg_use_credit[1]       = 1'b1;
    cfg_initial_credit[1]   = 4'd4;    // 16 credits (2^4, exponential encoding)
    cfg_prefetch_enable[1]  = 1'b0;
    cfg_fifo_threshold[1]   = 4'd2;
    cfg_ctrlrd_max_try[1]   = 8'd5;
end

// Disable channel 2
always_comb begin
    cfg_channel_enable[2]   = 1'b0;
    cfg_use_credit[2]       = 1'b0;
    cfg_initial_credit[2]   = 4'd0;
end
```

##### Monitoring Active Channels

```systemverilog
// Detect when new channel becomes active
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        prev_active_channels <= 8'h0;
    end else begin
        prev_active_channels <= active_channels;

        if (active_channels > prev_active_channels) begin
            $display("Channel activated: %d channels now active", active_channels);
        end else if (active_channels < prev_active_channels) begin
            $display("Channel deactivated: %d channels now active", active_channels);
        end
    end
end
```

##### Debugging with AXI ID

```systemverilog
// Waveform analysis: Decode channel ID from AXI ID
logic [CHAN_WIDTH-1:0] desc_channel_id;
assign desc_channel_id = m_axi_desc_arid[CHAN_WIDTH-1:0];

// Assertion: Verify channel ID in valid range
property p_valid_channel_id;
    @(posedge clk) disable iff (!rst_n)
    m_axi_desc_arvalid |-> (desc_channel_id < CHANNEL_COUNT);
endproperty
assert_valid_channel_id: assert property (p_valid_channel_id);

// Coverage: Track which channels issue requests
covergroup cg_channel_usage @(posedge clk);
    cp_desc_channel: coverpoint desc_channel_id {
        bins channels[] = {[0:CHANNEL_COUNT-1]};
    }
endgroup
```

##### Performance Optimization

**Skid Buffer Tuning:**
```systemverilog
// For high-bandwidth descriptor reads, increase R channel buffer
scheduler_group_array #(
    .AXI_SKID_DEPTH_AR  (2),    // Standard AR buffer
    .AXI_SKID_DEPTH_R   (8),    // Deeper R buffer for burst reads
    ...
) u_scheduler_group_array (...);

// For bursty control operations, increase arbiter skid buffers
scheduler_group_array #(
    .MONBUS_INPUT_SKID_DEPTH    (4),   // Deeper per-source buffering
    .MONBUS_OUTPUT_SKID_DEPTH   (8),   // Deeper output buffering
    ...
) u_scheduler_group_array (...);
```

**Clock Gating Configuration:**
```systemverilog
// Aggressive clock gating for power optimization
always_comb begin
    cfg_cg_enable           = 1'b1;
    cfg_cg_idle_threshold   = 8'd4;     // Gate after 4 idle cycles
    cfg_cg_force_on         = 1'b0;
    cfg_cg_gate_monitor     = 1'b1;
    cfg_cg_gate_reporter    = 1'b1;
    cfg_cg_gate_timers      = 1'b1;
end
```

#### Design Notes

##### AXI ID Width Requirements

**Minimum AXI_ID_WIDTH:**
```
AXI_ID_WIDTH >= CHAN_WIDTH = $clog2(CHANNEL_COUNT)
```

**Examples:**
- 32 channels -> CHAN_WIDTH = 5 -> AXI_ID_WIDTH >= 5
- 64 channels -> CHAN_WIDTH = 6 -> AXI_ID_WIDTH >= 6
- 128 channels -> CHAN_WIDTH = 7 -> AXI_ID_WIDTH >= 7

**Recommended:** Set `AXI_ID_WIDTH = 8` for flexibility up to 256 channels.

##### Program Engine Removal

**Historical Note:** Previous versions included a 4th AXI master for program engine writes. This has been **removed** and replaced with control engines:

**Before (v1.0):**
- 4 AXI masters: desc_read, prog_write, ctrlrd_read, ctrlwr_write
- 36 MonBus sources (32 channels + 4 AXI masters)

**After (v2.0 - Current):**
- 3 AXI masters: desc_read, ctrlrd_read, ctrlwr_write
- 35 MonBus sources (32 channels + 3 AXI masters)
- Program engine replaced by ctrlrd_engine and ctrlwr_engine
- Legacy prog_* ports retained in scheduler_group but tied off

##### MonBus Packet Filtering

Configure packet filtering to avoid MonBus congestion:

```systemverilog
// Basic monitoring: Errors + timeouts only
cfg_axi_monitor_enable  = 1'b1;
cfg_axi_error_enable    = 1'b1;
cfg_axi_timeout_enable  = 1'b1;
cfg_axi_perf_enable     = 1'b0;    // Disable performance packets
cfg_axi_compl_mask      = 16'h0000; // Disable completion packets

// Full monitoring: All packet types
cfg_axi_monitor_enable  = 1'b1;
cfg_axi_error_enable    = 1'b1;
cfg_axi_timeout_enable  = 1'b1;
cfg_axi_perf_enable     = 1'b1;
cfg_axi_compl_mask      = 16'hFFFF; // Enable all completion packets
```

**Warning:** Enabling all packet types simultaneously can overwhelm MonBus bandwidth. Use selective filtering based on debug requirements.

#### Related Documentation

- **Scheduler Group**: See `01_00_scheduler_group.md` for individual channel architecture
- **Scheduler**: See `01_01_scheduler.md` for scheduler FSM details
- **Descriptor Engine**: See `01_02_descriptor_engine.md` for descriptor processing
- **Control Write Engine**: See `01_03_ctrlwr_engine.md` for control write operations
- **Control Read Engine**: See `01_04_ctrlrd_engine.md` for control read operations
- **AXI Monitors**: See `../../amba/CLAUDE.md` for AXI monitor architecture
- **MonBus Protocol**: See `04_monbus_axil_group.md` for MonBus specification
