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

### Scheduler Group

#### Overview

The Scheduler Group provides a complete integrated channel processing unit that combines the Scheduler, Descriptor Engine, and Monitor Bus Aggregator into a cohesive module. This wrapper simplifies system integration by providing a unified interface for complete channel processing functionality.

**NOTE:** The program engine has been **removed** from this module and replaced by separate `ctrlrd_engine` and `ctrlwr_engine` interfaces. These control engines are instantiated externally and connected through the `ctrlrd_*` and `ctrlwr_*` ports. For backwards compatibility, the legacy `prog_*` AXI ports are retained but tied off.

The wrapper implements coordinated reset handling across all components, enhanced data interface with alignment bus support using RAPIDS package types, and unified monitor bus aggregation for comprehensive system visibility.

![scheduler_group](../assets/mermaid/scheduler_group.png)

#### Key Features

- **Integrated Channel Processing**: Complete descriptor processing and scheduling functionality
- **Control Engine Interfaces**: Separate `ctrlrd` (control read) and `ctrlwr` (control write) interfaces for external control operations
- **Descriptor AXI Interface**: Single descriptor read interface (512-bit data width) for fetching descriptors
- **Legacy Compatibility**: Retained `prog_*` AXI ports (tied off) for backwards compatibility
- **Address Alignment Bus**: Pre-calculated alignment information using RAPIDS package types for optimal AXI performance
- **Channel Reset Coordination**: Graceful reset handling with completion signaling
- **Monitor Bus Aggregation**: Unified monitor output from descriptor engine, scheduler, and (tied-off) program engine
- **RAPIDS Package Types**: Uses standardized `alignment_info_t` and `transfer_phase_t` types for enhanced data interface

#### Interface Specification

##### Clock and Reset

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **clk** | logic | 1 | Input | Yes | System clock |
| **rst_n** | logic | 1 | Input | Yes | Active-low asynchronous reset |

##### APB Programming Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **apb_valid** | logic | 1 | Input | Yes | APB descriptor fetch request valid |
| **apb_ready** | logic | 1 | Output | Yes | APB descriptor fetch request ready |
| **apb_addr** | logic | ADDR_WIDTH | Input | Yes | APB descriptor address |

##### RDA Packet Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **rda_valid** | logic | 1 | Input | Yes | RDA packet valid |
| **rda_ready** | logic | 1 | Output | Yes | RDA packet ready |
| **rda_packet** | logic | DATA_WIDTH | Input | Yes | RDA packet data |
| **rda_channel** | logic | CHAN_WIDTH | Input | Yes | RDA target channel |

##### EOS Completion Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **eos_completion_valid** | logic | 1 | Input | Yes | EOS completion notification valid |
| **eos_completion_ready** | logic | 1 | Output | Yes | EOS completion notification ready |
| **eos_completion_channel** | logic | CHAN_WIDTH | Input | Yes | Channel with EOS completion |

##### Configuration Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **cfg_idle_mode** | logic | 1 | Input | Yes | Global idle mode control |
| **cfg_channel_wait** | logic | 1 | Input | Yes | Channel wait control |
| **cfg_channel_enable** | logic | 1 | Input | Yes | Channel enable control |
| **cfg_use_credit** | logic | 1 | Input | Yes | Credit mode enable |
| **cfg_initial_credit** | logic | 4 | Input | Yes | Initial credit values (exponential encoding: 0->1, 1->2, 2->4, ..., 14->16384, 15->infinity) |
| **credit_increment** | logic | 1 | Input | Yes | Credit increment request |
| **cfg_prefetch_enable** | logic | 1 | Input | Yes | Descriptor prefetch enable |
| **cfg_fifo_threshold** | logic | 4 | Input | Yes | Descriptor FIFO threshold |
| **cfg_addr0_base** | logic | ADDR_WIDTH | Input | Yes | Address range 0 base |
| **cfg_addr0_limit** | logic | ADDR_WIDTH | Input | Yes | Address range 0 limit |
| **cfg_addr1_base** | logic | ADDR_WIDTH | Input | Yes | Address range 1 base |
| **cfg_addr1_limit** | logic | ADDR_WIDTH | Input | Yes | Address range 1 limit |
| **cfg_channel_reset** | logic | 1 | Input | Yes | Dynamic channel reset request |
| **cfg_ctrlrd_max_try** | logic | 8 | Input | Yes | Control read max retry count |

##### Status Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **descriptor_engine_idle** | logic | 1 | Output | Yes | Descriptor engine idle status |
| **program_engine_idle** | logic | 1 | Output | Yes | Program engine idle status (tied to 1'b1 - removed) |
| **scheduler_idle** | logic | 1 | Output | Yes | Scheduler idle status |
| **descriptor_credit_counter** | logic | 32 | Output | Yes | Current credit counter value |
| **fsm_state** | logic | 8 | Output | Yes | Current scheduler FSM state |
| **scheduler_error** | logic | 1 | Output | Yes | Scheduler error flag |
| **backpressure_warning** | logic | 1 | Output | Yes | Backpressure warning flag |

##### Data Engine Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **data_valid** | logic | 1 | Output | Yes | Data transfer request active |
| **data_ready** | logic | 1 | Input | Yes | Data engine ready for transfer |
| **data_address** | logic | ADDR_WIDTH | Output | Yes | Current data address |
| **data_length** | logic | 32 | Output | Yes | Remaining data length |
| **data_type** | logic | 2 | Output | Yes | Packet type from descriptor |
| **data_eos** | logic | 1 | Output | Yes | End of Stream indicator |
| **data_transfer_length** | logic | 32 | Input | Yes | Actual transfer length completed |
| **data_error** | logic | 1 | Input | Yes | Data transfer error |
| **data_done_strobe** | logic | 1 | Input | Yes | Data transfer completed |

##### Address Alignment Bus Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **data_alignment_info** | alignment_info_t | struct | Output | Yes | Pre-calculated alignment information (RAPIDS package type) |
| **data_alignment_valid** | logic | 1 | Output | Yes | Alignment information valid |
| **data_alignment_ready** | logic | 1 | Input | Yes | Alignment information ready |
| **data_alignment_next** | logic | 1 | Input | Yes | Request next alignment calculation |
| **data_transfer_phase** | transfer_phase_t | enum | Output | Yes | Current transfer phase (RAPIDS package type) |
| **data_sequence_complete** | logic | 1 | Output | Yes | Transfer sequence complete |

##### Control Read Engine Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **ctrlrd_valid** | logic | 1 | Output | Yes | Control read request valid |
| **ctrlrd_ready** | logic | 1 | Input | Yes | Control read request ready |
| **ctrlrd_addr** | logic | ADDR_WIDTH | Output | Yes | Control read address |
| **ctrlrd_data** | logic | 32 | Output | Yes | Control read expected data |
| **ctrlrd_mask** | logic | 32 | Output | Yes | Control read data mask |
| **ctrlrd_error** | logic | 1 | Input | Yes | Control read error (mismatch or AXI error) |
| **ctrlrd_result** | logic | 32 | Input | Yes | Control read actual data result |

##### Control Write Engine Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **ctrlwr_valid** | logic | 1 | Output | Yes | Control write request valid |
| **ctrlwr_ready** | logic | 1 | Input | Yes | Control write request ready |
| **ctrlwr_addr** | logic | ADDR_WIDTH | Output | Yes | Control write address |
| **ctrlwr_data** | logic | 32 | Output | Yes | Control write data |
| **ctrlwr_error** | logic | 1 | Input | Yes | Control write error (AXI error) |

##### RDA Credit Return Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **rda_complete_valid** | logic | 1 | Output | Yes | RDA completion notification |
| **rda_complete_ready** | logic | 1 | Input | Yes | RDA completion ready |
| **rda_complete_channel** | logic | CHAN_WIDTH | Output | Yes | Channel with RDA completion |

##### Descriptor Engine AXI4 Master Read Interface

**NOTE:** This interface connects internally to the descriptor engine. External connectivity is provided by `scheduler_group_array` which arbitrates multiple channels.

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **desc_ar_valid** | logic | 1 | Output | Yes | Read address valid |
| **desc_ar_ready** | logic | 1 | Input | Yes | Read address ready |
| **desc_ar_addr** | logic | ADDR_WIDTH | Output | Yes | Read address |
| **desc_ar_len** | logic | 8 | Output | Yes | Burst length |
| **desc_ar_size** | logic | 3 | Output | Yes | Burst size |
| **desc_ar_burst** | logic | 2 | Output | Yes | Burst type |
| **desc_ar_id** | logic | AXI_ID_WIDTH | Output | Yes | Read ID (internal transaction tracking) |
| **desc_ar_lock** | logic | 1 | Output | Yes | Lock type |
| **desc_ar_cache** | logic | 4 | Output | Yes | Cache type |
| **desc_ar_prot** | logic | 3 | Output | Yes | Protection type |
| **desc_ar_qos** | logic | 4 | Output | Yes | QoS identifier |
| **desc_ar_region** | logic | 4 | Output | Yes | Region identifier |
| **desc_r_valid** | logic | 1 | Input | Yes | Read data valid |
| **desc_r_ready** | logic | 1 | Output | Yes | Read data ready |
| **desc_r_data** | logic | DATA_WIDTH | Input | Yes | Read data |
| **desc_r_resp** | logic | 2 | Input | Yes | Read response |
| **desc_r_last** | logic | 1 | Input | Yes | Read last |
| **desc_r_id** | logic | AXI_ID_WIDTH | Input | Yes | Read ID |

##### Program Engine AXI4 Master Write Interface (Legacy - Tied Off)

**NOTE:** The program engine has been **removed** from `scheduler_group`. These ports are retained for backwards compatibility but are **tied off** (all outputs driven to 0, ready signals driven to 1). Control operations are now handled through `ctrlrd_*` and `ctrlwr_*` interfaces.

| Signal Name | Type | Width | Direction | Status | Description |
|-------------|------|-------|-----------|--------|-------------|
| **prog_aw_valid** | logic | 1 | Output | Tied to 0 | Write address valid (inactive) |
| **prog_aw_ready** | logic | 1 | Input | Ignored | Write address ready |
| **prog_aw_addr** | logic | ADDR_WIDTH | Output | Tied to 0 | Write address |
| **prog_aw_len** | logic | 8 | Output | Tied to 0 | Burst length |
| **prog_aw_size** | logic | 3 | Output | Tied to 0 | Burst size |
| **prog_aw_burst** | logic | 2 | Output | Tied to 0 | Burst type |
| **prog_aw_id** | logic | AXI_ID_WIDTH | Output | Tied to 0 | Write ID |
| **prog_aw_lock** | logic | 1 | Output | Tied to 0 | Lock type |
| **prog_aw_cache** | logic | 4 | Output | Tied to 0 | Cache type |
| **prog_aw_prot** | logic | 3 | Output | Tied to 0 | Protection type |
| **prog_aw_qos** | logic | 4 | Output | Tied to 0 | QoS identifier |
| **prog_aw_region** | logic | 4 | Output | Tied to 0 | Region identifier |
| **prog_w_valid** | logic | 1 | Output | Tied to 0 | Write data valid (inactive) |
| **prog_w_ready** | logic | 1 | Input | Ignored | Write data ready |
| **prog_w_data** | logic | 32 | Output | Tied to 0 | Write data |
| **prog_w_strb** | logic | 4 | Output | Tied to 0 | Write strobes |
| **prog_w_last** | logic | 1 | Output | Tied to 0 | Write last |
| **prog_b_valid** | logic | 1 | Input | Ignored | Write response valid |
| **prog_b_ready** | logic | 1 | Output | Tied to 1 | Write response ready (always ready) |
| **prog_b_resp** | logic | 2 | Input | Ignored | Write response |
| **prog_b_id** | logic | AXI_ID_WIDTH | Input | Ignored | Write ID |

##### Monitor Bus Interface

| Signal Name | Type | Width | Direction | Required | Description |
|-------------|------|-------|-----------|----------|-------------|
| **mon_valid** | logic | 1 | Output | Yes | Monitor packet valid |
| **mon_ready** | logic | 1 | Input | Yes | Monitor ready to accept packet |
| **mon_packet** | logic | 64 | Output | Yes | Monitor packet data |

#### Architecture

##### Internal Components

- **Descriptor Engine**: Handles APB and RDA descriptor processing with AXI read operations
- **Scheduler**: Main FSM managing descriptor execution, credit management, and control engine sequencing
- **Monitor Bus Aggregator**: Round-robin aggregation of monitor events from descriptor engine and scheduler
- **Control Engine Interfaces**: Exposed `ctrlrd` and `ctrlwr` ports for external control read/write engines

**NOTE:** The program engine has been **removed** and replaced by external control engines:
- Control operations are now handled by external `ctrlrd_engine` and `ctrlwr_engine` modules
- These connect through simplified `ctrlrd_*` and `ctrlwr_*` interfaces (not full AXI)
- Legacy `prog_*` AXI ports retained but tied off for backwards compatibility

##### Address Alignment Processing

The scheduler includes a dedicated Address Alignment FSM that runs in parallel with the main scheduler during the `SCHED_DESCRIPTOR_ACTIVE` state. This FSM pre-calculates all alignment information and provides it to data engines via the alignment bus interface, eliminating alignment calculation overhead from the critical AXI timing paths.

##### Channel Reset Coordination

All components support coordinated channel reset through the `cfg_channel_reset` input. Each component handles reset gracefully:
- **Descriptor Engine**: Completes AXI read transactions in WAIT_READ state before reset
- **Scheduler**: Completes control operations (ctrlrd/ctrlwr) before reset

Reset completion is indicated through the idle status outputs (`descriptor_engine_idle`, `scheduler_idle`). The `program_engine_idle` output is tied to 1'b1 (always idle) since the program engine has been removed.

##### Control Operation Sequencing

The scheduler coordinates control read and write operations through the external control engines:
1. Descriptor processing completes
2. If ctrlrd needed: Issue control read request and wait for result
3. If ctrlwr needed: Issue control write request and wait for completion
4. Activate data path engines
5. Return to idle state

Control engines are instantiated externally (typically in `scheduler_group_array`) and arbitrated across multiple channels.

#### Network 2.0 Support

The scheduler group supports the Network 2.0 protocol specification for RDA packet processing, which uses chunk enables instead of the older start/len approach for indicating valid data chunks within each 512-bit packet.

#### Usage Guidelines

##### Channel Reset Sequence

```systemverilog
// Example channel reset coordination
logic all_engines_idle = descriptor_engine_idle & program_engine_idle & scheduler_idle;

// Assert reset when needed
if (reset_request && !cfg_channel_reset) begin
    cfg_channel_reset <= 1'b1;
end 
// Deassert reset when all engines are idle
else if (cfg_channel_reset && all_engines_idle) begin
    cfg_channel_reset <= 1'b0;
end
```

##### Performance Optimization

- Use separate AXI interconnect paths for descriptor read and program write
- Configure alignment bus ready signals appropriately for optimal throughput
- Monitor FSM states and idle signals for debugging and performance analysis
- Utilize pre-calculated alignment information for efficient AXI transfers

##### Monitor Bus Configuration

The wrapper provides unified monitor output with agent ID-based filtering:
- Descriptor Engine events: Use agent ID `DESC_MON_AGENT_ID`
- Program Engine events: Use agent ID `PROG_MON_AGENT_ID`
- Scheduler events: Use agent ID `SCHED_MON_AGENT_ID`
