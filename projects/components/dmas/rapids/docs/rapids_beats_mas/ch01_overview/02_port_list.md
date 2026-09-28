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

# Top-Level Port List

**Module:** `rapids_core_beats.sv`
**Location:** `projects/components/dmas/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---


## Parameters

Every parameter of `rapids_core_beats`, as declared. The short aliases at the end are
what the port widths below are written in (`NC`, `AW`, `DW`, `IW`, `SCW`, `CIW`, `SW`).

| Parameter | Type | Default | Notes |
|---|---|---|---|
| `NUM_CHANNELS` | int | `8` | - |
| `CHAN_WIDTH` | int | `$clog2(NUM_CHANNELS)` | - |
| `ADDR_WIDTH` | int | `64` | - |
| `DATA_WIDTH` | int | `512` | - |
| `AXI_ID_WIDTH` | int | `8` | - |
| `SRAM_DEPTH` | int | `512` | - |
| `SEG_COUNT_WIDTH` | int | `$clog2(SRAM_DEPTH) + 1` | - |
| `PIPELINE` | int | `0` | - |
| `AR_MAX_OUTSTANDING` | int | `8` | - |
| `AW_MAX_OUTSTANDING` | int | `8` | - |
| `W_PHASE_FIFO_DEPTH` | int | `64` | - |
| `B_PHASE_FIFO_DEPTH` | int | `16` | - |
| `AXIS_ID_WIDTH` | int | `8` | - |
| `AXIS_DEST_WIDTH` | int | `4` | - |
| `AXIS_USER_WIDTH` | int | `1` | - |
| `DESC_MON_BASE_AGENT_ID` | int | `16` | 0x10 - Descriptor Engines (16-23) |
| `SCHED_MON_BASE_AGENT_ID` | int | `48` | 0x30 - Schedulers (48-55) |
| `DESC_AXI_MON_AGENT_ID` | int | `8` | 0x08 - Descriptor AXI Master Monitor |
| `SNK_AXIS_MON_AGENT_ID` | int | `9` | 0x09 - Sink-ingress AXIS monitor (rapids TASK-015) |
| `SRC_AXIS_MON_AGENT_ID` | int | `10` | 0x0A - Source-egress AXIS monitor (rapids TASK-015) |
| `ACLK_MHZ` | int | `100` | clk in MHz: the AXIS monitors' microsecond tick |
| `MON_UNIT_ID` | int | `1` | 0x1 |
| `MON_MAX_TRANSACTIONS` | int | `16` | - |
| `USE_AXI_MONITORS` | int | `1` | - |
| `USE_ROW_COL_MAJOR_ADDRESSING` | int | `1` | - |
| `GEN_MON` | bit | `1'b1` | - |
| `NC` | int | `NUM_CHANNELS` | - |
| `AW` | int | `ADDR_WIDTH` | - |
| `DW` | int | `DATA_WIDTH` | - |
| `IW` | int | `AXI_ID_WIDTH` | - |
| `SD` | int | `SRAM_DEPTH` | - |
| `SCW` | int | `SEG_COUNT_WIDTH` | - |
| `CIW` | int | `(NC > 1) ? $clog2(NC) : 1` | - |
| `SW` | int | `DW / 8` | - |

: Table 1.2.1: Parameters (from `rapids_core_beats.sv`)

---

## Port List (324 ports)

The module is two independent halves. Ports both halves carry are prefixed
`src_` / `snk_`; the direction-unique ports (the source's AXI read master and
AXIS egress, the sink's AXI write master and AXIS ingress) carry no prefix.
Sections follow the declaration order in the RTL, so a reader can walk this
page and the module side by side. Widths use the parameter aliases.

### Clock and Reset (shared - single clock/reset for the whole wrapper)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | - |
| `rst_n` | input | 1 | - |

: Table 1.2.2: Clock and Reset (shared - single clock/reset for the whole wrapper)

## SOURCE HALF (u_src) - shared-infrastructure ports (src_ prefixed)

### APB Programming Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_apb_valid` | input | NC | - |
| `src_apb_ready` | output | NC | - |
| `src_apb_addr` | input | NC x AW | - |

: Table 1.2.3: APB Programming Interface

### Per-channel configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_cfg_channel_enable` | input | NC | - |
| `src_cfg_channel_reset` | input | NC | - |

: Table 1.2.4: Per-channel configuration

### Scheduler Configuration (global)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_cfg_sched_enable` | input | 1 | - |
| `src_cfg_sched_timeout_cycles` | input | 32 | - |
| `src_cfg_sched_timeout_limit` | input | 8 | - |
| `src_cfg_sched_timeout_enable` | input | 1 | - |
| `src_cfg_sched_err_enable` | input | 1 | - |
| `src_cfg_sched_compl_enable` | input | 1 | - |
| `src_cfg_sched_perf_enable` | input | 1 | - |

: Table 1.2.5: Scheduler Configuration (global)

### Descriptor Engine Configuration (global)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_cfg_desceng_enable` | input | 1 | - |
| `src_cfg_desceng_prefetch` | input | 1 | - |
| `src_cfg_desceng_fifo_thresh` | input | 4 | - |
| `src_cfg_desceng_addr0_base` | input | AW | - |
| `src_cfg_desceng_addr0_limit` | input | AW | - |
| `src_cfg_desceng_addr1_base` | input | AW | - |
| `src_cfg_desceng_addr1_limit` | input | AW | - |

: Table 1.2.6: Descriptor Engine Configuration (global)

### Control Engine Configuration (Phase 2, global)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_cfg_ctrlrd_max_try` | input | 9 | - |
| `src_tick_1us` | input | 1 | - |

: Table 1.2.7: Control Engine Configuration (Phase 2, global)

### Descriptor AXI Monitor Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_cfg_desc_mon_enable` | input | 1 | - |
| `src_cfg_desc_mon_err_enable` | input | 1 | - |
| `src_cfg_desc_mon_perf_enable` | input | 1 | - |
| `src_cfg_desc_mon_perf_run` | input | 1 | - |
| `src_cfg_desc_mon_timeout_enable` | input | 1 | - |
| `src_cfg_desc_mon_timeout_cycles` | input | 32 | - |
| `src_cfg_desc_mon_latency_thresh` | input | 32 | - |
| `src_cfg_desc_mon_pkt_mask` | input | 16 | - |
| `src_cfg_desc_mon_err_select` | input | 4 | - |
| `src_cfg_desc_mon_err_mask` | input | 8 | - |
| `src_cfg_desc_mon_timeout_mask` | input | 8 | - |
| `src_cfg_desc_mon_compl_mask` | input | 8 | - |
| `src_cfg_desc_mon_thresh_mask` | input | 8 | - |
| `src_cfg_desc_mon_perf_mask` | input | 8 | - |
| `src_cfg_desc_mon_addr_mask` | input | 8 | - |
| `src_cfg_desc_mon_debug_mask` | input | 8 | - |

: Table 1.2.8: Descriptor AXI Monitor Configuration

### AXIS data-path monitor-lite configuration (rapids TASK-015)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_cfg_axis_mon_enable` | input | 1 | - |
| `src_cfg_axis_mon_err_enable` | input | 1 | - |
| `src_cfg_axis_mon_compl_enable` | input | 1 | - |
| `src_cfg_axis_mon_perf_enable` | input | 1 | - |
| `src_cfg_axis_mon_timeout_enable` | input | 1 | - |
| `src_cfg_axis_mon_timeout_cycles` | input | 32 | - |
| `src_cfg_axis_mon_latency_thresh` | input | 32 | - |
| `src_cfg_axis_mon_pkt_mask` | input | 16 | - |

: Table 1.2.9: AXIS data-path monitor-lite configuration (rapids TASK-015)

### Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_system_idle` | output | 1 | - |
| `src_descriptor_engine_idle` | output | NC | - |
| `src_scheduler_idle` | output | NC | - |
| `src_scheduler_state` | output | NC x 7 | - |
| `src_sched_error` | output | NC | - |

: Table 1.2.10: Status

### Descriptor AXI Monitor Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_cfg_sts_desc_mon_busy` | output | 1 | - |
| `src_cfg_sts_desc_mon_active_txns` | output | 8 | - |
| `src_cfg_sts_desc_mon_error_count` | output | 16 | - |
| `src_cfg_sts_desc_mon_txn_count` | output | 32 | - |
| `src_cfg_sts_desc_mon_conflict_error` | output | 1 | - |

: Table 1.2.11: Descriptor AXI Monitor Status

### AXIS data-path monitor-lite status (rapids TASK-015)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_cfg_sts_axis_mon_busy` | output | 1 | - |
| `src_cfg_sts_axis_mon_packet_count` | output | 32 | - |
| `src_cfg_sts_axis_mon_error_count` | output | 16 | - |
| `src_cfg_sts_axis_mon_dropped_count` | output | 16 | - |

: Table 1.2.12: AXIS data-path monitor-lite status (rapids TASK-015)

### Descriptor AXI Monitor perf window (feeds SRC_.MON.DAXMON_PERF_*).

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_sts_desc_mon_win_active` | output | 1 | - |
| `src_sts_desc_mon_win_cycles` | output | 32 | - |
| `src_sts_desc_mon_prod_cycles` | output | 32 | - |
| `src_sts_desc_mon_bp_cycles` | output | 32 | - |
| `src_sts_desc_mon_starv_cycles` | output | 32 | - |
| `src_sts_desc_mon_idle_cycles` | output | 32 | - |
| `src_sts_desc_mon_beat_count` | output | 32 | - |
| `src_sts_desc_mon_byte_count` | output | 64 | - |
| `src_sts_desc_mon_burst_count` | output | 32 | - |

: Table 1.2.13: Descriptor AXI Monitor perf window (feeds SRC_.MON.DAXMON_PERF_*).

### Descriptor Fetch AXI Master

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_m_axi_desc_arvalid` | output | 1 | - |
| `src_m_axi_desc_arready` | input | 1 | - |
| `src_m_axi_desc_araddr` | output | AW | - |
| `src_m_axi_desc_arlen` | output | 8 | - |
| `src_m_axi_desc_arsize` | output | 3 | - |
| `src_m_axi_desc_arburst` | output | 2 | - |
| `src_m_axi_desc_arid` | output | IW | - |
| `src_m_axi_desc_arlock` | output | 1 | - |
| `src_m_axi_desc_arcache` | output | 4 | - |
| `src_m_axi_desc_arprot` | output | 3 | - |
| `src_m_axi_desc_arqos` | output | 4 | - |
| `src_m_axi_desc_arregion` | output | 4 | - |
| `src_m_axi_desc_rvalid` | input | 1 | - |
| `src_m_axi_desc_rready` | output | 1 | - |
| `src_m_axi_desc_rdata` | input | 256 | - |
| `src_m_axi_desc_rresp` | input | 2 | - |
| `src_m_axi_desc_rlast` | input | 1 | - |
| `src_m_axi_desc_rid` | input | IW | - |

: Table 1.2.14: Descriptor Fetch AXI Master

### Control Read AXI Master (32-bit) [Phase 2]

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_m_axi_ctrlrd_arvalid` | output | 1 | - |
| `src_m_axi_ctrlrd_arready` | input | 1 | - |
| `src_m_axi_ctrlrd_araddr` | output | AW | - |
| `src_m_axi_ctrlrd_arlen` | output | 8 | - |
| `src_m_axi_ctrlrd_arsize` | output | 3 | - |
| `src_m_axi_ctrlrd_arburst` | output | 2 | - |
| `src_m_axi_ctrlrd_arid` | output | IW | - |
| `src_m_axi_ctrlrd_arlock` | output | 1 | - |
| `src_m_axi_ctrlrd_arcache` | output | 4 | - |
| `src_m_axi_ctrlrd_arprot` | output | 3 | - |
| `src_m_axi_ctrlrd_arqos` | output | 4 | - |
| `src_m_axi_ctrlrd_arregion` | output | 4 | - |
| `src_m_axi_ctrlrd_rvalid` | input | 1 | - |
| `src_m_axi_ctrlrd_rready` | output | 1 | - |
| `src_m_axi_ctrlrd_rdata` | input | 32 | - |
| `src_m_axi_ctrlrd_rresp` | input | 2 | - |
| `src_m_axi_ctrlrd_rlast` | input | 1 | - |
| `src_m_axi_ctrlrd_rid` | input | IW | - |

: Table 1.2.15: Control Read AXI Master (32-bit) [Phase 2]

### Control Write AXI Master (32-bit) [Phase 2]

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_m_axi_ctrlwr_awvalid` | output | 1 | - |
| `src_m_axi_ctrlwr_awready` | input | 1 | - |
| `src_m_axi_ctrlwr_awaddr` | output | AW | - |
| `src_m_axi_ctrlwr_awlen` | output | 8 | - |
| `src_m_axi_ctrlwr_awsize` | output | 3 | - |
| `src_m_axi_ctrlwr_awburst` | output | 2 | - |
| `src_m_axi_ctrlwr_awid` | output | IW | - |
| `src_m_axi_ctrlwr_awlock` | output | 1 | - |
| `src_m_axi_ctrlwr_awcache` | output | 4 | - |
| `src_m_axi_ctrlwr_awprot` | output | 3 | - |
| `src_m_axi_ctrlwr_awqos` | output | 4 | - |
| `src_m_axi_ctrlwr_awregion` | output | 4 | - |
| `src_m_axi_ctrlwr_wvalid` | output | 1 | - |
| `src_m_axi_ctrlwr_wready` | input | 1 | - |
| `src_m_axi_ctrlwr_wdata` | output | 32 | - |
| `src_m_axi_ctrlwr_wstrb` | output | 4 | - |
| `src_m_axi_ctrlwr_wlast` | output | 1 | - |
| `src_m_axi_ctrlwr_bvalid` | input | 1 | - |
| `src_m_axi_ctrlwr_bready` | output | 1 | - |
| `src_m_axi_ctrlwr_bid` | input | IW | - |
| `src_m_axi_ctrlwr_bresp` | input | 2 | - |

: Table 1.2.16: Control Write AXI Master (32-bit) [Phase 2]

## SOURCE HALF (u_src) - direction-unique ports (no prefix)

### AXI Transfer Configuration (source-only)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_axi_rd_xfer_beats` | input | 8 | - |
| `cfg_drain_size` | input | 8 | source: beats drained per AXIS packet |

: Table 1.2.17: AXI Transfer Configuration (source-only)

### Source Path - AXIS Master Interface (SRAM -> Network); tid = channel id

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axis_tdata` | output | DW | - |
| `m_axis_tstrb` | output | SW | - |
| `m_axis_tlast` | output | 1 | - |
| `m_axis_tid` | output | AXIS_ID_WIDTH | - |
| `m_axis_tdest` | output | AXIS_DEST_WIDTH | - |
| `m_axis_tuser` | output | AXIS_USER_WIDTH | - |
| `m_axis_tvalid` | output | 1 | - |
| `m_axis_tready` | input | 1 | - |

: Table 1.2.18: Source Path - AXIS Master Interface (SRAM -> Network); tid = channel id

### AXI4 Master - Data Read (Memory -> Source SRAM)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_rd_arid` | output | IW | - |
| `m_axi_rd_araddr` | output | AW | - |
| `m_axi_rd_arlen` | output | 8 | - |
| `m_axi_rd_arsize` | output | 3 | - |
| `m_axi_rd_arburst` | output | 2 | - |
| `m_axi_rd_arvalid` | output | 1 | - |
| `m_axi_rd_arready` | input | 1 | - |
| `m_axi_rd_rid` | input | IW | - |
| `m_axi_rd_rdata` | input | DW | - |
| `m_axi_rd_rresp` | input | 2 | - |
| `m_axi_rd_rlast` | input | 1 | - |
| `m_axi_rd_rvalid` | input | 1 | - |
| `m_axi_rd_rready` | output | 1 | - |

: Table 1.2.19: AXI4 Master - Data Read (Memory -> Source SRAM)

## SINK HALF (u_snk) - shared-infrastructure ports (snk_ prefixed)

### APB Programming Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_apb_valid` | input | NC | - |
| `snk_apb_ready` | output | NC | - |
| `snk_apb_addr` | input | NC x AW | - |

: Table 1.2.20: APB Programming Interface

### Per-channel configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_cfg_channel_enable` | input | NC | - |
| `snk_cfg_channel_reset` | input | NC | - |

: Table 1.2.21: Per-channel configuration

### Scheduler Configuration (global)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_cfg_sched_enable` | input | 1 | - |
| `snk_cfg_sched_timeout_cycles` | input | 32 | - |
| `snk_cfg_sched_timeout_limit` | input | 8 | - |
| `snk_cfg_sched_timeout_enable` | input | 1 | - |
| `snk_cfg_sched_err_enable` | input | 1 | - |
| `snk_cfg_sched_compl_enable` | input | 1 | - |
| `snk_cfg_sched_perf_enable` | input | 1 | - |

: Table 1.2.22: Scheduler Configuration (global)

### Descriptor Engine Configuration (global)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_cfg_desceng_enable` | input | 1 | - |
| `snk_cfg_desceng_prefetch` | input | 1 | - |
| `snk_cfg_desceng_fifo_thresh` | input | 4 | - |
| `snk_cfg_desceng_addr0_base` | input | AW | - |
| `snk_cfg_desceng_addr0_limit` | input | AW | - |
| `snk_cfg_desceng_addr1_base` | input | AW | - |
| `snk_cfg_desceng_addr1_limit` | input | AW | - |

: Table 1.2.23: Descriptor Engine Configuration (global)

### Control Engine Configuration (Phase 2, global)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_cfg_ctrlrd_max_try` | input | 9 | - |
| `snk_tick_1us` | input | 1 | - |

: Table 1.2.24: Control Engine Configuration (Phase 2, global)

### Descriptor AXI Monitor Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_cfg_desc_mon_enable` | input | 1 | - |
| `snk_cfg_desc_mon_err_enable` | input | 1 | - |
| `snk_cfg_desc_mon_perf_enable` | input | 1 | - |
| `snk_cfg_desc_mon_perf_run` | input | 1 | - |
| `snk_cfg_desc_mon_timeout_enable` | input | 1 | - |
| `snk_cfg_desc_mon_timeout_cycles` | input | 32 | - |
| `snk_cfg_desc_mon_latency_thresh` | input | 32 | - |
| `snk_cfg_desc_mon_pkt_mask` | input | 16 | - |
| `snk_cfg_desc_mon_err_select` | input | 4 | - |
| `snk_cfg_desc_mon_err_mask` | input | 8 | - |
| `snk_cfg_desc_mon_timeout_mask` | input | 8 | - |
| `snk_cfg_desc_mon_compl_mask` | input | 8 | - |
| `snk_cfg_desc_mon_thresh_mask` | input | 8 | - |
| `snk_cfg_desc_mon_perf_mask` | input | 8 | - |
| `snk_cfg_desc_mon_addr_mask` | input | 8 | - |
| `snk_cfg_desc_mon_debug_mask` | input | 8 | - |

: Table 1.2.25: Descriptor AXI Monitor Configuration

### AXIS data-path monitor-lite configuration (rapids TASK-015)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_cfg_axis_mon_enable` | input | 1 | - |
| `snk_cfg_axis_mon_err_enable` | input | 1 | - |
| `snk_cfg_axis_mon_compl_enable` | input | 1 | - |
| `snk_cfg_axis_mon_perf_enable` | input | 1 | - |
| `snk_cfg_axis_mon_timeout_enable` | input | 1 | - |
| `snk_cfg_axis_mon_timeout_cycles` | input | 32 | - |
| `snk_cfg_axis_mon_latency_thresh` | input | 32 | - |
| `snk_cfg_axis_mon_pkt_mask` | input | 16 | - |

: Table 1.2.26: AXIS data-path monitor-lite configuration (rapids TASK-015)

### Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_system_idle` | output | 1 | - |
| `snk_descriptor_engine_idle` | output | NC | - |
| `snk_scheduler_idle` | output | NC | - |
| `snk_scheduler_state` | output | NC x 7 | - |
| `snk_sched_error` | output | NC | - |

: Table 1.2.27: Status

### Descriptor AXI Monitor Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_cfg_sts_desc_mon_busy` | output | 1 | - |
| `snk_cfg_sts_desc_mon_active_txns` | output | 8 | - |
| `snk_cfg_sts_desc_mon_error_count` | output | 16 | - |
| `snk_cfg_sts_desc_mon_txn_count` | output | 32 | - |
| `snk_cfg_sts_desc_mon_conflict_error` | output | 1 | - |

: Table 1.2.28: Descriptor AXI Monitor Status

### AXIS data-path monitor-lite status (rapids TASK-015)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_cfg_sts_axis_mon_busy` | output | 1 | - |
| `snk_cfg_sts_axis_mon_packet_count` | output | 32 | - |
| `snk_cfg_sts_axis_mon_error_count` | output | 16 | - |
| `snk_cfg_sts_axis_mon_dropped_count` | output | 16 | - |

: Table 1.2.29: AXIS data-path monitor-lite status (rapids TASK-015)

### Descriptor AXI Monitor perf window (feeds SNK_.MON.DAXMON_PERF_*).

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_sts_desc_mon_win_active` | output | 1 | - |
| `snk_sts_desc_mon_win_cycles` | output | 32 | - |
| `snk_sts_desc_mon_prod_cycles` | output | 32 | - |
| `snk_sts_desc_mon_bp_cycles` | output | 32 | - |
| `snk_sts_desc_mon_starv_cycles` | output | 32 | - |
| `snk_sts_desc_mon_idle_cycles` | output | 32 | - |
| `snk_sts_desc_mon_beat_count` | output | 32 | - |
| `snk_sts_desc_mon_byte_count` | output | 64 | - |
| `snk_sts_desc_mon_burst_count` | output | 32 | - |

: Table 1.2.30: Descriptor AXI Monitor perf window (feeds SNK_.MON.DAXMON_PERF_*).

### Descriptor Fetch AXI Master

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_m_axi_desc_arvalid` | output | 1 | - |
| `snk_m_axi_desc_arready` | input | 1 | - |
| `snk_m_axi_desc_araddr` | output | AW | - |
| `snk_m_axi_desc_arlen` | output | 8 | - |
| `snk_m_axi_desc_arsize` | output | 3 | - |
| `snk_m_axi_desc_arburst` | output | 2 | - |
| `snk_m_axi_desc_arid` | output | IW | - |
| `snk_m_axi_desc_arlock` | output | 1 | - |
| `snk_m_axi_desc_arcache` | output | 4 | - |
| `snk_m_axi_desc_arprot` | output | 3 | - |
| `snk_m_axi_desc_arqos` | output | 4 | - |
| `snk_m_axi_desc_arregion` | output | 4 | - |
| `snk_m_axi_desc_rvalid` | input | 1 | - |
| `snk_m_axi_desc_rready` | output | 1 | - |
| `snk_m_axi_desc_rdata` | input | 256 | - |
| `snk_m_axi_desc_rresp` | input | 2 | - |
| `snk_m_axi_desc_rlast` | input | 1 | - |
| `snk_m_axi_desc_rid` | input | IW | - |

: Table 1.2.31: Descriptor Fetch AXI Master

### Control Read AXI Master (32-bit) [Phase 2]

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_m_axi_ctrlrd_arvalid` | output | 1 | - |
| `snk_m_axi_ctrlrd_arready` | input | 1 | - |
| `snk_m_axi_ctrlrd_araddr` | output | AW | - |
| `snk_m_axi_ctrlrd_arlen` | output | 8 | - |
| `snk_m_axi_ctrlrd_arsize` | output | 3 | - |
| `snk_m_axi_ctrlrd_arburst` | output | 2 | - |
| `snk_m_axi_ctrlrd_arid` | output | IW | - |
| `snk_m_axi_ctrlrd_arlock` | output | 1 | - |
| `snk_m_axi_ctrlrd_arcache` | output | 4 | - |
| `snk_m_axi_ctrlrd_arprot` | output | 3 | - |
| `snk_m_axi_ctrlrd_arqos` | output | 4 | - |
| `snk_m_axi_ctrlrd_arregion` | output | 4 | - |
| `snk_m_axi_ctrlrd_rvalid` | input | 1 | - |
| `snk_m_axi_ctrlrd_rready` | output | 1 | - |
| `snk_m_axi_ctrlrd_rdata` | input | 32 | - |
| `snk_m_axi_ctrlrd_rresp` | input | 2 | - |
| `snk_m_axi_ctrlrd_rlast` | input | 1 | - |
| `snk_m_axi_ctrlrd_rid` | input | IW | - |

: Table 1.2.32: Control Read AXI Master (32-bit) [Phase 2]

### Control Write AXI Master (32-bit) [Phase 2]

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_m_axi_ctrlwr_awvalid` | output | 1 | - |
| `snk_m_axi_ctrlwr_awready` | input | 1 | - |
| `snk_m_axi_ctrlwr_awaddr` | output | AW | - |
| `snk_m_axi_ctrlwr_awlen` | output | 8 | - |
| `snk_m_axi_ctrlwr_awsize` | output | 3 | - |
| `snk_m_axi_ctrlwr_awburst` | output | 2 | - |
| `snk_m_axi_ctrlwr_awid` | output | IW | - |
| `snk_m_axi_ctrlwr_awlock` | output | 1 | - |
| `snk_m_axi_ctrlwr_awcache` | output | 4 | - |
| `snk_m_axi_ctrlwr_awprot` | output | 3 | - |
| `snk_m_axi_ctrlwr_awqos` | output | 4 | - |
| `snk_m_axi_ctrlwr_awregion` | output | 4 | - |
| `snk_m_axi_ctrlwr_wvalid` | output | 1 | - |
| `snk_m_axi_ctrlwr_wready` | input | 1 | - |
| `snk_m_axi_ctrlwr_wdata` | output | 32 | - |
| `snk_m_axi_ctrlwr_wstrb` | output | 4 | - |
| `snk_m_axi_ctrlwr_wlast` | output | 1 | - |
| `snk_m_axi_ctrlwr_bvalid` | input | 1 | - |
| `snk_m_axi_ctrlwr_bready` | output | 1 | - |
| `snk_m_axi_ctrlwr_bid` | input | IW | - |
| `snk_m_axi_ctrlwr_bresp` | input | 2 | - |

: Table 1.2.33: Control Write AXI Master (32-bit) [Phase 2]

## Monitor Bus (SINGLE aggregated stream for the whole core)

The two halves' monitor outputs are merged through a top-level monbus_arbiter, so the core exposes exactly one monitor stream.

### Monitor Bus

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `mon_valid` | output | 1 | - |
| `mon_ready` | input | 1 | - |
| `mon_packet` | output | `monitor_common_pkg::monitor_packet_t` | - |
| `mon_timestamp` | output | `monitor_common_pkg::monbus_timestamp_t` | - |

: Table 1.2.34: Monitor Bus

## SINK HALF (u_snk) - direction-unique ports (no prefix)

### AXI Transfer Configuration (sink-only)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_axi_wr_xfer_beats` | input | 8 | - |
| `cfg_alloc_size` | input | 8 | sink: SRAM alloc size per AXIS fill |

: Table 1.2.35: AXI Transfer Configuration (sink-only)

### Sink Path - AXIS Slave Interface (Network -> SRAM); tid = channel id

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `s_axis_tdata` | input | DW | - |
| `s_axis_tstrb` | input | SW | - |
| `s_axis_tlast` | input | 1 | - |
| `s_axis_tid` | input | AXIS_ID_WIDTH | - |
| `s_axis_tdest` | input | AXIS_DEST_WIDTH | - |
| `s_axis_tuser` | input | AXIS_USER_WIDTH | - |
| `s_axis_tvalid` | input | 1 | - |
| `s_axis_tready` | output | 1 | - |

: Table 1.2.36: Sink Path - AXIS Slave Interface (Network -> SRAM); tid = channel id

### AXI4 Master - Data Write (Sink SRAM -> Memory)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_wr_awid` | output | IW | - |
| `m_axi_wr_awaddr` | output | AW | - |
| `m_axi_wr_awlen` | output | 8 | - |
| `m_axi_wr_awsize` | output | 3 | - |
| `m_axi_wr_awburst` | output | 2 | - |
| `m_axi_wr_awlock` | output | 1 | - |
| `m_axi_wr_awcache` | output | 4 | - |
| `m_axi_wr_awprot` | output | 3 | - |
| `m_axi_wr_awqos` | output | 4 | - |
| `m_axi_wr_awregion` | output | 4 | - |
| `m_axi_wr_awvalid` | output | 1 | - |
| `m_axi_wr_awready` | input | 1 | - |
| `m_axi_wr_wdata` | output | DW | - |
| `m_axi_wr_wstrb` | output | (DW/8) | - |
| `m_axi_wr_wlast` | output | 1 | - |
| `m_axi_wr_wvalid` | output | 1 | - |
| `m_axi_wr_wready` | input | 1 | - |
| `m_axi_wr_bid` | input | IW | - |
| `m_axi_wr_bresp` | input | 2 | - |
| `m_axi_wr_bvalid` | input | 1 | - |
| `m_axi_wr_bready` | output | 1 | - |

: Table 1.2.37: AXI4 Master - Data Write (Sink SRAM -> Memory)

## Debug Interface (per half, src_dbg_ / snk_dbg_ prefixed)

### Source half debug

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_dbg_rd_all_complete` | output | NC | - |
| `src_dbg_r_beats_rcvd` | output | 32 | - |
| `src_dbg_sram_writes` | output | 32 | - |
| `src_dbg_arb_request` | output | NC | - |
| `src_dbg_src_sram_bridge_pending` | output | NC | - |
| `src_dbg_src_sram_bridge_out_valid` | output | NC | - |
| `src_dbg_axis_beats_sent` | output | 32 | - |
| `src_dbg_axis_packets_sent` | output | 32 | - |

: Table 1.2.38: Source half debug

### Sink half debug

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_dbg_snk_sram_bridge_pending` | output | NC | - |
| `snk_dbg_snk_sram_bridge_out_valid` | output | NC | - |
| `snk_dbg_axis_beats_received` | output | 32 | - |
| `snk_dbg_axis_packets_received` | output | 32 | - |

: Table 1.2.39: Sink half debug

### Active-channel sideband for per-channel bus instrumentation

(axi_bus_meter). The W bus carries no wid, so the write engine's channel index must travel out of band to reach the meter at the top.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_active_channel_id` | output | CIW | - |
| `snk_active_channel_valid` | output | 1 | - |

: Table 1.2.40: Active-channel sideband for per-channel bus instrumentation

---

**Verified:** every row above is a declared port of `rapids_core_beats` and every
declared port has a row (324 of 324), generated from the module declaration on
2026-09-27. Regenerate rather than hand-edit when the interface changes.
