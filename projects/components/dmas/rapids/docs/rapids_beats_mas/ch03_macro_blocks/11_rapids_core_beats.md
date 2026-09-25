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

# RAPIDS Core Beats Specification

**Module:** `rapids_core_beats.sv`
**Location:** `projects/components/dmas/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The RAPIDS Core Beats module is the top-level integration of the "beats" architecture, combining the scheduler group array with sink and source data paths.

### Key Features

- **Complete RAPIDS Core:** Scheduler array + sink path + source path
- **8-Channel Architecture:** Full multi-channel support
- **Unified MonBus:** Aggregated monitoring from all subsystems
- **Configurable Parameters:** Data width, address width, SRAM depths

### Block Diagram

### Figure 3.11.1: RAPIDS Core Beats Block Diagram

```
                         rapids_core_beats
    +---------------------------------------------------------------------+
    |                                                                     |
    |  +---------------------------------------------------------------+  |
    |  |            beats_scheduler_group_array                        |  |
    |  |  [8 channels x (scheduler + descriptor_engine)]               |  |
    |  +----------------------------+----------------------------------+  |
    |                               |                                     |
    |            +------------------+------------------+                   |
    |            |                                    |                   |
    |            v                                    v                   |
    |  +-----------------------+        +-----------------------+        |
    |  |   sink_data_path      |        |  source_data_path     |        |
    |  | (or sink_data_path_   |        | (or source_data_path_ |        |
    |  |      axis)            |        |      axis)            |        |
    |  |                       |        |                       |        |
    |  | - snk_sram_controller |        | - src_sram_controller |        |
    |  | - axi_write_engine    |        | - axi_read_engine     |        |
    |  +-----------+-----------+        +-----------+-----------+        |
    |              |                                |                     |
    |              v                                v                     |
    |       AXI Write Master               AXI Read Master               |
    |                                                                     |
    |  MonBus Aggregation:                                               |
    |  +---------------------------------------------------------------+  |
    |  |  Scheduler Array MonBus + Sink Path MonBus + Source Path      |  |
    |  +----------------------------+----------------------------------+  |
    |                               |                                     |
    +-------------------------------|-------------------------------------+
                                    v
                          Unified MonBus Output
```

---

## Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;
parameter int ADDR_WIDTH = 64;
parameter int DATA_WIDTH = 512;
parameter int DESC_DATA_WIDTH = 256;
parameter int AXI_ID_WIDTH = 8;
parameter int SRAM_DEPTH = 512;

// AXI Parameters
parameter int AR_MAX_OUTSTANDING = 8;
parameter int AW_MAX_OUTSTANDING = 8;
parameter int R_PHASE_FIFO_DEPTH = 64;
parameter int W_PHASE_FIFO_DEPTH = 64;
parameter int B_PHASE_FIFO_DEPTH = 16;

// MonBus Parameters
parameter int MON_UNIT_ID = 1;

// Feature Enables
parameter bit ENABLE_AXIS_WRAPPERS = 0;          // Use AXIS interfaces
```

: Table 3.11.1: RAPIDS Core Beats Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 3.11.2: Clock and Reset

### Per-Channel APB Programming

The source and sink halves each carry their own kick-off port; there is no
shared `apb_*` port.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_apb_valid` | input | NC | Source channel kick-off (per-channel) |
| `src_apb_ready` | output | NC | Source ready for kick-off |
| `src_apb_addr` | input | NC x AW | Source first descriptor address |
| `snk_apb_valid` | input | NC | Sink channel kick-off (per-channel) |
| `snk_apb_ready` | output | NC | Sink ready for kick-off |
| `snk_apb_addr` | input | NC x AW | Sink first descriptor address |

: Table 3.11.3: APB Programming Interface

### Per-Channel Configuration

Configuration is per half as well: every knob exists as `src_cfg_*` and
`snk_cfg_*` (76 configuration ports in total, the bulk of them the descriptor
monitor masks). The scheduler-facing ones are:

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_cfg_channel_enable` / `snk_cfg_channel_enable` | input | NC | Enable per channel |
| `src_cfg_channel_reset` / `snk_cfg_channel_reset` | input | NC | Soft reset per channel |
| `src_cfg_sched_enable` / `snk_cfg_sched_enable` | input | 1 | Enable the scheduler half |
| `src_cfg_sched_timeout_cycles` / `snk_cfg_sched_timeout_cycles` | input | 32 | Write-progress timeout window (cycles) |
| `src_cfg_sched_timeout_limit` / `snk_cfg_sched_timeout_limit` | input | 8 | Consecutive-timeout windows before fatal escalation (0 = never) |
| `src_cfg_sched_timeout_enable` / `snk_cfg_sched_timeout_enable` | input | 1 | Enable timeout detection |
| `cfg_axi_rd_xfer_beats` | input | 8 | Source read burst size (ARLEN encoding) |
| `cfg_axi_wr_xfer_beats` | input | 8 | Sink write burst size (ARLEN encoding) |
| `cfg_alloc_size` | input | 8 | Beats allocated per sink fill request |
| `cfg_drain_size` | input | 8 | Beats drained per source AXIS packet |

: Table 3.11.4: Per-Channel Configuration

`*_cfg_sched_timeout_limit` is passed straight through to the
`scheduler_group_array_beats` instance (recoverable-timeout escalation, see the
[Scheduler](../ch02_fub_blocks/01_scheduler.md) FUB). The write-side COMMIT
strobes (`sched_wr_commit_strobe` / `sched_wr_commit_beats`) generated by the
sink data path's `axi_write_engine_beats` are routed internally from the sink
data path up into the scheduler array so completion is gated on B responses.

### Descriptor AXI Master Interfaces

There are TWO descriptor masters, one per half, 18 ports each. Both are
read-only, 256-bit.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_m_axi_desc_arvalid` / `snk_m_axi_desc_arvalid` | output | 1 | AR channel valid |
| `src_m_axi_desc_arready` / `snk_m_axi_desc_arready` | input | 1 | AR channel ready |
| `src_m_axi_desc_araddr` / `snk_m_axi_desc_araddr` | output | AW | AR address |
| `src_m_axi_desc_arid` / `snk_m_axi_desc_arid` | output | IW | AR id |
| `src_m_axi_desc_arlen` / `snk_m_axi_desc_arlen` | output | 8 | Burst length |
| `src_m_axi_desc_arsize` / `snk_m_axi_desc_arsize` | output | 3 | Burst size |
| `src_m_axi_desc_arburst` / `snk_m_axi_desc_arburst` | output | 2 | Burst type |
| `src_m_axi_desc_rvalid` / `snk_m_axi_desc_rvalid` | input | 1 | R channel valid |
| `src_m_axi_desc_rready` / `snk_m_axi_desc_rready` | output | 1 | R channel ready |
| `src_m_axi_desc_rdata` / `snk_m_axi_desc_rdata` | input | 256 | R data (one descriptor) |
| `src_m_axi_desc_rresp` / `snk_m_axi_desc_rresp` | input | 2 | R response |
| `src_m_axi_desc_rlast` / `snk_m_axi_desc_rlast` | input | 1 | R last |
| `src_m_axi_desc_rid` / `snk_m_axi_desc_rid` | input | IW | R id |

: Table 3.11.5: Descriptor AXI Master Interfaces (src and snk)

The AR sideband (`arlock`, `arcache`, `arprot`, `arqos`, `arregion`) is present
on both masters and driven to AXI defaults.

### Sink AXI Write Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_wr_awvalid` | output | 1 | AW channel valid |
| `m_axi_wr_awready` | input | 1 | AW channel ready |
| `m_axi_wr_awaddr` | output | AW | Write address |
| `m_axi_wr_awid` | output | IW | Write id (carries the channel index) |
| `m_axi_wr_awlen` | output | 8 | Burst length |
| `m_axi_wr_awsize` | output | 3 | Burst size |
| `m_axi_wr_awburst` | output | 2 | Burst type |
| `m_axi_wr_wvalid` | output | 1 | W channel valid |
| `m_axi_wr_wready` | input | 1 | W channel ready |
| `m_axi_wr_wdata` | output | DW | Write data |
| `m_axi_wr_wstrb` | output | DW/8 | Write strobes |
| `m_axi_wr_wlast` | output | 1 | Last beat |
| `m_axi_wr_bvalid` | input | 1 | B channel valid |
| `m_axi_wr_bready` | output | 1 | B channel ready |
| `m_axi_wr_bid` | input | IW | B id (routes the commit to a channel) |
| `m_axi_wr_bresp` | input | 2 | Write response |

: Table 3.11.6: Sink AXI Write Master Interface

The AW sideband (`awlock`, `awcache`, `awprot`, `awqos`, `awregion`) is present
and driven to AXI defaults. 21 ports in total.

### Source AXI Read Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_rd_arvalid` | output | 1 | AR channel valid |
| `m_axi_rd_arready` | input | 1 | AR channel ready |
| `m_axi_rd_araddr` | output | AW | Read address |
| `m_axi_rd_arid` | output | IW | Read id (carries the channel index) |
| `m_axi_rd_arlen` | output | 8 | Burst length |
| `m_axi_rd_arsize` | output | 3 | Burst size |
| `m_axi_rd_arburst` | output | 2 | Burst type |
| `m_axi_rd_rvalid` | input | 1 | R channel valid |
| `m_axi_rd_rready` | output | 1 | R channel ready |
| `m_axi_rd_rdata` | input | DW | Read data |
| `m_axi_rd_rid` | input | IW | R id (routes the beat to a channel) |
| `m_axi_rd_rresp` | input | 2 | Read response |
| `m_axi_rd_rlast` | input | 1 | Last beat |

: Table 3.11.7: Source AXI Read Master Interface

### Sink Ingress -- AXIS Slave

The sink takes network traffic on a standard AXI-Stream slave port. There is no
`snk_fill_*` port at core level: the fill handshake is internal to
`snk_data_path_axis_beats`, which converts AXIS into it.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `s_axis_tvalid` | input | 1 | Beat valid |
| `s_axis_tready` | output | 1 | Ready for beat |
| `s_axis_tdata` | input | DW | Beat data |
| `s_axis_tstrb` | input | SW | Byte strobes |
| `s_axis_tlast` | input | 1 | Last beat of packet |
| `s_axis_tid` | input | AXIS_ID_WIDTH | Channel id (low CIW bits select the channel) |
| `s_axis_tdest` | input | AXIS_DEST_WIDTH | Destination |
| `s_axis_tuser` | input | AXIS_USER_WIDTH | User sideband |

: Table 3.11.8: Sink Ingress AXIS Slave

### Source Egress -- AXIS Master

Likewise there is no `src_drain_*` port at core level; the drain handshake is
internal to `src_data_path_axis_beats`.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axis_tvalid` | output | 1 | Beat valid |
| `m_axis_tready` | input | 1 | Downstream ready |
| `m_axis_tdata` | output | DW | Beat data |
| `m_axis_tstrb` | output | SW | Byte strobes |
| `m_axis_tlast` | output | 1 | Last beat of packet |
| `m_axis_tid` | output | AXIS_ID_WIDTH | Channel id |
| `m_axis_tdest` | output | AXIS_DEST_WIDTH | Destination |
| `m_axis_tuser` | output | AXIS_USER_WIDTH | User sideband |

: Table 3.11.9: Source Egress AXIS Master

### Unified MonBus Interface

One packet port, carrying a struct rather than a flat 64-bit bus.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `mon_valid` | output | 1 | Packet valid |
| `mon_ready` | input | 1 | Consumer ready |
| `mon_packet` | output | `monitor_common_pkg::monitor_packet_t` | Packet payload |
| `mon_timestamp` | output | `monitor_common_pkg::monbus_timestamp_t` | Packet timestamp |

: Table 3.11.10: Unified MonBus Interface

### Aggregate Status

Status is reported per half. There is no `all_channels_idle`, `sink_idle`,
`source_idle` or `error_flags` port.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_system_idle` | output | 1 | Source half idle (all source schedulers idle) |
| `snk_system_idle` | output | 1 | Sink half idle (all sink schedulers idle) |
| `src_scheduler_idle` / `snk_scheduler_idle` | output | NC | Per-channel scheduler idle |
| `src_scheduler_state` / `snk_scheduler_state` | output | NC x 7 | Per-channel FSM state |
| `src_descriptor_engine_idle` / `snk_descriptor_engine_idle` | output | NC | Per-channel descriptor engine idle |
| `src_sched_error` / `snk_sched_error` | output | NC | Per-channel sticky scheduler error |

: Table 3.11.11: Aggregate Status

---

## Data Flow

### Figure 3.11.2: RAPIDS Core Complete Data Flow

```
                    SOFTWARE
                        |
                        v
            +------------------------+
            |     APB Kick-Off       |
            | (per-channel address)  |
            +------------------------+
                        |
                        v
            +------------------------+
            |  Scheduler Group Array |
            |  - Descriptor fetch    |
            |  - Channel scheduling  |
            +------------------------+
                 /            \
                v              v
    +----------------+    +----------------+
    | Sink Path      |    | Source Path    |
    | (Network->Mem) |    | (Mem->Network) |
    +----------------+    +----------------+
          |                      |
          v                      v
    +----------------+    +----------------+
    | AXI Write      |    | AXI Read       |
    | Master         |    | Master         |
    +----------------+    +----------------+
          |                      |
          v                      v
    +----------------------------------------+
    |           SYSTEM MEMORY                |
    +----------------------------------------+
```

---

## MonBus Aggregation

The unified MonBus output aggregates sources from all subsystems:

| Source Range | Origin | Description |
|--------------|--------|-------------|
| 0-15 | Scheduler Array | Per-channel scheduler + desc engine |
| 16-23 | Sink Data Path | Sink SRAM controllers |
| 24-31 | Source Data Path | Source SRAM controllers |
| 32 | AXI Write Engine | Write completions |
| 33 | AXI Read Engine | Read completions |

: Table 3.11.12: MonBus Source Assignment

---

## Integration Example

```systemverilog
rapids_core_beats #(
    .NUM_CHANNELS(8),
    .ADDR_WIDTH(64),
    .DATA_WIDTH(512),
    .SRAM_DEPTH(512)
) u_rapids_core (
    .clk                        (clk),
    .rst_n                      (rst_n),

    // APB kick-off (per half)
    .src_apb_valid              (src_kick_valid),
    .src_apb_ready              (src_kick_ready),
    .src_apb_addr               (src_kick_addr),
    .snk_apb_valid              (snk_kick_valid),
    .snk_apb_ready              (snk_kick_ready),
    .snk_apb_addr               (snk_kick_addr),

    // Configuration (per half)
    .src_cfg_channel_enable     (src_cfg_ch_enable),
    .snk_cfg_channel_enable     (snk_cfg_ch_enable),
    .src_cfg_sched_timeout_cycles(src_cfg_timeout),
    .snk_cfg_sched_timeout_cycles(snk_cfg_timeout),
    .cfg_axi_rd_xfer_beats      (cfg_rd_beats),
    .cfg_axi_wr_xfer_beats      (cfg_wr_beats),
    .cfg_alloc_size             (cfg_alloc_size),
    .cfg_drain_size             (cfg_drain_size),

    // Descriptor AXI -- one master per half
    .src_m_axi_desc_arvalid     (src_desc_arvalid),
    .src_m_axi_desc_arready     (src_desc_arready),
    .src_m_axi_desc_araddr      (src_desc_araddr),
    .src_m_axi_desc_rvalid      (src_desc_rvalid),
    .src_m_axi_desc_rready      (src_desc_rready),
    .src_m_axi_desc_rdata       (src_desc_rdata),
    .snk_m_axi_desc_arvalid     (snk_desc_arvalid),
    .snk_m_axi_desc_arready     (snk_desc_arready),
    .snk_m_axi_desc_araddr      (snk_desc_araddr),
    .snk_m_axi_desc_rvalid      (snk_desc_rvalid),
    .snk_m_axi_desc_rready      (snk_desc_rready),
    .snk_m_axi_desc_rdata       (snk_desc_rdata),

    // Sink AXI write master (memory side)
    .m_axi_wr_awvalid           (wr_awvalid),
    .m_axi_wr_awready           (wr_awready),
    .m_axi_wr_awaddr            (wr_awaddr),
    .m_axi_wr_awlen             (wr_awlen),
    .m_axi_wr_wvalid            (wr_wvalid),
    .m_axi_wr_wready            (wr_wready),
    .m_axi_wr_wdata             (wr_wdata),
    .m_axi_wr_wlast             (wr_wlast),
    .m_axi_wr_bvalid            (wr_bvalid),
    .m_axi_wr_bready            (wr_bready),
    .m_axi_wr_bresp             (wr_bresp),

    // Source AXI read master (memory side)
    .m_axi_rd_arvalid           (rd_arvalid),
    .m_axi_rd_arready           (rd_arready),
    .m_axi_rd_araddr            (rd_araddr),
    .m_axi_rd_arlen             (rd_arlen),
    .m_axi_rd_rvalid            (rd_rvalid),
    .m_axi_rd_rready            (rd_rready),
    .m_axi_rd_rdata             (rd_rdata),
    .m_axi_rd_rlast             (rd_rlast),

    // Sink ingress -- AXIS slave (network in)
    .s_axis_tvalid              (network_rx_tvalid),
    .s_axis_tready              (network_rx_tready),
    .s_axis_tdata               (network_rx_tdata),
    .s_axis_tlast               (network_rx_tlast),
    .s_axis_tid                 (network_rx_tid),

    // Source egress -- AXIS master (network out)
    .m_axis_tvalid              (network_tx_tvalid),
    .m_axis_tready              (network_tx_tready),
    .m_axis_tdata               (network_tx_tdata),
    .m_axis_tlast               (network_tx_tlast),
    .m_axis_tid                 (network_tx_tid),

    // Unified MonBus
    .mon_valid                  (mon_valid),
    .mon_ready                  (mon_ready),
    .mon_packet                 (mon_packet),
    .mon_timestamp              (mon_timestamp),

    // Status (per half)
    .src_system_idle            (src_idle),
    .snk_system_idle            (snk_idle)
);
```

**Note:** `rapids_core_beats` is a core-level block. The register interface,
configuration mapping, and top-level integration (APB slave, descriptor
kick-off, AXI monitors, and the MonBus AXI-Lite group) are provided by the
`rapids_regs`, `rapids_config_block`, and `rapids_beats_top` modules -- see
[RAPIDS Registers](12_rapids_regs.md), [RAPIDS Config Block](13_rapids_config_block.md),
and [RAPIDS Beats Top](14_rapids_beats_top.md).

---

**Last Updated:** 2026-07-02
