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
**Location:** `projects/components/rapids/rtl/macro_beats/`
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

**Source:** [03_rapids_core_beats_block.mmd](../assets/mermaid/03_rapids_core_beats_block.mmd)

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

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `apb_valid` | input | NC | Channel kick-off (per-channel) |
| `apb_ready` | output | NC | Ready for kick-off |
| `apb_addr` | input | NC*AW | First descriptor address |

: Table 3.11.3: APB Programming Interface

### Per-Channel Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_channel_enable` | input | NC | Enable per channel |
| `cfg_channel_reset` | input | NC | Soft reset per channel |
| `cfg_sched_timeout_cycles` | input | NC*16 | Timeout threshold |
| `cfg_sched_timeout_enable` | input | NC | Enable timeout |
| `cfg_desceng_enable` | input | NC | Enable descriptor engine |
| `cfg_desceng_prefetch` | input | NC | Enable prefetching |

: Table 3.11.4: Per-Channel Configuration

### Descriptor AXI Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `desc_m_axi_arvalid` | output | 1 | AR channel valid |
| `desc_m_axi_arready` | input | 1 | AR channel ready |
| `desc_m_axi_araddr` | output | AW | AR address |
| `desc_m_axi_rvalid` | input | 1 | R channel valid |
| `desc_m_axi_rready` | output | 1 | R channel ready |
| `desc_m_axi_rdata` | input | 256 | R data |

: Table 3.11.5: Descriptor AXI Master Interface

### Sink AXI Write Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_m_axi_awvalid` | output | 1 | AW channel valid |
| `snk_m_axi_awready` | input | 1 | AW channel ready |
| `snk_m_axi_awaddr` | output | AW | Write address |
| `snk_m_axi_awlen` | output | 8 | Burst length |
| `snk_m_axi_wvalid` | output | 1 | W channel valid |
| `snk_m_axi_wready` | input | 1 | W channel ready |
| `snk_m_axi_wdata` | output | DW | Write data |
| `snk_m_axi_wlast` | output | 1 | Last beat |
| `snk_m_axi_bvalid` | input | 1 | B channel valid |
| `snk_m_axi_bready` | output | 1 | B channel ready |
| `snk_m_axi_bresp` | input | 2 | Write response |

: Table 3.11.6: Sink AXI Write Master Interface

### Source AXI Read Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_m_axi_arvalid` | output | 1 | AR channel valid |
| `src_m_axi_arready` | input | 1 | AR channel ready |
| `src_m_axi_araddr` | output | AW | Read address |
| `src_m_axi_arlen` | output | 8 | Burst length |
| `src_m_axi_rvalid` | input | 1 | R channel valid |
| `src_m_axi_rready` | output | 1 | R channel ready |
| `src_m_axi_rdata` | input | DW | Read data |
| `src_m_axi_rlast` | input | 1 | Last beat |

: Table 3.11.7: Source AXI Read Master Interface

### Sink Fill Interface (or AXIS Slave)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `snk_fill_valid` | input | 1 | Fill data valid |
| `snk_fill_ready` | output | 1 | Ready for fill |
| `snk_fill_data` | input | DW | Fill data |
| `snk_fill_id` | input | 3 | Channel ID |
| `snk_fill_last` | input | 1 | Last beat |

: Table 3.11.8: Sink Fill Interface

### Source Drain Interface (or AXIS Master)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `src_drain_valid` | output | 1 | Drain data valid |
| `src_drain_ready` | input | 1 | Ready for drain |
| `src_drain_data` | output | DW | Drain data |
| `src_drain_id` | output | 3 | Channel ID |
| `src_drain_last` | output | 1 | Last beat |

: Table 3.11.9: Source Drain Interface

### Unified MonBus Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `monbus_pkt_valid` | output | 1 | Packet valid |
| `monbus_pkt_ready` | input | 1 | Consumer ready |
| `monbus_pkt_data` | output | 64 | Packet data |

: Table 3.11.10: Unified MonBus Interface

### Aggregate Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `all_channels_idle` | output | 1 | All channels idle |
| `scheduler_idle` | output | NC | Per-channel scheduler idle |
| `sink_idle` | output | 1 | Sink path idle |
| `source_idle` | output | 1 | Source path idle |
| `error_flags` | output | 32 | Combined error flags |

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
    .SRAM_DEPTH(512),
    .ENABLE_AXIS_WRAPPERS(0)
) u_rapids_core (
    .clk                    (clk),
    .rst_n                  (rst_n),

    // APB kick-off
    .apb_valid              (apb_kick_valid),
    .apb_ready              (apb_kick_ready),
    .apb_addr               (apb_kick_addr),

    // Configuration
    .cfg_channel_enable     (cfg_ch_enable),
    .cfg_sched_timeout_cycles(cfg_timeout),

    // Descriptor AXI
    .desc_m_axi_arvalid     (desc_arvalid),
    .desc_m_axi_arready     (desc_arready),
    .desc_m_axi_araddr      (desc_araddr),
    .desc_m_axi_rvalid      (desc_rvalid),
    .desc_m_axi_rready      (desc_rready),
    .desc_m_axi_rdata       (desc_rdata),

    // Sink AXI write
    .snk_m_axi_awvalid      (snk_awvalid),
    .snk_m_axi_awready      (snk_awready),
    .snk_m_axi_awaddr       (snk_awaddr),
    .snk_m_axi_wvalid       (snk_wvalid),
    .snk_m_axi_wready       (snk_wready),
    .snk_m_axi_wdata        (snk_wdata),
    .snk_m_axi_bvalid       (snk_bvalid),
    .snk_m_axi_bready       (snk_bready),

    // Source AXI read
    .src_m_axi_arvalid      (src_arvalid),
    .src_m_axi_arready      (src_arready),
    .src_m_axi_araddr       (src_araddr),
    .src_m_axi_rvalid       (src_rvalid),
    .src_m_axi_rready       (src_rready),
    .src_m_axi_rdata        (src_rdata),

    // Sink fill interface
    .snk_fill_valid         (network_rx_valid),
    .snk_fill_ready         (network_rx_ready),
    .snk_fill_data          (network_rx_data),
    .snk_fill_id            (network_rx_id),

    // Source drain interface
    .src_drain_valid        (network_tx_valid),
    .src_drain_ready        (network_tx_ready),
    .src_drain_data         (network_tx_data),
    .src_drain_id           (network_tx_id),

    // MonBus
    .monbus_pkt_valid       (mon_valid),
    .monbus_pkt_ready       (mon_ready),
    .monbus_pkt_data        (mon_data),

    // Status
    .all_channels_idle      (rapids_idle)
);
```

---

**Last Updated:** 2025-01-10
