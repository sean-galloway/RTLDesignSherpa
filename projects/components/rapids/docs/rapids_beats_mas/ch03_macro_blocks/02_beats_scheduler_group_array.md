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

# Beats Scheduler Group Array Specification

**Module:** `beats_scheduler_group_array.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Beats Scheduler Group Array instantiates 8 scheduler groups with a shared descriptor AXI master and unified MonBus output. It provides the complete scheduler infrastructure for all RAPIDS channels.

### Key Features

- **8-Channel Array:** One scheduler_group per channel
- **Shared Descriptor AXI:** Round-robin arbitration for descriptor fetches
- **Unified MonBus:** Aggregates 9 MonBus sources (8 scheduler + 1 arbiter)
- **Per-Channel Configuration:** Individual enable/reset per channel
- **Aggregate Status:** Combined idle and error flags

### Block Diagram

### Figure 3.2.1: Beats Scheduler Group Array Block Diagram

```
                    beats_scheduler_group_array
    +------------------------------------------------------------------+
    |                                                                  |
    |  +------------------+  +------------------+  +------------------+ |
    |  | scheduler_group  |  | scheduler_group  |  | scheduler_group  | |
    |  |      [0]         |  |      [1]         |  |      [7]         | |
    |  +--------+---------+  +--------+---------+  +--------+---------+ |
    |           |                     |                     |          |
    |           | AXI AR/R            | AXI AR/R            | AXI AR/R |
    |           v                     v                     v          |
    |  +----------------------------------------------------------+   |
    |  |              Round-Robin AXI AR/R Arbiter                |   |
    |  +----------------------------+-----------------------------+   |
    |                               |                                  |
    |                               v                                  |
    |                     Shared Descriptor AXI                        |
    |                                                                  |
    |  MonBus from each group:                                        |
    |           |                     |                     |          |
    |           v                     v                     v          |
    |  +----------------------------------------------------------+   |
    |  |            MonBus Round-Robin Arbiter (9 sources)        |   |
    |  +----------------------------+-----------------------------+   |
    |                               |                                  |
    +-------------------------------|----------------------------------+
                                    v
                          monbus_pkt_valid/data
```

**Source:** [03_beats_scheduler_group_array_block.mmd](../assets/mermaid/03_beats_scheduler_group_array_block.mmd)

---

## Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;                  // Number of channels
parameter int ADDR_WIDTH = 64;                   // Address bus width
parameter int DATA_WIDTH = 512;                  // Data bus width
parameter int DESC_DATA_WIDTH = 256;             // Descriptor width

// AXI ID Management
parameter int AXI_ID_WIDTH = 8;                  // ID field width
parameter int MAX_OUTSTANDING = 8;               // Outstanding descriptors

// Monitor Bus Parameters
parameter int MON_UNIT_ID = 1;                   // Unit ID for MonBus
```

: Table 3.2.1: Beats Scheduler Group Array Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 3.2.2: Clock and Reset

### Per-Channel APB Programming

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `apb_valid` | input | NC | Channel kick-off (per-channel) |
| `apb_ready` | output | NC | Ready for kick-off |
| `apb_addr` | input | NC*AW | First descriptor address |

: Table 3.2.3: APB Programming Interface

### Per-Channel Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_channel_enable` | input | NC | Enable per channel |
| `cfg_channel_reset` | input | NC | Soft reset per channel |
| `cfg_sched_timeout_cycles` | input | NC*16 | Timeout threshold |
| `cfg_sched_timeout_enable` | input | NC | Enable timeout |
| `cfg_desceng_enable` | input | NC | Enable descriptor engine |
| `cfg_desceng_prefetch` | input | NC | Enable prefetching |
| `cfg_desceng_fifo_thresh` | input | NC*4 | Prefetch threshold |
| `cfg_desceng_addr0_base` | input | NC*AW | Address range 0 base |
| `cfg_desceng_addr0_limit` | input | NC*AW | Address range 0 limit |

: Table 3.2.4: Per-Channel Configuration

### Shared Descriptor AXI Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arvalid` | output | 1 | AR channel valid |
| `m_axi_arready` | input | 1 | AR channel ready |
| `m_axi_araddr` | output | AW | AR address |
| `m_axi_arid` | output | ID_W | Transaction ID |
| `m_axi_arlen` | output | 8 | Burst length |
| `m_axi_arsize` | output | 3 | Burst size |
| `m_axi_arburst` | output | 2 | Burst type |
| `m_axi_rvalid` | input | 1 | R channel valid |
| `m_axi_rready` | output | 1 | R channel ready |
| `m_axi_rdata` | input | 256 | R data |
| `m_axi_rid` | input | ID_W | Response ID |
| `m_axi_rresp` | input | 2 | R response |
| `m_axi_rlast` | input | 1 | Last beat |

: Table 3.2.5: Shared Descriptor AXI Master Interface

### Per-Channel Scheduler Data Interfaces

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_valid` | output | NC | Read request per channel |
| `sched_rd_addr` | output | NC*AW | Read address |
| `sched_rd_beats` | output | NC*32 | Read beats |
| `sched_rd_done_strobe` | input | NC | Read complete |
| `sched_wr_valid` | output | NC | Write request per channel |
| `sched_wr_addr` | output | NC*AW | Write address |
| `sched_wr_beats` | output | NC*32 | Write beats |
| `sched_wr_done_strobe` | input | NC | Write complete |

: Table 3.2.6: Per-Channel Scheduler Data Interfaces

### Aggregate Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `all_channels_idle` | output | 1 | All channels idle |
| `scheduler_idle` | output | NC | Per-channel scheduler idle |
| `descriptor_engine_idle` | output | NC | Per-channel desc eng idle |
| `scheduler_state` | output | NC*7 | FSM states |
| `sched_error` | output | NC | Error flags |

: Table 3.2.7: Aggregate Status

### Unified MonBus Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `monbus_pkt_valid` | output | 1 | Packet valid |
| `monbus_pkt_ready` | input | 1 | Consumer ready |
| `monbus_pkt_data` | output | 64 | Packet data |

: Table 3.2.8: Unified MonBus Interface

---

## AXI Arbitration

### Figure 3.2.2: Descriptor AXI Arbitration Sequence

```
        Channel[0]    Channel[1]    Arbiter        AXI Master
            |             |            |               |
    AR REQ  |------------>|            |               |
            |             | AR REQ     |               |
            |             |----------->|               |
            |             |            | GRANT[0]      |
            |<-------------------------|               |
            |             |            |  AR VALID     |
            |             |            |-------------->|
            |             |            |  AR READY     |
            |             |            |<--------------|
            |             |            | GRANT[1]      |
            |             |<-----------|               |
            |             |            |  AR VALID     |
            |             |            |-------------->|
            |             |            |  R DATA       |
            |             |            |<--------------|
            |    R DATA   |            |               |
            |<-------------------------|               |
            |             |    R DATA  |               |
            |             |<-----------|               |
            |             |            |               |
```

**Source:** [03_scheduler_group_array_arbitration.mmd](../assets/mermaid/03_scheduler_group_array_arbitration.mmd)

---

## MonBus Aggregation

The unified MonBus output aggregates 9 sources using round-robin arbitration:

| Source ID | Origin | Description |
|-----------|--------|-------------|
| 0-7 | scheduler_group[0:7] | Per-channel aggregated MonBus |
| 8 | AXI Arbiter | Arbitration events |

: Table 3.2.9: MonBus Source Assignment

Each scheduler_group provides a single MonBus output that combines both scheduler and descriptor engine packets (2:1 internal arbitration).

---

## Integration Context

```systemverilog
beats_scheduler_group_array #(
    .NUM_CHANNELS(8),
    .ADDR_WIDTH(64),
    .DATA_WIDTH(512)
) u_scheduler_array (
    .clk                    (clk),
    .rst_n                  (rst_n),

    // APB programming (per-channel)
    .apb_valid              (apb_kick_valid),
    .apb_ready              (apb_kick_ready),
    .apb_addr               (apb_kick_addr),

    // Configuration (per-channel)
    .cfg_channel_enable     (cfg_ch_enable),
    .cfg_sched_timeout_cycles(cfg_timeout_cycles),
    // ... additional config ...

    // Shared descriptor AXI
    .m_axi_arvalid          (desc_axi_arvalid),
    .m_axi_arready          (desc_axi_arready),
    .m_axi_araddr           (desc_axi_araddr),
    .m_axi_rvalid           (desc_axi_rvalid),
    .m_axi_rready           (desc_axi_rready),
    .m_axi_rdata            (desc_axi_rdata),

    // Per-channel scheduler outputs
    .sched_rd_valid         (sched_rd_valid),
    .sched_rd_addr          (sched_rd_addr),
    .sched_rd_beats         (sched_rd_beats),
    .sched_rd_done_strobe   (sched_rd_done_strobe),
    .sched_wr_valid         (sched_wr_valid),
    .sched_wr_addr          (sched_wr_addr),
    .sched_wr_beats         (sched_wr_beats),
    .sched_wr_done_strobe   (sched_wr_done_strobe),

    // Status
    .all_channels_idle      (all_schedulers_idle),

    // Unified MonBus
    .monbus_pkt_valid       (sched_array_monbus_valid),
    .monbus_pkt_ready       (sched_array_monbus_ready),
    .monbus_pkt_data        (sched_array_monbus_data)
);
```

---

**Last Updated:** 2025-01-10
