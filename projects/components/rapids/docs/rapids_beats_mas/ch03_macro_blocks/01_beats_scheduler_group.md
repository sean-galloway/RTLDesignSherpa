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

# Beats Scheduler Group Specification

**Module:** `beats_scheduler_group.sv`
**Location:** `projects/components/rapids/rtl/macro_beats/`
**Status:** Implemented
**Last Updated:** 2025-01-10

---

## Overview

The Beats Scheduler Group wraps a single channel's scheduler and descriptor engine together with MonBus aggregation. It provides a clean integration point for the scheduler_group_array.

### Key Features

- **Single Channel Integration:** One scheduler + one descriptor engine
- **MonBus Aggregation:** Combines scheduler and descriptor engine MonBus outputs
- **Configuration Pass-Through:** Routes configuration to both sub-modules
- **Status Aggregation:** Combined idle and error status

### Block Diagram

### Figure 3.1.1: Beats Scheduler Group Block Diagram

```
                    beats_scheduler_group
    +-------------------------------------------------------+
    |                                                       |
    |  +-------------------+    +-------------------+       |
    |  | descriptor_engine |    |     scheduler     |       |
    |  |                   |--->|                   |       |
    |  | - AXI AR/R        |    | - FSM             |       |
    |  | - Prefetch FIFO   |desc| - Beat tracking   |       |
    |  | - Address check   |--->| - Error handling  |       |
    |  +--------+----------+    +---------+---------+       |
    |           |                         |                 |
    |           | monbus                  | monbus          |
    |           v                         v                 |
    |  +-----------------------------------------------+    |
    |  |           MonBus Arbiter (2:1)                |    |
    |  +----------------------+------------------------+    |
    |                         |                             |
    +-------------------------|-----------------------------+
                              v
                       monbus_pkt_valid/data
```

**Source:** [03_beats_scheduler_group_block.mmd](../assets/mermaid/03_beats_scheduler_group_block.mmd)

---

## Parameters

```systemverilog
parameter int CHANNEL_ID = 0;                    // Channel identifier
parameter int NUM_CHANNELS = 8;                  // Total channels
parameter int ADDR_WIDTH = 64;                   // Address bus width
parameter int DATA_WIDTH = 512;                  // Data bus width

// Monitor Bus Parameters
parameter int DESC_MON_AGENT_ID = 16 + CHANNEL_ID;  // Descriptor engine agent
parameter int SCHED_MON_AGENT_ID = 48 + CHANNEL_ID; // Scheduler agent
parameter int MON_UNIT_ID = 1;
```

: Table 3.1.1: Beats Scheduler Group Parameters

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low reset |

: Table 3.1.2: Clock and Reset

### APB Programming Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `apb_valid` | input | 1 | Channel kick-off |
| `apb_ready` | output | 1 | Ready for kick-off |
| `apb_addr` | input | AW | First descriptor address |

: Table 3.1.3: APB Programming Interface

### Configuration Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_channel_enable` | input | 1 | Enable channel |
| `cfg_channel_reset` | input | 1 | Soft reset |
| `cfg_sched_timeout_cycles` | input | 16 | Timeout threshold |
| `cfg_sched_timeout_enable` | input | 1 | Enable timeout |
| `cfg_desceng_enable` | input | 1 | Enable descriptor engine |
| `cfg_desceng_prefetch` | input | 1 | Enable prefetching |
| `cfg_desceng_fifo_thresh` | input | 4 | Prefetch threshold |
| `cfg_desceng_addr0_base` | input | AW | Address range 0 base |
| `cfg_desceng_addr0_limit` | input | AW | Address range 0 limit |

: Table 3.1.4: Configuration Interface

### Descriptor AXI Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arvalid` | output | 1 | AR channel valid |
| `m_axi_arready` | input | 1 | AR channel ready |
| `m_axi_araddr` | output | AW | AR address |
| `m_axi_rvalid` | input | 1 | R channel valid |
| `m_axi_rready` | output | 1 | R channel ready |
| `m_axi_rdata` | input | 256 | R data (descriptor) |
| `m_axi_rresp` | input | 2 | R response |

: Table 3.1.5: Descriptor AXI Master Interface

### Scheduler Data Interfaces

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_valid` | output | 1 | Read request |
| `sched_rd_addr` | output | AW | Read address |
| `sched_rd_beats` | output | 32 | Read beats |
| `sched_rd_done_strobe` | input | 1 | Read complete |
| `sched_wr_valid` | output | 1 | Write request |
| `sched_wr_addr` | output | AW | Write address |
| `sched_wr_beats` | output | 32 | Write beats |
| `sched_wr_done_strobe` | input | 1 | Write complete |

: Table 3.1.6: Scheduler Data Interfaces

### Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `scheduler_idle` | output | 1 | Scheduler idle |
| `descriptor_engine_idle` | output | 1 | Descriptor engine idle |
| `scheduler_state` | output | 7 | FSM state |
| `sched_error` | output | 1 | Error flag |

: Table 3.1.7: Status Interface

### MonBus Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `monbus_pkt_valid` | output | 1 | Packet valid |
| `monbus_pkt_ready` | input | 1 | Consumer ready |
| `monbus_pkt_data` | output | 64 | Packet data |

: Table 3.1.8: MonBus Interface

---

## Internal Architecture

```
Internal Signal Flow:

apb_valid/addr -----> descriptor_engine -----> scheduler
                             |                     |
                      desc_valid/packet           |
                             |                     |
                             +--> descriptor_ready <--+

MonBus Aggregation:

desc_engine.monbus_pkt ----+
                           |---> round_robin_arbiter ---> monbus_out
scheduler.monbus_pkt   ----+
```

---

**Last Updated:** 2025-01-10
