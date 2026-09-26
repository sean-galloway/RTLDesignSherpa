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

**Module:** `scheduler_group_beats.sv`
**Location:** `projects/components/dmas/rapids/rtl/macro_beats/`
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
                       mon_valid/mon_packet
```

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
| `cfg_channel_enable` | input | 1 | Enable this channel |
| `cfg_channel_reset` | input | 1 | Per-channel soft reset |
| `cfg_sched_timeout_cycles` | input | 32 | Write-progress timeout window (cycles) |
| `cfg_sched_timeout_limit` | input | 8 | Consecutive-timeout windows before fatal escalation (0 = never) |
| `cfg_sched_timeout_enable` | input | 1 | Enable timeout detection |
| `cfg_sched_err_enable` | input | 1 | Enable error reporting |
| `cfg_sched_compl_enable` | input | 1 | Enable completion reporting |
| `cfg_sched_perf_enable` | input | 1 | Enable performance monitoring |
| `cfg_desceng_prefetch` | input | 1 | Enable descriptor prefetch chaining |
| `cfg_desceng_fifo_thresh` | input | 4 | Prefetch threshold (descriptors buffered ahead) |
| `cfg_desceng_addr0_base` | input | ADDR_WIDTH | Valid address range 0 base |
| `cfg_desceng_addr0_limit` | input | ADDR_WIDTH | Valid address range 0 limit |
| `cfg_desceng_addr1_base` | input | ADDR_WIDTH | Valid address range 1 base |
| `cfg_desceng_addr1_limit` | input | ADDR_WIDTH | Valid address range 1 limit |
| `cfg_ctrlrd_max_try` | input | 9 | ctrlrd poll retry budget (0-511) |
| `tick_1us` | input | 1 | 1 us tick for ctrlrd retry spacing |

: Table 3.1.4: Configuration Interface

### Descriptor AXI Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `desc_ar_valid` | output | 1 | AR valid |
| `desc_ar_ready` | input | 1 | AR ready |
| `desc_ar_addr` | output | ADDR_WIDTH | Descriptor fetch address |
| `desc_ar_len` | output | 8 | Burst length - 1 |
| `desc_ar_size` | output | 3 | Burst size (log2 bytes) |
| `desc_ar_burst` | output | 2 | Burst type |
| `desc_ar_id` | output | AXI_ID_WIDTH | Transaction ID |
| `desc_ar_lock` | output | 1 | Lock type |
| `desc_ar_cache` | output | 4 | Cache attributes |
| `desc_ar_prot` | output | 3 | Protection attributes |
| `desc_ar_qos` | output | 4 | Quality of service |
| `desc_ar_region` | output | 4 | Region identifier |
| `desc_r_valid` | input | 1 | R valid |
| `desc_r_ready` | output | 1 | R ready |
| `desc_r_data` | input | 256 | Descriptor payload (fixed 256-bit) |
| `desc_r_resp` | input | 2 | Read response |
| `desc_r_last` | input | 1 | Last beat |
| `desc_r_id` | input | AXI_ID_WIDTH | Response ID |

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
| `sched_wr_done_strobe` | input | 1 | Write AW-issue strobe |
| `sched_wr_commit_strobe` | input | 1 | Write COMMIT strobe (B response) |
| `sched_wr_commit_beats` | input | 32 | Beats committed this strobe |

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
| `i_mon_time` | input | monbus_timestamp_t | Shared monitor timebase |
| `mon_valid` | output | 1 | Monitor packet valid |
| `mon_ready` | input | 1 | Consumer ready |
| `mon_packet` | output | monitor_packet_t | Monitor packet |
| `mon_timestamp` | output | monbus_timestamp_t | Packet timestamp |

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

**Last Updated:** 2026-07-02
