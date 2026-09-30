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

# Scheduler Group

**Module:** `scheduler_group.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/macro/`
**Status:** Implemented
**Last Updated:** 2026-09-30

---

## Overview

The scheduler group wraps one channel: a descriptor engine, the scheduler, the two control engines (control read and control write) and a MonBus arbiter that merges their monitor packets. It is the unit the scheduler group array instantiates once per channel.

The structure is identical to the RAPIDS Beats group. The one change is the packet-record port set: the scheduler now publishes a per-direction record of the packet's byte length and start offset, and the group passes it through unchanged.

### Key Features

- **One channel, four engines:** descriptor engine, scheduler, control read engine, control write engine.
- **Packet-record pass-through:** `sched_rd_pkt_*` and `sched_wr_pkt_*` connect the scheduler straight to the group boundary.
- **MonBus aggregation:** a four-client arbiter merges the four engines' packets.
- **Completion gating:** `cfg_sched_compl_enable` drops CORE Completion packets from the descriptor engine and the scheduler at the arbiter input and acknowledges the emitters, so nothing stalls (rapids ISSUE-005). Errors are never gated.
- **Status aggregation:** idle, FSM state and sticky error are exported.

### Block Diagram

### Figure 3.1.1: Scheduler Group Block Diagram

```
                              scheduler_group
  +---------------------------------------------------------------------+
  |                                                                     |
  |  +-------------------+ descriptor  +------------------+  ctrlrd  +-------------+
  |  | descriptor_engine |------------>|    scheduler     |<-------->| ctrlrd_eng  |
  |  | AXI AR/R fetch    |             | FSM, beat math   |  ctrlwr  +-------------+
  |  +---------+---------+             | packet records   |<-------->| ctrlwr_eng  |
  |            |                       +---+-----+-----+--+          +-------------+
  |            | mon                       |     |     |
  |            v                           |     |     +--> sched_rd_* / sched_wr_*
  |  +---------------------------+         |     |          sched_*_pkt_*  (byte length, offset)
  |  | completion gate, 4:1 MonBus arbiter |<--- mon ---+
  |  +--------------+------------+         |
  +-----------------|--------------------------------------------------------+
                    v
             mon_valid / mon_packet
```

---

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CHANNEL_ID` | 0 | Channel identifier. |
| `NUM_CHANNELS` | 8 | Total channels. |
| `CHAN_WIDTH` | `$clog2(NUM_CHANNELS)` | Channel id width. |
| `ADDR_WIDTH` | 64 | Address width. |
| `DATA_WIDTH` | 512 | Data width in bits. Sets the beat size seen by the scheduler. |
| `AXI_ID_WIDTH` | 8 | AXI ID width for the descriptor and control masters. |
| `DESC_MON_AGENT_ID` | 16 | MonBus agent id of the descriptor engine. |
| `SCHED_MON_AGENT_ID` | 48 | MonBus agent id of the scheduler. |
| `CTRLRD_MON_AGENT_ID` | 32 | MonBus agent id of the control read engine. |
| `CTRLWR_MON_AGENT_ID` | 33 | MonBus agent id of the control write engine. |
| `MON_UNIT_ID` | 1 | MonBus unit id. |
| `MON_CHANNEL_ID` | 0 | Base MonBus channel id. |
| `EN_READ` | 1 | Enable the read direction of the scheduler. |
| `EN_WRITE` | 1 | Enable the write direction of the scheduler. |
| `USE_ROW_COL_MAJOR_ADDRESSING` | 1 | Descriptor engine addressing mode. |
| `GEN_MON` | 1 | Enable monitor packet generation. |
| `OFF_W` | `$clog2(DATA_WIDTH/8)` | Width of the packet-record byte offset. New in RAPIDS. |

: Table 3.1.1: Scheduler Group Parameters

---

## Port List

### Clock, Reset and Kick-Off

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock. |
| `rst_n` | input | 1 | Active-low reset. |
| `apb_valid` | input | 1 | Channel kick-off. |
| `apb_ready` | output | 1 | Descriptor engine ready for kick-off. |
| `apb_addr` | input | AW | First descriptor address. |

: Table 3.1.2: Clock, Reset and Kick-Off

### Configuration Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_channel_enable` | input | 1 | Enable this channel. |
| `cfg_channel_reset` | input | 1 | Per-channel soft reset. |
| `cfg_sched_timeout_cycles` | input | 32 | Write-progress timeout window in cycles. |
| `cfg_sched_timeout_limit` | input | 8 | Consecutive timeout windows before a fatal error. 0 means never. |
| `cfg_sched_timeout_enable` | input | 1 | Enable timeout detection. |
| `cfg_sched_err_enable` | input | 1 | Enable error reporting. |
| `cfg_sched_compl_enable` | input | 1 | 1 passes CORE Completion packets to the monitor bus; 0 drops them at the arbiter inputs. |
| `cfg_sched_perf_enable` | input | 1 | Enable performance monitoring. |
| `cfg_ctrlrd_max_try` | input | 9 | Control-read poll retry budget, 0 to 511. |
| `tick_1us` | input | 1 | 1 us tick for control-read retry spacing. |
| `cfg_desceng_prefetch` | input | 1 | Enable descriptor prefetch. |
| `cfg_desceng_fifo_thresh` | input | 4 | Prefetch threshold. |
| `cfg_desceng_addr0_base` | input | AW | Valid descriptor address range 0 base. |
| `cfg_desceng_addr0_limit` | input | AW | Valid descriptor address range 0 limit. |
| `cfg_desceng_addr1_base` | input | AW | Valid descriptor address range 1 base. |
| `cfg_desceng_addr1_limit` | input | AW | Valid descriptor address range 1 limit. |

: Table 3.1.3: Configuration Interface

### Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `descriptor_engine_idle` | output | 1 | Descriptor engine idle. |
| `scheduler_idle` | output | 1 | Scheduler idle. |
| `scheduler_state` | output | 7 | Scheduler FSM state, one-hot. |
| `sched_error` | output | 1 | Scheduler error, sticky. |

: Table 3.1.4: Status Interface

### Descriptor AXI Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `desc_ar_valid` / `desc_ar_ready` | output / input | 1 | AR handshake. |
| `desc_ar_addr` | output | AW | Descriptor fetch address. |
| `desc_ar_len` | output | 8 | Burst length minus one. |
| `desc_ar_size` | output | 3 | Burst size. |
| `desc_ar_burst` | output | 2 | Burst type. |
| `desc_ar_id` | output | IW | Transaction ID. |
| `desc_ar_lock`, `_cache`, `_prot`, `_qos`, `_region` | output | 1, 4, 3, 4, 4 | Attribute fields. |
| `desc_r_valid` / `desc_r_ready` | input / output | 1 | R handshake. |
| `desc_r_data` | input | 256 | Descriptor payload, fixed 256 bits. |
| `desc_r_resp` | input | 2 | Read response. |
| `desc_r_last` | input | 1 | Last beat. |
| `desc_r_id` | input | IW | Response ID. |

: Table 3.1.5: Descriptor AXI Master Interface

### Control Read and Control Write AXI Interfaces

The control read engine fetches a 32-bit semaphore word: `ctrlrd_ar_*` carries the AR channel (address, length, size, burst, id and the same attribute fields as above) and `ctrlrd_r_valid`, `ctrlrd_r_ready`, `ctrlrd_r_data[31:0]`, `ctrlrd_r_id`, `ctrlrd_r_resp` and `ctrlrd_r_last` the R channel. The control write engine writes a 32-bit word: `ctrlwr_aw_*` carries the AW channel, `ctrlwr_w_valid`, `ctrlwr_w_ready`, `ctrlwr_w_data[31:0]`, `ctrlwr_w_strb[3:0]` and `ctrlwr_w_last` the W channel, and `ctrlwr_b_valid`, `ctrlwr_b_ready`, `ctrlwr_b_id` and `ctrlwr_b_resp` the B channel. These are unchanged from RAPIDS Beats. See [Control Read Engine](../../rapids_beats_mas/ch02_fub_blocks/08_ctrlrd_engine.md) and [Control Write Engine](../../rapids_beats_mas/ch02_fub_blocks/09_ctrlwr_engine.md).

### Scheduler Data Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_valid` | output | 1 | Read request. |
| `sched_rd_addr` | output | AW | Working source byte address. |
| `sched_rd_beats` | output | 32 | Beats still to read. |
| `sched_wr_valid` | output | 1 | Write request. |
| `sched_wr_ready` | input | 1 | Write engine reports the last burst of the descriptor committed. |
| `sched_wr_addr` | output | AW | Working destination byte address. |
| `sched_wr_beats` | output | 32 | Beats still to write. |
| `sched_rd_done_strobe` | input | 1 | Read burst issued. |
| `sched_rd_beats_done` | input | 32 | Beats in that burst. |
| `sched_wr_done_strobe` | input | 1 | Write AW issued. |
| `sched_wr_beats_done` | input | 32 | Beats in that AW. |
| `sched_wr_commit_strobe` | input | 1 | Write B response received. |
| `sched_wr_commit_beats` | input | 32 | Beats committed by that B response. |
| `sched_rd_error` | input | 1 | Sticky read error from the read engine. |
| `sched_wr_error` | input | 1 | Sticky write error, including a packet-length error from the sink path. |

: Table 3.1.6: Scheduler Data Interface

### Packet Record Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_pkt_valid` | output | 1 | One-cycle pulse: a read-side packet record is available. |
| `sched_rd_pkt_ready` | input | 1 | Consumer has room in its record queue. |
| `sched_rd_pkt_bytes` | output | 32 | Packet length in bytes. |
| `sched_rd_pkt_offset` | output | OFF_W | Byte offset of the packet start within its first memory beat. |
| `sched_wr_pkt_valid` | output | 1 | One-cycle pulse: a write-side packet record is available. |
| `sched_wr_pkt_ready` | input | 1 | Consumer has room in its record queue. |
| `sched_wr_pkt_bytes` | output | 32 | Packet length in bytes. |
| `sched_wr_pkt_offset` | output | OFF_W | Byte offset of the packet start within its first memory beat. |

: Table 3.1.7: Packet Record Interface

The group wires these signals directly to the scheduler. The read-side record goes to the source data path and the write-side record to the sink data path. The scheduler holds a descriptor in its fetch state while a required record queue is full, using the ready inputs. See [Packet Record Interface](../ch04_interfaces/04_packet_record_interface_spec.md).

### MonBus Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `i_mon_time` | input | `monbus_timestamp_t` | Shared monitor timebase. |
| `mon_valid` | output | 1 | Monitor packet valid. |
| `mon_ready` | input | 1 | Consumer ready. |
| `mon_packet` | output | `monitor_packet_t` | Monitor packet. |
| `mon_timestamp` | output | `monbus_timestamp_t` | Packet timestamp. |

: Table 3.1.8: MonBus Interface

---

## Internal Architecture

### Descriptor Path

The descriptor engine fetches 256-bit descriptors from the address range the configuration allows and hands each one to the scheduler with its type, end-of-stream, end-of-list and error flags. The scheduler reports `scheduler_idle` back to the descriptor engine as `channel_idle`. No byte or beat arithmetic happens in the descriptor engine.

### Control Engines

When a descriptor asks the scheduler to wait on or update a semaphore, the scheduler talks to the control engines through valid and ready handshakes with an address, data and mask. Both engines share the group's `AXI_ID_WIDTH` and each raises its own MonBus packets.

### MonBus Aggregation

A four-client arbiter merges the descriptor engine, scheduler, control read and control write packets. `cfg_sched_compl_enable` gates only the CORE Completion packets of the descriptor engine and the scheduler: with it low, those packets are consumed at the arbiter input and never reach `mon_packet`. Error packets are never gated. `GEN_MON` masks every arbiter input when clear.

---

## Differences from RAPIDS Beats

| Item | RAPIDS Beats | RAPIDS |
|------|--------------|--------|
| Parameter `OFF_W` | absent | present, `$clog2(DATA_WIDTH/8)` |
| `sched_rd_pkt_*`, `sched_wr_pkt_*` ports | absent | present, wired to the scheduler |
| Everything else | | Unchanged |

: Table 3.1.9: Scheduler Group Delta

The beats chapter is [Beats Scheduler Group](../../rapids_beats_mas/ch03_macro_blocks/01_beats_scheduler_group.md). The scheduler is described in [Scheduler](../ch02_fub_blocks/01_scheduler.md).

---

**Last Updated:** 2026-09-30
