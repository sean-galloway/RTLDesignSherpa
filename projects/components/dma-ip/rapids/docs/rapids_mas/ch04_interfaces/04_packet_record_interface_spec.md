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

# Packet Record Interface Specification

**Module:** `scheduler.sv` (producer), `src_data_path_axis.sv` and `snk_data_path_axis.sv` (consumers)
**Location:** `projects/components/dma-ip/rapids/rtl/fub/` and `rtl/macro/`
**Status:** Implemented
**Last Updated:** 2026-09-30

---

## Overview

The packet record interface is new in the byte-granular design. It tells a data path how many bytes a descriptor covers and where in its first beat the data starts. RAPIDS Beats has no equivalent, because every transfer there is a whole number of aligned beats.

The scheduler is the producer. It emits one record per data descriptor. The source or sink data path is the consumer and holds the records in a small queue per channel. The record interface is internal to each half: it does not appear on the `rapids_core` or `rapids_top` ports.

### Figure 4.4.1: Scheduler Byte Math

![Scheduler byte math](../assets/graphviz/03_scheduler_byte_math.png)

**Source:** [assets/graphviz/03_scheduler_byte_math.dot](../assets/graphviz/03_scheduler_byte_math.dot)

---

## Signals

There is one set per direction. The source half uses `sched_rd_pkt_*` and the sink half uses `sched_wr_pkt_*`. Each signal is a vector with one entry per channel.

| Signal | Direction (scheduler view) | Width per channel | Description |
|--------|----------------------------|-------------------|-------------|
| `sched_*_pkt_valid` | output | 1 | One-cycle pulse: a record is presented. |
| `sched_*_pkt_ready` | input | 1 | The consumer queue has room. |
| `sched_*_pkt_bytes` | output | 32 | Descriptor length in bytes. |
| `sched_*_pkt_offset` | output | `OFF_W` | Address offset inside the first beat. |

: Table 4.4.1: Packet Record Signals

`OFF_W` is `$clog2(DATA_WIDTH/8)`, 5 for a 256-bit build.

---

## Protocol

The scheduler raises `valid` for one cycle, in the cycle it leaves the descriptor fetch state. It does not leave that state until every enabled direction can take the record, so `ready` is a pre-condition of the pulse, not a wait state after it. Both directions of a channel see exactly one pulse per data descriptor.

A consumer accepts a record when `valid` and its queue is not full. It drives `ready` low when the queue is full, which is what holds the scheduler in its fetch state.

| Rule | Detail |
|------|--------|
| Records per descriptor | One, for data descriptors of nonzero length. |
| Zero-length descriptors | No record. |
| Non-data descriptors | No record. |
| Order | Records are consumed in the order pushed, per channel. |
| Queue depth | Four records per channel in each data path. |
| Pop | The record pops on the last beat of its packet. |

: Table 4.4.2: Record Rules

The offset is taken from the source address in the read direction and from the destination address in the write direction. The length is the same for both. When both directions are enabled, each data path receives its own offset.

---

## Unused Direction

A scheduler group array instantiated for only one direction ties the other direction off inside the half. The unused `valid`, `bytes` and `offset` outputs are left open and the unused `ready` inputs are held at all ones, so the scheduler never waits on a queue that does not exist.

---

## Consumer Behavior

- The source data path uses the record to compute the number of memory beats, to decide when a pop emits a stream beat, to set `TSTRB` and `TLAST`, and to retire the record.
- The sink data path uses the record to decide how far to shift each incoming beat, to check the received length at `TLAST`, and it holds off `TREADY` for a channel until the record exists.

---

**Last Updated:** 2026-09-30
