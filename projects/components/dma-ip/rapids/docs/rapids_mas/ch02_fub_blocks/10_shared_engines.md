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

# Shared Engines

**Modules:** `descriptor_engine_shared.sv`, `ctrlrd_engine_shared.sv`, `ctrlwr_engine_shared.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/fub/`
**Status:** Implemented
**Last Updated:** 2026-10-17

---

## Overview

With `SHARED_ENGINES = 1` (the default) each scheduler group array, one per half, builds one descriptor engine, one control-read engine and one control-write engine for all of its channels. These replace the `NUM_CHANNELS` copies of each that `SHARED_ENGINES = 0` builds. Each shared engine picks the next channel to serve round-robin on the scheduler side and owns its AXI master outright, so the array's AXI-side arbiters are gone. ARID and AWID carry the channel.

Each scheduler sees the same per-channel interface as with a dedicated engine. The schedulers, the array's ports and everything above the array are the same in both builds. The [Scheduler Group Array](../ch03_macro_blocks/02_scheduler_group_array.md) chapter describes how the array instantiates the engines and the MonBus sources they add. This chapter describes the engines themselves.

### Key Features

- **One fetch path per half:** a single AR issuer, one set of address-range comparators and one R path for every channel.
- **Per-channel ordering:** each channel keeps one descriptor fetch in flight, so its descriptors arrive in order. Fetches for different channels overlap on the bus under their own ARIDs.
- **No R-channel blocking:** a fetch issues only when its channel's FIFO has room, and an R beat for a channel reset mid-fetch is accepted and dropped.
- **Owner-register control engines:** one `ctrlrd_engine` and one `ctrlwr_engine`, each wrapped with a round-robin pick and an owner register.
- **Descriptor injection (`INJ_EN`):** a second writer into the descriptor FIFOs for the tile's cell-issued descriptors. See [Tile Packet Header](../ch03_macro_blocks/14_tile_header.md).

### Cost

On the Genesys 2 board build (8 channels per half, 256 bits) the three per-channel engine sets took 15,283 LUTs and 19,308 flip-flops across both halves:

- descriptor engines: 11,009 LUTs and 7,360 flip-flops for 16 engines;
- control-read engines: 2,388 LUTs and 7,038 flip-flops;
- control-write engines: 1,886 LUTs and 4,910 flip-flops.

Sharing removed 11,024 LUTs (20%) and 16,483 flip-flops (37%) from RAPIDS. The HAS [Resource Estimates](../../rapids_has/ch06_performance/03_resources.md) chapter has the full before and after.

---

## descriptor_engine_shared

### Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `NUM_CHANNELS` | 8 | Channels served. |
| `CHAN_WIDTH` | `$clog2(NUM_CHANNELS)` (1 minimum) | Channel ID width. `AXI_ID_WIDTH` must be at least this; elaboration fails otherwise. |
| `ADDR_WIDTH` | 64 | Address width. |
| `AXI_ID_WIDTH` | 8 | ARID and RID width. ARID = channel. |
| `FIFO_DEPTH` | 8 | Descriptor FIFO depth per channel. |
| `USE_ROW_COL_MAJOR_ADDRESSING` | 1 | Enables the EXTENDED descriptor's second fetch and its chunk-1 FIFO. |
| `MON_AGENT_BASE` | 0x10 | MonBus agent is `MON_AGENT_BASE + channel`. |
| `MON_UNIT_ID` | 0x01 | MonBus unit ID. |
| `MON_FIFO_DEPTH` | 4 | Depth of the MonBus packet FIFO. |
| `INJ_EN` | 0 | 1 builds the injection slot (set by the array when `TILE_HDR = 1`). |

: Table 2.10.1: descriptor_engine_shared Parameters

### Port List

Every per-channel port is a packed `[NUM_CHANNELS-1:0]` vector of the signal a dedicated `descriptor_engine` has, so channel `c` sees bit or element `c`.

| Group | Signals | Description |
|-------|---------|-------------|
| Clock and reset | `clk`, `rst_n` | Single clock, active-low asynchronous reset. |
| Kick (per channel) | `apb_valid`, `apb_ready`, `apb_addr` | Staged descriptor address from the configuration block. |
| Scheduler (per channel) | `channel_idle`, `descriptor_valid`, `descriptor_ready`, `descriptor_packet`, `descriptor_ext_packet`, `descriptor_error`, `descriptor_eos`, `descriptor_eol`, `descriptor_eod`, `descriptor_type` | The same handshake and flags as `descriptor_engine`. |
| AXI4 read master | `ar_*`, `r_*` (256-bit `r_data`) | Owned outright; one master per half. |
| Configuration | `cfg_prefetch_enable`, `cfg_fifo_threshold`, `cfg_addr0_base`/`limit`, `cfg_addr1_base`/`limit`, `cfg_channel_reset` | Shared by every channel, as before; the reset is per channel. |
| Injection | `inj_valid`, `inj_ch`, `inj_data`, `inj_dropped`, `inj_dropped_clr` | Unused (tied off) unless `INJ_EN = 1`. |
| Status | `descriptor_engine_idle` (per channel) | Channel has no fetch pending or in flight. |
| MonBus | `i_mon_time`, `mon_valid`, `mon_ready`, `mon_packet`, `mon_timestamp` | One stream for every channel. |

: Table 2.10.2: descriptor_engine_shared Ports

### Per-Channel State

Each channel keeps only what a fetch needs between the kick and the FIFO write:

| State | Meaning |
|-------|---------|
| `S_IDLE` | Nothing to fetch. |
| `S_PEND` | Chunk-0 address pending (from a kick or from chaining). |
| `S_ISSUE` | Chunk-0 request is in the shared issue slot. |
| `S_WAIT` | Chunk-0 AR accepted, waiting for R. |
| `S_PEND2`, `S_ISSUE2`, `S_WAIT2` | The same three steps for an EXTENDED descriptor's chunk 1. |

: Table 2.10.3: Per-Channel Fetch States

Beside the state code each channel has one pending fetch address, a kick-in-progress flag, an owed-beat flag (`r_owe`), its descriptor FIFO and, when EXTENDED descriptors are built, a chunk-1 FIFO kept in lockstep with it. An injection slot is added when `INJ_EN = 1`.

### Operation

**Issue.** A round-robin pick among channels in `S_PEND` or `S_PEND2` loads one request into the issue slot. A channel is eligible only while its FIFO has a free entry, so a channel that has stopped consuming never takes an R beat it cannot store. The range check runs at the slot: an address outside both configured ranges is refused with no AR and raises the channel's descriptor error. Once ARVALID is high, the address and ID hold until accepted.

**Return.** Each R beat is routed by RID to its channel and written straight into that channel's FIFO, so there is no 256-bit holding register per channel. The exception is an EXTENDED descriptor's chunk 0, which waits for chunk 1. A non-OKAY response, or a beat that does not parse as a valid descriptor, raises the channel's descriptor error.

**Chaining and prefetch.** The next-pointer decision and the prefetch throttle are the per-channel engine's: autonomous chaining while the descriptor allows it, up to the FIFO threshold plus one buffered.

**Channel reset.** A reset in the middle of a fetch sets `r_owe`. The owed beat is accepted and dropped when it arrives, and the channel takes no new kick until then. Reset also drains the channel's FIFO, so descriptors prefetched for an aborted chain are never delivered.

**Injection.** An injected descriptor is a pulse with no backpressure. It waits in its channel's one-entry slot and is written into the FIFO, with no fetch, once the channel's fetch side is idle and the FIFO has room. An injection therefore never takes an entry an R beat needs. A descriptor that arrives while the slot is full, while the channel is held in reset, or that is EXTENDED is dropped and sets the channel's sticky `inj_dropped` bit. A drop is not a descriptor error.

### MonBus

Completion and error packets go through a `MON_FIFO_DEPTH`-entry FIFO. Two behaviours differ from the per-channel engine:

- A refused kick address reports 0 in the response field. The per-channel engine reported its last latched read response, which was stale.
- An issue-side refusal and an R-side event can occur in the same cycle. The issue-side packet waits one cycle. If a second collision arrives while it waits, the waiting packet is dropped. Tests that count descriptor-engine packets must allow for this.

---

## ctrlrd_engine_shared and ctrlwr_engine_shared

The two control engines share one structure: an unmodified `ctrlrd_engine` or `ctrlwr_engine` with three things around it. A control engine runs one request at a time, so nothing inside it has to change.

| Element | Behaviour |
|---------|-----------|
| Round-robin pick | Offered to the engine only while it is idle, its last MonBus packet has drained, and no error remains from the previous owner. A stale error is cleared with a one-cycle engine reset before the next channel is taken. |
| Owner register | Set when the engine accepts a request. ARID or AWID carries the owner, and every R or B response belongs to the engine. |
| Per-channel view | The owner sees the engine's `*_idle` and `*_error` as a dedicated engine would show them. Every other channel sees idle 1 and error 0. |
| Channel reset | The owner's `cfg_channel_reset` resets the engine only while the owner's operation is in flight, so a channel held in reset cannot hold the engine for the others. |
| MonBus | Packets are re-tagged with the owner's channel and agent ID: 0x20 + channel for control reads, 0x28 + channel for control writes. |

: Table 2.10.4: Shared Control Engine Wrapper

### Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `NUM_CHANNELS` | 8 | Channels served. |
| `CHAN_WIDTH` | `$clog2(NUM_CHANNELS)` (1 minimum) | Channel ID width. |
| `ADDR_WIDTH` | 64 | Address width. |
| `AXI_ID_WIDTH` | 8 | ARID or AWID width. |
| `MON_AGENT_BASE` | 0x20 (read), 0x28 (write) | MonBus agent is `MON_AGENT_BASE + channel`. |
| `MON_UNIT_ID` | 0x01 | MonBus unit ID. |

: Table 2.10.5: Shared Control Engine Parameters

### Port List

| Group | ctrlrd_engine_shared | ctrlwr_engine_shared |
|-------|----------------------|----------------------|
| Requests (per channel) | `ctrlrd_valid`, `ctrlrd_ready`, `ctrlrd_addr`, `ctrlrd_data`, `ctrlrd_mask` | `ctrlwr_valid`, `ctrlwr_ready`, `ctrlwr_addr`, `ctrlwr_data` |
| Status (per channel) | `ctrlrd_error`, `ctrlrd_idle` | `ctrlwr_error`, `ctrlwr_idle` |
| Configuration | `cfg_ctrlrd_max_try`, `cfg_channel_reset`, `tick_1us` | `cfg_channel_reset` |
| AXI4 master | `ar_*`, `r_*` (32-bit data) | `aw_*`, `w_*` (32-bit data, 4-bit strobe), `b_*` |
| MonBus | `i_mon_time`, `mon_valid`, `mon_ready`, `mon_packet`, `mon_timestamp` | the same |

: Table 2.10.6: Shared Control Engine Ports

### Trade-off

A `CTRL_READ` that keeps polling holds the control-read engine, so other channels' control reads wait behind it, up to `cfg_ctrlrd_max_try` retries. Data transfers are not affected. The control-write engine keeps one write in flight, which the array-level serializer of the per-channel build also enforced.

---

## Related Chapters

- [Scheduler Group Array](../ch03_macro_blocks/02_scheduler_group_array.md): instantiation, MonBus sources, and the `SHARED_ENGINES = 0` AXI arbiters.
- [Descriptor Engine](../../rapids_beats_mas/ch02_fub_blocks/02_descriptor_engine.md), [Control-Read Engine](../../rapids_beats_mas/ch02_fub_blocks/08_ctrlrd_engine.md), [Control-Write Engine](../../rapids_beats_mas/ch02_fub_blocks/09_ctrlwr_engine.md): the per-channel engines whose behaviour the shared engines keep.
- [Tile Packet Header](../ch03_macro_blocks/14_tile_header.md): the descriptor injection path.
