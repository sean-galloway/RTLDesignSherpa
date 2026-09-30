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

# AXI Read Engine

**Module:** `axi_read_engine.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/fub/`
**Status:** Implemented
**Last Updated:** 2026-09-30

---

## Overview

The AXI read engine turns per-channel read requests from the schedulers into AXI4 read bursts and routes the returning data to the SRAM controller. It is a streaming pipeline with no state machine. The channel identity travels in the AXI ID.

The engine is beat based, as in RAPIDS Beats. The scheduler has already converted the descriptor's byte length into a beat count. Two things change for byte-granular RAPIDS: the engine must cope with a channel address that is not beat aligned, and it must never let a burst cross a 4 KB boundary.

### Key Features

- **Streaming pipeline:** no FSM, round-robin arbitration across channels.
- **Aligned AR address:** `ARADDR` is the channel address rounded down to a beat boundary. The lanes below the offset are read and ignored by the data path.
- **4 KB burst cap:** the burst length is limited so that no burst crosses a 4 KB boundary, whatever the start address.
- **Configurable burst length:** `cfg_axi_rd_xfer_beats`, clamped to what the buffer can hold (rapids BUG-009).
- **Space-checked:** a channel is only granted when the SRAM controller has room for the whole burst.
- **Sticky error:** SLVERR or DECERR on R sets `sched_rd_error` for the channel.

### Block Diagram

### Figure 2.3.1: AXI Read Engine Block Diagram

```
                     +-----------------------------------+
 sched_rd_valid  --->|                                   |---> m_axi_arid
 sched_rd_addr   --->|  per-channel request, round robin |---> m_axi_araddr  (beat aligned)
 sched_rd_beats  --->|  arbiter, 4 KB burst cap          |---> m_axi_arlen
 cfg_..xfer_beats -->|                                   |---> m_axi_arsize / arburst
                     |                                   |---> m_axi_arvalid
 sched_rd_done   <---|                                   |<--- m_axi_arready
 sched_rd_beats_d <--|                                   |
 sched_rd_error  <---|                                   |<--- m_axi_rid / rdata / rresp / rlast
                     |                                   |<--- m_axi_rvalid
 axi_rd_alloc_*  <-->|  allocation and fill handshake    |---> m_axi_rready
 axi_rd_sram_*   --->|                                   |
                     +-----------------------------------+
```

---

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `NUM_CHANNELS` | 8 | Number of channels. Channel id is carried in the AXI ID. |
| `ADDR_WIDTH` | 64 | AXI address width. |
| `DATA_WIDTH` | 512 | AXI data width in bits. The Genesys 2 build uses 256. |
| `ID_WIDTH` | 8 | AXI ID width. |
| `SEG_COUNT_WIDTH` | 8 | Width of the per-channel free-space count from the SRAM controller. Sets the burst clamp. |
| `PIPELINE` | 1 | 1 allows the next AR before the previous burst's data has returned. 0 waits for the burst to complete. |
| `AR_MAX_OUTSTANDING` | 8 | Maximum outstanding AR transactions. |
| `STROBE_EVERY_BEAT` | 0 | Declared for compatibility with STREAM. The completion strobe in this engine is generated on the AR handshake regardless of its value. |

: Table 2.3.1: AXI Read Engine Parameters

The module also accepts the short aliases `NC`, `AW`, `DW`, `IW`, `SCW` and `CIW` (the channel id width, `$clog2(NUM_CHANNELS)`).

### Derived Constants

| Constant | Definition | Meaning |
|----------|------------|---------|
| `BYTES_PER_BEAT` | `DW / 8` | Bytes per beat. |
| `AXSIZE` | `$clog2(BYTES_PER_BEAT)` | Value driven on `ARSIZE`. Full-width beats. |
| `SD_BEATS` | `1 << (SCW - 1)` | Buffer depth in beats implied by `SEG_COUNT_WIDTH`. |
| `XFER_MAX` | `SD_BEATS < 256 ? SD_BEATS - 1 : 254` | Largest burst length value the engine will use. |

: Table 2.3.2: AXI Read Engine Derived Constants

---

## Port List

### Clock, Reset and Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | Clock. |
| `rst_n` | input | 1 | Active-low reset. |
| `cfg_axi_rd_xfer_beats` | input | 8 | Configured burst length (ARLEN value, 0 to 255). Clamped to `XFER_MAX`. |
| `cfg_channel_reset` | input | NC | Per-channel reset, level or pulse. Stops the channel's ARs, drains and discards its in-flight R data, and clears its error flag. |

: Table 2.3.3: Clock, Reset and Configuration

### Scheduler Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_valid` | input | NC | Channel has a read request. |
| `sched_rd_addr` | input | NC x AW | Working source byte address. |
| `sched_rd_beats` | input | NC x 32 | Beats still to read for the channel. |
| `sched_rd_done_strobe` | output | NC | Registered pulse, one cycle after the AR handshake for the channel. |
| `sched_rd_beats_done` | output | NC x 32 | Beats issued by that AR (`ARLEN + 1`). |
| `sched_rd_error` | output | NC | Sticky read error for the channel, set by any non-OKAY R response. |

: Table 2.3.4: Scheduler Interface

The address is a byte address and may carry an offset in its low bits. The scheduler advances it to the next beat boundary after each done strobe, so only the first burst of a descriptor can see a non-zero offset.

### SRAM Allocation and Fill Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `axi_rd_alloc_req` | output | 1 | Registered pulse, one cycle after the AR handshake, reserving space for the burst. |
| `axi_rd_alloc_size` | output | 8 | Beats to reserve. |
| `axi_rd_alloc_id` | output | IW | Channel that owns the reservation. |
| `axi_rd_alloc_space_free` | input | NC x SCW | Free space per channel. A channel is granted only if it fits the burst. |
| `axi_rd_sram_valid` | output | 1 | Follows `m_axi_rvalid`. |
| `axi_rd_sram_ready` | input | 1 | SRAM controller accepts the beat. Drives `m_axi_rready`. |
| `axi_rd_sram_id` | output | IW | Follows `m_axi_rid`. |
| `axi_rd_sram_data` | output | DW | Follows `m_axi_rdata`. |

: Table 2.3.5: SRAM Allocation and Fill Interface

### AXI4 Read Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arid` | output | IW | Read address ID (the channel). |
| `m_axi_araddr` | output | AW | Beat-aligned read address. |
| `m_axi_arlen` | output | 8 | Burst length minus one. |
| `m_axi_arsize` | output | 3 | `AXSIZE`, full-width beats. |
| `m_axi_arburst` | output | 2 | INCR. |
| `m_axi_arvalid` | output | 1 | Address valid. |
| `m_axi_arready` | input | 1 | Address ready. |
| `m_axi_rid` | input | IW | Response ID. |
| `m_axi_rdata` | input | DW | Read data. |
| `m_axi_rresp` | input | 2 | Read response. |
| `m_axi_rlast` | input | 1 | Last beat of the burst. |
| `m_axi_rvalid` | input | 1 | Data valid. |
| `m_axi_rready` | output | 1 | Data ready. |

: Table 2.3.6: AXI4 Read Master Interface

### Debug

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `dbg_rd_all_complete` | output | NC | Channel has no outstanding reads. |
| `dbg_r_beats_rcvd` | output | 32 | Total R beats received. |
| `dbg_sram_writes` | output | 32 | Total beats written to the SRAM controller. |
| `dbg_arb_request` | output | NC | Arbiter request vector. |

: Table 2.3.7: Debug Outputs

---

## Operation

### Burst Length Cap (rapids BUG-009)

`cfg_axi_rd_xfer_beats` is an ARLEN value, but a burst must fit in the buffer that stages it. The engine clamps the configured value to `XFER_MAX`, giving the working limit `w_xfer_cfg`. Without the clamp an ARLEN of 255 wraps the 8-bit `ARLEN + 1` and a channel is granted with no space reserved. This is the same fix as in RAPIDS Beats.

### Byte-Granular Burst Sizing

The engine sizes each burst from the channel's current byte address and remaining beats. Three steps produce `ARLEN`:

1. Distance to the next 4 KB boundary, in beats: `w_beats_to_4k = (4096 - {sched_rd_addr[11:AXSIZE], AXSIZE'b0}) >> AXSIZE`. The offset bits are dropped first, so the distance is measured from the aligned beat.
2. Burst cap: `w_cap_beats = min(w_xfer_cfg + 1, w_beats_to_4k)`.
3. Burst length: `w_transfer_size = (sched_rd_beats <= w_cap_beats) ? sched_rd_beats - 1 : w_cap_beats - 1`.

`m_axi_araddr` is `{sched_rd_addr[grant][AW-1:AXSIZE], AXSIZE'b0}`. The offset never reaches the bus. The first beat of the burst carries the bytes before the offset, and the data path discards them.

Because the cap always rounds toward the boundary, a burst can be shorter than the configured length, and a later burst restarts on the boundary. The scheduler needs no knowledge of this. It only sees `beats_done` per burst.

### Streaming Pipeline

An arbiter picks a channel that has `sched_rd_valid` set and enough `axi_rd_alloc_space_free` for its burst. When the AR handshakes, the engine pulses `axi_rd_alloc_req` one cycle later with the burst size so the SRAM controller reserves the space, and pulses `sched_rd_done_strobe` for the channel. R beats pass straight through: `axi_rd_sram_valid`, `axi_rd_sram_id` and `axi_rd_sram_data` follow the R channel, and `m_axi_rready` is `axi_rd_sram_ready`.

With `PIPELINE = 1` the next AR for a channel can issue while earlier data is still in flight. With `PIPELINE = 0` the channel waits for the burst to finish. The top and core default to 1.

### Figure 2.3.2: Burst Segmentation with a Mid-Beat Start

The example uses 32-byte beats (OFF_W 5) and a configured burst of 16 beats. A descriptor reads 8,200 bytes from address 0xFF8. The scheduler computes offset 0x18 (24) and `beats_total = (24 + 8200 + 31) >> 5 = 257`.

| Burst | Channel address | `ARADDR` | Beats to 4 KB | `ARLEN` | Beats left after |
|-------|-----------------|----------|----------------|---------|------------------|
| 1 | 0x0FF8 | 0x0FE0 | 1 | 0 | 256 |
| 2 | 0x1000 | 0x1000 | 128 | 15 | 240 |
| 3 | 0x1200 | 0x1200 | 112 | 15 | 224 |
| ... | | | | 15 | continues |

: Table 2.3.8: Burst Segmentation Example

The first burst is one beat because the aligned start is 32 bytes below the 4 KB boundary. From then on each burst is the configured 16 beats until the remainder runs out. The scheduler advances its address to the next beat boundary after each done strobe, which is why burst 2 starts at 0x1000, not 0x0FF8 plus a beat.

### Done Strobe

The engine pulses `sched_rd_done_strobe[ch]` once per AR handshake, with `sched_rd_beats_done[ch]` equal to `ARLEN + 1`. The scheduler subtracts this from its remaining count and advances the address. The strobe therefore reports beats issued, not beats returned.

---

## Error Handling

| Error | Detection | Response |
|-------|-----------|----------|
| AXI SLVERR | `m_axi_rresp == 2'b10` on an accepted beat | Set sticky `sched_rd_error` for the channel |
| AXI DECERR | `m_axi_rresp == 2'b11` on an accepted beat | Set sticky `sched_rd_error` for the channel |
| Any other non-zero response | `m_axi_rresp != 2'b00` on an accepted beat | Same: the test is not-OKAY, and the channel is taken from `RID` |

: Table 2.3.9: Error Handling

The scheduler turns the sticky error into its ERROR state and a MonBus event. The engine does not abort the burst: the remaining R beats still pass through, so the interconnect is not left mid-burst.

### Channel Reset

`cfg_channel_reset[ch]` clears the sticky `sched_rd_error[ch]`, so a channel reset recovers a read error without `aresetn`. The reset also has to settle AR bursts that are already on the bus, because an AXI master cannot recall them:

- A channel in reset, or flushing, issues no new AR and does not enter the allocation pipeline.
- `r_rd_flush[ch]` is set by the reset and holds until the channel has no burst outstanding. While it holds, each R beat whose `RID` names the channel is accepted (`m_axi_rready` is forced high) and dropped: `axi_rd_sram_valid` stays low, so nothing reaches the SRAM, and its `RRESP` does not set the error flag.
- The completion strobe and pending allocation of the channel are cleared, so the scheduler does not see a stale done pulse after the reset.
- Other channels are not affected: every term is indexed by channel, and R beats of other channels pass as usual.

The channel's SRAM partition is cleared by the SRAM controller wrapper (see [Sink Data Path](../ch03_macro_blocks/03_snk_data_path.md) and [Source Data Path AXIS](../ch03_macro_blocks/07_src_data_path_axis.md)). The discard is what guarantees that no beat of the reset channel reaches the partition after it has been cleared.

---

## Differences from RAPIDS Beats

| Item | RAPIDS Beats | RAPIDS |
|------|--------------|--------|
| `ARADDR` | Channel address as given (always aligned) | Aligned down to the beat |
| Burst cap | Configured length and remaining beats | Also capped at the 4 KB boundary |
| Everything else | | Unchanged |

: Table 2.3.10: Read Engine Delta

The beat-count chapter for the beats engine is [AXI Read Engine (RAPIDS Beats)](../../rapids_beats_mas/ch02_fub_blocks/03_axi_read_engine.md). The scheduler that feeds this engine is described in [Scheduler](01_scheduler.md).

---

**Last Updated:** 2026-09-30
