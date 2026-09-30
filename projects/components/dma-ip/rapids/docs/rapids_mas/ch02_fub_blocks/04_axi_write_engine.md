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

# AXI Write Engine

**Module:** `axi_write_engine.sv`
**Location:** `projects/components/dma-ip/rapids/rtl/fub/`
**Status:** Implemented
**Last Updated:** 2026-09-30

---

## Overview

The AXI write engine drains data from the SRAM controller and issues AXI4 write bursts to system memory. It is a streaming pipeline with no state machine. It also tracks the write responses, which is how the scheduler learns that data has been committed.

Byte-granular RAPIDS changes the engine in three places. Write strobes now come from the SRAM instead of being all ones, so a partial first or last beat writes only the bytes that belong to the packet. Burst lengths are capped at the 4 KB boundary. `AWADDR` is beat aligned.

### Key Features

- **Streaming pipeline:** no FSM, round-robin arbitration across channels.
- **Real write strobes:** `m_axi_wstrb` is the strobe word stored beside each data beat (`axi_wr_sram_strb`). Lanes outside the packet are not written.
- **Aligned AW address:** `AWADDR` is the channel address rounded down to a beat boundary.
- **4 KB burst cap:** the same cap as the read engine, applied to both the burst length and the final-burst test.
- **Configurable burst length:** `cfg_axi_wr_xfer_beats`, clamped to what the buffer can hold (rapids BUG-009).
- **Two completion strobes:** done on the AW handshake, commit on the B response.
- **Sticky error:** a non-OKAY B response sets `sched_wr_error`.

### Block Diagram

### Figure 2.4.1: AXI Write Engine Block Diagram

```
                     +-----------------------------------+
 sched_wr_valid  --->|                                   |---> m_axi_awid / awaddr (aligned)
 sched_wr_addr   --->|  per-channel request, round robin |---> m_axi_awlen / awsize / awburst
 sched_wr_beats  --->|  arbiter, 4 KB burst cap          |---> m_axi_awvalid <-- awready
 cfg_..xfer_beats -->|                                   |
                     |                                   |---> m_axi_wdata
 sched_wr_done   <---|                                   |---> m_axi_wstrb  (from SRAM strobe)
 sched_wr_commit <---|                                   |---> m_axi_wlast / wuser / wvalid
 sched_wr_error  <---|                                   |<--- m_axi_wready
                     |                                   |
 axi_wr_drain_*  <-->|  reserve and drain                |<--- m_axi_bid / bresp / bvalid
 axi_wr_sram_*   <-->|                                   |---> m_axi_bready
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
| `USER_WIDTH` | 8 | Width of `m_axi_wuser`, which carries the active channel. |
| `SEG_COUNT_WIDTH` | 8 | Width of the per-channel available-data count from the SRAM controller. Sets the burst clamp. |
| `PIPELINE` | 1 | 1 allows further AWs before earlier B responses return. 0 waits for the B. |
| `AW_MAX_OUTSTANDING` | 8 | Maximum outstanding AW transactions per channel. |
| `W_PHASE_FIFO_DEPTH` | 64 | Depth of the W-phase transaction FIFO, kept in order with the AW issue. |
| `B_PHASE_FIFO_DEPTH` | 16 | Depth of the B-phase transaction FIFO used to match responses. |

: Table 2.4.1: AXI Write Engine Parameters

The module also accepts the short aliases `NC`, `AW`, `DW`, `IW`, `UW`, `SCW` and `CIW` (the channel id width).

### Derived Constants

| Constant | Definition | Meaning |
|----------|------------|---------|
| `BYTES_PER_BEAT` | `DW / 8` | Bytes per beat. |
| `AXSIZE` | `$clog2(BYTES_PER_BEAT)` | Value driven on `AWSIZE`. |
| `XFER_MAX` | `min(2^(SCW-1) - 1, 254)` | Largest burst length value the engine will use. |

: Table 2.4.2: AXI Write Engine Derived Constants

---

## Port List

### Clock, Reset and Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | Clock. |
| `rst_n` | input | 1 | Active-low reset. |
| `cfg_axi_wr_xfer_beats` | input | 8 | Configured burst length (AWLEN value, 0 to 255). Clamped to `XFER_MAX`. |
| `cfg_channel_reset` | input | NC | Per-channel reset, level or pulse. Stops new bursts, completes open bursts with null beats, and clears the channel's error flag. |

: Table 2.4.3: Clock, Reset and Configuration

### Scheduler Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_wr_valid` | input | NC | Channel has a write request. |
| `sched_wr_ready` | output | NC | Pulses when the B response of the last burst of a descriptor arrives. |
| `sched_wr_addr` | input | NC x AW | Working destination byte address. |
| `sched_wr_beats` | input | NC x 32 | Beats still to write for the channel. |
| `sched_wr_burst_len` | input | NC x 8 | Requested burst length. Present on the port; the engine sizes bursts from `cfg_axi_wr_xfer_beats` and the 4 KB cap. |
| `sched_wr_done_strobe` | output | NC | Pulses on the AW handshake for the channel. |
| `sched_wr_beats_done` | output | NC x 32 | Beats issued by that AW (`AWLEN + 1`). |
| `sched_wr_commit_strobe` | output | NC | Pulses when the B response for the channel arrives. |
| `sched_wr_commit_beats` | output | NC x 32 | Beats confirmed by that B response, recovered from the B-phase FIFO. |
| `sched_wr_error` | output | NC | Sticky write error for the channel. |

: Table 2.4.4: Scheduler Interface

The done strobe advances the scheduler's destination address, which lets the next AW issue without waiting for a response. The commit strobe is what the scheduler counts when it decides the descriptor is complete. Both strobes are per channel and report beat counts, not bytes.

### SRAM Reservation and Drain Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `axi_wr_drain_req` | output | NC | Pulses for the granted channel on the AW handshake. |
| `axi_wr_drain_size` | output | NC x 8 | Beats to reserve (`AWLEN + 1`). |
| `axi_wr_drain_data_avail` | input | NC x SCW | Data available per channel after reservations. |
| `axi_wr_sram_valid` | input | NC | Per-channel valid, registered. Used for arbitration. |
| `axi_wr_sram_valid_comb` | input | NC | Per-channel valid, combinational. Gates `m_axi_wvalid`. |
| `axi_wr_sram_drain` | output | 1 | Drain request. Equal to `wvalid && wready`. |
| `axi_wr_sram_id` | output | CIW | Channel selected for the drain. |
| `axi_wr_sram_data` | input | DW | Data from the selected channel. |
| `axi_wr_sram_strb` | input | DW/8 | Byte strobes stored with that data beat. New in RAPIDS. |

: Table 2.4.5: SRAM Drain Interface

### AXI4 Write Master Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_awid` | output | IW | Write address ID (the channel). |
| `m_axi_awaddr` | output | AW | Beat-aligned write address. |
| `m_axi_awlen` | output | 8 | Burst length minus one. |
| `m_axi_awsize` | output | 3 | `AXSIZE`, full-width beats. |
| `m_axi_awburst` | output | 2 | INCR. |
| `m_axi_awvalid` | output | 1 | Address valid. |
| `m_axi_awready` | input | 1 | Address ready. |
| `m_axi_wdata` | output | DW | Write data. |
| `m_axi_wstrb` | output | DW/8 | Write strobes, equal to `axi_wr_sram_strb`. |
| `m_axi_wlast` | output | 1 | Last beat of the burst. |
| `m_axi_wuser` | output | UW | Channel of the beat being written. |
| `m_axi_wvalid` | output | 1 | Data valid. |
| `m_axi_wready` | input | 1 | Data ready. |
| `m_axi_bid` | input | IW | Response ID. |
| `m_axi_bresp` | input | 2 | Write response. |
| `m_axi_bvalid` | input | 1 | Response valid. |
| `m_axi_bready` | output | 1 | Response ready. |

: Table 2.4.6: AXI4 Write Master Interface

### Debug and Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `dbg_wr_all_complete` | output | NC | Channel has no outstanding writes. |
| `dbg_aw_transactions` | output | 32 | Total AW handshakes. |
| `dbg_w_beats` | output | 32 | Total W beats. |
| `o_active_channel_id` | output | CIW | Channel whose burst is driving, or about to drive, the W bus. |
| `o_active_channel_valid` | output | 1 | `o_active_channel_id` is meaningful. |

: Table 2.4.7: Debug and Status Outputs

---

## Operation

### Burst Length Cap (rapids BUG-009)

`cfg_axi_wr_xfer_beats` is an AWLEN value, but a burst cannot be larger than the SRAM that stages it: the engine waits for the whole burst to be present before issuing the AW, and a burst the buffer cannot hold would wait forever. The engine clamps the configured value to `XFER_MAX`. Without the clamp an AWLEN of 255 wraps the 8-bit `AWLEN + 1` and the engine issues an AW on an empty buffer. This is the same fix as in RAPIDS Beats.

### Byte-Granular Burst Sizing

The sizing follows the read engine:

1. `w_beats_to_4k` is the distance from the aligned channel address to the next 4 KB boundary, in beats.
2. `w_cap_beats = min(w_xfer_cfg + 1, w_beats_to_4k)`.
3. `w_transfer_size` (the AWLEN) is `sched_wr_beats - 1` if `sched_wr_beats <= w_cap_beats`, otherwise `w_cap_beats - 1`.

A channel may issue when the buffer holds at least `w_transfer_size + 1` beats (`w_has_data`), or when this is the final burst. The final-burst test is `sched_wr_beats > 0`, `sched_wr_beats <= w_cap_beats`, and the available data covers all remaining beats. The 4 KB cap therefore applies to both tests, so a descriptor that ends just past a boundary still finishes on a short final burst.

`m_axi_awaddr` is `{sched_wr_addr[ch][AW-1:AXSIZE], AXSIZE'b0}`. The offset of a descriptor that starts mid-beat never reaches the bus. The first W beat of that descriptor carries `WSTRB` bits only for the bytes at and above the offset, and the last carries only the bytes up to the end of the packet.

### Write Strobes

Each SRAM word holds a data beat and its strobe word side by side (see [Sink Data Path](../ch03_macro_blocks/03_snk_data_path.md)). The write engine takes both from the drain port and presents them together, so the strobe always matches the data. In RAPIDS Beats `WSTRB` was tied high.

### Streaming Pipeline

Each channel with `sched_wr_valid` and a burst that passes the data test requests arbitration. On grant the AW is issued, and on the AW handshake the engine pulses `axi_wr_drain_req` with the burst size so the drain controller reserves the beats. W beats stream from the drain port that `axi_wr_sram_id` selects. `axi_wr_sram_drain` equals `m_axi_wvalid && m_axi_wready`. `m_axi_wlast` closes each burst, and `m_axi_wuser` carries the channel.

With `PIPELINE = 1` a channel may issue further AWs before earlier B responses return, up to `AW_MAX_OUTSTANDING`. With `PIPELINE = 0` the channel waits for each B. That costs throughput, so the top and core default to 1.

### Two Completion Strobes

| Strobe | Raised when | Scheduler use |
|--------|-------------|---------------|
| `sched_wr_done_strobe` | AW handshake for the channel | Advance the destination address and the issued-beat count. |
| `sched_wr_commit_strobe` | B response for the channel | Count committed beats. The descriptor is complete when all beats are committed. |

: Table 2.4.8: Completion Strobes

`sched_wr_ready` is a third, coarser pulse: it fires when the B response belongs to the last burst of a descriptor.

---

## Error Handling

| Error | Detection | Response |
|-------|-----------|----------|
| AXI SLVERR | `m_axi_bresp == 2'b10` | Set sticky `sched_wr_error` for the channel |
| AXI DECERR | `m_axi_bresp == 2'b11` | Set sticky `sched_wr_error` for the channel |
| Any other non-zero response | `m_axi_bresp != 2'b00` | Same: the test is not-OKAY, and the channel is taken from `BID` |

: Table 2.4.9: Error Handling

The sink data path ORs `sched_wr_error` with its own packet-length error before passing it to the scheduler.

### Channel Reset

`cfg_channel_reset[ch]` clears the sticky `sched_wr_error[ch]`, so a channel reset recovers a B-response error without `aresetn`. A burst whose AW has been accepted must still receive all of its W beats, so the engine settles in-flight work rather than dropping it:

- `w_kill[ch]` is the reset level ORed with `r_wr_flush[ch]`. The flush bit is set by the reset and holds until the channel has no open burst and no B response due.
- No new AW is arbitrated for a channel with `w_kill` set. `AWADDR` comes from `sched_wr_addr`, which the scheduler does not clear, so the value on the bus stays stable across the reset.
- An open burst is completed with null W beats: `WSTRB` is zero, `WDATA` repeats the last captured value and the SRAM drain is not popped, so the null beats modify no byte at the destination. A beat that was presented on W and not accepted when the reset hit is the one exception: it is replayed unchanged, with its own strobes, from a captured copy, so the W channel does not change its payload while `WVALID` is high. At most one beat per reset is replayed this way.
- B responses of a channel with `w_kill` set are consumed. The commit strobe, `sched_wr_ready`, the done strobe and the error flag are suppressed for them.
- Other channels are not affected.

The reset therefore leaves no partial state in the engine: the B-phase FIFO drains through the flush, and the channel restarts with clean counters when the scheduler next raises `sched_wr_valid`.

---

## Differences from RAPIDS Beats

| Item | RAPIDS Beats | RAPIDS |
|------|--------------|--------|
| `WSTRB` | All ones | `axi_wr_sram_strb` |
| SRAM drain port | Data only | Data plus strobe word |
| `AWADDR` | Channel address as given (always aligned) | Aligned down to the beat |
| Burst cap and final-burst test | Configured length and remaining beats | Also capped at the 4 KB boundary |
| Everything else | | Unchanged |

: Table 2.4.10: Write Engine Delta

The beats chapter is [AXI Write Engine (RAPIDS Beats)](../../rapids_beats_mas/ch02_fub_blocks/04_axi_write_engine.md). The read-side counterpart is [AXI Read Engine](03_axi_read_engine.md).

---

**Last Updated:** 2026-09-30
