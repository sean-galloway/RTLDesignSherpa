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

# monbus_group_core

**Module:** `monbus_group_core.sv`
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

The `monbus_group_core` module is the protocol-agnostic heart of the `monbus_*_*_group` family. It receives a single monitor-bus (MonBus) stream plus a side-band timestamp, applies per-protocol filter masks, and routes each accepted packet into one of two destinations: a record-granular error/interrupt FIFO drained over an AXI4-shaped slave-read port, or a beat-granular write FIFO drained over an AXI4-shaped master-write port with watermark and timeout flushing.

This core is the single source of truth for filtering, FIFO management, optional compression, and the burst writer/slicer state machines. The `monbus_<p1>_<p2>_group.sv` wrappers are pure structural adapters — they bridge its two AXI4-shaped FUB ports into protocol-specific leaf skids, and nothing more.

### Key Features

- Single MonBus ingress with per-protocol filter masks (AXI, AXIS, CORE)
- Free-running timestamp generator distributed to every monitor (`mon_time_out`)
- Error/interrupt FIFO: record-granular (192-bit records = 128-bit packet + 64-bit timestamp)
- Write FIFO: beat-granular (one entry = one 64-bit beat)
- AXI4-shaped slave-read drain with burst AR support and a 3-slice record slicer
- AXI4-shaped master-write burst writer with address-window, 4KB, and watermark controls
- Runtime-selectable compression (`cfg_compress_en`) with optional half-beat packing
- Raw mode emits complete 24-byte (3-beat) records; compressed mode emits self-tagged 8-byte slots
- Timing-closed 3-stage geometry pipeline for burst planning at 100 MHz

Aggregated monitor packets have to serve two consumers with very different needs: a CPU interrupt handler that walks recent error records, and a bulk-capture memory buffer that stores a long trace. This core splits the filtered stream between an error FIFO (read on demand by an IRQ handler) and a write FIFO (flushed to memory as AXI bursts), and handles all the address arithmetic, record framing, and optional compression in one place.

**Use Cases:**
- Central MonBus capture block behind `monbus_arbiter` in an SoC monitoring subsystem
- Streaming error records to a CPU IRQ handler while bulk-capturing a full trace to DRAM
- Compressed trace capture to fit more monitor history in a fixed buffer
- Building protocol-specific group wrappers (AXI4/AXI4, AXI4/AXIL, AXIL/AXI4, AXIL/AXIL) on a shared core

**Key Benefit:** All the hard logic — filtering, dual-FIFO routing, burst geometry, compression — lives once in this core. The four protocol-pair wrappers reduce to thin structural adapters, so a bug fix or feature lands in one file for every group.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `FIFO_DEPTH_ERR` | int | 64 | Error FIFO depth in 192-bit records |
| `FIFO_DEPTH_WRITE` | int | 96 | Write FIFO depth in 64-bit beats (beat-granular) |
| `ADDR_WIDTH` | int | 32 | Address width for both FUB ports |
| `AXI_ID_WIDTH_M` | int | 1 | Master-write ID width (1 in AXIL builds) |
| `AXI_ID_WIDTH_S` | int | 1 | Slave-read ID width (1 in AXIL builds) |
| `MAX_BURST_BEATS` | int | 1 | Max beats per master-write sub-burst (1 for AXIL, up to 256 for AXI4) |
| `FLUSH_TIMEOUT_CYCLES` | int | 1024 | Cycles since last accepted W beat before forcing a flush |
| `NUM_PROTOCOLS` | int | 3 | Informational only |
| `USE_COMPRESSION` | int | 0 | 0 = raw 3-beat records only; 1 = elaborate the compressor hardware |
| `HALF_BEAT_EN` | int | 0 | 1 = pack two 30-bit half-slots per beat (requires `USE_COMPRESSION==1`) |

---

## Ports

### Clock, Reset, and Clear

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `axi_aclk` | input | 1 | Core clock |
| `axi_aresetn` | input | 1 | Active-low asynchronous reset |
| `cam_clear` | input | 1 | Synchronous clear of the compressor template CAM + stats (no effect when `USE_COMPRESSION==0`); pulse when idle |

### MonBus Ingress and Timestamp

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `monbus_valid` | input | 1 | Incoming packet valid |
| `monbus_ready` | output | 1 | Core ready to accept the packet |
| `monbus_packet` | input | `monitor_packet_t` (128) | Monitor packet |
| `monbus_timestamp` | input | `monbus_timestamp_t` (64) | Side-band timestamp for the packet |
| `mon_time_out` | output | `monbus_timestamp_t` (64) | Free-running counter; drive to every wrapper's `i_mon_time` |

### Status / IRQ / Debug

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `irq_out` | output | 1 | Asserted while the error FIFO is non-empty |
| `err_fifo_full` | output | 1 | Error FIFO cannot accept a write |
| `write_fifo_full` | output | 1 | Write FIFO cannot accept a beat |
| `err_fifo_count` | output | 16 | Error FIFO occupancy (records) |
| `write_fifo_count` | output | 16 | Write FIFO occupancy (beats) |

### Address Window and Flush Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_base_addr` | input | ADDR_WIDTH | Base address of the master-write capture window |
| `cfg_limit_addr` | input | ADDR_WIDTH | Inclusive limit address of the capture window |
| `cfg_flush_watermark` | input | 16 | Beat count in the write FIFO that triggers a flush burst |
| `cfg_compress_en` | input | 1 | Runtime compression select (meaningful only when `USE_COMPRESSION==1`); hold stable while the write path is active |

### Per-Protocol Filter Masks

Three protocol groups (AXI = protocol 0, AXIS = protocol 1, CORE = protocol 4), each with a packet-drop mask, an error-select mask, and per-packet-type event masks. All are 16 bits.

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_axi_pkt_mask` | input | 16 | AXI: per-packet-type drop mask (bit = packet type) |
| `cfg_axi_err_select` | input | 16 | AXI: per-packet-type route-to-error-FIFO select |
| `cfg_axi_error_mask` | input | 16 | AXI: per-event-code mask for Error packets |
| `cfg_axi_timeout_mask` | input | 16 | AXI: per-event-code mask for Timeout packets |
| `cfg_axi_compl_mask` | input | 16 | AXI: per-event-code mask for Completion packets |
| `cfg_axi_thresh_mask` | input | 16 | AXI: per-event-code mask for Threshold packets |
| `cfg_axi_perf_mask` | input | 16 | AXI: per-event-code mask for Perf packets |
| `cfg_axi_addr_mask` | input | 16 | AXI: per-event-code mask for AddrMatch packets |
| `cfg_axi_debug_mask` | input | 16 | AXI: per-event-code mask for Debug packets |
| `cfg_axis_pkt_mask` | input | 16 | AXIS: per-packet-type drop mask |
| `cfg_axis_err_select` | input | 16 | AXIS: per-packet-type route-to-error-FIFO select |
| `cfg_axis_error_mask` | input | 16 | AXIS: per-event-code mask for Error packets |
| `cfg_axis_timeout_mask` | input | 16 | AXIS: per-event-code mask for Timeout packets |
| `cfg_axis_compl_mask` | input | 16 | AXIS: per-event-code mask for Completion packets |
| `cfg_axis_credit_mask` | input | 16 | AXIS: per-event-code mask for Credit packets |
| `cfg_axis_channel_mask` | input | 16 | AXIS: per-event-code mask for Channel packets |
| `cfg_axis_stream_mask` | input | 16 | AXIS: per-event-code mask for Stream packets |
| `cfg_core_pkt_mask` | input | 16 | CORE: per-packet-type drop mask |
| `cfg_core_err_select` | input | 16 | CORE: per-packet-type route-to-error-FIFO select |
| `cfg_core_error_mask` | input | 16 | CORE: per-event-code mask for Error packets |
| `cfg_core_timeout_mask` | input | 16 | CORE: per-event-code mask for Timeout packets |
| `cfg_core_compl_mask` | input | 16 | CORE: per-event-code mask for Completion packets |
| `cfg_core_thresh_mask` | input | 16 | CORE: per-event-code mask for Threshold packets |
| `cfg_core_perf_mask` | input | 16 | CORE: per-event-code mask for Perf packets |
| `cfg_core_debug_mask` | input | 16 | CORE: per-event-code mask for Debug packets |

### Compressor Statistics

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `mon_compressor_stat_tier1_a` | output | 32 | Tier-1 compression counter A (0 in raw mode) |
| `mon_compressor_stat_tier1_b` | output | 32 | Tier-1 compression counter B |
| `mon_compressor_stat_tier1_c` | output | 32 | Tier-1 compression counter C |
| `mon_compressor_stat_tier0` | output | 32 | Tier-0 (raw escape) count |
| `mon_compressor_stat_cam_miss` | output | 32 | Template CAM miss count |
| `mon_compressor_stat_delta_ts_ovf` | output | 32 | Delta-timestamp overflow count |
| `mon_compressor_stat_event_data_ovf` | output | 32 | Event-data overflow count |
| `mon_compressor_stat_ed_delta_ovf` | output | 32 | Event-data-delta overflow count |

### AXI4-Shaped Master-Write FUB (bulk capture)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `fub_m_awid` | output | AXI_ID_WIDTH_M | Write address ID (driven to 0) |
| `fub_m_awaddr` | output | ADDR_WIDTH | Write burst start address |
| `fub_m_awlen` | output | 8 | Sub-burst length (beats − 1) |
| `fub_m_awsize` | output | 3 | Fixed 3 (8 bytes/beat) |
| `fub_m_awburst` | output | 2 | Fixed INCR (2'b01) |
| `fub_m_awvalid` | output | 1 | AW valid |
| `fub_m_awready` | input | 1 | AW ready |
| `fub_m_wdata` | output | 64 | Write beat data (from write FIFO) |
| `fub_m_wstrb` | output | 8 | Write strobes (fixed 8'hFF) |
| `fub_m_wlast` | output | 1 | Last beat of the sub-burst |
| `fub_m_wvalid` | output | 1 | W valid |
| `fub_m_wready` | input | 1 | W ready |
| `fub_m_bid` | input | AXI_ID_WIDTH_M | Write response ID (ignored) |
| `fub_m_bresp` | input | 2 | Write response (ignored) |
| `fub_m_bvalid` | input | 1 | B valid |
| `fub_m_bready` | output | 1 | B ready |

### AXI4-Shaped Slave-Read FUB (error drain)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `fub_s_arid` | input | AXI_ID_WIDTH_S | Read address ID |
| `fub_s_araddr` | input | ADDR_WIDTH | Read address (unused; drain is a stream) |
| `fub_s_arlen` | input | 8 | Burst length (beats − 1) |
| `fub_s_arsize` | input | 3 | Burst size (unused; always 64-bit) |
| `fub_s_arburst` | input | 2 | Burst type (unused; always INCR) |
| `fub_s_arvalid` | input | 1 | AR valid |
| `fub_s_arready` | output | 1 | AR ready (accepts only when idle) |
| `fub_s_rid` | output | AXI_ID_WIDTH_S | Read data ID (echoes burst ID) |
| `fub_s_rdata` | output | 64 | Sliced record beat |
| `fub_s_rresp` | output | 2 | Read response (fixed OKAY) |
| `fub_s_rlast` | output | 1 | Last beat of the burst |
| `fub_s_rvalid` | output | 1 | R valid |
| `fub_s_rready` | input | 1 | R ready |

---

## Functional Description

### Free-Running Timestamp

A counter (`r_ts_counter`) increments every clock and is exposed as `mon_time_out`. Every monitor wrapper drives its `i_mon_time` from this output, so all packets across the group share one time base.

### Packet Filtering

Each incoming packet is decomposed into `pkt_type`, `pkt_protocol` (bits [108:105]), and `pkt_event_code`. Filtering runs in three tiers per protocol:

1. **Drop mask** (`cfg_*_pkt_mask[pkt_type]`) — if set, the packet is dropped outright.
2. **Error-select** (`cfg_*_err_select[pkt_type]`) — if set (and not dropped), the packet routes to the error FIFO; otherwise it routes to the write path.
3. **Event mask** — when the event code's high nibble is 0 (`ec_in_mask_range`), the low nibble indexes a per-packet-type event mask; a set bit forces a drop and clears the error-FIFO routing.

An unrecognized protocol drops the packet. The final routing decision is `pkt_to_write_path = !pkt_drop && !pkt_to_err_fifo`.

### Error FIFO and Slave-Read Drain

Accepted error packets are stored as 192-bit records `{timestamp, packet}` in `u_err_fifo`, and `irq_out` asserts whenever the FIFO is non-empty. The slave-read drain presents each record as three 64-bit slices over a burst read:

- slice 0 = `{tag=4'h0, source_ts[59:0]}`
- slice 1 = `packet[127:64]`
- slice 2 = `packet[63:0]` (record is popped here)

AR is accepted whenever no burst is in flight (`fub_s_arready = !r_rd_in_burst`) — there is no slice-position or FIFO-occupancy condition. That has two consequences worth knowing before you write the driver: an AR on an empty FIFO is accepted and `rvalid` simply stalls until a record arrives, and `rvalid` drops mid-burst if the FIFO underruns, resuming when a new record shows up. `rlast` asserts on the `(arlen+1)`-th beat. Size `arlen` as a multiple of 3 minus one so the burst lands cleanly on record boundaries.

### Write Path — Raw Expander vs Compressor

Two producers feed the beat-granular write FIFO, selected at runtime by `w_use_comp = (USE_COMPRESSION != 0) && cfg_compress_en`:

- **Raw expander** (always elaborated): a 3-state FSM (`EXP_TS`/`EXP_HI`/`EXP_LO`) pushes `{ts, pkt_hi, pkt_lo}` beats atomically — a record is never split across backpressure. It uses per-beat `wr_ready` rather than a "3 slots free" precheck, because the precheck would build a count → valid → count combinational loop.
- **Compressor** (elaborated only when `USE_COMPRESSION==1`): `monbus_compressor` sits between the input and the FIFO, emitting one self-tagged 64-bit slot per record. A 2-deep input skid registers `(source_ts, packet)` right at the compressor boundary so the route-dominated aggregator → CAM path ends at a local flop (+1 cycle latency, throughput preserved, slot stream bit-exact). When `HALF_BEAT_EN==1`, `monbus_halfbeat_packer` packs two 30-bit half-slots per beat downstream of the compressor.

Only one path is active at a time; the two FIFO-write outputs are muxed by `w_use_comp`. `monbus_ready` is driven by whichever path accepted the packet (drop, error-FIFO write ready, or write-path term).

### Master-Write Burst Writer

The write FIFO is flushed to memory as AXI4 bursts. A flush fires when either the FIFO occupancy reaches `cfg_flush_watermark` or `FLUSH_TIMEOUT_CYCLES` elapse since the last accepted W beat — and at least one whole record (`BEATS_PER_UNIT`, 3 in raw mode, 1 compressed) is available.

Burst length is bounded by the minimum of FIFO occupancy, `MAX_BURST_BEATS`, distance to `cfg_limit_addr`, and distance to the next 4KB boundary, then rounded down to whole records. The address arithmetic is pipelined over 3 registered stages — the plan trails `r_wr_addr`, which moves in `WR_IDLE` (at each drain commit and on the rewind-snap and base-step-over branches) — keeping the wide window/4KB/round-to-record chain off the 100 MHz critical path. The fresh FIFO-occupancy cap is applied combinationally at commit, so a stale count cannot short the burst. The mod-3 whole-record rounding uses `math_mod_3_compress` carry-save instances rather than a wide divider.

The writer FSM (`WR_IDLE` → `WR_AW` → `WR_W` → `WR_B`) emits as many AW + N×W + B sub-bursts as needed to drain the planned beat count, advancing the address one 8-byte beat per accepted W. When the current window/4KB region cannot fit a whole record, the writer rewinds `r_wr_addr` to `cfg_base_addr` and re-settles the geometry pipeline.

---

## Usage Example

You don't instantiate `monbus_group_core` directly — the group wrappers do. A wrapper connects the two AXI4-shaped FUBs to protocol leaves:

```systemverilog
monbus_group_core #(
    .FIFO_DEPTH_ERR       (64),
    .FIFO_DEPTH_WRITE     (96),
    .ADDR_WIDTH           (32),
    .AXI_ID_WIDTH_M       (8),
    .AXI_ID_WIDTH_S       (8),
    .MAX_BURST_BEATS      (64),      // AXI4 build; use 1 for AXIL master-write
    .FLUSH_TIMEOUT_CYCLES (1024),
    .USE_COMPRESSION      (0)
) u_core (
    .axi_aclk    (axi_aclk),
    .axi_aresetn (axi_aresetn),
    .cam_clear   (cam_clear),

    .monbus_valid     (monbus_valid),
    .monbus_ready     (monbus_ready),
    .monbus_packet    (monbus_packet),
    .monbus_timestamp (monbus_timestamp),
    .mon_time_out     (mon_time_out),

    .cfg_base_addr       (cfg_base_addr),
    .cfg_limit_addr      (cfg_limit_addr),
    .cfg_flush_watermark (cfg_flush_watermark),
    .cfg_compress_en     (cfg_compress_en),
    // ... per-protocol masks ...

    // AXI4-shaped master-write FUB -> axi4_master_wr leaf
    .fub_m_awaddr (wr_fub_awaddr), .fub_m_awlen (wr_fub_awlen),
    .fub_m_awvalid(wr_fub_awvalid), .fub_m_awready(wr_fub_awready),
    .fub_m_wdata  (wr_fub_wdata),  .fub_m_wlast (wr_fub_wlast),
    // ...

    // AXI4-shaped slave-read FUB <- axi4_slave_rd leaf
    .fub_s_arlen  (rd_fub_arlen),  .fub_s_arvalid(rd_fub_arvalid),
    .fub_s_rdata  (rd_fub_rdata),  .fub_s_rlast (rd_fub_rlast)
    // ...
);
```

---

## Design Notes

### Hold `cfg_compress_en` Stable

`cfg_compress_en` changes both the record framing (raw 3-beat vs compressed 1-beat) and `BEATS_PER_UNIT`. Flip it mid-stream and you mix formats in the write FIFO, which corrupts burst sizing. Program it once before monitoring starts.

### AXIL Builds Use the Same Core

AXIL group wrappers instantiate this same AXI4-shaped core with `MAX_BURST_BEATS=1` and ID widths of 1, supplying single-beat defaults (len=0, size=$clog2(8), INCR, id=0) at the leaf. There is no AXIL-specific variant of the core, and there doesn't need to be.

### FIFO Granularity Difference

The error FIFO is record-granular (192-bit); the write FIFO is beat-granular (64-bit). `err_fifo_count` reports records while `write_fifo_count` reports beats — don't compare them directly.

### Timing-Motivated Structure

Several structural choices exist purely to close 100 MHz timing: the 3-stage geometry pipeline, local registering of `cfg_base_addr`/`cfg_limit_addr` with a `max_fanout` cap, the registered raw FIFO count shared by both the flush trigger and the burst cap, and the compressor input skid. A prior split (fresh trigger against a lagged cap) shorted bursts to 21/24 beats — both now derive from the same registered count.

### 4KB and Window Compliance

The burst is always sized so its last byte stays at or below `cfg_limit_addr` and never crosses a 4KB boundary, satisfying AXI4 addressing rules without mid-burst wrapping.

---

## Related Modules

### Used By
- **monbus_axi4_axi4_group.sv** — AXI4 slave-read + AXI4 master-write wrapper
- **monbus_axi4_axil_group.sv** — AXI4 slave-read + AXIL master-write wrapper
- **monbus_axil_axi4_group.sv** — AXIL slave-read + AXI4 master-write wrapper
- **monbus_axil_axil_group.sv** — AXIL slave-read + AXIL master-write wrapper

### Uses
- **gaxi_fifo_sync.sv** — error FIFO and write FIFO
- **gaxi_skid_buffer.sv** — compressor input skid
- **monbus_compressor.sv** — optional packet compressor (present when `USE_COMPRESSION==1`)
- **monbus_halfbeat_packer.sv** — optional half-beat packer (`HALF_BEAT_EN==1`)
- **math_mod_3_compress.sv** (`rtl/math/`) — carry-save mod-3 for whole-record rounding
- **monitor_common_pkg** — packet types, protocols, `monitor_packet_t`, `monbus_timestamp_t`

### See Also
- **monbus_arbiter.sv** — aggregates multiple monitor streams upstream of this core
- **monbus_group.md** — group-level overview

---

## References

### Source Code
- RTL: `rtl/amba/monitor/monbus_group_core.sv`
- Package: `rtl/amba/includes/monitor_common_pkg.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Compressor: `docs/markdown/rtl-amba/monitor/monbus_compressor.md`
- Packet Format: `docs/markdown/rtl-amba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](../_book_monitor_index.md)
- [Back to rtl-amba Index](../index.md)
