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

# monbus_group_core_1wr

**Module:** `monbus_group_core_1wr.sv`
**Location:** `rtl/amba/ocelus/`
**Status:** New (2026-10-23); simulated, not yet on a board. Wrappers: [monbus_axil4_group_1wr](monbus_axil4_group_1wr.md), [monbus_axi4_group_1wr](monbus_axi4_group_1wr.md)

**Plane:** output plane

---

## Overview

`monbus_group_core_1wr` is `monbus_group_core` with its slave-read side removed. Everything the group accepts is written to memory over **one** AXI4-shaped master-write FUB, but into **two** address windows: packets the per-protocol `err_select` masks pick go to the error window as raw 3-beat records, never compressed; everything else goes to the trace window exactly as `monbus_group_core` writes it (raw records, or compressor slots when `USE_COMPRESSION=1` and `cfg_compress_en` is set).

It exists for systems where the CPU does not walk an error FIFO over a read port: a host that reads the error window out of memory instead, prompted by `irq_out`, which pulses once per whole error record the memory system has acknowledged, with `err_rec_count` counting them. By the time the host sees the pulse, that record is in the window.

### What changed from `monbus_group_core`

| `monbus_group_core` | `monbus_group_core_1wr` |
|---|---|
| Two ports: AXI4-shaped slave-read (`fub_s_*`) for errors, master-write (`fub_m_*`) for trace | One port: master-write (`fub_m_*`) for both |
| Error FIFO holds 192-bit records, sliced into 3 beats by the read port | Error FIFO holds 64-bit beats (`FIFO_DEPTH_ERR` counts beats, three per record) |
| `irq_out` is a level: error records waiting to be read | `irq_out` is a one-cycle pulse per whole error record landed (its B returned), and `err_rec_count` counts them |
| One window: `cfg_base_addr` / `cfg_limit_addr` / `cfg_flush_watermark` | Two windows: the trace window as before, plus `cfg_err_base_addr` / `cfg_err_limit_addr` / `cfg_err_flush_watermark` |
| One burst writer, inline | Two `monbus_burst_writer` instances merged by `monbus_wr_mux2`, errors first |

The filter, the trace path (expander, optional compressor and half-beat packer, write FIFO) and the compressor statistics are the original's. The writer logic is the original's too, lifted into `monbus_burst_writer` unchanged below its port list.

### Key Features

- Single MonBus ingress with per-protocol filter masks (AXI, AXIS, CORE; CXS shares the AXIS masks)
- Error window: raw 3-beat records, own beat FIFO, own watermark and (shorter) timeout flush, priority at the write port
- Trace window: raw records or runtime-selectable compression, as `monbus_group_core`
- One AXI4-shaped master-write FUB: W follows AW order, B credits routed back to the writer that issued the AW
- `irq_out` pulses once per whole error record acknowledged by memory and `err_rec_count` counts them, so a `hwset` W1C status bit latches "an error record landed" and the host knows how many to read

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `FIFO_DEPTH_ERR` | int | 192 | Error FIFO depth in 64-bit beats (three per record, so 64 records) |
| `FIFO_DEPTH_WRITE` | int | 96 | Trace write FIFO depth in 64-bit beats |
| `ADDR_WIDTH` | int | 32 | Address width of the write FUB and both windows |
| `AXI_ID_WIDTH_M` | int | 1 | Write FUB ID width (both writers issue ID 0) |
| `MAX_BURST_BEATS` | int | 1 | Beats per AW: 1 behind an AXIL leaf, up to 256 behind AXI4 |
| `FLUSH_TIMEOUT_CYCLES` | int | 1024 | Trace writer: cycles since the last W before a forced flush |
| `ERR_FLUSH_TIMEOUT_CYCLES` | int | 64 | Error writer: the same, shorter so errors leave promptly |
| `NUM_PROTOCOLS` | int | 3 | Informational |
| `USE_COMPRESSION` | int | 0 | Trace path: 1 builds the compressor and CAM |
| `HALF_BEAT_EN` | int | 0 | Trace path: pack two 30-bit slots per beat (needs `USE_COMPRESSION=1`) |

: Parameters

---

## Ports

Only the ports that differ from `monbus_group_core` are listed; the MonBus input, `mon_time_out`, the FIFO status outputs, the per-protocol masks, `cfg_compress_en`, the compressor statistics and the `fub_m_*` write FUB are unchanged. The `fub_s_*` slave-read FUB does not exist here.

| Port | Dir | Width | Description |
|------|-----|-------|-------------|
| `irq_out` | out | 1 | One-cycle pulse per whole error record landed (all three beats' B returned). Registered. Latch it host-side. |
| `err_rec_count` | out | 16 | Whole error records landed, free-running; the host's read pointer is `cfg_err_base_addr + 24 * (count mod records-per-window)` |
| `err_fifo_count` | out | 16 | Error FIFO occupancy in beats (was records) |
| `cfg_base_addr`, `cfg_limit_addr` | in | `ADDR_WIDTH` | Trace window, inclusive |
| `cfg_flush_watermark` | in | 16 | Trace writer flush threshold, beats |
| `cfg_err_base_addr`, `cfg_err_limit_addr` | in | `ADDR_WIDTH` | Error window, inclusive. Must not overlap the trace window; the core does not check. |
| `cfg_err_flush_watermark` | in | 16 | Error writer flush threshold, beats. 3 flushes every record as it lands. |

: Ports that differ from monbus_group_core

---

## Architecture

```
monbus_valid/packet/ts
        |
        v
   [ filter ]  (monbus_group_core's: pkt_mask / err_select / event masks)
     |      |
     |      +--> pkt_to_err_fifo ---> monbus_record_expander --> err FIFO (64b) --> monbus_burst_writer (err window)  --+
     |                                                                                                                  |
     +--> pkt_to_write_path --> monbus_record_expander ---+                                                             v
                               [monbus_compressor] ------+--> write FIFO (64b) --> monbus_burst_writer (trace window) --> monbus_wr_mux2 --> fub_m_*
                                                                                                                         (errors first)
```

Each window has its own writer, so each has its own running pointer, window budget, 4 KB geometry, watermark and timeout, exactly as the single writer in `monbus_group_core`. The two writers share the port through `monbus_wr_mux2`: fixed priority to the error writer at AW, then W beats in AW order and B credits routed back in AW order. A writer only raises AW for beats already in its FIFO, so a granted burst always completes and the mux's ordering queues cannot deadlock.

`monbus_ready` is asserted when the packet is dropped, or its path's expander (or the compressor skid) takes it this cycle. The error path's acceptance is the expander's beat-0 handshake, so an error record is consumed off MonBus exactly when its first beat enters the error FIFO.

### Memory layout

Both windows carry the same raw record layout as `monbus_group_core`'s trace window: beat 0 is `{tag=4'h0, source_ts[59:0]}`, beat 1 is `packet[127:64]`, beat 2 is `packet[63:0]`, 8-byte stride, records never split across a window wrap or a 4 KB boundary. A host walking the error window reads whole 24-byte records from `cfg_err_base_addr`; `monbus.parse_stream` decodes either window.

### Why the error path is never compressed

A compressed slot is only decodable against the compressor's template CAM state, which is a trace-stream property. Error records are read in isolation by an interrupt handler, so each must stand alone: raw, self-describing, three beats.

---

## Configuration notes

- **Windows must not overlap.** The core writes each window independently; overlapping them interleaves records. By decision nothing checks this: the windows are software-owned, like the single window of `monbus_group_core`.
- **Error watermark.** 3 (one record) is the normal setting: a record is flushed as soon as it lands. Larger values batch records and delay `irq_out`.
- **`irq_out` is a pulse per record, not per burst.** The error writer's sub-bursts do not line up with records (`MAX_BURST_BEATS=1` makes a record three AWs; 16 can end mid-record), so the core keeps the error writer's sub-burst lengths in AW order, pools the beats each B acknowledges, and drains the pool one record per cycle: one pulse and one `err_rec_count` step per record actually in the window. Consecutive records give consecutive-cycle pulses; use a `hwset` W1C bit or read `err_rec_count`, never edge-detect.
- **Error flooding starves trace.** Fixed priority means a sustained error stream holds the port. That is the intent: errors are rare and matter more than trace throughput.

---

## Verification

- The bench is `bin/TBClasses/amba/monbus_group_1wr/monbus_group_1wr_tb.py`, shared by the core and both wrappers. A framework GAXI master in multi-signal mode drives the MonBus ingress, packet and source timestamp on one handshake, gapped by a FlexConfigGen profile; `MonbusGroupHarness`'s multi-outstanding consumer is the write slave, throttled by a FlexRandomizer. Every landed beat is attributed to a window by its burst's AW address, each window is decoded with the shared `parse_stream()` and compared record by record (packet and source timestamp) with what was sent, addresses are checked sequential with wrap, and `irq_out` pulses and `err_rec_count` are checked against the number of error records sent (not bursts).
- `val/amba/test_monbus_group_core_1wr.py` drives the bare core at its FUB. Cells are `TEST_TYPE` (errors_only, trace_only, mixed) by `MAX_BURST_BEATS`; the REG_LEVEL grid is 1 cell at gate, 6 at func (shapes 1 and 16), 9 at full (adds 64), and TEST_LEVEL deepens each cell.
- `val/amba/test_monbus_axil4_group_1wr.py` and `val/amba/test_monbus_axi4_group_1wr.py` run the same bench at each wrapper's external pins; see their pages for the grids.
- `formal/amba/monbus_wr_mux2`: the merge is proven at the ports (see [monbus_wr_mux2](monbus_wr_mux2.md)).
- The writer's own proof is `formal/amba/monbus_group_core`, over the inline copy in `monbus_group_core`; `monbus_burst_writer` is that text below its port list and has no separate harness yet.

---

## Related

- [monbus_group_core](monbus_group_core.md): the two-port original; filter, trace path and writer semantics are documented there in full
- [monbus_burst_writer](monbus_burst_writer.md), [monbus_wr_mux2](monbus_wr_mux2.md), [monbus_record_expander](monbus_record_expander.md): the three blocks this core is assembled from
- [monbus_axil4_group_1wr](monbus_axil4_group_1wr.md), [monbus_axi4_group_1wr](monbus_axi4_group_1wr.md): the protocol wrappers; instantiate one of these, not the bare core
- [monbus_compressor](monbus_compressor.md): the trace path's optional encoder
- `rtl/amba/filelists/monbus_group_core_1wr.f`
