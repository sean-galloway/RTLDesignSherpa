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

# monbus_burst_writer

**Module:** `monbus_burst_writer.sv`
**Location:** `rtl/amba/ocelus/`
**Status:** New (2026-10-23); the writer text of `monbus_group_core`, lifted out

**Plane:** output plane

---

## Overview

`monbus_burst_writer` drains a 64-bit beat-granular FIFO into an address window `[cfg_base_addr, cfg_limit_addr]` as AXI4 INCR bursts. It is the continuous, FSM-free burst writer of `monbus_group_core` (the amba BUG-039 redesign) with the FIFO and the configuration turned into ports, so that `monbus_group_core_1wr` can run one per address window behind a single port. Below its port list the text is the original's; `monbus_group_core` keeps its inline copy because that copy is timing-closed and formally proven, and the two are meant to stay identical.

What it does, in the original's terms: an AW issues whenever a flush trigger (watermark or timeout) holds and at least one whole record is in the FIFO, an outstanding slot is free, and the window geometry allows a whole record from the running pointer; batches of sub-bursts run back to back; W streams the FIFO in AW order; B is a pure credit return. Records are never split across a window wrap or a 4 KB boundary, and a burst is only ever planned from beats already in the FIFO. The full account, with the epoch model and the pointer discipline, is in [monbus_group_core](monbus_group_core.md).

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `ADDR_WIDTH` | int | 32 | Address width |
| `AXI_ID_WIDTH_M` | int | 1 | Write FUB ID width (always issues ID 0) |
| `MAX_BURST_BEATS` | int | 1 | Beats per AW: 1 behind an AXIL leaf, up to 256 behind AXI4 |
| `FLUSH_TIMEOUT_CYCLES` | int | 1024 | Cycles since the last W handshake, with beats queued, before a forced flush |

: Parameters

---

## Ports

| Port | Dir | Width | Description |
|------|-----|-------|-------------|
| `axi_aclk`, `axi_aresetn` | in | 1 | Clock, active-low async reset |
| `fifo_rd_valid` | in | 1 | FIFO not empty |
| `fifo_rd_ready` | out | 1 | FIFO pop (the W handshake) |
| `fifo_rd_data` | in | 64 | Head beat |
| `fifo_beat_count` | in | 16 | Live FIFO occupancy in beats, zero-extended; the writer registers it itself |
| `beats_per_unit` | in | 16 | Record size: 3 for raw records, 1 for compressed slots. Hold stable while beats are queued. |
| `cfg_base_addr`, `cfg_limit_addr` | in | `ADDR_WIDTH` | Window, inclusive; a change is adopted at the next epoch boundary |
| `cfg_flush_watermark` | in | 16 | Flush when the registered beat count reaches this |
| `fub_m_aw*`, `fub_m_w*`, `fub_m_b*` | | | AXI4-shaped write FUB: 8-byte INCR, `wstrb` all ones, `awid` 0, `bid`/`bresp` ignored |
| `f_*` | out | | Formal-only probes of the counters (`ifdef FORMAL`), the same set the original exposes |

: Ports

---

## Behaviour

Identical to the inline writer of `monbus_group_core`; the only textual differences are the port names and that `beats_per_unit` arrives as an input (the original derives it from `cfg_compress_en`). With `beats_per_unit == 1` the whole-record rounding on every cap folds away, as in the original's compressed mode.

Up to four sub-bursts may be outstanding (`WR_OS_CAP`); `fub_m_bready` is high while any is. The B order is the AW order, which AXI4 guarantees for a single ID.

---

## Verification

The proof over this logic is `formal/amba/monbus_group_core` (the inline copy). No separate harness yet; the lifted module is exercised end to end by `val/amba/test_monbus_group_core_1wr.py` at `MAX_BURST_BEATS` 1 and 16. The lint gate is `make -C rtl/amba verilator-monbus_burst_writer`.

---

## Related

- [monbus_group_core](monbus_group_core.md): the original, with the writer's design rationale
- [monbus_group_core_1wr](monbus_group_core_1wr.md): two of these behind [monbus_wr_mux2](monbus_wr_mux2.md)
- `rtl/amba/filelists/monbus_burst_writer.f`
