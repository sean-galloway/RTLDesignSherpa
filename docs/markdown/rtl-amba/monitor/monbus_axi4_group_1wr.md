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

# monbus_axi4_group_1wr

**Module:** `monbus_axi4_group_1wr.sv`
**Location:** `rtl/amba/ocelus/`
**Status:** New (2026-10-23); simulated, not yet on a board

**Plane:** output plane

---

## Overview

`monbus_axi4_group_1wr` is the AXI4 wrapper of [monbus_group_core_1wr](monbus_group_core_1wr.md): the single-write-port group core behind an `axi4_master_wr` leaf. It has one external bus, the `m_axi_*` burst master-write port, and no slave-read side. Error-selected packets land in the error window as raw 3-beat records, everything else in the trace window, and the host is told about error records by `irq_out` and `err_rec_count`.

The core's AXI4-shaped write FUB drives the leaf straight through. The fields the core does not produce are tied at the leaf boundary: `awlock` 0, `awcache` 0010 (normal non-cacheable bufferable), `awprot` 0, `awqos` 0, `awregion` 0, `awuser` and `wuser` 0. Both of the core's writers issue `awid` 0, which the AW-ordered merge inside the core relies on; `bid` and `buser` are ignored.

Use it where the memory ring sits behind an AXI4 fabric and records should be bunched into bursts. Its two-port counterpart is [monbus_axil4_axi4_group](monbus_axil4_axi4_group.md); its single-beat sibling is [monbus_axil4_group_1wr](monbus_axil4_group_1wr.md).

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `FIFO_DEPTH_ERR` | int | 192 | Error FIFO depth in beats (three per record) |
| `FIFO_DEPTH_WRITE` | int | 96 | Trace write FIFO depth in beats |
| `ADDR_WIDTH` | int | 32 | Address width of the write port and both windows |
| `AXI_ID_WIDTH` | int | 8 | Write ID width; the port always issues ID 0 |
| `AXI_USER_WIDTH` | int | 1 | User-signal width; driven 0 |
| `MAX_BURST_BEATS` | int | 64 | Beats per AW, up to 256; both writers use it |
| `FLUSH_TIMEOUT_CYCLES` | int | 1024 | Trace writer: cycles since the last W before a forced flush |
| `ERR_FLUSH_TIMEOUT_CYCLES` | int | 64 | Error writer: the same, shorter |
| `NUM_PROTOCOLS` | int | 3 | Informational |
| `USE_COMPRESSION` | int | 0 | Trace path: 1 builds the compressor and CAM |
| `HALF_BEAT_EN` | int | 0 | Trace path: pack two 30-bit slots per beat (needs `USE_COMPRESSION=1`) |
| `SKID_DEPTH_AW`, `SKID_DEPTH_W`, `SKID_DEPTH_B` | int | 2, 4, 2 | Leaf skid depths; W at 4 to absorb burst traffic |

: Parameters

---

## Ports

| Port | Dir | Width | Description |
|------|-----|-------|-------------|
| `axi_aclk`, `axi_aresetn` | in | 1 | Clock, active-low async reset |
| `cam_clear` | in | 1 | Synchronous compressor CAM and statistics clear |
| `monbus_valid`, `monbus_ready`, `monbus_packet`, `monbus_timestamp` | | | MonBus ingress, as every group |
| `mon_time_out` | out | 64 | Free-running timestamp |
| `m_axi_aw*`, `m_axi_w*`, `m_axi_b*` | | | Full AXI4 master write, 64-bit data, INCR, 8-byte beats, `wstrb` all ones |
| `irq_out` | out | 1 | One-cycle pulse per whole error record landed. Latch it host-side with a `hwset` W1C bit. |
| `err_rec_count` | out | 16 | Whole error records landed, free-running |
| `cfg_base_addr`, `cfg_limit_addr`, `cfg_flush_watermark` | in | | Trace window and flush threshold (beats) |
| `cfg_err_base_addr`, `cfg_err_limit_addr`, `cfg_err_flush_watermark` | in | | Error window and flush threshold (beats; 3 flushes every record) |
| `cfg_compress_en` | in | 1 | Trace path compression enable (`USE_COMPRESSION=1` builds) |
| `cfg_axi_*`, `cfg_axis_*`, `cfg_core_*` | in | 16 each | Per-protocol filter masks, as every group |
| `err_fifo_full`, `write_fifo_full`, `err_fifo_count`, `write_fifo_count` | out | | FIFO status, counts in beats |
| `mon_compressor_stat_*` | out | 32 each | Compressor statistics |

: Ports

---

## Behaviour

Everything observable is the core's; see [monbus_group_core_1wr](monbus_group_core_1wr.md) for the window rules, the error-first merge and the `irq_out` contract. At this wrapper's pins the error writer's bursts and the trace writer's bursts share one ID and one ordered W stream: a burst's W beats follow its AW, and B returns in AW order. Records are never split across a window wrap or a 4 KB boundary, so a burst may be shorter than `MAX_BURST_BEATS`. The two windows must not overlap; by decision nothing checks this.

---

## Verification

`val/amba/test_monbus_axi4_group_1wr.py` runs the family bench (`bin/TBClasses/amba/monbus_group_1wr/`, described on the [core page](monbus_group_core_1wr.md)) at the `m_axi_*` pins. Every burst's beat count must match its `awlen` with `wlast` on the final beat only. Cells are `TEST_TYPE` (errors_only, trace_only, mixed) by `MAX_BURST_BEATS`: 1 cell at gate, 6 at func (16 and the default 64), 9 at full (adds the AXI4 maximum 256). TEST_LEVEL deepens each cell. Lint: `make -C rtl/amba verilator-monbus_axi4_group_1wr`.

---

## Related

- [monbus_group_core_1wr](monbus_group_core_1wr.md): the core
- [monbus_axil4_group_1wr](monbus_axil4_group_1wr.md): the AXIL single-beat sibling
- [monbus_axil4_axi4_group](monbus_axil4_axi4_group.md): the two-port AXI4-write group
- `rtl/amba/filelists/monbus_axi4_group_1wr.f`
