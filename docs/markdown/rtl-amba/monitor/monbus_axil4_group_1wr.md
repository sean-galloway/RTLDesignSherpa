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

# monbus_axil4_group_1wr

**Module:** `monbus_axil4_group_1wr.sv`
**Location:** `rtl/amba/ocelus/`
**Status:** New (2026-10-23); simulated, not yet on a board

**Plane:** output plane

---

## Overview

`monbus_axil4_group_1wr` is the AXI4-Lite wrapper of [monbus_group_core_1wr](monbus_group_core_1wr.md): the single-write-port group core behind an `axil4_master_wr` leaf. It has one external bus, the `m_axil_*` master-write port, and no slave-read side. Error-selected packets land in the error window as raw 3-beat records, everything else in the trace window, and the host is told about error records by `irq_out` and `err_rec_count` rather than by walking a FIFO over a read port.

The leaf is single-beat, so the core's `MAX_BURST_BEATS` is forced to 1 and every record is three AXIL writes at 8-byte stride. The AXI4 fields the core drives (`awid`, `awlen`, `awsize`, `awburst`, `wlast`) stop at the wrapper; AXIL has no use for them.

Use it where the memory ring sits behind an AXIL fabric and the CPU reads error records out of memory. Its two-port counterpart is [monbus_axil4_axil4_group](monbus_axil4_axil4_group.md); its burst sibling is [monbus_axi4_group_1wr](monbus_axi4_group_1wr.md).

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `FIFO_DEPTH_ERR` | int | 192 | Error FIFO depth in beats (three per record) |
| `FIFO_DEPTH_WRITE` | int | 96 | Trace write FIFO depth in beats |
| `ADDR_WIDTH` | int | 32 | Address width of the write port and both windows |
| `FLUSH_TIMEOUT_CYCLES` | int | 1024 | Trace writer: cycles since the last W before a forced flush |
| `ERR_FLUSH_TIMEOUT_CYCLES` | int | 64 | Error writer: the same, shorter |
| `NUM_PROTOCOLS` | int | 3 | Informational |
| `USE_COMPRESSION` | int | 0 | Trace path: 1 builds the compressor and CAM |
| `HALF_BEAT_EN` | int | 0 | Trace path: pack two 30-bit slots per beat (needs `USE_COMPRESSION=1`) |
| `SKID_DEPTH_AW`, `SKID_DEPTH_W`, `SKID_DEPTH_B` | int | 2, 2, 2 | Leaf skid depths; nothing to absorb at one beat per AW |

: Parameters

There is no `MAX_BURST_BEATS` (forced to 1) and no `S_AXIL_DATA_WIDTH` (no read port).

---

## Ports

| Port | Dir | Width | Description |
|------|-----|-------|-------------|
| `axi_aclk`, `axi_aresetn` | in | 1 | Clock, active-low async reset |
| `cam_clear` | in | 1 | Synchronous compressor CAM and statistics clear |
| `monbus_valid`, `monbus_ready`, `monbus_packet`, `monbus_timestamp` | | | MonBus ingress, as every group |
| `mon_time_out` | out | 64 | Free-running timestamp |
| `m_axil_aw*`, `m_axil_w*`, `m_axil_b*` | | | AXI4-Lite master write, 64-bit data, `awprot` 0, `wstrb` all ones |
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

Everything observable is the core's; see [monbus_group_core_1wr](monbus_group_core_1wr.md) for the window rules, the error-first merge and the `irq_out` contract. At this wrapper's pins each record is three single-beat writes, and the error writer's records interleave with trace writes at the AW level, errors first. The two windows must not overlap; by decision nothing checks this.

---

## Verification

`val/amba/test_monbus_axil4_group_1wr.py` runs the family bench (`bin/TBClasses/amba/monbus_group_1wr/`, described on the [core page](monbus_group_core_1wr.md)) at the `m_axil_*` pins through the harness's AXIL consumer, where every burst is one beat. Cells are `TEST_TYPE` (errors_only, trace_only, mixed) by `FIFO_DEPTH_ERR`: 1 cell at gate, 3 at func, 6 at full, where a 24-beat error FIFO (8 records) makes the error path backpressure the ingress. TEST_LEVEL deepens each cell. Lint: `make -C rtl/amba verilator-monbus_axil4_group_1wr`.

---

## Related

- [monbus_group_core_1wr](monbus_group_core_1wr.md): the core
- [monbus_axi4_group_1wr](monbus_axi4_group_1wr.md): the AXI4 burst sibling
- [monbus_axil4_axil4_group](monbus_axil4_axil4_group.md): the two-port AXIL group
- `rtl/amba/filelists/monbus_axil4_group_1wr.f`
