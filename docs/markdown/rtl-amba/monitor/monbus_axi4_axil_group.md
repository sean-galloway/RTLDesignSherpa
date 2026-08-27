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

# MonBus Group — AXI4 / AXIL

**Module:** `monbus_axi4_axil_group.sv`
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

The `monbus_axi4_axil_group` module is the AXI4-slave-read + AXIL-master-write wrapper around `monbus_group_core`. It pairs a full AXI4 slave-read leaf (the burst-capable error/interrupt drain port) with a single-beat AXI4-Lite master-write leaf (the bulk-capture port). The slave-read FUB passes through to the core's AXI4-shaped read FUB, while the master-write side forces `MAX_BURST_BEATS=1` so the core emits one beat per AW — matching AXIL's single-beat semantics.

### Key Features

- AXI4 burst reads on the error-drain side (walk multiple records per burst)
- AXIL single-beat writes on the bulk-capture side (`MAX_BURST_BEATS=1`)
- Thin structural adapter — all logic lives in `monbus_group_core`
- AXI4-only AR sideband fields dropped at the wrapper boundary
- Master-write ID forced to width 1 (AXIL has no ID)
- Optional runtime compression (`cfg_compress_en`) with `USE_COMPRESSION`
- Full per-protocol filter mask set (AXI / AXIS / CORE) passed to the core

---

## Module Purpose

Some systems read error records over a high-throughput AXI4 port but write the bulk trace to a simple AXI4-Lite peripheral bus (a register-file-style capture sink, a low-cost bridge, or a control-plane fabric). This wrapper mixes the two: an `axi4_slave_rd` leaf for burst error reads and an `axil4_master_wr` leaf for single-beat trace writes, both driven by the shared capture core.

**Use Cases:**
- Trace capture to an AXIL-only memory-mapped sink while reading errors over AXI4
- Control-plane monitoring where the write path is a lightweight AXIL bus
- Mixed-fabric SoCs pairing an AXI4 CPU read port with an AXIL capture port

**Key Benefit:** Reuses the exact same capture core as the all-AXI4 variant — only `MAX_BURST_BEATS` and the master-write leaf differ — so behavior and configuration stay identical across the family, with the write side degrading gracefully to single beats.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `FIFO_DEPTH_ERR` | int | 64 | Error FIFO depth in 192-bit records |
| `FIFO_DEPTH_WRITE` | int | 96 | Write FIFO depth in 64-bit beats |
| `ADDR_WIDTH` | int | 32 | Address width for both ports |
| `AXI_ID_WIDTH` | int | 8 | Slave-read ID width |
| `AXI_USER_WIDTH` | int | 1 | AXI user-signal width (slave-read side) |
| `FLUSH_TIMEOUT_CYCLES` | int | 1024 | Cycles before a timeout-triggered flush |
| `NUM_PROTOCOLS` | int | 3 | Informational only |
| `USE_COMPRESSION` | int | 0 | 0 = raw 3-beat records; 1 = elaborate the compressor |
| `SKID_DEPTH_AR` | int | 2 | Slave-read AR channel skid depth |
| `SKID_DEPTH_R` | int | 4 | Slave-read R channel skid depth |
| `SKID_DEPTH_AW` | int | 2 | AXIL master-write AW channel skid depth |
| `SKID_DEPTH_W` | int | 2 | AXIL master-write W channel skid depth |
| `SKID_DEPTH_B` | int | 2 | AXIL master-write B channel skid depth |

Internally, the core is instantiated with `AXI_ID_WIDTH_M=1`, `AXI_ID_WIDTH_S=AXI_ID_WIDTH`, and `MAX_BURST_BEATS=1`.

---

## Port Groups

### Clock, Reset, Clear

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `axi_aclk` | input | 1 | Clock |
| `axi_aresetn` | input | 1 | Active-low asynchronous reset |
| `cam_clear` | input | 1 | Synchronous compressor CAM + stats clear |

### MonBus Ingress and Timestamp

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `monbus_valid` | input | 1 | Incoming packet valid |
| `monbus_ready` | output | 1 | Ready to accept |
| `monbus_packet` | input | `monitor_packet_t` (128) | Monitor packet |
| `monbus_timestamp` | input | `monbus_timestamp_t` (64) | Side-band timestamp |
| `mon_time_out` | output | `monbus_timestamp_t` (64) | Free-running counter for wrappers' `i_mon_time` |

### S-Side — AXI4 Slave Read (error record drain)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axi_arid` | input | AXI_ID_WIDTH | Read address ID |
| `s_axi_araddr` | input | ADDR_WIDTH | Read address |
| `s_axi_arlen` | input | 8 | Burst length (beats − 1) |
| `s_axi_arsize` | input | 3 | Burst size |
| `s_axi_arburst` | input | 2 | Burst type |
| `s_axi_arlock` | input | 1 | Lock |
| `s_axi_arcache` | input | 4 | Cache attributes |
| `s_axi_arprot` | input | 3 | Protection |
| `s_axi_arqos` | input | 4 | QoS |
| `s_axi_arregion` | input | 4 | Region |
| `s_axi_aruser` | input | AXI_USER_WIDTH | User |
| `s_axi_arvalid` | input | 1 | AR valid |
| `s_axi_arready` | output | 1 | AR ready |
| `s_axi_rid` | output | AXI_ID_WIDTH | Read data ID |
| `s_axi_rdata` | output | 64 | Read data (sliced error record) |
| `s_axi_rresp` | output | 2 | Read response |
| `s_axi_rlast` | output | 1 | Read last |
| `s_axi_ruser` | output | AXI_USER_WIDTH | User (tied to 0) |
| `s_axi_rvalid` | output | 1 | R valid |
| `s_axi_rready` | input | 1 | R ready |

### M-Side — AXIL Master Write (bulk trace capture)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `m_axil_awvalid` | output | 1 | AW valid |
| `m_axil_awready` | input | 1 | AW ready |
| `m_axil_awaddr` | output | ADDR_WIDTH | Write address |
| `m_axil_awprot` | output | 3 | Protection |
| `m_axil_wvalid` | output | 1 | W valid |
| `m_axil_wready` | input | 1 | W ready |
| `m_axil_wdata` | output | 64 | Write data |
| `m_axil_wstrb` | output | 8 | Write strobes |
| `m_axil_bvalid` | input | 1 | B valid |
| `m_axil_bready` | output | 1 | B ready |
| `m_axil_bresp` | input | 2 | Write response |

### Status and Egress Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `irq_out` | output | 1 | Error FIFO non-empty |
| `cfg_base_addr` | input | ADDR_WIDTH | Capture window base |
| `cfg_limit_addr` | input | ADDR_WIDTH | Capture window limit |
| `cfg_flush_watermark` | input | 16 | Flush-trigger beat count |
| `cfg_compress_en` | input | 1 | Runtime compression enable |
| `cfg_axi_*` / `cfg_axis_*` / `cfg_core_*` | input | 16 each | Per-protocol filter masks (drop / err-select / per-event-code); see `monbus_group_core` |
| `err_fifo_full` | output | 1 | Error FIFO full |
| `write_fifo_full` | output | 1 | Write FIFO full |
| `err_fifo_count` | output | 16 | Error FIFO occupancy (records) |
| `write_fifo_count` | output | 16 | Write FIFO occupancy (beats) |
| `mon_compressor_stat_*` | output | 32 each | Compressor statistics (0 in raw mode) |

---

## Functional Description

### S-Side Error Drain (AXI4 slave read)

Identical to the AXI4/AXI4 variant on the read side: the `axi4_slave_rd` leaf terminates the AXI4 read channel and hands a clean read FUB to the core, whose slicer serves each 192-bit error record as three 64-bit beats. Full AXI4 bursts can request multiple records at once. The AXI4-only AR sideband fields (`arlock`/`arcache`/`arqos`/`arregion`/`aruser`) are dropped at the wrapper boundary; `s_axi_ruser` is tied to 0.

### M-Side Bulk Capture (AXIL master write)

The core is parameterized with `MAX_BURST_BEATS=1`, so its master-write burst writer emits one AW per beat — the single-beat pattern AXIL requires. The core's AXI4-shaped master-write FUB is bridged to the `axil4_master_wr` leaf: `awaddr`, `awvalid/awready`, `wdata`, `wstrb`, `wvalid/wready`, and `bresp`/`bvalid`/`bready` connect through, while the AXI4-only FUB outputs the core still drives (`awid`, `awlen`, `awsize`, `awburst`, `wlast`) are captured in unused nets and discarded. The AXIL leaf drives `awprot=0`, and the core's `bid` input is tied to 0.

### Shared Egress Configuration

Filtering, FIFO sizing, address-window, watermark, timeout, and compression are all handled by `monbus_group_core` via the same config ports as every other group wrapper. The three per-protocol mask groups (`cfg_axi_*`, `cfg_axis_*`, `cfg_core_*`) behave identically here.

---

## Usage Example

```systemverilog
monbus_axi4_axil_group #(
    .ADDR_WIDTH      (32),
    .AXI_ID_WIDTH    (8),
    .USE_COMPRESSION (0)
) u_mon_group (
    .axi_aclk    (aclk),
    .axi_aresetn (aresetn),
    .cam_clear   (1'b0),

    .monbus_valid     (agg_valid),
    .monbus_ready     (agg_ready),
    .monbus_packet    (agg_packet),
    .monbus_timestamp (agg_timestamp),
    .mon_time_out     (mon_time),

    // AXI4 slave-read drain -> CPU
    .s_axi_arid(cpu_arid), .s_axi_araddr(cpu_araddr), .s_axi_arlen(cpu_arlen),
    .s_axi_arvalid(cpu_arvalid), .s_axi_arready(cpu_arready),
    .s_axi_rdata(cpu_rdata), .s_axi_rlast(cpu_rlast),
    .s_axi_rvalid(cpu_rvalid), .s_axi_rready(cpu_rready),
    // ... AR sideband ...

    // AXIL master-write bulk capture -> peripheral sink
    .m_axil_awaddr(cap_awaddr), .m_axil_awvalid(cap_awvalid), .m_axil_awready(cap_awready),
    .m_axil_wdata(cap_wdata), .m_axil_wstrb(cap_wstrb),
    .m_axil_wvalid(cap_wvalid), .m_axil_wready(cap_wready),
    .m_axil_bvalid(cap_bvalid), .m_axil_bready(cap_bready), .m_axil_bresp(cap_bresp),

    .irq_out             (mon_irq),
    .cfg_base_addr       (cap_base),
    .cfg_limit_addr      (cap_limit),
    .cfg_flush_watermark (16'd48),
    .cfg_compress_en     (1'b0)
    // ... per-protocol masks ...
);
```

---

## Design Notes

### AXIL Forces Single-Beat Writes

The only functional difference from the AXI4/AXI4 variant is `MAX_BURST_BEATS=1` and the AXIL master-write leaf. Every flush emits one beat per AW handshake, so throughput on the capture side is lower than the AXI4/AXI4 group — appropriate for a lightweight AXIL sink.

### Core Still Drives AXI4 FUB Fields

Because the core is AXI4-shaped internally, it always drives `awlen`/`awsize`/`awburst`/`awid`/`wlast`. On the AXIL side these are simply not routed to the leaf (captured in `_unused` nets). This is intentional and keeps the core single-source.

### Read Side Is Unchanged

The error-drain path is byte-for-byte the same as the AXI4/AXI4 group — the record slicer, burst AR handling, and IRQ behavior are all in the shared core.

---

## Related Modules

### Used By
- SoC monitoring subsystems reading errors over AXI4 but capturing the trace over AXIL

### Uses
- **monbus_group_core.sv** — protocol-agnostic capture core (all logic), `MAX_BURST_BEATS=1`
- **axi4_slave_rd.sv** — AXI4 slave-read leaf (error drain)
- **axil4_master_wr.sv** — AXIL master-write leaf (bulk capture)
- **monitor_common_pkg** — packet and timestamp types

### See Also
- **monbus_axi4_axi4_group.sv** — AXI4 read + AXI4 write variant
- **monbus_axil_axi4_group.sv** — AXIL read + AXI4 write variant
- **monbus_axil_axil_group.sv** — AXIL read + AXIL write variant
- **monbus_arbiter.sv** — upstream aggregation

---

## References

### Source Code
- RTL: `rtl/amba/monitor/monbus_axi4_axil_group.sv`
- Core: `rtl/amba/monitor/monbus_group_core.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Group Core: `docs/markdown/rtl-amba/monitor/monbus_group_core.md`
- Packet Format: `docs/markdown/rtl-amba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](../_book_monitor_index.md)
- [Back to rtl-amba Index](../index.md)
