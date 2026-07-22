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

# MonBus Group — AXI4 / AXI4

**Module:** `monbus_axi4_axi4_group.sv`
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

The `monbus_axi4_axi4_group` module is the AXI4-slave-read + AXI4-master-write wrapper around `monbus_group_core`. It pairs a full AXI4 slave-read leaf (the error/interrupt drain port, supporting burst reads) with a full AXI4 master-write leaf (the bulk-capture port, emitting large write bursts). Both leaves are true AXI4, so their FUB interfaces pass straight through to the core's AXI4-shaped FUB ports; the wrapper only supplies safe constant defaults for the AXI4 sideband fields the core does not produce.

### Key Features

- Full AXI4 on both the error-drain (slave read) and bulk-capture (master write) sides
- Burst AR support on the slave-read drain (walk multiple error records per burst)
- Large write bursts on the master-write side (`MAX_BURST_BEATS` up to 256)
- Thin structural adapter — all logic lives in `monbus_group_core`
- Configurable skid depths on all five AXI channels
- Optional runtime compression (`cfg_compress_en`) with `USE_COMPRESSION`
- Full per-protocol filter mask set (AXI / AXIS / CORE) passed to the core

---

## Module Purpose

An SoC monitoring subsystem needs to expose captured monitor packets to two AXI4 consumers: a CPU that reads error records over a slave port, and a DMA-style write path that dumps a bulk trace to memory. This wrapper wires the two AXI4 leaf protocol adapters (`axi4_slave_rd`, `axi4_master_wr`) to the shared capture core, giving a drop-in AXI4/AXI4 capture block.

**Use Cases:**
- AXI4-connected monitoring block where both the error-read and trace-write masters are AXI4
- High-throughput trace capture that benefits from long master-write bursts
- CPU IRQ handler reading error records via AXI4 burst reads

**Key Benefit:** True AXI4 on both sides with zero protocol translation loss — the leaves pass through to the core, so burst geometry, IDs, and full-size bursts are available end to end.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `FIFO_DEPTH_ERR` | int | 64 | Error FIFO depth in 192-bit records |
| `FIFO_DEPTH_WRITE` | int | 96 | Write FIFO depth in 64-bit beats |
| `ADDR_WIDTH` | int | 32 | Address width for both AXI4 ports |
| `AXI_ID_WIDTH_S` | int | 8 | Slave-read ID width |
| `AXI_ID_WIDTH_M` | int | 8 | Master-write ID width |
| `AXI_USER_WIDTH` | int | 1 | AXI user-signal width |
| `MAX_BURST_BEATS` | int | 64 | Max beats per master-write sub-burst |
| `FLUSH_TIMEOUT_CYCLES` | int | 1024 | Cycles before a timeout-triggered flush |
| `NUM_PROTOCOLS` | int | 3 | Informational only |
| `USE_COMPRESSION` | int | 0 | 0 = raw 3-beat records; 1 = elaborate the compressor |
| `SKID_DEPTH_AR` | int | 2 | Slave-read AR channel skid depth |
| `SKID_DEPTH_R` | int | 4 | Slave-read R channel skid depth |
| `SKID_DEPTH_AW` | int | 2 | Master-write AW channel skid depth |
| `SKID_DEPTH_W` | int | 4 | Master-write W channel skid depth |
| `SKID_DEPTH_B` | int | 2 | Master-write B channel skid depth |

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
| `s_axi_arid` | input | AXI_ID_WIDTH_S | Read address ID |
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
| `s_axi_rid` | output | AXI_ID_WIDTH_S | Read data ID |
| `s_axi_rdata` | output | 64 | Read data (sliced error record) |
| `s_axi_rresp` | output | 2 | Read response |
| `s_axi_rlast` | output | 1 | Read last |
| `s_axi_ruser` | output | AXI_USER_WIDTH | User (tied to 0) |
| `s_axi_rvalid` | output | 1 | R valid |
| `s_axi_rready` | input | 1 | R ready |

### M-Side — AXI4 Master Write (bulk trace capture)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `m_axi_awid` | output | AXI_ID_WIDTH_M | Write address ID |
| `m_axi_awaddr` | output | ADDR_WIDTH | Write address |
| `m_axi_awlen` | output | 8 | Burst length (beats − 1) |
| `m_axi_awsize` | output | 3 | Burst size |
| `m_axi_awburst` | output | 2 | Burst type |
| `m_axi_awlock` | output | 1 | Lock |
| `m_axi_awcache` | output | 4 | Cache attributes |
| `m_axi_awprot` | output | 3 | Protection |
| `m_axi_awqos` | output | 4 | QoS |
| `m_axi_awregion` | output | 4 | Region |
| `m_axi_awuser` | output | AXI_USER_WIDTH | User |
| `m_axi_awvalid` | output | 1 | AW valid |
| `m_axi_awready` | input | 1 | AW ready |
| `m_axi_wdata` | output | 64 | Write data |
| `m_axi_wstrb` | output | 8 | Write strobes |
| `m_axi_wlast` | output | 1 | Write last |
| `m_axi_wuser` | output | AXI_USER_WIDTH | User |
| `m_axi_wvalid` | output | 1 | W valid |
| `m_axi_wready` | input | 1 | W ready |
| `m_axi_bid` | input | AXI_ID_WIDTH_M | Write response ID |
| `m_axi_bresp` | input | 2 | Write response |
| `m_axi_buser` | input | AXI_USER_WIDTH | User (ignored) |
| `m_axi_bvalid` | input | 1 | B valid |
| `m_axi_bready` | output | 1 | B ready |

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

The `axi4_slave_rd` leaf terminates the incoming AXI4 read channel and presents a clean FUB read interface (`fub_axi_ar*` / `fub_axi_r*`) to the core. The core's slave-read slicer serves each 192-bit error record as three 64-bit beats (timestamp, packet-hi, packet-lo). Because the leaf is full AXI4, a single AR burst can request several records at once. The AXI4-only AR sideband fields (`arlock`/`arcache`/`arqos`/`arregion`/`aruser`) are consumed by the leaf and not forwarded to the core; `s_axi_ruser` is tied to 0.

### M-Side Bulk Capture (AXI4 master write)

The core's master-write FUB drives the `axi4_master_wr` leaf, which emits the full AXI4 write channel. The wrapper hard-wires the AXI4 sideband fields the core does not generate to safe defaults at the leaf's FUB inputs: `awlock=0`, `awcache=4'b0010` (normal non-cacheable bufferable), `awprot=0`, `awqos=0`, `awregion=0`, `awuser=0`, `wuser=0`. `MAX_BURST_BEATS` defaults to 64, so a flush typically drains as one large sub-burst.

### Shared Egress Configuration

All filtering, FIFO sizing, address-window, watermark, timeout, and compression behavior is set by the config ports and handed straight to `monbus_group_core`. The three per-protocol mask groups (`cfg_axi_*`, `cfg_axis_*`, `cfg_core_*`) select which packet types drop, which route to the error FIFO, and which event codes are masked — identical semantics across all four group wrappers.

---

## Usage Example

```systemverilog
monbus_axi4_axi4_group #(
    .ADDR_WIDTH      (32),
    .AXI_ID_WIDTH_S  (8),
    .AXI_ID_WIDTH_M  (8),
    .MAX_BURST_BEATS (64),
    .USE_COMPRESSION (0)
) u_mon_group (
    .axi_aclk    (aclk),
    .axi_aresetn (aresetn),
    .cam_clear   (1'b0),

    .monbus_valid     (agg_valid),   // from monbus_arbiter
    .monbus_ready     (agg_ready),
    .monbus_packet    (agg_packet),
    .monbus_timestamp (agg_timestamp),
    .mon_time_out     (mon_time),

    // AXI4 slave-read drain -> CPU
    .s_axi_arid (cpu_arid), .s_axi_araddr(cpu_araddr), .s_axi_arlen(cpu_arlen),
    .s_axi_arvalid(cpu_arvalid), .s_axi_arready(cpu_arready),
    .s_axi_rid (cpu_rid), .s_axi_rdata(cpu_rdata), .s_axi_rlast(cpu_rlast),
    .s_axi_rvalid(cpu_rvalid), .s_axi_rready(cpu_rready),
    // ... AR sideband ...

    // AXI4 master-write bulk capture -> memory
    .m_axi_awaddr(cap_awaddr), .m_axi_awlen(cap_awlen), .m_axi_awvalid(cap_awvalid),
    .m_axi_awready(cap_awready), .m_axi_wdata(cap_wdata), .m_axi_wlast(cap_wlast),
    .m_axi_wvalid(cap_wvalid), .m_axi_wready(cap_wready),
    .m_axi_bvalid(cap_bvalid), .m_axi_bready(cap_bready),
    // ... AW sideband ...

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

### Both Sides Are Full AXI4

Unlike the AXIL variants, neither leaf forces `MAX_BURST_BEATS=1` and neither injects single-beat defaults into the core — the AXI4 IDs and burst lengths flow through. This is the highest-throughput member of the group family.

### AW Sideband Defaults Live in the Wrapper

The core deliberately does not model `awlock`/`awcache`/`awqos`/`awregion`/`awuser`. The wrapper supplies conservative constants at the master-write leaf so downstream interconnect sees a well-formed AXI4 burst.

### Skid Depths Are Tunable

The five `SKID_DEPTH_*` parameters size the per-channel skid buffers in the leaves; increase them to absorb more backpressure on congested interconnect.

---

## Related Modules

### Used By
- SoC monitoring subsystems requiring an AXI4/AXI4 MonBus capture block

### Uses
- **monbus_group_core.sv** — protocol-agnostic capture core (all logic)
- **axi4_slave_rd.sv** — AXI4 slave-read leaf (error drain)
- **axi4_master_wr.sv** — AXI4 master-write leaf (bulk capture)
- **monitor_common_pkg** — packet and timestamp types

### See Also
- **monbus_axi4_axil_group.sv** — AXI4 read + AXIL write variant
- **monbus_axil_axi4_group.sv** — AXIL read + AXI4 write variant
- **monbus_axil_axil_group.sv** — AXIL read + AXIL write variant
- **monbus_arbiter.sv** — upstream aggregation

---

## References

### Source Code
- RTL: `rtl/amba/monitor/monbus_axi4_axi4_group.sv`
- Core: `rtl/amba/monitor/monbus_group_core.sv`

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Group Core: `docs/markdown/RTLAmba/monbus_group_core.md`
- Packet Format: `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](../_book_monitor_index.md)
- [Back to RTLAmba Index](../index.md)
