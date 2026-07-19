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

# Monitor Bus Group — AXIL Slave-Read / AXI4 Master-Write

**Module:** `monbus_axil_axi4_group.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`monbus_axil_axi4_group` is the mixed-fabric wrapper of the monitor-bus delivery family. It wraps the protocol-agnostic `monbus_group_core` with an **AXIL slave-read err-drain port** (CPU IRQ handler pops error records) and a **full AXI4 burst master-write port** (streams captured records into a memory ring, bunching multiple records into multi-beat bursts to amortize address-channel overhead). It is the delivery block `stream_char` / `rapids_char` instantiate for MonBus egress when the drain fabric is AXIL but the memory ring lives behind an AXI4 fabric.

### Key Features

- AXIL slave-read err-FIFO drain (CPU-facing IRQ path)
- AXI4 burst master-write bulk-capture (`MAX_BURST_BEATS` up to 256, default 64)
- Selectable err-drain data width: 64-bit (one beat per record slice) or 32-bit (2:1 read serializer for a 32-bit host crossbar)
- Shared per-protocol egress packet filter (AXI / AXIS / CORE)
- `irq_out` asserted whenever the err FIFO is non-empty
- Optional runtime compression (`USE_COMPRESSION` + `cfg_compress_en`)
- Compressor statistics and FIFO status/count outputs

---

## Module Purpose

Like the AXIL/AXIL variant, this wrapper splits the arbitrated monitor-bus stream into a CPU-facing error drain and a memory-ring bulk dump. The difference is the dump side: a full AXI4 burst master lets the burst writer emit many records in a single AW + N × W + B, which is throughput-optimal when the ring sits behind an AXI4 fabric.

The core's FUBs are AXI4-shaped internally. On the read side the wrapper bridges the AXIL leaf into the core's AXI4-shaped read FUB (`arid=0 / arlen=0 / arsize=3 / arburst=INCR`). On the write side the core drives most AXI4 fields directly; the fields the core does not produce (`awlock / awcache / awqos / awregion / awuser / wuser`) are tied to safe defaults at the AXI4 leaf boundary.

**Use Cases:**
- MonBus egress for `stream_char` / `rapids_char` with an AXIL drain and an AXI4 ring fabric
- CPU IRQ error drain plus high-throughput burst dump into memory
- Trace capture where amortizing AXI4 address-channel overhead matters

**Key Benefit:** A lightweight AXIL CPU drain paired with a full AXI4 burst dump, so trace records land in memory with minimal address-channel overhead.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| FIFO_DEPTH_ERR | int | 64 | Error FIFO depth, in records |
| FIFO_DEPTH_WRITE | int | 96 | Write FIFO depth, in beats (96 beats = 32 raw records) |
| ADDR_WIDTH | int | 32 | Address width on the slave-read and master-write ports |
| S_AXIL_DATA_WIDTH | int | 64 | Err-drain read data width. 64 = one beat per 64-bit record slice; 32 = a 2:1 read serializer presents each slice as a low then high beat (6 beats/record) for a 32-bit host crossbar |
| AXI_ID_WIDTH | int | 8 | Master-write AXI4 ID width |
| AXI_USER_WIDTH | int | 1 | Master-write AXI4 USER width |
| MAX_BURST_BEATS | int | 64 | Maximum beats per master-write AW (AXI4 protocol max is 256) |
| FLUSH_TIMEOUT_CYCLES | int | 1024 | Cycles since last accepted W handshake before a timeout-driven flush |
| NUM_PROTOCOLS | int | 3 | Informational — AXI / AXIS / CORE filter configs are unconditional |
| USE_COMPRESSION | int | 0 | Elaboration: 0 omits the compressor (raw-only); 1 elaborates it for runtime selection via `cfg_compress_en` |
| SKID_DEPTH_AR | int | 2 | Slave-read AR skid depth |
| SKID_DEPTH_R | int | 4 | Slave-read R skid depth |
| SKID_DEPTH_AW | int | 2 | Master-write AW skid depth |
| SKID_DEPTH_W | int | 4 | Master-write W skid depth (deeper to absorb burst W) |
| SKID_DEPTH_B | int | 2 | Master-write B skid depth |

---

## Port Groups

### Clock, Reset, and CAM Clear

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| axi_aclk | input | 1 | Clock |
| axi_aresetn | input | 1 | Active-low asynchronous reset |
| cam_clear | input | 1 | Synchronous clear of the compressor CAM + stat counters (tied off in raw-only builds) |

### Monitor-Bus Input + Timestamp

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| monbus_valid | input | 1 | Monitor-bus packet valid |
| monbus_ready | output | 1 | Monitor-bus ready (backpressure to the arbiter) |
| monbus_packet | input | `monitor_packet_t` | 128-bit monitor packet |
| monbus_timestamp | input | `monbus_timestamp_t` | 64-bit source timestamp |
| mon_time_out | output | `monbus_timestamp_t` | Free-running 64-bit timestamp counter |

### AXIL Slave Read — Err-FIFO Drain

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axil_arvalid | input | 1 | Read-address valid |
| s_axil_arready | output | 1 | Read-address ready |
| s_axil_araddr | input | ADDR_WIDTH | Read address |
| s_axil_arprot | input | 3 | Read protection attributes |
| s_axil_rvalid | output | 1 | Read-data valid |
| s_axil_rready | input | 1 | Read-data ready |
| s_axil_rdata | output | S_AXIL_DATA_WIDTH | Read data (record slice, or half-slice in 32-bit mode) |
| s_axil_rresp | output | 2 | Read response |

### AXI4 Master Write — Burst Bulk Capture

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axi_awid | output | AXI_ID_WIDTH | Write-address ID |
| m_axi_awaddr | output | ADDR_WIDTH | Write burst base address (within the ring window) |
| m_axi_awlen | output | 8 | Burst length minus 1 (`sub_burst_beats - 1`) |
| m_axi_awsize | output | 3 | Beat size (fixed at 3 = 8 bytes) |
| m_axi_awburst | output | 2 | Burst type (fixed INCR) |
| m_axi_awlock | output | 1 | Lock (tied 0 at the leaf) |
| m_axi_awcache | output | 4 | Cache (tied `4'b0010` Normal Non-cacheable Bufferable) |
| m_axi_awprot | output | 3 | Protection (tied 0) |
| m_axi_awqos | output | 4 | QoS (tied 0) |
| m_axi_awregion | output | 4 | Region (tied 0) |
| m_axi_awuser | output | AXI_USER_WIDTH | User (tied 0) |
| m_axi_awvalid | output | 1 | Write-address valid |
| m_axi_awready | input | 1 | Write-address ready |
| m_axi_wdata | output | 64 | Write data (one 64-bit beat) |
| m_axi_wstrb | output | 8 | Write strobe |
| m_axi_wlast | output | 1 | Last beat of the sub-burst |
| m_axi_wuser | output | AXI_USER_WIDTH | Write-data user (tied 0) |
| m_axi_wvalid | output | 1 | Write-data valid |
| m_axi_wready | input | 1 | Write-data ready |
| m_axi_bid | input | AXI_ID_WIDTH | Write-response ID |
| m_axi_bresp | input | 2 | Write response |
| m_axi_buser | input | AXI_USER_WIDTH | Write-response user (unused) |
| m_axi_bvalid | input | 1 | Write-response valid |
| m_axi_bready | output | 1 | Write-response ready |

### Interrupt

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| irq_out | output | 1 | Asserted whenever the err FIFO is non-empty |

### Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_base_addr | input | ADDR_WIDTH | Master-write ring base address |
| cfg_limit_addr | input | ADDR_WIDTH | Master-write ring limit address (writer wraps, does not saturate) |
| cfg_flush_watermark | input | 16 | Write-FIFO depth (beats) at which a flush fires |
| cfg_compress_en | input | 1 | Runtime compression enable (effective only when `USE_COMPRESSION=1`) |

### Per-Protocol Filter Masks

Three protocols (AXI, AXIS, CORE), each with a packet-type mask, an err-select mask, and per-event-category masks. All are 16-bit inputs — same shape as the AXIL/AXIL variant.

| Port | Protocol | Role |
|------|----------|------|
| cfg_axi_pkt_mask | AXI | Drop by packet type |
| cfg_axi_err_select | AXI | Route to err FIFO by packet type |
| cfg_axi_error_mask / cfg_axi_timeout_mask / cfg_axi_compl_mask / cfg_axi_thresh_mask / cfg_axi_perf_mask / cfg_axi_addr_mask / cfg_axi_debug_mask | AXI | Per-event-code drop masks |
| cfg_axis_pkt_mask | AXIS | Drop by packet type |
| cfg_axis_err_select | AXIS | Route to err FIFO by packet type |
| cfg_axis_error_mask / cfg_axis_timeout_mask / cfg_axis_compl_mask / cfg_axis_credit_mask / cfg_axis_channel_mask / cfg_axis_stream_mask | AXIS | Per-event-code drop masks |
| cfg_core_pkt_mask | CORE | Drop by packet type |
| cfg_core_err_select | CORE | Route to err FIFO by packet type |
| cfg_core_error_mask / cfg_core_timeout_mask / cfg_core_compl_mask / cfg_core_thresh_mask / cfg_core_perf_mask / cfg_core_debug_mask | CORE | Per-event-code drop masks |

### Status / Debug

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| err_fifo_full | output | 1 | Err FIFO write port not ready |
| write_fifo_full | output | 1 | Write FIFO write port not ready |
| err_fifo_count | output | 16 | Err FIFO entry count (records) |
| write_fifo_count | output | 16 | Write FIFO entry count (beats) |
| mon_compressor_stat_tier1_a / _tier1_b / _tier1_c / _tier0 / _cam_miss / _delta_ts_ovf / _event_data_ovf / _ed_delta_ovf | output | 32 each | Compressor statistics (live only when `USE_COMPRESSION=1`) |

---

## Functional Description

### S-Side Err-Drain Read Protocol

Each monbus err record is three 64-bit slices — `{tag, source_ts}`, `packet[127:64]`, `packet[63:0]`. A 64-bit `axil4_slave_rd` leaf bridges the external AXIL read onto the core's 64-bit read FUB, and the core's slice counter returns the three slices in sequence; the err-FIFO record is popped only after the packet-low slice is read.

- **64-bit drain (`S_AXIL_DATA_WIDTH == 64`):** the leaf is wired straight through — 3 beats/record.
- **32-bit drain (`S_AXIL_DATA_WIDTH == 32`):** a phase bit splits each 64-bit leaf beat into a low then high 32-bit external read — 6 beats/record. The AR is forwarded to the leaf only on the low phase (one core read per pair, no prefetch); the low read consumes the beat and latches its high half; the high read replays the latch, gating R on its own accepted AR (`r_hi_ar`) to honor AXIL AR-before-R ordering. This is the identical mechanism used in `monbus_axil_axil_group`.

### M-Side Bulk-Capture Protocol (AXI4 Burst)

Surviving (non-err) packets go to the write FIFO and are streamed out the AXI4 master-write port by the core's burst writer. Because this is a full AXI4 master, one drain cycle typically becomes one large sub-burst — e.g. 24 beats = 8 raw records in a single AW + 24 × W + B — capped per AW by `MAX_BURST_BEATS`. `awsize` is fixed at 3 (8 bytes/beat), `awburst` at INCR, `awlen = sub_burst_beats - 1`, and `wlast` asserts on the final beat of each sub-burst. The address is **circular** within `[cfg_base_addr, cfg_limit_addr]` (wraps, does not saturate). The writer fires on watermark or timeout. See [`monbus_group`](monbus_group.md) for the full burst-writer geometry (3-stage pipeline, mod-3 rounding, 4KB-boundary respect, rewind-snap).

The core drives `awid / awaddr / awlen / awsize / awburst` and `wdata / wstrb / wlast / wvalid`. The AXI4 fields the core does not produce are tied to safe defaults at the leaf: `awlock=0`, `awcache=4'b0010` (Normal Non-cacheable Bufferable), `awprot=0`, `awqos=0`, `awregion=0`, `awuser=0`, `wuser=0`.

### Interrupt

`irq_out` is asserted by the core whenever the err FIFO is non-empty.

### Shared Egress Packet Filter

The per-protocol filter (AXI, AXIS, CORE) decides for each packet: drop, route to the err FIFO (`err_select`), or route to the write FIFO (default). Protocols not in the supported set (APB, ARB) are always dropped. The filter config is identical across all four family wrappers — see [`monbus_group`](monbus_group.md) for the per-event category tables and masking rules.

### Compression

When `USE_COMPRESSION=1`, `monbus_compressor` is selectable at runtime via `cfg_compress_en`, emitting one 64-bit self-tagged slot per record instead of three raw beats; `cam_clear` synchronously empties the template CAM and zeroes stats between runs. In raw-only builds these fold away. (Unlike the AXIL/AXIL variant, this wrapper does not expose `HALF_BEAT_EN`.)

---

## Usage Example

```systemverilog
monbus_axil_axi4_group #(
    .FIFO_DEPTH_ERR       (64),
    .FIFO_DEPTH_WRITE     (96),    // beats (3x for raw mode)
    .ADDR_WIDTH           (32),
    .S_AXIL_DATA_WIDTH    (64),    // or 32 for a narrow host crossbar
    .AXI_ID_WIDTH         (8),
    .MAX_BURST_BEATS      (64),
    .FLUSH_TIMEOUT_CYCLES (1024),
    .USE_COMPRESSION      (0)
) u_monbus_egress (
    .axi_aclk    (aclk),
    .axi_aresetn (aresetn),
    .cam_clear   (1'b0),

    // Arbitrated monitor-bus input
    .monbus_valid     (mon_valid),
    .monbus_ready     (mon_ready),
    .monbus_packet    (mon_packet),
    .monbus_timestamp (mon_timestamp),
    .mon_time_out     (mon_time),

    // CPU-facing AXIL err drain
    .s_axil_arvalid (cpu_arvalid),
    .s_axil_arready (cpu_arready),
    .s_axil_araddr  (cpu_araddr),
    .s_axil_arprot  (cpu_arprot),
    .s_axil_rvalid  (cpu_rvalid),
    .s_axil_rready  (cpu_rready),
    .s_axil_rdata   (cpu_rdata),
    .s_axil_rresp   (cpu_rresp),

    // AXI4 burst memory-ring dump
    .m_axi_awid    (ring_awid),
    .m_axi_awaddr  (ring_awaddr),
    .m_axi_awlen   (ring_awlen),
    /* ... remaining m_axi_aw*, m_axi_w*, m_axi_b* ... */

    .irq_out             (monbus_irq),
    .cfg_base_addr       (RING_BASE),
    .cfg_limit_addr      (RING_LIMIT),
    .cfg_flush_watermark (16'd24),
    .cfg_compress_en     (1'b0),

    // Per-protocol filter masks (AXI / AXIS / CORE) ...
    .cfg_axi_pkt_mask    (axi_pkt_mask),
    .cfg_axi_err_select  (axi_err_select),
    /* ... remaining masks ... */

    .err_fifo_count   (err_count),
    .write_fifo_count (wr_count)
    /* ... compressor stats ... */
);
```

---

## Design Notes

### When to Pick This Over AXIL/AXIL

Choose this wrapper when the memory ring lives behind an AXI4 fabric and you want to bunch records into multi-beat bursts to amortize address-channel overhead. The memory image is identical to the AXIL-master case; only the address-channel handshake count differs. Pick `MAX_BURST_BEATS` to taste (up to 256).

### AXI4 Leaf Default Tie-Offs

The core only produces the AXI4 fields it needs. The remaining AXI4 qualifier fields (`awlock / awcache / awqos / awregion / awuser / wuser`) are tied at the `axi4_master_wr` leaf boundary, with `awcache` set to Normal Non-cacheable Bufferable — appropriate for a trace-ring write that must reach memory.

### Why One Core + Four Wrappers

The filter, FIFOs, burst writer, and drain live once in `monbus_group_core`; the AXIL read leaf, the AXI4 write leaf, and the two FUB bridges live here. Each family wrapper carries only the exact port shape its fabric demands.

---

## Related Modules

### Used By
- `stream_char` / `rapids_char` MonBus egress (AXIL drain + AXI4 ring)
- Trace-capture topologies needing high-throughput burst dump into AXI4 memory

### Uses
- **monbus_group_core.sv** — Protocol-agnostic filter + FIFO + burst-writer + drain
- **axil4_slave_rd.sv** — Slave-read (err-drain) skid leaf
- **axi4_master_wr.sv** — Master-write (burst bulk-capture) skid leaf
- **monbus_compressor.sv** — Optional runtime compressor (`USE_COMPRESSION=1`)
- **monitor_common_pkg** — `monitor_packet_t` / `monbus_timestamp_t` types
- **reset_defs.svh** — Reset macros

### See Also
- **monbus_axil_axil_group.sv** — Same drain, AXIL single-beat master-write
- **monbus_axi4_axil_group.sv** / **monbus_axi4_axi4_group.sv** — AXI4-burst slave-read variants
- **monbus_arbiter.sv** — Upstream multi-source merge (instantiate before this wrapper for N>1 sources)
- **axi4_dma_observer.sv** — Instantiates this wrapper as its central filter + err FIFO + dump writer

---

## References

### Source Code
- RTL: `rtl/amba/monitor/monbus_axil_axi4_group.sv`
- Core: `rtl/amba/monitor/monbus_group_core.sv`
- Tests: `val/amba/test_monbus_axil_axi4_group.py`

### Documentation
- Family spec: `docs/markdown/RTLAmba/monbus_group.md`
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Packet format: `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
