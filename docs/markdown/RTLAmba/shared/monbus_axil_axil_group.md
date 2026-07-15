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

# Monitor Bus Group — AXIL Slave-Read / AXIL Master-Write

**Module:** `monbus_axil_axil_group.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`monbus_axil_axil_group` is the all-AXI4-Lite wrapper of the monitor-bus delivery family. It wraps the protocol-agnostic `monbus_group_core` with an **AXIL slave-read err-drain port** (for the CPU IRQ handler to pop error records) and an **AXIL single-beat master-write port** (to stream captured records into a memory ring). It is the delivery block that `stream_char` / `rapids_char` instantiate for MonBus egress when both the drain and dump fabrics are AXIL.

This wrapper replaces the legacy `monbus_axil_group.sv`, which fused the core and the AXIL skids into one module.

### Key Features

- AXIL slave-read err-FIFO drain (CPU-facing IRQ path)
- AXIL single-beat master-write bulk-capture (memory-ring egress)
- Selectable err-drain data width: 64-bit (one beat per record slice) or 32-bit (2:1 read serializer for a 32-bit host crossbar)
- Shared per-protocol egress packet filter (AXI / AXIS / CORE)
- `irq_out` asserted whenever the err FIFO is non-empty
- Optional runtime compression (`USE_COMPRESSION` + `cfg_compress_en`) with half-beat packing (`HALF_BEAT_EN`)
- Compressor statistics and FIFO status/count outputs

---

## Module Purpose

The monitor bus produces a single arbitrated stream of 128-bit packets plus a 64-bit timestamp. That stream has to be split into two destinations: error/interrupt records the CPU polls, and bulk trace records written into a memory ring for later offline analysis. `monbus_group_core` does the filtering, FIFOing, watermark/timeout burst-writing, and slave-read drain. This wrapper gives the core an exact AXIL port shape on both the CPU-facing (slave-read) and memory-facing (master-write) sides, so the caller ties off no spurious AXI4-only fields.

The core's FUBs are AXI4-shaped internally; the wrapper bridges the AXIL leaves to those FUBs (supplying `arid=0 / arlen=0 / arsize=3 / arburst=INCR` on the read side and forcing `MAX_BURST_BEATS=1` on the write side).

**Use Cases:**
- MonBus egress for `stream_char` / `rapids_char` on an AXIL fabric
- CPU IRQ-driven error drain with a memory-mapped ring dump
- Minimal-footprint monitor delivery where both fabrics are AXIL
- 32-bit host crossbar drain via the built-in 2:1 read serializer

**Key Benefit:** Exact AXIL port shape on both sides with no fake AXI4 fields, plus a built-in 32-bit err-drain serializer for narrow host buses.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| FIFO_DEPTH_ERR | int | 64 | Error FIFO depth, in records |
| FIFO_DEPTH_WRITE | int | 96 | Write FIFO depth, in beats (96 beats = 32 raw records) |
| ADDR_WIDTH | int | 32 | Address width on the slave-read and master-write ports |
| S_AXIL_DATA_WIDTH | int | 64 | Err-drain read data width. 64 = one beat per 64-bit record slice (3 beats/record); 32 = a 2:1 read serializer presents each slice as a low then high beat (6 beats/record) for a 32-bit host crossbar |
| FLUSH_TIMEOUT_CYCLES | int | 1024 | Cycles since last accepted W handshake before a timeout-driven flush |
| NUM_PROTOCOLS | int | 3 | Informational — AXI / AXIS / CORE filter configs are unconditional |
| USE_COMPRESSION | int | 0 | Elaboration: 0 omits the compressor (raw-only); 1 elaborates it for runtime selection via `cfg_compress_en` |
| HALF_BEAT_EN | int | 0 | Elaboration: pack two 30-bit half-slots per 64-bit beat downstream of the compressor (requires `USE_COMPRESSION=1`) |
| SKID_DEPTH_AR | int | 2 | Slave-read AR skid depth |
| SKID_DEPTH_R | int | 4 | Slave-read R skid depth |
| SKID_DEPTH_AW | int | 2 | Master-write AW skid depth |
| SKID_DEPTH_W | int | 2 | Master-write W skid depth |
| SKID_DEPTH_B | int | 2 | Master-write B skid depth |

The AXIL master forces `MAX_BURST_BEATS=1` in the core, so this wrapper has no `MAX_BURST_BEATS` parameter (unlike the AXI4-master variant).

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
| s_axil_araddr | input | ADDR_WIDTH | Read address (record-slice index; address value not memory-mapped by the core) |
| s_axil_arprot | input | 3 | Read protection attributes |
| s_axil_rvalid | output | 1 | Read-data valid |
| s_axil_rready | input | 1 | Read-data ready |
| s_axil_rdata | output | S_AXIL_DATA_WIDTH | Read data (record slice, or half-slice in 32-bit mode) |
| s_axil_rresp | output | 2 | Read response |

### AXIL Master Write — Bulk Capture

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axil_awvalid | output | 1 | Write-address valid |
| m_axil_awready | input | 1 | Write-address ready |
| m_axil_awaddr | output | ADDR_WIDTH | Write address (within `[cfg_base_addr, cfg_limit_addr]`) |
| m_axil_awprot | output | 3 | Write protection attributes |
| m_axil_wvalid | output | 1 | Write-data valid |
| m_axil_wready | input | 1 | Write-data ready |
| m_axil_wdata | output | 64 | Write data (one 64-bit beat) |
| m_axil_wstrb | output | 8 | Write strobe |
| m_axil_bvalid | input | 1 | Write-response valid |
| m_axil_bready | output | 1 | Write-response ready |
| m_axil_bresp | input | 2 | Write response |

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

Three protocols (AXI, AXIS, CORE), each with a packet-type mask, an err-select mask, and per-event-category masks. All are 16-bit inputs.

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

Each monbus err record is three 64-bit slices — `{tag, source_ts}`, `packet[127:64]`, `packet[63:0]`. A 64-bit `axil4_slave_rd` leaf bridges the external AXIL read onto the core's 64-bit read FUB, and the core's slice counter returns the three slices in sequence; the err-FIFO record is popped only after slice 2 (packet low half) is read.

- **64-bit drain (`S_AXIL_DATA_WIDTH == 64`, `g_drain_direct`):** the leaf is wired straight through, one beat per slice — 3 beats/record.
- **32-bit drain (`S_AXIL_DATA_WIDTH == 32`, `g_drain_2to1`):** a phase bit splits each 64-bit leaf beat into a low then high 32-bit external read — 6 beats/record. The external AR is forwarded to the leaf only on the low phase, so the leaf issues exactly one core read per pair and never prefetches. The low read streams and consumes the beat while latching its high half; the high read replays the latch and gates R on its own accepted AR (`r_hi_ar`) to honor AXIL AR-before-R ordering (a master still holding `rready` from the low beat cannot consume the high beat early, which would desync the pair and double the core reads).

### M-Side Bulk-Capture Protocol

Surviving (non-err) packets go to the write FIFO and are streamed out the AXIL master-write port by the core's burst writer. Because this is an AXIL master, `MAX_BURST_BEATS=1` — each record is emitted as single-beat AW/W/B handshakes at consecutive addresses (three per raw record). The writer fires on watermark (`write_fifo_count >= cfg_flush_watermark`) or timeout (`FLUSH_TIMEOUT_CYCLES`), and the address is **circular** within `[cfg_base_addr, cfg_limit_addr]` — it wraps rather than saturating. Host-side ring pointers must match this wrap behavior. See [`monbus_group`](monbus_group.md) for the full burst-writer geometry.

### Interrupt

`irq_out` is asserted by the core whenever the err FIFO is non-empty, so a CPU can take an interrupt and drain records over the slave-read port.

### Shared Egress Packet Filter

The per-protocol filter (AXI, AXIS, CORE) decides for each packet: drop (via `pkt_mask` or a per-event mask), route to the err FIFO (via `err_select`), or route to the write FIFO (default). Protocols not in the supported set (APB, ARB) are always dropped. The filter config is identical across all four family wrappers — see [`monbus_group`](monbus_group.md) for the per-event category tables and masking rules.

### Compression

When `USE_COMPRESSION=1`, `monbus_compressor` can be selected at runtime via `cfg_compress_en`, emitting one 64-bit self-tagged slot per record into the write FIFO instead of three raw beats; `HALF_BEAT_EN=1` further packs two 30-bit half-slots per beat. `cam_clear` synchronously empties the compressor template CAM and zeroes its stat counters between runs. In raw-only builds these fold away.

---

## Usage Example

```systemverilog
monbus_axil_axil_group #(
    .FIFO_DEPTH_ERR       (64),
    .FIFO_DEPTH_WRITE     (96),    // beats (3x for raw mode)
    .ADDR_WIDTH           (32),
    .S_AXIL_DATA_WIDTH    (64),    // or 32 for a narrow host crossbar
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

    // CPU-facing err drain
    .s_axil_arvalid (cpu_arvalid),
    .s_axil_arready (cpu_arready),
    .s_axil_araddr  (cpu_araddr),
    .s_axil_arprot  (cpu_arprot),
    .s_axil_rvalid  (cpu_rvalid),
    .s_axil_rready  (cpu_rready),
    .s_axil_rdata   (cpu_rdata),
    .s_axil_rresp   (cpu_rresp),

    // Memory-ring dump
    .m_axil_awvalid (ring_awvalid),
    .m_axil_awready (ring_awready),
    .m_axil_awaddr  (ring_awaddr),
    /* ... m_axil_w*, m_axil_b* ... */

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

### Legacy Replacement

This wrapper (plus its three siblings) replaces the fused `monbus_axil_group.sv`. Key surface changes from the legacy module: `cfg_flush_watermark` is a new required input, `err_fifo_count` / `write_fifo_count` are 16 bits, and `FIFO_DEPTH_WRITE` is in beats (not records). See the migration section in [`monbus_group`](monbus_group.md).

### Why One Core + Four Wrappers

SystemVerilog cannot conditionally include ports in a single module's port list, so each protocol combination gets its own thin wrapper with the exact port shape. The filter, FIFOs, burst writer, and drain live once in `monbus_group_core`; the AXIL leaves and the FUB bridge live here.

### 32-Bit Drain Serializer

The `g_drain_2to1` path exists for 32-bit host crossbars. It is a careful 2:1 serializer: consuming the leaf beat on the low read (rather than holding it across both) makes `s_axil_rvalid` pulse once per external beat, so a master holding `rready` cannot mis-toggle the phase. See the shared mechanism note in the AXIL/AXI4 wrapper — the two wrappers use identical code.

---

## Related Modules

### Used By
- `stream_char` / `rapids_char` MonBus egress (AXIL fabric)
- Any monitor-delivery topology with AXIL drain and AXIL dump fabrics

### Uses
- **monbus_group_core.sv** — Protocol-agnostic filter + FIFO + burst-writer + drain
- **axil4_slave_rd.sv** — Slave-read (err-drain) skid leaf
- **axil4_master_wr.sv** — Master-write (bulk-capture) skid leaf
- **monbus_compressor.sv** — Optional runtime compressor (`USE_COMPRESSION=1`)
- **monitor_common_pkg** — `monitor_packet_t` / `monbus_timestamp_t` types
- **reset_defs.svh** — Reset macros

### See Also
- **monbus_axil_axi4_group.sv** — Same drain, AXI4-burst master-write
- **monbus_axi4_axil_group.sv** / **monbus_axi4_axi4_group.sv** — AXI4-burst slave-read variants
- **monbus_arbiter.sv** — Upstream multi-source merge (instantiate before this wrapper for N>1 sources)
- **sdpram_slave_axil_axil.sv** — Canonical memory-ring backend for the master-write port

---

## References

### Source Code
- RTL: `rtl/amba/shared/monbus_axil_axil_group.sv`
- Core: `rtl/amba/shared/monbus_group_core.sv`
- Tests: `val/amba/test_monbus_axil_axil_group.py`, `test_monbus_axil_axil_group_compressed.py`, `test_monbus_axil_axil_group_master_write.py`

### Documentation
- Family spec: `docs/markdown/RTLAmba/shared/monbus_group.md`
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Packet format: `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
