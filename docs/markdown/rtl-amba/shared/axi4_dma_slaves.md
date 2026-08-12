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

# AXI4 DMA Slaves

**Module:** `axi4_dma_slaves.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`axi4_dma_slaves` bundles a synthetic AXI4 read *source* and write *sink* into one block that a DMA or streaming engine can plug into for source/sink characterization without a real memory backend. The read side (`axi4_slave_rd_pattern_gen`) answers AR bursts with LFSR-generated data; the write side (`axi4_slave_wr_crc_check`) accepts AW/W bursts and CRCs the data. Both compute CRC-32 with the same configuration, so a master that reads the pattern and writes it straight back produces matching read/write CRCs when the datapath is clean.

### Key Features

- One-instance source + sink slave pair for DMA / streaming-engine characterization
- Read side: LFSR-driven synthetic data source with per-channel CRC-32
- Write side: CRC-32-checking sink with per-channel accounting
- Shared CRC configuration across both sides — read and write CRCs are directly comparable
- LFSR configuration affects only the read (pattern-generation) side
- Independent read-LFSR and write-CRC resets so either side can be re-armed alone
- Per-channel and aggregate CRC / beat-count telemetry from both sides
- Per-side `busy_rd` / `busy_wr` status for harness-level stop triggers

---

## Module Purpose

Characterizing a DMA needs a memory model on both its read and write ports. Rather than instantiate a real RAM (and its checking logic) twice, this block wraps the two purpose-built synthetic slaves and exposes their combined port surface as a single AXI4 read+write slave. The read side manufactures a deterministic pattern; the write side verifies one. Because the CRC polynomial, init, xorout, and reflection settings are threaded identically into both children, the two CRCs are on the same footing — the master writes back the same LFSR data it read, and both sides compute against the same CRC.

**Use Cases:**
- `stream_char_harness` attaches this to STREAM's `m_axi_rd` / `m_axi_wr` to characterize DMA throughput, response-delay sweeps, and end-to-end CRC integrity
- RAPIDS characterization: source/sink termination for an engine's AXI4 master ports
- Any AXI4 master needing a fast, checkable, memory-free source/sink pair

**Key Benefit:** A drop-in memory replacement that is both non-blocking (never the bottleneck) and self-checking (read and write CRCs must agree), all from a single instantiation.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| NUM_CHANNELS | int | 1 | Independent LFSR/CRC contexts on each side (channel = id low bits) |
| AXI_ID_WIDTH | int | 8 | AXI ID width |
| AXI_ADDR_WIDTH | int | 32 | AXI address width |
| AXI_DATA_WIDTH | int | 64 | AXI data width |
| AXI_USER_WIDTH | int | 1 | AXI user signal width |
| SKID_DEPTH_AR | int | 2 | Read AR skid depth |
| SKID_DEPTH_R | int | 4 | Read R skid depth |
| SKID_DEPTH_AW | int | 2 | Write AW skid depth |
| SKID_DEPTH_W | int | 4 | Write W skid depth |
| SKID_DEPTH_B | int | 2 | Write B skid depth |
| LFSR_WIDTH | int | 32 | LFSR width (read side only) |
| LFSR_SEED | logic [31:0] | 32'hDEADBEEF | Base LFSR seed (read side only) |
| LFSR_TAPS | logic [47:0] | {12'd23, 12'd3, 12'd2, 12'd1} | Maximal-length Fibonacci taps (read side only) |
| CRC_WIDTH | int | 32 | CRC width (shared) |
| CRC_DATA_WIDTH | int | 32 | Bits per CRC update (shared) |
| CRC_POLY | logic [31:0] | 32'h04C11DB7 | CRC-32/Ethernet polynomial (shared) |
| CRC_INIT | logic [31:0] | 32'hFFFFFFFF | CRC initial value (shared) |
| CRC_XOROUT | logic [31:0] | 32'hFFFFFFFF | CRC final XOR (shared) |
| CRC_REFIN | int | 1 | Reflect input (shared) |
| CRC_REFOUT | int | 1 | Reflect output (shared) |
| REPLICATION_FACTOR | int | (AXI_DATA_WIDTH+31)/32 | Read-side pattern replication factor |
| CRC_SLICE_OFFSET | int | 0 | Write-side 32-bit CRC slice offset |
| CIW | int | (NUM_CHANNELS>1) ? $clog2(NUM_CHANNELS) : 1 | Derived: channel-index width |

**Note:** the CRC parameters are passed unchanged to both children on purpose — that shared configuration is what makes read and write CRCs comparable.

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | AXI clock |
| aresetn | input | 1 | Active-low asynchronous reset |
| read_lfsr_reset | input | 1 | Re-arm the read-side LFSR + CRC (independent of write side) |
| write_crc_reset | input | 1 | Re-arm the write-side CRC (independent of read side) |

### Read-Side Telemetry

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| read_crc_value | output | NUM_CHANNELS × 32 | Per-channel read CRC-32 |
| read_crc_valid | output | NUM_CHANNELS | Per-channel read CRC valid |
| read_beat_count | output | NUM_CHANNELS × 32 | Per-channel read beats |
| read_beat_count_total | output | 32 | Aggregate read beat count |

### Write-Side Telemetry

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| write_crc_value | output | NUM_CHANNELS × 32 | Per-channel write CRC-32 |
| write_crc_valid | output | NUM_CHANNELS | Per-channel write CRC valid |
| write_beat_count | output | NUM_CHANNELS × 32 | Per-channel write beats |
| write_beat_count_total | output | 32 | Aggregate write beat count |

### AXI4 Read Slave (AR + R)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_arid … s_axi_arvalid | input | — | AR channel (id, addr, len, size, burst, lock, cache, prot, qos, region, user, valid) |
| s_axi_arready | output | 1 | AR ready |
| s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser, s_axi_rvalid | output | — | R channel (LFSR pattern data, `OKAY` resp) |
| s_axi_rready | input | 1 | R ready |

### AXI4 Write Slave (AW + W + B)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_awid … s_axi_awvalid | input | — | AW channel (id, addr, len, size, burst, lock, cache, prot, qos, region, user, valid) |
| s_axi_awready | output | 1 | AW ready |
| s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser, s_axi_wvalid | input | — | W channel |
| s_axi_wready | output | 1 | W ready |
| s_axi_bid, s_axi_bresp, s_axi_buser, s_axi_bvalid | output | — | B channel (`OKAY` resp) |
| s_axi_bready | input | 1 | B ready |

### Status

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| busy_rd | output | 1 | Read-side busy (from the read pattern generator) |
| busy_wr | output | 1 | Write-side busy (from the write CRC checker) |

---

## Functional Description

### Structural Composition

The module is a thin structural wrapper: it instantiates one `axi4_slave_rd_pattern_gen` (`u_rd_pattern_gen`) and one `axi4_slave_wr_crc_check` (`u_wr_crc_check`) and fans the top-level ports out to them. There is no additional logic — all behavior lives in the two children, documented separately.

### Read Side (LFSR Source)

`u_rd_pattern_gen` handles the AR/R channels. It returns per-channel LFSR-generated data (32-bit LFSR replicated to the bus width) and accumulates a per-channel CRC-32 over the emitted stream. Its `crc_lfsr_reset` is driven from the top-level `read_lfsr_reset`. LFSR configuration (`LFSR_WIDTH`, `LFSR_SEED`, `LFSR_TAPS`, `REPLICATION_FACTOR`) reaches only this side.

### Write Side (CRC Sink)

`u_wr_crc_check` handles the AW/W/B channels. It CRCs the selected 32-bit slice of each accepted W beat per channel and returns `OKAY` B responses. Its `crc_reset` is driven from the top-level `write_crc_reset`, and `CRC_SLICE_OFFSET` selects the CRC'd lane.

### Shared CRC vs Independent Resets

The CRC configuration (`CRC_POLY`, `CRC_INIT`, `CRC_XOROUT`, `CRC_REFIN`, `CRC_REFOUT`, widths) is threaded identically into both children so the read and write CRCs compute over the same algorithm — the intended usage is that the master writes back the LFSR data it read, and the two CRCs must then agree. The two reset inputs are kept separate so the harness can re-arm one side without disturbing the other; in practice both are usually driven from the same CSR clear pulse.

---

## Usage Example

```systemverilog
// Source/sink pair on a DMA's read and write master ports.
axi4_dma_slaves #(
    .NUM_CHANNELS   (4),
    .AXI_ID_WIDTH   (8),
    .AXI_ADDR_WIDTH (32),
    .AXI_DATA_WIDTH (64)
) u_dma_slaves (
    .aclk            (aclk),
    .aresetn         (aresetn),
    .read_lfsr_reset (csr_clear_pulse),
    .write_crc_reset (csr_clear_pulse),

    // Read telemetry
    .read_crc_value        (rd_crc),   .read_crc_valid        (rd_crc_valid),
    .read_beat_count       (rd_beats), .read_beat_count_total (rd_beats_total),
    // Write telemetry
    .write_crc_value       (wr_crc),   .write_crc_valid       (wr_crc_valid),
    .write_beat_count      (wr_beats), .write_beat_count_total(wr_beats_total),

    // Read slave <- DUT m_axi_rd
    .s_axi_arid (m_rd_arid), /* ... AR ... */ .s_axi_arready(m_rd_arready),
    .s_axi_rid  (m_rd_rid),  /* ... R  ... */ .s_axi_rready (m_rd_rready),

    // Write slave <- DUT m_axi_wr
    .s_axi_awid (m_wr_awid), /* ... AW ... */ .s_axi_awready(m_wr_awready),
    .s_axi_wdata(m_wr_wdata),/* ... W  ... */ .s_axi_wready (m_wr_wready),
    .s_axi_bid  (m_wr_bid),  /* ... B  ... */ .s_axi_bready (m_wr_bready),

    .busy_rd (rd_busy),
    .busy_wr (wr_busy)
);

// End-to-end integrity: after a loopback run, compare per channel.
assign integrity_ok = (rd_crc[ch] == wr_crc[ch]);
```

---

## Design Notes

- **Pure composition:** the block adds no logic of its own — it exists to give the harness one instance and one port list instead of two, and to enforce the shared-CRC contract at the parameter level.
- **Shared CRC config is intentional:** identical CRC parameters on both children are what let a loopback test compare read vs write CRCs directly.
- **LFSR is read-only:** the write side has no pattern generator; it only checks. LFSR parameters therefore reach only the read child.
- **Independent re-arm:** separate `read_lfsr_reset` / `write_crc_reset` allow re-seeding one side mid-experiment; typical harnesses drive both from one CSR pulse.
- **No memory backend:** addresses are ignored for data — the read side derives data from the LFSR phase (or, in the master-side blocks, from an address hash), not from stored contents.

---

## Related Modules

### Used By
- `projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/stream_char_harness.sv` — attaches to STREAM's `m_axi_rd` / `m_axi_wr`
- `projects/NexysA7/rapids_characterization/flows-rapids-beats/rtl/rapids_char_harness.sv` — source/sink termination

### Uses
- **axi4_slave_rd_pattern_gen.sv** — the read-side LFSR data source + CRC
- **axi4_slave_wr_crc_check.sv** — the write-side CRC-checking sink

### See Also
- **axi4_master_wr_pattern_gen.sv** / **axi4_master_rd_crc_check.sv** — the master-side counterparts (drive traffic instead of terminating it)
- **axi4_dma_observer.sv** — non-intrusive observability wrapper for a DMA's master ports

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi4_dma_slaves.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Index: `docs/markdown/rtl-amba/index.md`
- Read child: `docs/markdown/rtl-amba/shared/axi4_slave_rd_pattern_gen.md`
- Write child: `docs/markdown/rtl-amba/shared/axi4_slave_wr_crc_check.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
