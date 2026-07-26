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

# AXI4 Slave Read Pattern Generator

**Module:** `axi4_slave_rd_pattern_gen.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`axi4_slave_rd_pattern_gen` is a read-only AXI4 slave that answers AR bursts with deterministic, LFSR-generated data and accumulates a running CRC-32 over the stream it emits. It exists to serve as a synthetic data *source* for DMA / streaming-engine characterization: a master under test issues read bursts, the slave returns a reproducible pseudo-random pattern, and the same pattern (and CRC) can be regenerated anywhere else in the system to prove end-to-end data integrity.

### Key Features

- Read-only AXI4 slave (AR + R channels) built on the standard `axi4_slave_rd` protocol handler
- Per-channel independent LFSR + CRC-32 state, demuxed off the low bits of `arid`
- 32-bit maximal-length Fibonacci LFSR (seed `0xDEADBEEF`, taps `{32,22,2,1}`) replicated to fill the data bus
- CRC-32/Ethernet accumulator per channel (poly `0x04C11DB7`, reflected in/out) matching the write-side checker bit-for-bit
- Gapless back-to-back bursts (AR accepted on the last beat) so `rvalid` never drops mid-stream
- Per-channel CRC / beat-count telemetry plus an aggregate beat-count total for harness stop triggers
- Single `crc_lfsr_reset` pulse re-arms all channel LFSRs and CRCs together

---

## Module Purpose

Characterizing a DMA read path needs a slave that is both *fast* (never the bottleneck) and *checkable* (the returned data is a known function of the request). A real memory backend gives neither cheaply. This module instead generates its read data from a Fibonacci LFSR, so every beat is a deterministic function of `(seed, beat_index)`, and folds that same data into a CRC-32 the harness can compare against an independently computed golden value.

**Use Cases:**
- Feeding a DMA / streaming engine's read (`m_axi_rd`) port during throughput characterization
- End-to-end integrity checks where read data is looped back to a write-CRC sink
- Per-channel multi-context validation, where each channel's data must be independent of another channel's interleave on the shared AXI port
- On-chip (FPGA) stimulus in the STREAM / RAPIDS characterization harnesses

**Key Benefit:** A memory-free, deterministic read slave whose per-channel CRC-32 is bit-identical to the write-side checker — integrity can be proven with a single register compare, and the slave never starves the master.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| NUM_CHANNELS | int | 1 | Number of independent LFSR/CRC contexts; channel index is `arid[CIW-1:0]` |
| SKID_DEPTH_AR | int | 2 | AR channel skid buffer depth |
| SKID_DEPTH_R | int | 4 | R channel skid buffer depth |
| AXI_ID_WIDTH | int | 8 | AXI ID width |
| AXI_ADDR_WIDTH | int | 32 | AXI address width |
| AXI_DATA_WIDTH | int | 64 | AXI data width (may be wider; must be handled by replication) |
| AXI_USER_WIDTH | int | 1 | AXI user signal width |
| LFSR_WIDTH | int | 32 | LFSR width (fixed at 32 for timing/simplicity) |
| LFSR_SEED | logic [31:0] | 32'hDEADBEEF | Base LFSR seed; channel N uses `LFSR_SEED ^ N` |
| LFSR_TAPS | logic [47:0] | {12'd32, 12'd22, 12'd2, 12'd1} | Maximal-length Fibonacci tap indices |
| CRC_WIDTH | int | 32 | CRC width |
| CRC_DATA_WIDTH | int | 32 | Bits processed per CRC update (the 32-bit LFSR output) |
| CRC_POLY | logic [31:0] | 32'h04C11DB7 | CRC-32/Ethernet polynomial |
| CRC_INIT | logic [31:0] | 32'hFFFFFFFF | CRC initial value |
| CRC_XOROUT | logic [31:0] | 32'hFFFFFFFF | CRC final XOR |
| CRC_REFIN | int | 1 | Reflect input bytes |
| CRC_REFOUT | int | 1 | Reflect output |
| REPLICATION_FACTOR | int | (AXI_DATA_WIDTH+31)/32 | Derived: number of 32-bit LFSR copies per beat |
| CIW | int | (NUM_CHANNELS>1) ? $clog2(NUM_CHANNELS) : 1 | Derived: channel-index width |

**Note:** `CRC_*` must match `axi4_slave_wr_crc_check` (and the AXIS pattern blocks) exactly, or cross-block CRC comparison is meaningless.

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | input | 1 | AXI clock |
| aresetn | input | 1 | Active-low asynchronous reset |

### Test Control

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| crc_lfsr_reset | input | 1 | Pulse to reload all channel LFSR seeds and clear all CRCs / beat counts |

### Per-Channel Telemetry

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| read_crc_value | output | NUM_CHANNELS × 32 | Running CRC-32 per channel |
| read_crc_valid | output | NUM_CHANNELS | Per-channel CRC valid (set after first accepted beat) |
| read_beat_count | output | NUM_CHANNELS × 32 | Per-channel beats emitted |
| read_beat_count_total | output | 32 | Sum of per-channel beat counts (harness stop trigger) |

### AXI4 Read Address Channel (AR)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_arid | input | AXI_ID_WIDTH | Read address ID (low bits select the channel context) |
| s_axi_araddr | input | AXI_ADDR_WIDTH | Read address (unused for data generation) |
| s_axi_arlen | input | 8 | Burst length minus 1 (beats − 1) |
| s_axi_arsize | input | 3 | Burst size |
| s_axi_arburst | input | 2 | Burst type |
| s_axi_arlock | input | 1 | Lock type |
| s_axi_arcache | input | 4 | Cache attributes |
| s_axi_arprot | input | 3 | Protection attributes |
| s_axi_arqos | input | 4 | Quality of service |
| s_axi_arregion | input | 4 | Region identifier |
| s_axi_aruser | input | AXI_USER_WIDTH | User sideband (echoed on R) |
| s_axi_arvalid | input | 1 | AR valid |
| s_axi_arready | output | 1 | AR ready |

### AXI4 Read Data Channel (R)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_rid | output | AXI_ID_WIDTH | Read data ID (echoes captured `arid`) |
| s_axi_rdata | output | AXI_DATA_WIDTH | LFSR pattern data (32-bit LFSR replicated to fill the bus) |
| s_axi_rresp | output | 2 | Response, always `OKAY` |
| s_axi_rlast | output | 1 | Last beat of burst |
| s_axi_ruser | output | AXI_USER_WIDTH | User sideband (echoes captured `aruser`) |
| s_axi_rvalid | output | 1 | R valid |
| s_axi_rready | input | 1 | R ready |

### Status

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| busy | output | 1 | Protocol-handler busy indicator (from `axi4_slave_rd`) |

---

## Functional Description

### LFSR Pattern Generation

Each channel owns a `shifter_lfsr_fibonacci` instance (32-bit, taps `{32,22,2,1}`) seeded with `LFSR_SEED ^ channel_index`. XOR-ing the channel index into the seed guarantees each channel produces a distinct stream, so channel interleave at the shared AXI port cannot corrupt any one channel's sequence. Only the channel currently being served advances on a given R-beat handshake; all other channel LFSRs hold their state. On the global `crc_lfsr_reset` pulse every channel reloads its seed simultaneously.

### Data Replication to the Bus Width

The 32-bit LFSR output is expanded to `AXI_DATA_WIDTH` by replication. A generate block picks the right path: a direct assignment when the bus is exactly 32 bits, a whole-number replication when the width is a multiple of 32, or a replicate-and-truncate for non-aligned widths (`REPLICATION_FACTOR = (AXI_DATA_WIDTH+31)/32` copies, sliced down). The active channel's replicated word drives `s_axi_rdata`.

### Per-Channel CRC-32

Each channel has its own `dataint_crc` instance (CRC-32/Ethernet, `REFIN`/`REFOUT` = 1). The CRC absorbs one 32-bit LFSR word per accepted beat for that channel (`load_from_cascade` gated by "R beat AND active channel == this channel", `cascade_sel = 4'b1000`). A per-channel valid flag sets on the first accepted beat and a per-channel beat counter increments alongside. `crc_lfsr_reset` clears the CRC (via `load_crc_start`), the valid flag, and the counter. The `read_beat_count_total` output is a combinational sum across all channels, used by the harness as a workload-completion trigger.

### Burst FSM and Gapless Back-to-Back Bursts

A small two-state FSM (`RD_IDLE`, `RD_BURST`) drives the FUB-side AR/R handshake. AR is accepted when idle *or* on the last beat of the current burst — the latter (`w_rd_last_beat`) lets the next burst reload `r_rd_id` / `r_rd_beats_remaining` on the same cycle the current one finishes, keeping `rvalid` continuously asserted. The original idle-only accept forced a one-cycle dead gap per burst, which surfaced as ~1 starvation cycle per burst on the master's R channel (a slave-model artifact, not a DUT limitation); accepting the AR on `rlast` removes it. `rresp` is hardwired to `OKAY` and `rlast` asserts when `r_rd_beats_remaining` reaches 0.

### Standard Protocol Handler

All AR/R skid buffering and AXI protocol compliance are delegated to a `axi4_slave_rd` instance. The pattern-gen FSM and LFSR/CRC logic ride on that module's FUB-side (`fub_axi_ar*` / `fub_axi_r*`) interface, so the external `s_axi_*` ports are fully AXI4-compliant. (A header TODO notes that hand-rolled FUB logic should eventually wrap `axi4_slave_rd_mon` instead — tracked as task #78 — but the current handler is the standard `axi4_slave_rd`.)

---

## Usage Example

```systemverilog
// Synthetic read source for a 4-channel DMA characterization run.
axi4_slave_rd_pattern_gen #(
    .NUM_CHANNELS   (4),
    .AXI_ID_WIDTH   (8),
    .AXI_ADDR_WIDTH (32),
    .AXI_DATA_WIDTH (64),
    .LFSR_SEED      (32'hDEADBEEF)
) u_rd_src (
    .aclk                  (aclk),
    .aresetn               (aresetn),
    .crc_lfsr_reset        (csr_clear_pulse),   // re-arm all channels

    // Telemetry to the harness CSR block
    .read_crc_value        (rd_crc_value),
    .read_crc_valid        (rd_crc_valid),
    .read_beat_count       (rd_beat_count),
    .read_beat_count_total (rd_beats_total),

    // AR/R wired to the DUT's read master port
    .s_axi_arid    (dut_arid),   .s_axi_araddr  (dut_araddr),
    .s_axi_arlen   (dut_arlen),  .s_axi_arsize  (dut_arsize),
    .s_axi_arburst (dut_arburst),.s_axi_arlock  (dut_arlock),
    .s_axi_arcache (dut_arcache),.s_axi_arprot  (dut_arprot),
    .s_axi_arqos   (dut_arqos),  .s_axi_arregion(dut_arregion),
    .s_axi_aruser  (dut_aruser), .s_axi_arvalid (dut_arvalid),
    .s_axi_arready (dut_arready),

    .s_axi_rid   (dut_rid),   .s_axi_rdata  (dut_rdata),
    .s_axi_rresp (dut_rresp), .s_axi_rlast  (dut_rlast),
    .s_axi_ruser (dut_ruser), .s_axi_rvalid (dut_rvalid),
    .s_axi_rready(dut_rready),

    .busy (rd_busy)
);
```

---

## Design Notes

- **Seed-per-channel independence:** `LFSR_SEED ^ N` is deliberately simple but sufficient — a maximal-length LFSR seeded at distinct points produces streams that stay decorrelated over the characterization window, so per-channel CRCs are independently checkable.
- **CRC over the LFSR word, not the replicated bus:** only the 32-bit LFSR output feeds the CRC (`cascade_sel = 4'b1000`), so the CRC value is bus-width independent and interchangeable with the 32-bit-wide write checker and AXIS blocks.
- **Gapless accept is a measurement fix:** the back-to-back AR accept was added specifically so the read model wouldn't inject a false ~6% starvation artifact into the master's utilization numbers.
- **Reset separation:** `crc_lfsr_reset` is distinct from `aresetn` so the harness can re-arm the pattern between runs without a full block reset.
- **Standards note:** the AR/R glue is hand-rolled on top of `axi4_slave_rd`; the header flags a future refactor to the monitored `axi4_slave_rd_mon` wrapper (task #78).

---

## Related Modules

### Used By
- `axi4_dma_slaves` — bundles this read source with `axi4_slave_wr_crc_check` into a single source/sink slave pair
- `projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/stream_char_harness.sv` — on-chip read stimulus
- `projects/NexysA7/rapids_characterization/flows-rapids-beats/rtl/rapids_char_harness.sv` — on-chip read stimulus

### Uses
- **axi4_slave_rd.sv** — standard AXI4 read slave protocol handler (AR/R skid + compliance)
- **shifter_lfsr_fibonacci.sv** — per-channel maximal-length Fibonacci LFSR
- **dataint_crc.sv** — per-channel CRC-32 accumulator

### See Also
- **axi4_slave_wr_crc_check.sv** — the matching write-side CRC sink (same CRC config)
- **axi4_dma_slaves.sv** — the source/sink bundle
- **axis4_master_pattern_gen.sv** — AXIS equivalent of this generator

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi4_slave_rd_pattern_gen.sv`
- Protocol Handler: `rtl/amba/axi4/axi4_slave_rd.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Index: `docs/markdown/rtl-amba/index.md`
- Harness: `projects/NexysA7/ddr2-characterization/README.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
