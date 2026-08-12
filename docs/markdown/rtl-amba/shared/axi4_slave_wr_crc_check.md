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

# AXI4 Slave Write CRC Checker

**Module:** `axi4_slave_wr_crc_check.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`axi4_slave_wr_crc_check` is a write-only AXI4 slave that accepts AW/W bursts, folds the written data into a per-channel CRC-32, and returns B responses. It is the *sink* counterpart to `axi4_slave_rd_pattern_gen`: a master under test writes data, this slave CRCs it, and the resulting CRC can be compared against an independently computed golden value to prove the write path carried the data intact.

### Key Features

- Write-only AXI4 slave (AW + W + B channels) built on the standard `axi4_slave_wr` protocol handler
- Per-channel independent CRC-32 state, demuxed off the low bits of the captured `awid`
- CRC-32/Ethernet (poly `0x04C11DB7`, reflected in/out) — bit-identical to `axi4_slave_rd_pattern_gen`
- Configurable 32-bit data slice (`CRC_SLICE_OFFSET`) selects which 32-bit lane of a wide bus is CRC'd
- Gapless back-to-back bursts (AW accepted on the last W beat) so `wready` never drops mid-stream
- Separately-latched B id/user so back-to-back bursts return the correct response id
- Per-channel CRC / beat-count telemetry plus an aggregate beat-count total for harness stop triggers

---

## Module Purpose

The write half of a DMA characterization loop needs a slave that accepts write traffic at full rate and reports whether the data arrived correctly. This module CRCs the incoming write data per channel using exactly the same CRC-32 configuration as the read pattern generator, so if a master reads the LFSR pattern and writes it straight back, the write-side CRC must equal the read-side CRC. Any mismatch localizes a data-path corruption to the write path.

**Use Cases:**
- Terminating a DMA / streaming engine's write (`m_axi_wr`) port during characterization
- End-to-end integrity checks where read data is looped back and re-verified on write
- Per-channel multi-context validation on a shared write port
- On-chip (FPGA) write sink in the STREAM / RAPIDS characterization harnesses

**Key Benefit:** A memory-free write slave that produces a per-channel CRC-32 directly comparable to the read generator — a single register compare confirms the write path is clean, and the sink never backpressures the master unnecessarily.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| NUM_CHANNELS | int | 1 | Number of independent CRC contexts; channel index is `awid[CIW-1:0]` |
| SKID_DEPTH_AW | int | 2 | AW channel skid buffer depth |
| SKID_DEPTH_W | int | 4 | W channel skid buffer depth |
| SKID_DEPTH_B | int | 2 | B channel skid buffer depth |
| AXI_ID_WIDTH | int | 8 | AXI ID width |
| AXI_ADDR_WIDTH | int | 32 | AXI address width |
| AXI_DATA_WIDTH | int | 64 | AXI data width |
| AXI_USER_WIDTH | int | 1 | AXI user signal width |
| CRC_WIDTH | int | 32 | CRC width |
| CRC_DATA_WIDTH | int | 32 | Bits processed per CRC update |
| CRC_POLY | logic [31:0] | 32'h04C11DB7 | CRC-32/Ethernet polynomial |
| CRC_INIT | logic [31:0] | 32'hFFFFFFFF | CRC initial value |
| CRC_XOROUT | logic [31:0] | 32'hFFFFFFFF | CRC final XOR |
| CRC_REFIN | int | 1 | Reflect input bytes |
| CRC_REFOUT | int | 1 | Reflect output |
| CRC_SLICE_OFFSET | int | 0 | Which 32-bit slice of `wdata` to CRC (in 32-bit units) |
| CIW | int | (NUM_CHANNELS>1) ? $clog2(NUM_CHANNELS) : 1 | Derived: channel-index width |

**Note:** `CRC_*` must match `axi4_slave_rd_pattern_gen` exactly. A compile-time `$error` fires if `CRC_SLICE_OFFSET` selects a slice beyond `AXI_DATA_WIDTH`.

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
| crc_reset | input | 1 | Pulse to clear all channel CRCs, valid flags, and beat counts |

### Per-Channel Telemetry

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| write_crc_value | output | NUM_CHANNELS × 32 | Running CRC-32 per channel |
| write_crc_valid | output | NUM_CHANNELS | Per-channel CRC valid (set after first accepted W beat) |
| write_beat_count | output | NUM_CHANNELS × 32 | Per-channel W beats absorbed |
| write_beat_count_total | output | 32 | Sum of per-channel beat counts (harness stop trigger) |

### AXI4 Write Address Channel (AW)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_awid | input | AXI_ID_WIDTH | Write address ID (low bits select the channel context) |
| s_axi_awaddr | input | AXI_ADDR_WIDTH | Write address (unused for CRC) |
| s_axi_awlen | input | 8 | Burst length minus 1 |
| s_axi_awsize | input | 3 | Burst size |
| s_axi_awburst | input | 2 | Burst type |
| s_axi_awlock | input | 1 | Lock type |
| s_axi_awcache | input | 4 | Cache attributes |
| s_axi_awprot | input | 3 | Protection attributes |
| s_axi_awqos | input | 4 | Quality of service |
| s_axi_awregion | input | 4 | Region identifier |
| s_axi_awuser | input | AXI_USER_WIDTH | User sideband (echoed on B) |
| s_axi_awvalid | input | 1 | AW valid |
| s_axi_awready | output | 1 | AW ready |

### AXI4 Write Data Channel (W)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_wdata | input | AXI_DATA_WIDTH | Write data (the selected 32-bit slice is CRC'd) |
| s_axi_wstrb | input | AXI_DATA_WIDTH/8 | Write byte strobes (not used to gate the CRC) |
| s_axi_wlast | input | 1 | Last beat of burst |
| s_axi_wuser | input | AXI_USER_WIDTH | User sideband |
| s_axi_wvalid | input | 1 | W valid |
| s_axi_wready | output | 1 | W ready |

### AXI4 Write Response Channel (B)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_bid | output | AXI_ID_WIDTH | Response ID (separately latched at WLAST) |
| s_axi_bresp | output | 2 | Response, always `OKAY` |
| s_axi_buser | output | AXI_USER_WIDTH | User sideband |
| s_axi_bvalid | output | 1 | B valid |
| s_axi_bready | input | 1 | B ready |

### Status

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| busy | output | 1 | Protocol-handler busy indicator (from `axi4_slave_wr`) |

---

## Functional Description

### Data Slice Extraction

A wide AXI bus carries several 32-bit lanes; only one is CRC'd so the CRC stays interchangeable with the 32-bit read generator. A generate block assigns `data_slice` directly when the bus is 32 bits wide, and otherwise selects `wdata[CRC_SLICE_OFFSET*32 +: 32]`. A compile-time assertion rejects a `CRC_SLICE_OFFSET` that would read past the end of the bus.

### Per-Channel CRC-32

Each channel owns a `dataint_crc` instance (CRC-32/Ethernet, `REFIN`/`REFOUT` = 1, `cascade_sel = 4'b1000`) fed the 32-bit `data_slice`. The channel selector `w_active_ch` is the low `CIW` bits of the captured `awid` (`r_wr_id`) — because the AW FSM accepts one burst at a time and W is in-order with AW, the active burst's id identifies the channel during its W beats. A CRC absorbs one word per accepted W beat for its channel (`ch_load_from_cascade` = "accepted W beat AND active channel == this channel"). Per-channel valid flags and beat counters track alongside; `crc_reset` clears them all. `write_beat_count_total` is a combinational sum across channels for the harness stop trigger.

### Write Burst FSM and Gapless Bursts

A compact FSM tracks a single active burst via `r_wr_active`. `awready` asserts when not active *or* on the last W beat of the current burst (`w_wr_last_beat`), letting the next burst's AW be accepted back-to-back so `wready` (`= r_wr_active`) never drops between bursts. This mirrors the read-slave gapless fix — without it, a one-cycle `!active` gap per burst would become the write-side throughput limiter once the read slave feeds data gaplessly.

### Back-to-Back B Response Id Latching

When bursts run back-to-back, `r_wr_id` is reloaded with the *next* burst's id on the same cycle the current burst's WLAST lands -- so the B channel cannot be driven from it. Instead an inline 16-deep B-response FIFO (`BFIFO_DEPTH = 16`) pushes the completing burst's `{user, id}` on every WLAST and pops on the B handshake. Multiple outstanding B responses queue cleanly; gapless multi-channel bursts never drop one. (An earlier single-outstanding `r_b_pending` design did drop them, which is exactly why the FIFO replaced it.)

### Standard Protocol Handler

AW/W/B skid buffering and AXI compliance are delegated to a `axi4_slave_wr` instance; the CRC and FSM logic ride on its FUB-side (`fub_axi_aw*` / `fub_axi_w*` / `fub_axi_b*`) interface. (A header TODO tracks a future refactor to wrap the monitored `axi4_slave_wr_mon` — task #79.)

---

## Usage Example

```systemverilog
// Synthetic write sink for a 4-channel DMA characterization run.
axi4_slave_wr_crc_check #(
    .NUM_CHANNELS   (4),
    .AXI_ID_WIDTH   (8),
    .AXI_ADDR_WIDTH (32),
    .AXI_DATA_WIDTH (64),
    .CRC_SLICE_OFFSET(0)
) u_wr_sink (
    .aclk                   (aclk),
    .aresetn                (aresetn),
    .crc_reset              (csr_clear_pulse),

    // Telemetry to the harness CSR block
    .write_crc_value        (wr_crc_value),
    .write_crc_valid        (wr_crc_valid),
    .write_beat_count       (wr_beat_count),
    .write_beat_count_total (wr_beats_total),

    // AW/W/B wired to the DUT's write master port
    .s_axi_awid   (dut_awid),   .s_axi_awaddr  (dut_awaddr),
    .s_axi_awlen  (dut_awlen),  .s_axi_awsize  (dut_awsize),
    .s_axi_awburst(dut_awburst),.s_axi_awlock  (dut_awlock),
    .s_axi_awcache(dut_awcache),.s_axi_awprot  (dut_awprot),
    .s_axi_awqos  (dut_awqos),  .s_axi_awregion(dut_awregion),
    .s_axi_awuser (dut_awuser), .s_axi_awvalid (dut_awvalid),
    .s_axi_awready(dut_awready),

    .s_axi_wdata (dut_wdata), .s_axi_wstrb (dut_wstrb),
    .s_axi_wlast (dut_wlast), .s_axi_wuser (dut_wuser),
    .s_axi_wvalid(dut_wvalid),.s_axi_wready(dut_wready),

    .s_axi_bid   (dut_bid),   .s_axi_bresp (dut_bresp),
    .s_axi_buser (dut_buser), .s_axi_bvalid(dut_bvalid),
    .s_axi_bready(dut_bready),

    .busy (wr_busy)
);
```

---

## Design Notes

- **CRC config must match the source:** the whole point is a comparable value. `CRC_POLY`, `CRC_INIT`, `CRC_XOROUT`, `CRC_REFIN`, `CRC_REFOUT`, and the 32-bit slice width are all fixed to mirror `axi4_slave_rd_pattern_gen`.
- **Channel demux by AW id, not W sideband:** because W is in-order behind AW and only one burst is active at a time, the captured `awid` unambiguously names the channel for that burst's W beats.
- **B responses queue through a 16-deep FIFO** (`BFIFO_DEPTH`): up to 16 completed bursts can await their B handshake without loss, so a slow B-drain or gapless multi-channel bursts are safe up to that depth.
- **Gapless accept is a measurement fix:** the back-to-back AW accept prevents the sink from injecting a false ~1-cycle-per-burst starvation into write-side utilization numbers.
- **Standards note:** the AW/W/B glue is hand-rolled on top of `axi4_slave_wr`; a future refactor to `axi4_slave_wr_mon` is tracked as task #79.

---

## Related Modules

### Used By
- `axi4_dma_slaves` — bundles this write sink with `axi4_slave_rd_pattern_gen` into a single source/sink slave pair
- `projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/stream_char_harness.sv` — on-chip write sink
- `projects/NexysA7/rapids_characterization/flows-rapids-beats/rtl/rapids_char_harness.sv` — on-chip write sink

### Uses
- **axi4_slave_wr.sv** — standard AXI4 write slave protocol handler (AW/W/B skid + compliance)
- **dataint_crc.sv** — per-channel CRC-32 accumulator

### See Also
- **axi4_slave_rd_pattern_gen.sv** — the matching read-side pattern source (same CRC config)
- **axi4_dma_slaves.sv** — the source/sink bundle
- **axis4_slave_pattern_check.sv** — AXIS equivalent checker

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi4_slave_wr_crc_check.sv`
- Protocol Handler: `rtl/amba/axi4/axi4_slave_wr.sv`

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
