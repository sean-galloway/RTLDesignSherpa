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

# AXI-Stream Slave Pattern Checker

**Module:** `axis4_slave_pattern_check.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`axis4_slave_pattern_check` is an AXI-Stream slave that consumes a stream and checks it against a deterministic, per-channel LFSR pattern, computing a per-channel CRC-32 as it goes. It is the AXIS *source* checker for the RAPIDS characterization harness and is pattern/CRC-consistent with `axi4_slave_rd_pattern_gen`: the per-channel CRC-32 it computes is bit-identical to `axi4_slave_rd_pattern_gen.read_crc_value` for the same stream (self-check path: `rd_gen → m_axis → axis_check`).

### Key Features

- AXI-Stream slave (`s_axis_*`), pure sink with `tready` driven by a `ready_en` input to model backpressure
- Per-channel independent LFSR (seed `^ ch`) and CRC-32, copied verbatim from `axi4_slave_rd_pattern_gen`
- Incoming beats demuxed by `s_axis_tid[CIW-1:0]` into the matching channel context
- Per-beat compare against the locally regenerated pattern; sticky `o_data_error` on any mismatch
- Per-channel actual-CRC / beat-count telemetry plus aggregate beat and packet (`tlast`) counters
- LFSR advances only on accepted beats, so the check is independent of upstream stalls and cross-channel interleave

---

## Module Purpose

Characterizing a stream-*producing* engine (a "source") needs a checker that knows what the engine should emit. This block seeds every channel identically to the generator and, on each accepted beat, regenerates the expected pattern for that channel and compares it against the received `tdata`. It also folds the regenerated data into a per-channel CRC-32 for a whole-run summary. Because the LFSR advances only on accepted beats and is demuxed by `tid`, the check is robust to backpressure and to arbitrary interleave of channels on the shared stream.

**Use Cases:**
- Terminating and verifying a RAPIDS source engine's AXIS output during characterization
- Source self-check: check a stream produced from `axi4_slave_rd_pattern_gen` and compare CRCs
- Per-channel integrity checking under backpressure (via `ready_en`)
- On-chip (FPGA) stream checker in the RAPIDS characterization harness

**Key Benefit:** A memory-free stream checker that both pinpoints (sticky `o_data_error` per beat) and summarizes (per-channel CRC-32 identical to the generator) integrity, robust to stalls and channel interleave.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| NUM_CHANNELS | int | 1 | Independent LFSR/CRC contexts; channel = `tid` low bits |
| AXIS_DATA_WIDTH | int | 512 | Stream data width (must be a multiple of `LFSR_WIDTH`) |
| AXIS_ID_WIDTH | int | 8 | `tid` width |
| AXIS_DEST_WIDTH | int | 4 | `tdest` width |
| AXIS_USER_WIDTH | int | 1 | `tuser` width |
| LFSR_WIDTH | int | 32 | LFSR width (fixed; must match the generator) |
| LFSR_SEED | logic [31:0] | 32'hDEADBEEF | Base LFSR seed; channel N uses `seed ^ N` |
| LFSR_TAPS | logic [47:0] | {12'd32, 12'd22, 12'd2, 12'd1} | Maximal-length Fibonacci taps |
| CRC_WIDTH | int | 32 | CRC width |
| CRC_DATA_WIDTH | int | 32 | Bits per CRC update |
| CRC_POLY | logic [31:0] | 32'h04C11DB7 | CRC-32/Ethernet polynomial |
| CRC_INIT | logic [31:0] | 32'hFFFFFFFF | CRC initial value |
| CRC_XOROUT | logic [31:0] | 32'hFFFFFFFF | CRC final XOR |
| CRC_REFIN | int | 1 | Reflect input |
| CRC_REFOUT | int | 1 | Reflect output |
| BEAT_COUNT_WIDTH | int | 32 | Width of beat / packet counters |
| STRB_WIDTH | int | AXIS_DATA_WIDTH/8 | Derived: `tstrb` width |
| REP | int | AXIS_DATA_WIDTH/LFSR_WIDTH | Derived: 32-bit LFSR copies per beat |
| CIW | int | (NUM_CHANNELS>1) ? $clog2(NUM_CHANNELS) : 1 | Derived: channel-index width |

**Note:** LFSR + CRC parameters must match `axi4_slave_rd_pattern_gen` / `axis4_master_pattern_gen` for cross-block CRC consistency.

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk | input | 1 | Stream clock |
| rst_n | input | 1 | Active-low asynchronous reset |

### Configuration / Control

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_start | input | 1 | Pulse to arm and seed all channels (also clears errors/counters) |
| cfg_lfsr_seed | input | LFSR_WIDTH | Seed override (0 → use `LFSR_SEED` param) |
| ready_en | input | 1 | Drives `s_axis_tready` (tie high for a pure sink; deassert to model backpressure) |

### Telemetry

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_actual_crc | output | NUM_CHANNELS × 32 | Per-channel actual CRC-32 |
| o_actual_crc_valid | output | NUM_CHANNELS | Per-channel CRC valid |
| o_data_error | output | 1 | Sticky: any beat mismatched the expected pattern |
| o_beat_count | output | NUM_CHANNELS × 32 | Per-channel beats received |
| o_beat_count_total | output | 32 | Sum across channels (harness stop trigger) |
| o_pkt_count | output | BEAT_COUNT_WIDTH | Aggregate `tlast` beats received |

### AXI-Stream Slave (s_axis)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axis_tvalid | input | 1 | Beat valid |
| s_axis_tready | output | 1 | Ready (= `ready_en`) |
| s_axis_tdata | input | AXIS_DATA_WIDTH | Received data (compared to `{REP{lfsr_out[ch]}}`) |
| s_axis_tstrb | input | STRB_WIDTH | Byte strobes (not used by the check) |
| s_axis_tlast | input | 1 | Packet last (counted into `o_pkt_count`) |
| s_axis_tid | input | AXIS_ID_WIDTH | Channel selector (`tid[CIW-1:0]`) |
| s_axis_tdest | input | AXIS_DEST_WIDTH | Destination (unused) |
| s_axis_tuser | input | AXIS_USER_WIDTH | User sideband (unused) |

---

## Functional Description

### Readiness and Beat Handshake

`s_axis_tready` is driven directly from `ready_en` — tie it high for a pure, always-ready sink, or deassert it to model downstream backpressure. An accepted beat is `w_beat = tvalid && tready`. Because the same handshake gates both the compare and the LFSR/CRC advance, the checker and the upstream generator advance in lockstep. The active channel for a beat is `s_axis_tid[CIW-1:0]`.

### Per-Channel LFSR + CRC Regeneration (Verbatim from the Generator)

Each channel owns a `shifter_lfsr_fibonacci` (32-bit, taps `{32,22,2,1}`, seed `w_seed ^ ch`) and a `dataint_crc` (CRC-32/Ethernet, `cascade_sel = 4'b1000`). On `cfg_start` (the arm/load pulse) every channel reloads its seed and clears its CRC / counters. A channel advances only on an accepted beat carrying its `tid` (`ch_beat = w_beat && w_ch == ch`). The seed, taps, replication, CRC instantiation, and gating are copied verbatim from `axi4_slave_rd_pattern_gen`, so the per-channel CRC is bit-identical. Each channel exposes `o_actual_crc`, `o_actual_crc_valid`, and `o_beat_count`; `o_beat_count_total` is a combinational sum.

### Per-Beat Compare and Sticky Error

The expected data for the active channel is its current LFSR value replicated to the bus width (`expected_data_per_ch[w_ch] = {REP{lfsr_out[ch]}}`), sampled *before* the LFSR advances on the same edge. A mismatch (`w_beat && tdata != expected`) latches `o_data_error` sticky until the next `cfg_start`. Because the compare uses the pre-advance value and the LFSR steps only on accepted beats, the check is independent of upstream stalls and of how channels interleave on the shared stream.

### Packet Counting

`o_pkt_count` increments on every accepted beat that carries `tlast`, giving an aggregate packet count across channels. Both `o_data_error` and `o_pkt_count` are cleared by `cfg_start`.

---

## Usage Example

```systemverilog
// AXIS checker terminating a 4-channel RAPIDS source engine.
axis4_slave_pattern_check #(
    .NUM_CHANNELS    (4),
    .AXIS_DATA_WIDTH (512),
    .AXIS_ID_WIDTH   (8),
    .LFSR_SEED       (32'hDEADBEEF)
) u_axis_chk (
    .clk (clk),
    .rst_n (rst_n),

    // Control
    .cfg_start     (csr_arm_pulse),
    .cfg_lfsr_seed (32'd0),       // use param default
    .ready_en      (sink_ready),  // 1 = always ready; toggle to backpressure

    // Telemetry to the harness CSR block
    .o_actual_crc       (chk_crc),
    .o_actual_crc_valid (chk_crc_valid),
    .o_data_error       (chk_data_error),
    .o_beat_count       (chk_beats),
    .o_beat_count_total (chk_beats_total),
    .o_pkt_count        (chk_pkts),

    // Stream from the DUT source
    .s_axis_tvalid (m_tvalid), .s_axis_tready (m_tready),
    .s_axis_tdata  (m_tdata),  .s_axis_tstrb  (m_tstrb),
    .s_axis_tlast  (m_tlast),  .s_axis_tid    (m_tid),
    .s_axis_tdest  (m_tdest),  .s_axis_tuser  (m_tuser)
);

// Clean check: no mismatch and per-channel CRC matches the generator's.
assign stream_ok = !chk_data_error && (chk_crc[ch] == gen_expected_crc[ch]);
```

---

## Design Notes

- **CRC-consistency by construction:** the LFSR and CRC blocks are copied verbatim from `axi4_slave_rd_pattern_gen`, so a stream produced by that generator (or by `axis4_master_pattern_gen`) yields identical per-channel CRCs here.
- **Compare uses the pre-advance LFSR value:** the expected data is sampled before the channel's LFSR steps on the same clock edge, so the beat is compared against the value the generator emitted, not the next one.
- **Two integrity signals:** sticky `o_data_error` pinpoints that *some* beat disagreed, while the per-channel CRC lets the harness confirm the exact stream matched end-to-end.
- **Backpressure via `ready_en`:** exposing readiness as a config input lets sweeps drive the checker as an always-ready sink or as a throttling one without extra logic.
- **Data width constraint:** `AXIS_DATA_WIDTH` must be a multiple of `LFSR_WIDTH` since the expected data is `REP × lfsr_out`.

---

## Related Modules

### Used By
- `projects/NexysA7/rapids_characterization/flows-rapids-beats/rtl/rapids_char_harness.sv` — on-chip AXIS source checker
- RAPIDS source-path characterization flows

### Uses
- **shifter_lfsr_fibonacci.sv** — per-channel maximal-length Fibonacci LFSR
- **dataint_crc.sv** — per-channel CRC-32 accumulator

### See Also
- **axis4_master_pattern_gen.sv** — the matching AXIS generator (same LFSR/CRC config)
- **axi4_slave_rd_pattern_gen.sv** — the AXI4 read pattern source this is copied from
- **axi4_master_rd_crc_check.sv** — the AXI4 read-side per-beat compare + CRC counterpart

---

## References

### Source Code
- RTL: `rtl/amba/shared/axis4_slave_pattern_check.sv`

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Index: `docs/markdown/RTLAmba/index.md`
- Harness: `projects/components/rapids/CONTROL_ENGINE_INTEGRATION.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
