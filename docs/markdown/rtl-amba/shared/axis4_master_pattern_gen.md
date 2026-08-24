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

# AXI-Stream Master Pattern Generator

**Module:** `axis4_master_pattern_gen.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

`axis4_master_pattern_gen` is an AXI-Stream master that emits a deterministic, per-channel LFSR data pattern for characterization and verification. It is the AXIS *sink* stimulus for the RAPIDS characterization harness, and it is pattern/CRC-consistent with the AXI4 pattern blocks: the per-channel 32-bit CRC-32 it computes is bit-identical to what `axi4_slave_wr_crc_check` produces for the same emitted stream (self-check path: `axis_gen → m_axi_wr → wr_crc_check`).

### Key Features

- AXI-Stream master (`m_axis_*`) with no address channel — simpler than the AXI4 pattern generators
- Per-channel independent LFSR (seed `^ ch`) and CRC-32, copied verbatim from `axi4_slave_rd_pattern_gen`
- Sequential per-channel scheduling — finish one channel's beats, then the next, so each channel's LFSR sequence is contiguous
- Channel mask (`cfg_channel_mask`) selects active channels (0 → all)
- Programmable beats-per-channel and `tlast` cadence (`cfg_beats_per_pkt`)
- Per-channel expected-CRC / beat-count telemetry plus an aggregate total
- LFSR/CRC advance only on accepted beats, so beat N of channel C is a deterministic function of `(seed ^ C, N)` independent of `tready` stalls

Characterizing a stream-consuming engine (a "sink") needs a deterministic source that a downstream checker can predict. This block streams a known LFSR pattern per channel and computes the CRC-32 that the same data will produce when it lands in a CRC-checking sink. Because the LFSR advances only on accepted beats, backpressure never perturbs the sequence — the emitted data is a pure function of channel and beat index, and the exported per-channel CRC is the golden value for end-to-end integrity.

**Use Cases:**
- Driving a RAPIDS sink engine's AXIS input during characterization
- Sink self-check: stream into a DMA write path terminated by `axi4_slave_wr_crc_check` and compare CRCs
- Per-channel throughput / backpressure sweeps with deterministic, reproducible data
- On-chip (FPGA) stream stimulus in the RAPIDS characterization harness

**Key Benefit:** A memory-free, backpressure-insensitive stream source whose per-channel CRC-32 matches the AXI4 CRC blocks bit-for-bit, so a stream integrity test reduces to a single register compare.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| NUM_CHANNELS | int | 1 | Independent LFSR/CRC contexts; channel index drives `tid` |
| AXIS_DATA_WIDTH | int | 512 | Stream data width (must be a multiple of `LFSR_WIDTH`) |
| AXIS_ID_WIDTH | int | 8 | `tid` width |
| AXIS_DEST_WIDTH | int | 4 | `tdest` width |
| AXIS_USER_WIDTH | int | 1 | `tuser` width |
| LFSR_WIDTH | int | 32 | LFSR width (fixed; must match the AXI4 blocks) |
| LFSR_SEED | logic [31:0] | 32'hDEADBEEF | Base LFSR seed; channel N uses `seed ^ N` |
| LFSR_TAPS | logic [47:0] | {12'd23, 12'd3, 12'd2, 12'd1} | Maximal-length Fibonacci taps |
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

**Note:** LFSR + CRC parameters must match `axi4_slave_rd_pattern_gen` / `axi4_slave_wr_crc_check` for cross-block CRC consistency.

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk | input | 1 | Stream clock |
| rst_n | input | 1 | Active-low asynchronous reset |

### Configuration / Control

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_start | input | 1 | Pulse to begin a run (seeds all channels) |
| cfg_lfsr_seed | input | LFSR_WIDTH | Seed override (0 → use `LFSR_SEED` param) |
| cfg_channel_mask | input | NUM_CHANNELS | Active channels (0 → all channels active) |
| cfg_num_beats | input | BEAT_COUNT_WIDTH | Beats to send per channel |
| cfg_beats_per_pkt | input | BEAT_COUNT_WIDTH | `tlast` cadence (0 → one packet per channel) |
| cfg_tdest | input | AXIS_DEST_WIDTH | Value driven on `tdest` |
| cfg_busy | output | 1 | High while running (state != IDLE) |
| cfg_done | output | 1 | One-cycle pulse at end of run |

### Per-Channel Telemetry

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| o_expected_crc | output | NUM_CHANNELS × 32 | Per-channel expected CRC-32 |
| o_expected_crc_valid | output | NUM_CHANNELS | Per-channel CRC valid |
| o_beat_count | output | NUM_CHANNELS × 32 | Per-channel beats emitted |
| o_beat_count_total | output | 32 | Sum across channels (harness stop trigger) |

### AXI-Stream Master (m_axis)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| m_axis_tvalid | output | 1 | Beat valid (asserted in the RUN state) |
| m_axis_tready | input | 1 | Downstream ready |
| m_axis_tdata | output | AXIS_DATA_WIDTH | `{REP{lfsr_out[ch]}}` — 32-bit LFSR replicated to fill the bus |
| m_axis_tstrb | output | STRB_WIDTH | All-ones (full beat) |
| m_axis_tlast | output | 1 | Packet last (per `cfg_beats_per_pkt`, and each channel's final beat) |
| m_axis_tid | output | AXIS_ID_WIDTH | Channel index of the current beat |
| m_axis_tdest | output | AXIS_DEST_WIDTH | Driven from `cfg_tdest` |
| m_axis_tuser | output | AXIS_USER_WIDTH | Tied to 0 |

---

## Functional Description

### Scheduling FSM

A three-state FSM (`IDLE`, `RUN`, `DONE`) sequences a run. On `cfg_start` the effective channel mask, beats-per-channel, and `tlast` cadence are latched; if there are no beats or no active channel it drops straight to `DONE`, otherwise it selects the first active channel and enters `RUN`. `DONE` pulses `cfg_done` for one cycle and returns to `IDLE`. `m_axis_tvalid` is asserted exactly in `RUN`.

### Sequential Per-Channel Scheduling

Channels are streamed one at a time in ascending index order among the masked set. A `f_next_active_after` function priority-scans the mask for the lowest active channel index strictly greater than the current one (or the first active channel at start). When the current channel's beats are exhausted (`w_ch_last_beat`), the FSM advances to the next active channel and reloads its beat count; when none remain it goes to `DONE`. Because channels run to completion in turn, each channel's LFSR sequence is contiguous and uninterrupted.

### Per-Channel LFSR + CRC (Verbatim from the AXI4 blocks)

Each channel owns a `shifter_lfsr_fibonacci` (32-bit, taps `{23,3,2,1}`, seed `w_seed ^ ch`) and a `dataint_crc` (CRC-32/Ethernet, `cascade_sel = 4'b1000`). The active channel advances on its accepted beat (`ch_beat = w_beat && r_ch == ch`); all channels reload their seed / clear their CRC on the global load pulse (`cfg_start` in IDLE). The seed, taps, replication, CRC instantiation, and gating are copied verbatim from `axi4_slave_rd_pattern_gen` so the per-channel 32-bit CRC is bit-identical. Per-channel valid flags and beat counters track alongside, and `o_beat_count_total` is a combinational sum for the harness stop trigger.

### Stream Outputs and tlast Cadence

`m_axis_tdata` is the active channel's LFSR output replicated `REP` times; `tid` carries the channel index; `tstrb` is all-ones (full beats); `tdest` is driven from `cfg_tdest`; `tuser` is 0. `tlast` asserts on each channel's final beat, and additionally every `cfg_beats_per_pkt` beats when that cadence is non-zero (0 → one packet spanning the channel's whole run). A per-channel packet counter (`r_pkt_cnt`) resets at each `tlast` and at channel boundaries.

### Backpressure Insensitivity

Because the LFSR and CRC advance only on accepted beats (`w_beat = tvalid && tready`), a downstream `tready` stall simply holds the current beat — the emitted value for beat N of channel C is always `f(seed ^ C, N)` regardless of stall pattern. This is what lets the exported per-channel CRC serve as a stable golden value.

---

## Usage Example

```systemverilog
// AXIS stimulus for a 4-channel RAPIDS sink characterization run.
axis4_master_pattern_gen #(
    .NUM_CHANNELS    (4),
    .AXIS_DATA_WIDTH (512),
    .AXIS_ID_WIDTH   (8),
    .LFSR_SEED       (32'hDEADBEEF)
) u_axis_gen (
    .clk (clk),
    .rst_n (rst_n),

    // Control
    .cfg_start         (csr_start_pulse),
    .cfg_lfsr_seed     (32'd0),        // use param default
    .cfg_channel_mask  (4'b1111),      // all channels
    .cfg_num_beats     (32'd1024),     // per channel
    .cfg_beats_per_pkt (32'd16),       // tlast every 16 beats
    .cfg_tdest         (4'd0),
    .cfg_busy          (gen_busy),
    .cfg_done          (gen_done),

    // Golden CRCs for the downstream checker
    .o_expected_crc       (gen_crc),
    .o_expected_crc_valid (gen_crc_valid),
    .o_beat_count         (gen_beats),
    .o_beat_count_total   (gen_beats_total),

    // Stream to the DUT sink
    .m_axis_tvalid (s_tvalid), .m_axis_tready (s_tready),
    .m_axis_tdata  (s_tdata),  .m_axis_tstrb  (s_tstrb),
    .m_axis_tlast  (s_tlast),  .m_axis_tid    (s_tid),
    .m_axis_tdest  (s_tdest),  .m_axis_tuser  (s_tuser)
);
```

---

## Design Notes

- **CRC-consistency by construction:** the LFSR and CRC blocks are copied verbatim from `axi4_slave_rd_pattern_gen`, so a stream emitted here and re-CRC'd by `axi4_slave_wr_crc_check` (or checked by `axis4_slave_pattern_check`) yields identical per-channel CRCs.
- **Sequential scheduling keeps sequences contiguous:** finishing one channel before starting the next means each channel's LFSR runs as an unbroken sequence, matching how the checker regenerates it.
- **No address channel:** as a pure stream the generator is simpler than the AXI4 pattern gens — no `dma_address_gen`, no burst FSM, just per-channel beat counting.
- **Backpressure-safe:** advancing only on accepted beats decouples the data sequence from `tready` timing.
- **Data width constraint:** `AXIS_DATA_WIDTH` must be a multiple of `LFSR_WIDTH` since `tdata = REP × lfsr_out`.

---

## Related Modules

### Used By
- `projects/NexysA7/rapids_characterization/flows-rapids-beats/rtl/rapids_char_harness.sv` — on-chip AXIS sink stimulus
- RAPIDS sink-path characterization flows

### Uses
- **shifter_lfsr_fibonacci.sv** — per-channel maximal-length Fibonacci LFSR
- **dataint_crc.sv** — per-channel CRC-32 accumulator

### See Also
- **axis4_slave_pattern_check.sv** — the matching AXIS checker (same LFSR/CRC config)
- **axi4_slave_rd_pattern_gen.sv** — the AXI4 read pattern source this is copied from
- **axi4_slave_wr_crc_check.sv** — CRC sink whose values match this generator

---

## References

### Source Code
- RTL: `rtl/amba/shared/axis4_master_pattern_gen.sv`

### Documentation
- Architecture: `docs/markdown/rtl-amba/shared/README.md`
- Index: `docs/markdown/rtl-amba/index.md`
- Harness: `projects/components/dmas/rapids/CONTROL_ENGINE_INTEGRATION.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to rtl-amba Index](../index.md)
