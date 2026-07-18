# Test Methodology

This chapter describes what is exercised on the FPGA block (Figure 2.1) and how
throughput and data integrity are measured.

## What is under test

The split RAPIDS beats DMA — the `rapids_src_beats` (read → AXIS) and
`rapids_snk_beats` (AXIS → write) engines. Because all stimulus, checking, and
memory are on-chip, the board runs at line rate and every measurement is taken at
the DUT's own AXI/AXIS ports.

## What is measured, and how

| Quantity | How it is obtained |
|----------|--------------------|
| Data integrity | Per-channel golden CRC-32: SINK `WR_CRC[ch]` vs `GEN_EXP_CRC[ch]`; SOURCE `CHK_ACT_CRC[ch]` vs `RD_CRC[ch]`; plus `STATUS.data_error` |
| Throughput | AXIS/AXI bus meters + exact byte/packet counters (`OBS_SIN/SOUT_BYTES/PKTS`) over the timed window |
| Utilization | `OBS_{RD,WR,SIN,SOUT}_{PROD,BP,STARV,IDLE}` buckets |
| Scaling | Repeat across the active-channel mask |

: What is measured

**A measurement run uses atomic launch (Waveform 5.1):** configure the DUT by
name over APB, load descriptors into the per-half descriptor RAM, stage the kick
parameters (`CSR_KICK_MASK`, `CSR_KICK_BASE_*`, `CSR_KICK_STRIDE`), then write a
single `CSR_GO` that arms the bus meters, starts the generator, and fires the
channel kicks together. `CSR_OBS_TARGET = channels × beats` freezes the meter
window deterministically; the host then reads the CRCs and counters.

## Workloads

| Axis | Values |
|------|--------|
| Channels | 1, 2, 4 (Nexys) / up to 8 (Genesys 2) |
| Beats | 1, 4, 8, 16 |
| Backpressure | off, on (SOURCE only, via `chk_ready_en`) |
| Seed | default, alternate (SINK only — SOURCE read-gen is fixed `0xDEADBEEF`) |

: Characterization workloads

## The oracle

Every beat is checked against a deterministic **golden CRC-32** (LFSR seed
`0xDEADBEEF`, taps `{32,22,2,1}`, poly `0x04C11DB7`). The host's
`rapids_char_golden.py` computes the same value the on-chip checkers do; a pass is
a match on both paths (`make suite` = 48/48).

## Measurement pitfalls

- **Arm every run** — the bus meters have no auto-reset; use `OBS_CTRL.arm` or the
  `CSR_GO` write, or the window stays frozen on the first capture.
- **SINK re-arm** — the sink is fully trustworthy only on the first arm after a
  board reset; the runner pulses `CHANNEL_RESET` before each run.
- The generator self-CRC (`GEN_EXP_VLD`) is corroboration only; PASS anchors on
  the data-path CRC (`WR_CRC`).
