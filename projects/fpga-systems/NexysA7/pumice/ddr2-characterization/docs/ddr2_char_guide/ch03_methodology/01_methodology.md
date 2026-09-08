# Test Methodology

This chapter describes what is exercised on the FPGA block (Figure 2.1) and how
throughput, latency, and data integrity are measured.

## What is under test

The **pumice** memory controller (black box) driving the real onboard DDR2,
stimulated by the two master-side AXI4 engines. Every measurement is taken on the
internal AXI wires between the engines and the controller, so the numbers reflect
the controller + PHY + device as a whole.

## What is measured, and how

| Quantity | How it is obtained |
|----------|--------------------|
| Throughput | `beats × bytes_per_beat / (TIMER_CYCLES × 10 ns)` — the timer bounds the run in `sys_clk` cycles |
| Latency histogram | `OBS_HIST_SEL` selects bus (rd/wr) + metric (AR→firstR / AR→RLAST) + bin; `OBS_HIST_COUNT` / `OBS_HIST_TOTAL` read it back. Bin *b* covers [2^b, 2^(b+1)) cycles |
| Data integrity | `CRC_ACTUAL` vs `CRC_EXPECTED` (`CRC_MATCH`), plus `BEATS_MISM` |
| Utilization | `OBS_{RD,WR}_{PROD,BP,STARV,IDLE}` bus-meter buckets |

: What is measured

**A measurement run:** program the engine config (address pattern, burst length,
txn count, LFSR seed), `clear_stats`, kick with `CTRL.start_wr` / `start_rd`, poll
`STATUS.wr_done` / `rd_done`, then read the timer, CRC, histogram, and meters. The
write engine latches the expected CRC as it generates the pattern; the read engine
re-reads and computes the actual CRC.

## Workloads

| Axis | Values |
|------|--------|
| Access pattern | `incremental`, `row_major`, `col_major`, `col_major_interleaved` |
| Controller preset | `baseline`, `bank_interleave`, `open_page`, `inorder`, `reorder`, … (over the pumice APB slave) |
| Burst / count / stride | swept per `--char-profile` (smoke / matrix / full) |

: Characterization workloads

## The oracle

Integrity is judged against a deterministic **LFSR pattern + CRC-32**: the write
engine's `CRC_EXPECTED` must equal the read engine's `CRC_ACTUAL` with
`BEATS_MISM = 0`. The same golden logic runs in sim (Chapter 6).

## Measurement pitfalls

- `STATUS.any_error` is **sticky** — clear it with `clear_stats` between phases or
  every later run looks wedged.
- Keep board runs `txn ≤ 1024` (read-engine CAM ceiling) for clean completion;
  the *rate* stays valid at scale.
- `col_major` stride × large txn can alias past the 128 MB device — bound it.
- The sim must be built at the board's exact `DFI_RATE` / GEAR or it passes while
  the board fails (Chapter 6).
