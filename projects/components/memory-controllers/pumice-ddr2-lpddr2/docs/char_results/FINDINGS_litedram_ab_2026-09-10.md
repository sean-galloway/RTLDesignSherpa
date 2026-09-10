# LiteDRAM vs pumice through the SAME harness (2026-09-10)

Same board (Nexys A7-100T, MT47H64M16 x16 DDR2), same operating point (75 MHz
sys / 1:2 / DDR2-300, MR0 = 0x0432: BL4, CL3), same RTL in front of the
controller (`char_engine_block`: chargen_regs, generator arrays, crossbars, bus
meters, latency histograms), same UART bridge and address map, same host
program (`pumice_char` matrix profile, `--char-scale 1000`, one writer + one
reader), same CSV writer. The only difference is the controller behind the
AXI4 port.

Sources: `litedram_2026-09-10_matrix.csv` (this run, timing-clean bitstream,
WNS +0.195 ns) and `board_2026-09-10_burstlen.csv` (pumice `open_page`, the
best pumice preset). Bandwidth is from the hardware first/last stamps of the
engine that ran; latency is the AR-to-first-R histogram mean in MC cycles.
Peak at this point is 600 MB/s.

## Streaming (page-friendly) patterns

| scenario | pumice wr | LiteDRAM wr | pumice rd | LiteDRAM rd | pumice lat | LiteDRAM lat |
|---|---|---|---|---|---|---|
| incremental_bl4 | 551.3 | 554.1 | 290.8 | 564.1 | 49.4 | 24.7 |
| incremental_bl8 | 551.4 | 554.2 | 291.7 | 564.1 | 49.2 | 24.7 |
| incremental_bl16 | 551.3 | 554.2 | 291.7 | 564.1 | 49.3 | 24.8 |
| row_major_bl4 | 570.2 | 569.2 | 290.8 | 579.4 | 49.4 | 24.8 |
| row_major_bl8 | 570.3 | 569.2 | 291.8 | 579.5 | 49.2 | 24.8 |
| row_major_bl16 | 570.3 | 569.3 | 291.8 | 579.5 | 49.2 | 24.7 |

Writes are equal (both ~92-95% of peak). Reads are not: LiteDRAM sustains
94-97% of peak where pumice is pinned at 48.6%, and LiteDRAM's read latency
is half of pumice's.

## Page-thrash patterns

| scenario | pumice wr | LiteDRAM wr | pumice rd | LiteDRAM rd |
|---|---|---|---|---|
| col_major_bl4 | 98.3 | 207.5 | 102.4 | 289.7 |
| col_major_bl8 | 163.8 | 304.0 | 172.0 | 386.3 |
| col_major_bl16 | 262.1 | 396.4 | 237.5 | 463.6 |
| col_major_interleaved_bl4 | 196.6 | 180.2 | 213.0 | 184.3 |
| col_major_interleaved_bl8 | 208.9 | 276.9 | 225.3 | 280.1 |
| col_major_interleaved_bl16 | 311.3 | 376.8 | 273.0 | 380.9 |
| col_major_bl8_multiid | 163.8 | 304.0 | 172.0 | 386.3 |
| col_major_bl8_gap | 163.8 | 300.0 | 172.0 | 300.0 |

LiteDRAM is 1.4-2.8x better on same-bank row thrash. Bank interleave is the
one place pumice leads (bl4 interleaved: 213 vs 184 rd), consistent with
LiteDRAM's per-bank machines not pipelining activates across banks at BL4
(the host summary flags "bank interleave gives no gain over same-bank
thrash" for LiteDRAM at every burst length).

## What this settles

- PUMICE-025's framing ("BL4 at this operating point needs a column every MC
  cycle, so the read ceiling is a property of the operating point") is
  disproven: LiteDRAM at the same BL4 / 75 MHz / 1:2 reads at 579 MB/s
  through identical engines. The 48.6% read ceiling is pumice's.
- It is read-specific and command-path-shaped: pumice's write path already
  matches LiteDRAM, so the DFI/PHY/data path is not the limit. The read side
  loses half its column slots somewhere between AR accept and R return
  (the return ring / rd CAM / AR-order commit are the suspects; PUMICE-025
  already exonerated the generator and the RD data path).
- The 24.7-cycle LiteDRAM read latency is a useful floor: pumice's 49.2 is
  ~25 cycles of extra pipeline for the same DRAM access.

## Method notes

- One writer, one reader (generator 0) on both sides; the multi-writer
  bank_parallel scenario is excluded until PUMICE-027 (B out of AW order vs
  the position-routed write bridge) is resolved.
- LiteDRAM has no runtime knobs; its "config" is what `litedram_hp.yml`
  generated (ROW_BANK_COL, open page with lookahead auto-precharge,
  cmd_buffer_depth 16). pumice numbers are its `open_page` preset (FR-FCFS,
  row-major, open page), the best of its matrix.
- LiteDRAM utilisation columns are meter-window artefacts at this run size,
  as the host notes; bandwidth is stamp-based and unaffected.
- Repro: `make -C projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart program`
  then `make ... host-litedram_char ARGS="--char-profile matrix --char-scale 1000 --csv <path>"`.
