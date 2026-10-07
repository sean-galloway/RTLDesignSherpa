# LiteDRAM vs pumice through the SAME harness (2026-10-03, post sdpram fix)

Re-run of the 2026-09-10 A/B after `amba 71d48b6f7` made the sdpram burst
boundary free. Same methodology as the original: same board (Nexys A7-100T,
MT47H64M16 x16 DDR2, JTAG 210292BFA3EE), same operating point (75 MHz sys /
1:2 / DDR2-300), same `char_engine_block` harness, same host program
(`--char-profile matrix --char-scale 1000`). Only the controller behind the
AXI4 port differs. Both images were built from the same commit on
2026-10-03: pumice `build-perf` (sha256 `61d35ff7...`, WNS +0.132 ns) and
LiteDRAM `flows-litedram-uart` (sha256 `44a1b836...`, WNS +0.321 ns).

Sources: `board_2026-10-03` = `projects/fpga-systems/NexysA7/mem-ctrl-ip/pumice/build-perf/
reports/char_postfix_2026-10-03.csv` (pumice `open_page`, the best pumice
preset, 84/84 integrity PASS) and `litedram_2026-10-03_matrix.csv` under
`projects/fpga-systems/NexysA7/mem-ctrl-ip/pumice/ddr2-characterization/char_results/`
(14/14 PASS). Bandwidth is timer-based (bytes / FPGA-timer cycles); both
sides normalized to the 75 MHz engine clock.

## Streaming (page-friendly) patterns

| scenario | pumice wr | LiteDRAM wr | pumice rd | LiteDRAM rd | ld/pum rd |
|---|---|---|---|---|---|
| incremental_bl4 | 555.5 | 554.2 | 561.5 | 564.1 | 1.00x |
| incremental_bl8 | 555.4 | 554.2 | 561.6 | 564.1 | 1.00x |
| incremental_bl16 | 555.4 | 554.2 | 561.6 | 564.1 | 1.00x |
| row_major_bl4 | 570.2 | 569.2 | 572.2 | 579.4 | 1.01x |
| row_major_bl8 | 570.3 | 569.3 | 572.3 | 579.5 | 1.01x |
| row_major_bl16 | 570.3 | 569.3 | 572.3 | 579.5 | 1.01x |

**The 2026-09-10 headline is dead: pumice now matches LiteDRAM on every
page-friendly pattern.** Writes were already equal; reads went from 48.6% of
peak (290.8 MB/s) to ~95% (572.3). That closure was the 09-10 intake/ring
fixes (`board_2026-09-10_read_fixed_ring64.csv`, 571.3 MB/s) and it HOLDS on
today's image. The sdpram fix changed nothing measurable here (see below).

## Page-thrash patterns

| scenario | pumice wr | LiteDRAM wr | pumice rd | LiteDRAM rd | ld/pum rd |
|---|---|---|---|---|---|
| col_major_bl4 | 114.7 | 207.5 | 114.7 | 289.7 | 2.53x |
| col_major_bl8 | 192.5 | 304.0 | 195.2 | 386.3 | 1.98x |
| col_major_bl16 | 290.8 | 396.4 | 286.7 | 463.6 | 1.62x |
| col_major_interleaved_bl4 | 213.0 | 180.2 | 237.6 | 184.3 | 0.78x |
| col_major_interleaved_bl8 | 235.9 | 276.9 | 262.1 | 280.1 | 1.07x |
| col_major_interleaved_bl16 | 340.8 | 376.8 | 364.5 | 380.9 | 1.04x |

LiteDRAM still leads same-bank row thrash (1.6-2.5x) — that gap is the
controller's ACT/PRE pipelining, not the harness. Bank interleave at BL4
remains the one place pumice leads (0.78x), same signature as 09-10.
col_major pumice numbers moved vs 09-10 (e.g. bl8 rd 172.0 -> 195.2) from
controller scheduling work between the runs, not the sdpram fix.

## What the sdpram fix did here: nothing measurable (as expected)

The harness sdpram (`sdpram_slave_axil_axil`) serves the UART/CSR bridge;
the characterization engines run autonomously after the kick, so the old
~2cyc/burst-boundary tax was off the datapath. Evidence:

- LiteDRAM side is UNCHANGED from the 09-10 baseline within rebuild noise:
  13 of 14 rows land within 25 read-cycles (e.g. incremental_bl4 rd 272,312
  -> 272,311), and the one larger row, col_major_interleaved_bl16, differs by
  3,495 cycles = 0.22% (1,613,076 vs 1,616,571). Nothing measurable, and
  nothing pointing at the sdpram path.
- pumice open_page page-friendly rows are within noise of the 09-10
  read_fixed_ring64 baseline (571.3 -> 572.3, +0.2%).
- This is the same signature measured on the Genesys2 stream/rapids-beats
  harnesses on 2026-10-03 (stream 40/40 cycle-identical; beats full_matrix
  max +0.57%). The fix pays where transfers are small and boundary-dense
  (rapids byte: up to +400% at 1-beat) — the ddr2-char engines are not that
  workload.

## Measurement caveats (do not compare these columns across dates)

- **rd_avg_latency_cyc is not comparable to 09-10.** Both sides read ~2-4x
  higher today (LiteDRAM 24.7 -> 48-96; pumice 49 -> 96-192) because the
  shared harness latency histogram changed semantics (engine rework of
  2026-09-13 "four generators per direction" and after). Within THIS run the
  relative comparison is fair; across dates it is not.
- **LiteDRAM flow BUILD_CLK_HZ CSR reads 100e6** on a 75 MHz engine clock
  (the pumice flow reads 75e6 correctly). The raw `clk_mhz` column of
  `litedram_2026-10-03_matrix.csv` therefore inflates BW by 4/3; the table
  above is normalized from recorded cycles at 75 MHz. Filed as a bug in the
  fpga-systems lane; the UART works because the divisor uses the 75 MHz
  parameter, only the identity register disagrees.
- The pre-fix `board_2026-09-10_*.csv` / `litedram_2026-09-10_matrix.csv`
  record no bitstream sha; provenance is date + flow only.

## Area / timing (2026-10-03 images, xc7a100tcsg324-1)

| image | WNS | endpoints | LUTs |
|---|---|---|---|
| pumice build-perf | +0.132 ns | 94,398 | see `utilization_impl.txt` |
| LiteDRAM | +0.321 ns | 75,996 | see `reports/utilization_hier.rpt` |

Both timing-clean at 75 MHz. The 09-10 comparison was pumice +0.039 ns /
LiteDRAM +0.195 ns — same closure class.

## Addendum 2026-10-04 — concurrent both-directions, the A/B's third table

The matrix above runs a write phase then a read phase; the 09-10 A/B's third
claim (pumice 2.00x with both directions live) needed the concurrent profiles
re-run on the post-fix images. Done 2026-10-04 on the SAME 2026-10-03
bitstreams (pumice sha256 `61d35ff7...` still loaded; LiteDRAM sha256
`44a1b836...` re-flashed for the run, pumice re-flashed after — board left as
found). Profiles `concurrent` (1w+1r) and `multigen` (1w+2r), `--char-scale
1000`. Sources: `build-perf/reports/concurrent_postfix_2026-10-04.csv` +
`multigen_postfix_2026-10-04.csv` (pumice, 4/4 + 4/4 integrity) and
`char_results/litedram_concurrent_2026-10-04.csv` +
`litedram_multigen_2026-10-04.csv` (LiteDRAM, 4/4 + 4/4). LiteDRAM `clk_mhz`
again reads 100.0 from the identity register (the known flow bug); normalized
to the real 75 MHz by scaling 0.75 from recorded cycles.

| scenario | pumice total | LiteDRAM total | pum/ld | 09-10 pumice | 09-10 LiteDRAM |
|---|---|---|---|---|---|
| incremental bl8, 1w+1r | 552.4 | 247.5 | 2.23x | 552.6 | 247.5 |
| row_major bl8, 1w+1r | **571.1** | **285.8** | **2.00x** | 570.1 | 285.6 |
| row_major bl8, 1w+2r | **569.8** | **316.5** | **1.80x** | 570.2 | 316.4 |

**The concurrent claim stands post-fix, both sides.** pumice reproduces its
09-10 totals within +0.2% (sdpram fix off the datapath, as the matrix showed),
and LiteDRAM reproduces within 0.07-0.2% after 75 MHz normalization — so the
2.00x / 1.80x advantage is a property of the two controllers, not of the
measurement vintage. Also re-verified post-fix on the pumice side only: the
bank/gap knee (PUMICE-036) spot-check, 48 points at gaps 0/4/8/15 — see the
AT-A-GLANCE knee section; 4+4 reproduces the committed pre-fix record to the
digit (bus 549.9 both eras), the incremental/row_major knees match at every
count within spot resolution, and knee DID NOT MOVE.
