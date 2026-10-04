# TASK-038: rebuild the ddr2-char harness images with the fixed sdpram slave and repin the perf data

**Priority:** P2
**Status:** closed 2026-10-04 (FIXED — see the CLOSED section below)
**Owner:** seang

amba 71d48b6f7 (2026-10-02) fixed `rtl/amba/shared/sdpram_core.sv`: burst
commands now queue two deep per direction and the tracker reloads the cycle
the active burst completes, so a burst boundary is FREE. The old core charged
~2.0 cycles per write burst and ~1.6 per read burst at every boundary, and
every board-measured figure this area pins was taken with that cost in the
path. The RS AXI4 harness (the proof case) moved 249.65 -> 244.00 cyc/block
with its codeword seams going 97.0%/98.5% -> 100.0%/100.0%, sim and board
agreeing to the digit.

## What to do

Rebuild and re-measure every pumice-family board harness that pulls the
sdpram, then repin the docs:

- `projects/fpga-systems/NexysA7/pumice/build-perf/`
  (`ddr2_char_harness.f`) — the pumice board perf characterization image.
- `projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/`
  (`litedram_char_harness.f`) — the LiteDRAM same-harness A/B image; BOTH
  sides of the A/B move, so the comparison needs re-running, not editing.
- Sim-side equivalence checks that assert cycle windows
  (`ddr2_char_framework` cosim) — re-baseline expectations the way
  `test_rs_loop_uart.py` was (58d123430) if any window moved.

Then repin every pinned figure taken with the pre-fix slave: the board perf
char numbers, the LiteDRAM A/B table, the bank/gap knee data
(PUMICE-036) if it moved, and any HAS/MAS chapter quoting board-measured
throughput. `pumice_char.py --char/--char-scale` is the measurement entry
point.

## Done when

- Fresh images for both harnesses close timing and pass their board smoke.
- Every doc/table that pins a board-measured figure either carries a
  post-fix number or a dated note saying the figure is pre-fix.
- The pumice-vs-LiteDRAM A/B is re-measured on images built from the same
  commit, same as the original methodology.

## Not in scope

- The sdpram fix itself (done, amba 71d48b6f7; full val/amba regression
  2234/2234).
- rapids and stream harnesses — filed separately (rapids TASK-023, stream
  TASK-016).
- Any attempt to improve the numbers beyond what the fix delivers; this is
  a re-pin, not a new perf push.

## CLOSED 2026-10-04

Both harnesses rebuilt and re-measured on the post-fix tree, every pinned
doc/table repinned, task done-criteria met:

- **Images + smoke.** pumice `build-perf` (sha256 `61d35ff7...`, WNS +0.132 ns)
  and LiteDRAM `flows-litedram-uart` (sha256 `44a1b836...`, WNS +0.321 ns),
  both timing-clean at 75 MHz, built from one commit 2026-10-03. Board smoke:
  pumice matrix 84/84 integrity, LiteDRAM matrix 14/14, both 2026-10-03; the
  10-03 bitstreams were re-used 2026-10-04 for the concurrent/knee re-runs
  (board left with the pumice image, as found). Full analysis:
  `docs/char_results/FINDINGS_litedram_ab_2026-10-03.md` + its 2026-10-04
  addendum (mem-ctrl-ip pumice docs).
- **Headline: the sdpram fix changed nothing measurable on these harnesses**
  (it serves the UART/CSR bridge; the engines run autonomously). LiteDRAM side
  cycle-identical to 09-10 on all 14 matrix points; pumice streaming within
  +0.2%; close_page `col_major` bl8 read 195.2 MB/s to the digit of the
  2026-09-26 campaign. The A/B moves anyway because pumice's reads closed the
  09-10 gap via the intake/ring fixes — now at LiteDRAM parity (1.00-1.01x)
  page-friendly, still 1.6-2.5x behind on same-bank thrash.
- **Concurrent A/B re-measured both sides 2026-10-04** (the 09-10 third table
  was the one gap in the 10-03 campaign): pumice 571.1 / LiteDRAM 285.8 MB/s
  total 1+1 row_major (2.00x stands), multigen 569.8 / 316.5 (1.80x stands).
  Raw: `build-perf/reports/{concurrent,multigen}_postfix_2026-10-04.csv`,
  `ddr2-characterization/char_results/litedram_{concurrent,multigen}_2026-10-04.csv`.
- **Knee (PUMICE-036) did not move.** 48-point spot-check at gaps 0/4/8/15
  (`build-perf/reports/bank_gap_sweep_postfix_2026-10-04.json`): 4+4 reproduces
  the committed pre-fix record to the digit (bus 550.0 vs 549.9 MB/s); every
  cell's knee matches the published table within spot resolution; the
  per-direction rd/wr bases at 2+2/3+3 are not comparable across eras because
  the concurrent window measurement was rewritten three times since 2026-09-14
  (caveat recorded in AT-A-GLANCE).
- **Sim side:** no cycle-window expectations exist in the ddr2_char_framework
  cosim (functional/timeout asserts only — verified by inspection), so no
  re-baseline was needed; the full `test_ddr2_char_uart.py` suite passes 12/12
  on the post-fix tree (one failure on first run was a stale Verilator PCH
  artifact in a persistent build dir, not a design regression).
- **Docs repinned** with post-fix numbers or dated pre-fix notes: AT-A-GLANCE
  (streaming + concurrent tables, knee spot-check note, page vintage banner),
  design-requirements Axis 2, MAS page_policy / csr_map / ch07 timing (both
  files) / 4x pre-ring-fix 180 MB/s history notes, HAS config_bits + parameters,
  flows-litedram-uart README, ddr2_char_guide ch08 header + troubleshooting,
  DDR2_BANDWIDTH_MEASUREMENT, 09-10 FINDINGS supersession banner. Left alone
  by ruling: closed task/bug files, 2026-07 FINDINGS, generated
  `pumice_csr.md`, front-matter revision rows — dated historical records
  satisfy the contract as-is.
