# TASK-023: rebuild the Genesys2 rapids harness images with the fixed sdpram slave and repin the perf data

**Priority:** P2
**Status:** closed 2026-10-03 (FIXED — see the CLOSED section below)
**Owner:** TBD

amba 71d48b6f7 (2026-10-02) fixed `rtl/amba/shared/sdpram_core.sv`: burst
commands now queue two deep per direction and the tracker reloads the cycle
the active burst completes, so a burst boundary is FREE. The old core charged
~2.0 cycles per write burst and ~1.6 per read burst at every boundary, and
every board-measured figure this area pins was taken with that cost in the
path. The RS AXI4 harness (the proof case) moved 249.65 -> 244.00 cyc/block
with its codeword seams going 97.0%/98.5% -> 100.0%/100.0%, sim and board
agreeing to the digit.

NOTE: the `rapids_byte_perf_prelim_*.json` reports captured 2026-10-02 were
measured on images built BEFORE the fix -- treat them as pre-fix baselines,
not as current numbers.

## What to do

Rebuild and re-measure both Genesys2 rapids harnesses that pull the sdpram,
then repin the docs:

- `projects/fpga-systems/Genesys2/rapids/` (`rapids_byte_harness.f`) —
  the byte perf + monitor images.
- `projects/fpga-systems/Genesys2/rapids_beats/flows-rapids-beats/`
  (`rapids_char_harness.f`) — the char harness.

Then repin every pinned figure taken with the pre-fix slave:
`reports/perf/` JSONs, and any doc/table quoting rapids board throughput.

## Done when

- Fresh images for both harnesses close timing and pass their board smoke.
- Every doc/table that pins a board-measured figure either carries a
  post-fix number or a dated note saying the figure is pre-fix.

## Not in scope

- The sdpram fix itself (done, amba 71d48b6f7; full val/amba regression
  2234/2234).
- pumice and stream harnesses — filed separately (pumice TASK-038, stream
  TASK-016).
- TASK-022 (byte-specific proofs) and any other active rapids work; this is
  a re-pin, not new feature work.

## CLOSED 2026-10-03

Both harnesses rebuilt on the post-fix tree (sdpram 71d48b6f7), timing-closed
and board-verified on Genesys2 200300B818A0:

- rapids byte, all four variants (metrics in `reports/build/metrics_*.json`):
  std 117/117 PASS (`rapids_byte_perf_20261003_122406.json`), perf 28/28
  PASS (`rapids_byte_perf_20261003_121944.json`), mon + obs board smoke PASS.
  Headline 8ch/4096 unchanged: 3182/3199 MB/s. **Small transfers moved
  hugely, zero regressions**: std b1 mean +106% (max +400% sink), b4 +33%
  (max +220%), b16 +4.7%, b64 +1.5%, fading to +0.01% at b4096; aligned
  profile shows the same decay (b1 sink up to +400%).
- rapids beats char: bare k325t image (sha 168acd76..., WNS +0.343 ns) smoke
  PASS + default suite 48/48 (`reports/rapids_char_suite_2026-10-03.json`);
  observers image (sha d22db961..., WNS +0.471 ns, preserved as
  `flows-rapids-beats/bitstream/rapids_char_obs_20261003.bit`) smoke PASS +
  all 7 dw256 campaigns re-run (139 configs, all PASS, `*_20261003.json`).
  Deltas: full_matrix max +0.57% (ch8_b256 sink), obs_C b1 source +26.1%,
  obs_E +0.65% at resp-delay 96, zero regressions; saturated 3.19/3.20 GB/s
  points unchanged. The pre-fix `rapids_byte_perf_prelim_2026-10-02_*.json`
  are committed as the dated pre-fix baselines this task called for.

**Verdict: SIGNIFICANTLY different at small transfers (the fix's target
workload), unchanged at the saturated headline points.** Fine 4KB/16KB
latency sweeps and pre-dw256 512-bit figures carry dated pre-fix notes (not
re-run — different SRAM geometry / retired design points).

Docs repinned: rapids/README.md, reports/perf/README.md (regenerated,
rev 0.11), rapids_beats/README.md (BOARD=genesys2 now explicit — the flow
Makefile defaults BOARD to nexys), rapids_beats/reports/perf/README.md.
