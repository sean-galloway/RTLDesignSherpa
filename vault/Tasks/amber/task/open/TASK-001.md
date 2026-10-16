# TASK-001: amber G2 rig measurement upgrade (latency counters + live tally window)

**Priority:** P3 (observation quality; functional path unaffected)
**Status:** OPEN
**Filed:** 2026-10-16, from BUG-004 closure + the first board perf sweep
(`results/perf_sweep_20261016T111032Z.json`)

The BUG-004 fix made the MonBus tally path lossless and correctly keyed,
and the sweep proved the board can now produce real hit/miss/evict/drain
rate curves. Four gaps remain between this rig and the stream
`perf_profiler` level of analysis. All are Genesys2 bring-up collateral
(`projects/fpga-systems/Genesys2/cache-ip/amber/`) — no amber IP RTL
changes except where noted.

## Items

1. **Wire `tally_clear` / `tally_freeze` to the harness CSR.** Both are
   tied off in `amber_pair_harness.sv` (line ~1299) although
   `monbus_tally_axil` takes them as ports and `hcsr_ctrl` is an unused
   dead output today. CTRL[0] = clear pulse (write-strobe generated),
   CTRL[1] = freeze level. Removes the sweep's before/after differential
   bookkeeping and, more importantly, makes the first-event latch bank
   re-armable per run instead of one-shot-per-FPGA-load.

2. **Injector latency counters (the stream perf_profiler analog).** The
   cycle injectors are blocking (one outstanding), so per-request latency
   is exactly FSM_WAIT_RSP occupancy. Add CSRs: run-cycle count, and
   per-request latency min/max/sum (and a small histogram, 4-8 buckets).
   This turns the sweep's wall-clock guesswork into real silicon latency
   distributions: hit latency vs miss latency vs snoop-stalled latency,
   per configuration. `amber_cycle_injector.sv` has 16 CSR words, 6
   free.

3. **Bigger / re-armable latch bank.** `TALLY_NUM_LATCH=4` captured the
   first four events of an FPGA session — one shot, ever. Either bump the
   parameter (16 is cheap) or make the bank a ring so the watch mask can
   sample different event classes per run once item 1 lands.

4. **RDL entries for the latch readback words.** The 9 cfgr words
   (latch status/packet/timestamp at offsets 0x10-0x40) are decoded in
   `monbus_tally_axil` but absent from `tally_regs.rdl`, so hosts must
   read raw offsets (see `_latch_capture` in `host/amber_perf_sweep.py`).
   Add them to the RDL and regenerate so the named-register API covers
   them.

## Non-goals / recorded decisions

- **AXI completion events stay off in amber_top** (`cfg_compl_enable=0`
  on both AXI monlites). Fill/drain end events already measure fabric
  traffic volume; enabling completions would add ~1 packet per AXI beat
  for no new analytic value. The profile's bin 4 watches drop reports
  instead (health). Revisit only if a future analysis needs per-beat AXI
  timing, which is the latency counters' job (item 2).
