# TASK-001: amber G2 rig measurement upgrade (latency counters + live tally window)

**Priority:** P3 (observation quality; functional path unaffected)
**Status:** CLOSED 2026-11-02 — all four items landed. Board rebuild +
sweep re-run pending (needs the Genesys 2); jet T13's blocker is cleared.
**Filed:** 2026-10-16, from BUG-004 closure + the first board perf sweep
(`results/perf_sweep_20261016T111032Z.json`)

The BUG-004 fix made the MonBus tally path lossless and correctly keyed,
and the sweep proved the board can now produce real hit/miss/evict/drain
rate curves. Item 1 (clear/freeze wiring) landed 2026-11-01; three gaps
remain between this rig and the stream `perf_profiler` level of analysis.
All are Genesys2 bring-up collateral
(`projects/fpga-systems/Genesys2/cache-ip/amber/`) — no amber IP RTL
changes except where noted.

## Items

1. ~~**Wire `tally_clear` / `tally_freeze` to the harness CSR.**~~ **DONE
   2026-11-01.** `amber_harness_csr` CTRL[0] is now write-1-pulse
   (self-clearing, reads 0) driving `tally_clear`; CTRL[1] is a level
   driving `tally_freeze` (`amber_pair_harness.sv`). Host:
   `AmberDriver.tally_clear()` (RMW, preserves freeze) /
   `tally_freeze(on)`; `harness_probe()` magic moved to 0xC0FFEE58 so the
   scratch round-trip can't fire a spurious clear or stick freeze; the
   perf sweep now freezes → reads → clears per run instead of
   before/after subtraction, and every run re-arms the latch bank. DV:
   `tally_clear_freeze_test` in `test_amber_pair_harness_axil.py` pins
   W1P readback, clear-to-zero, frozen-run drop, and resume-after-unfreeze
   (was red before the wiring, green after; func+gate). Original text:

   > Both are tied off in `amber_pair_harness.sv` (line ~1299) although
   > `monbus_tally_axil` takes them as ports and `hcsr_ctrl` is an unused
   > dead output today. CTRL[0] = clear pulse (write-strobe generated),
   > CTRL[1] = freeze level. Removes the sweep's before/after differential
   > bookkeeping and, more importantly, makes the first-event latch bank
   > re-armable per run instead of one-shot-per-FPGA-load.

2. ~~**Injector latency counters (the stream perf_profiler analog).**~~
   **DONE 2026-11-02.** `amber_cycle_injector` widened to a 32-word decode
   window (`addr[6:2]`; the original 16 offsets untouched). New read-only
   CSRs, all cleared on run start: `LAT_MIN 0x24`, `LAT_MAX 0x28`,
   `RUN_CYCLES 0x2C`, `LAT_SUM_LO/HI 0x40/0x44` (64-bit), and
   `LAT_HIST0..7 0x48-0x64` (8 log2 buckets: bucket b = [2^b, 2^(b+1)-1],
   bucket 7 ≥ 128). Latency = accept→response cycles (WAIT_RSP occupancy
   + 1). DV: `injector_latency_test` (min≤max, count·min ≤ sum ≤
   count·max, histogram total == TRANS_COUNT, sum ≤ run_cycles). Host:
   regmap + `CycleInjector.latency()` + per-config stats in the sweep.
   Original text:

   > The cycle injectors are blocking (one outstanding), so per-request
   > latency is exactly FSM_WAIT_RSP occupancy. Add CSRs: run-cycle count,
   > and per-request latency min/max/sum (and a small histogram, 4-8
   > buckets). This turns the sweep's wall-clock guesswork into real
   > silicon latency distributions. `amber_cycle_injector.sv` has 16 CSR
   > words, 6 free. (Note: 3 were actually free below 0x40; the window
   > was widened instead.)

3. ~~**Bigger / re-armable latch bank.**~~ **DONE 2026-11-02.**
   `TALLY_NUM_LATCH=16` at the harness instantiation (the tally was
   already fully parameterized). Item 1's clear re-arms the bank per run.
   DV: `tally_latch_bank_test` (all-types watch mask fills all 16 slots,
   per-slot VALID, non-decreasing timestamps, clear re-arms). Original
   text:

   > `TALLY_NUM_LATCH=4` captured the first four events of an FPGA session
   > — one shot, ever. Either bump the parameter (16 is cheap) or make the
   > bank a ring so the watch mask can sample different event classes per
   > run once item 1 lands.

4. ~~**RDL entries for the latch readback words.**~~ **DONE 2026-11-02.**
   The 9 cfgr words (LATCH_STATUS 0x10, LATCH_PKT0-3 0x18-0x30,
   LATCH_TS_LO/HI 0x38/0x40) are declared in `tally_regs.rdl` as
   `sw=r, hw=na` (the read path stays the hand mux in
   `monbus_tally_axil`; the RDL gives hosts named access) and the block
   regenerated (`check_rdl_regen.py` clean). The sweep's `_latch_capture`
   now uses named reads, loops to FILL instead of 4, and the raw-offset
   constants are gone. Original text:

   > The 9 cfgr words (latch status/packet/timestamp at offsets 0x10-0x40)
   > are decoded in `monbus_tally_axil` but absent from `tally_regs.rdl`,
   > so hosts must read raw offsets (see `_latch_capture` in
   > `host/amber_perf_sweep.py`). Add them to the RDL and regenerate so
   > the named-register API covers them.

## Race found while verifying (2026-11-02)

The new DV exposed a seed-dependent corner in the clear protocol:
`tally_clear` realigns the tally's 3-beat reassembler but cannot flush a
partial record buffered in the upstream group, so a clear landing
mid-record phase-shifts the record stream and every later packet lands in
UNEXPECTED (bins 0..7 read as zero — "tally never resumed"). The
documented protocol is now **settle → freeze → clear** everywhere (DV
test, `AmberDriver.tally_clear` docstring, address_map CTRL row, and a
comment at the reassembler in `monbus_tally_axil.sv`). The sweep already
settled (0.25 s) before reading, so board runs were never exposed.

## Non-goals / recorded decisions

- **AXI completion events stay off in amber_top** (`cfg_compl_enable=0`
  on both AXI monlites). Fill/drain end events already measure fabric
  traffic volume; enabling completions would add ~1 packet per AXI beat
  for no new analytic value. The profile's bin 4 watches drop reports
  instead (health). Revisit only if a future analysis needs per-beat AXI
  timing, which is the latency counters' job (item 2).
