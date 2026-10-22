# mem-ctrl recovery — Phase 0 report (2026-10-21)

Plan: `docs/superpowers/plans/2026-10-21-mem-ctrl-recovery.md` §3 Phase 0.
Tree: shared `main`, HEAD at start ea5cf4360 (+ working-tree edits listed in §6).

## 1. What Phase 0 set out to do, and what happened

| item | result |
|---|---|
| Park Stage B of the 100 MHz plan | Done. Ledger line in `.superpowers/sdd/2026-10-20-pumice-100mhz/progress.md`; scratch file kept as evidence. |
| Contract TB: bank-ready / init ports were constant-tied | Fixed. `mc_store_arbiter_macro_tb_top.sv` now has TB-level inputs; the test drives those. All four acceptance cells now fail for their designed reason (§3). |
| A pumice-with-CAMs perf proxy at board timings | Built: `ddr2_char_framework/dv/tests/test_ddr2_char_perf.py` (§2). |
| Record the pumice-CAM baseline | Done (§2). It needed one RTL fix first (§4). |
| Timing-override and multi-generator knobs | Added (`TEST_TIMING_OVERRIDES`, `TEST_NUM_GEN`); the floor is logged beside every number. Multi-gen not yet exercised. |
| Housekeeping note | §6. |

## 2. pumice-CAM baseline (FRFCFS core, board geometry, 75 MHz, tREFI=585, txn=1024, one generator)

Taken on the FINAL arbiter text (a8331c9d6 + BUG-028 fix; Verilator build
verified to have compiled that exact file). Programmed timings (board
derivation): tRC 5, tRCD 2, tRP 2, tRAS 4, tRFC 11, tRRD 2, tFAW 4, tWTR 4,
tCCD 1, tWR 4, tRTP 2, tRTW 21. Floors at these timings: col_major rd gap 6 →
369.2 MB/s, wr gap 8 → 319.9; streaming 599.9.

| family | wr MB/s | wr lat (cyc) | rd MB/s | rd lat (cyc) | mism |
|---|---|---|---|---|---|
| incremental | 556.1 | 51.2 | 558.7 | 50.4 | 0 |
| row_major | 571.9 | 51.0 | 568.7 | 50.4 | 0 |
| col_ilv | 306.9 | 95.8 | 353.6 | 95.9 | 0 |
| col_major | 195.1 | 99.6 | 194.9 | 101.4 | 0 |

Command-gap histograms (`PERF_CMD_TRACE=1`): col_major inter-row gap 17
cycles for RD and WR (987/989 of them), ACT→ACT 24.5 cycles (13 and 15
alternating with refresh); row_major and incremental stream at gap 1. So the
pre-Stage-A FRFCFS core on the CAM backend pays +11 cycles over the rd floor
and +9 over the wr floor per row switch. (For the record: the reverted
Stage A arbiter measured gap 15 / 212.8 MB/s on col_major and 329.5/329.7 on
col_ilv before its read-drop regression was found; its registered pool
qualify did shorten the row-switch loop by two cycles, which the new core
must beat anyway.) Phase 2 target unchanged: col_major rd ≥ 360 / wr ≥ 310.

Latency: streaming AR-to-first-R ~50 cycles, col_major ~100. Comparable only
within one histogram semantics (plan §3 Phase 2 note). These numbers match
the granite-harness FRFCFS proxy the 100 MHz plan used as "pumice baseline"
(col_ilv 306/353 there too), confirming that proxy measured the same core.

Raw: `/tmp/claude-1000/.../scratchpad/pumice_cam_baseline_final_txn1024.json`
(+ `.gaps.json`); the scratchpad does not survive the session, this file is
the durable record.

## 3. Contract cells against the real FRFCFS arbiter (post-TB-fix)

| cell | result | why (old core) |
|---|---|---|
| store_arbiter_contract (baseline) | PASS | — |
| hold_on_gate_block | FAIL | `cmd_valid_o` dropped while gate blocked (drop-on-reject) |
| zero_bubble_stream | FAIL | 4 idle cycles in a 16-cycle steady window (pipeline bubbles) |
| post_pop_winner | FAIL | post-pop cycle is a bubble |
| override_preempts_speculation | FAIL | held WRA fires in cycle 0 before the init override |

Before the TB fix the deposits on `u_arb.bank_*_ready_i` were folded away by
Verilator, so the hold cell failed for the wrong reason ("command changed")
and the override cell's assertion order mislabelled its failure. Both fixed;
the four cells are the acceptance tests for `mc_bank_pick`.

## 4. Found and fixed: pumice BUG-028 (refresh drain deadlock)

First proxy run: col_major writer wedged after 16 rows at tREFI=585 (txn 64
and 256 identical; 39 rows at 1024). Snapshot: refresh requested and draining,
bank 0 row open and precharge-ready, `w_guarded=0x1` with every fired/in-flight
guard clear, nothing picked. Mechanism: the refresh branch's drain PRE is
blocked by the pre-pick shadow of the DEMAND PRE for the same bank, and the
refresh branch shadows the demand classes, so neither PRE can issue.
Exposed by CLOSE_ON_DRAIN=0 (BUG-027 fix, 2026-10-20): with AP on the last
column no demand PRE existed. Fix: `w_guarded_drain` in `mc_cmd_arbiter.sv`
(drop only the demand-PRE shadow from the drain picker's guard). Granite
inherits the change through the shared module. Item:
`vault/tracking/.../pumice-ddr2-lpddr2/bug/active/BUG-028.md`.

Verification: col_major tREFI=585 at txn 64/256/1024 completes, mism 0
(table above); contract cells unchanged (§3); pumice `run-all-func` both
geometries: see §7.

## 5. Found and NOT an RTL bug: the proxy's checker swap moved the read return

Every post-swap run lost exactly the first read word (aligner probe
`captured = valids − 1`, `blocked_real = 1`) and the whole return stream
shifted one ticket (host AXI probe: beat k carried address k+1's data; read
engine never saw its last beat). Cause: `DFISlavePHY` times read return and
write capture off `dram.timings.CL/CWL`; my MC-cycle-calibrated checker set
CL=3 where the uart suite's CL=5 is what `t_rddata_en=4` was tuned against.
The data arrived one cycle before the aligner's enable window and was
credit-blocked. Fixed by keeping the slave's CL/CWL/BL in the calibrated
profile. Lesson recorded in memory; a mis-set `t_rddata_en` on the board
would show the identical signature (one-word slip, never resyncs).

Residual model finding worth an issue later: the calibrated checker reports
one `tWR` soft violation per col_major row ("PRE 0 cycles after last WR data
beat, needs 2"), i.e. pumice's PRE-after-WR accounting counts from the
command while the DFI write data lands later. 1078 in the 1024-txn run, none
in row_major. Not pursued in Phase 0.

## 6. Housekeeping observed, not changed

- `targets/granite/fpga/reports*`: the working-tree reports describe the
  reverted aged core (-33/-35 ns); `reports_fp1/`, `reports_retry*` hold
  routed `.dcp` experiment residue. Do not commit them with this work.
- `reports/regr/` is gitignored; this report must be force-added if it is
  to survive a fresh clone (the 100 MHz baseline report was).
- The pumice uart suite's checker is uncalibrated (CSV tCK 3.077 ns →
  2.2× the JEDEC cycle counts) and reports phantom `cmd_during_refresh` /
  `tRAS` violations; only the perf proxy is calibrated. Candidate Phase 1
  cleanup for both harness suites.
- Read debug tap (`RD_DBG_FIFO_DEPTH`) defaults to 0 in the sim harness, so
  `MISM_PROBE` sees nothing there; the AXI-port probe (`AXI_R_PROBE`) and the
  BFM memory dump (`MEM_DUMP_ROWS`) replace it.

## 7. Gates

| gate | status |
|---|---|
| store-arbiter contract baseline cell | PASS |
| four acceptance cells fail for designed reasons | yes |
| perf proxy, four families, mism 0 | PASS (table §2) |
| pumice `make clean-all && make run-all-func` (both geometries) | FIRST RUN (on Stage A + fix): 25 failed / 191 passed default, 22 / 194 board, all refresh-adjacent read drops. A/B: Stage A alone fails the same cells, a8331c9d6 passes them -> Stage A reverted, arbiter = a8331c9d6 + BUG-028 fix. Re-run: see addendum. |
| common-ip lint of `mc_cmd_arbiter` (standalone, -Wall) | clean |

## 7a. Stage A (bf53f9556) found broken and reverted

The committed Stage A arbiter had only ever been checked against the
contract baseline cell. Its first full-suite run (this session) failed 25
default-geometry and 22 board-geometry cells, every one a read-return drop
around a refresh (`pumice_dfi_rd_return_checker`: "read DROP ... refresh-drain
read loss"; AXI "got 4 of 8 responses"). Three-way A/B on two of them
(`test_pumice_top_burst_len[5]`,
`test_pumice_top_concurrent_rw[0-bl8-rdlat2-refi_default-depth32_board]`):
Stage A + BUG-028 fix FAIL/FAIL, Stage A alone FAIL/FAIL, a8331c9d6 PASS/PASS.
The arbiter in the working tree is now a8331c9d6's text plus the BUG-028
drain-guard fix (37 lines added, 1 changed vs a8331c9d6); the `MC_ARB_BANK_OH`
guard disappears with Stage A. The recovery plan already retires the Stage
A/B line, so nothing downstream depends on it.

## 7b. Second full-suite run on the rebuilt arbiter, and the one cell it moved

On a8331c9d6 + BUG-028 fix: board geometry 216 passed / 1 skipped (the bar);
default geometry 215 passed / 1 skipped / 1 failed:
`test_pumice_core_dfi.py::test_pumice_core_refresh_credit`, arm D ("disarm:
only 2 REFs"). A/B (twice each): pre-fix 3 REFs, fix 2 REFs, so the fix
moved it. Waves (both variants, `fst2vcd` + a transition dump) show why,
and why it is the cell, not the RTL:

- Arm D starts with the credit bank FULL (8), not with ~3 leftovers: the
  integrity spot-check reads between arms C and D are idle time with
  pull-in still armed, and the controller re-banks six REFs in that gap
  (grants every ~10 cycles at 52.3–53.9 µs in both runs).
- The controller then correctly raises no refresh request for 8 ticks of
  arm D's 8.3-tick stretch; the strict REF arrives in the last tick.
  Pre-fix: 1 grant inside the window (64.7 µs). Fix: the window closes
  ~50 ns earlier and that grant falls outside it.
- The pre-fix "3" = that one REF + two pull-in grants issued 146 ns and
  13 ns BEFORE the window whose DFI commands (CMD_DELAY ≈ 7 cycles) landed
  inside it. The fix's drain is one cycle faster per episode and its
  demand runs faster (10.4 vs 15.4 cycles per burst), so one of those
  no longer spills in: 2.

Resolution: the stretch is lengthened from 800 to 1300 cycles (13.5 ticks:
8 burn the bank, ≥5 strict), with the mechanism recorded in the test. Both
arbiter variants now report `disarm 8` (twice each). Final full-suite run on
the committed text: §7c.

## 7c. Final gate (arbiter = a8331c9d6 + BUG-028 fix; refresh_credit arm D at 1300 cycles)

`make clean-all && make run-all-func` in `research-ip/pumice-ddr2-lpddr2/dv/tests`:

| geometry | result |
|---|---|
| default (fub 32 + macro 78 lint + top) | 216 passed / 1 skipped |
| board (TEST_DRAM_BEAT=32 BL=4 DEVICE_W=16, top) | 216 passed / 1 skipped |
| phy | 32 passed / 4 skipped |

"OK: run-all-func passed at BOTH geometries". The bar (216 / 1 / 78) is met.

## 8. Files touched (for the commit pathspec)

- `projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_cmd_arbiter.sv` (BUG-028 fix)
- `projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_store_arbiter_macro_tb_top.sv` (TB ports)
- `projects/components/mem-ctrl-ip/common-ip/dv/tests/macro/test_mc_store_arbiter_contract.py`
- `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/test_ddr2_char_perf.py` (new)
- `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/dv/tests/top/test_pumice_core_dfi.py` (refresh_credit arm D stretch)
- `docs/superpowers/plans/2026-10-21-mem-ctrl-recovery.md` (new)
- `.superpowers/sdd/2026-10-20-pumice-100mhz/progress.md` (park ruling)
- `vault/tracking/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/bug/active/BUG-028.md` (new), `bug/INDEX.md`
- `reports/regr/mem-ctrl-recovery-phase0-2026-10-21.md` (this file, gitignored dir)
