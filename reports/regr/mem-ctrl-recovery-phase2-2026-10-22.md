# mem-ctrl recovery — Phase 2 report (2026-10-22)

Plan: `docs/superpowers/plans/2026-10-21-mem-ctrl-recovery.md` §3 Phase 2.
Tree: shared `main`, HEAD at start d40415a17 (Phase 1). Owner's go: "do phase
2. once pumice and granite are clean, we will worry about scoria and andesite."

## 1. What landed

| item | where |
|---|---|
| `mc_bank_pick`, the per-bank pick core on the head-record contract | `common-ip/rtl/fub/mc_bank_pick.sv` (+ `.f`) |
| `SCHED_CORE` on `mc_scheduler_plane` (`MC_SCHED_BANK_PICK` default, `MC_SCHED_FRFCFS` research); `BANK_FIFO`, `BANK_IN_ORDER`, the `*_bh_*` head-view ports and `mc_bank_sched` retired | `mc_scheduler_plane.sv`, `mc_cmd_arbiter.sv`, `mc_xddr2_entry_store.sv`, `mc_common_pkg.sv` |
| Record gains `behind_same_row` (younger same-row entry behind, schedulable or still filling); write backends export `sch_pend` | `mc_common_pkg.sv`, `mc_bank_head_records.sv`, `mc_wr_data_cam.sv`, `mc_xddr2_entry_store.sv`, `mc_storage_plane.sv` |
| Bank timer `LA_AP`: the lookahead extrapolates the auto-precharge self-close (exact: max(preblk,ras)+tRP within LA) | `mc_bank_timer.sv`, `mc_bank_timers.sv` (`BANK_LA_AP`); the plane sets LA 2 / LA_AP on for BANK_PICK, 4 / off for FRFCFS |
| pumice: BANK_PICK default; `SCHED_CORE` forwarded through `pumice_core`, `pumice_top`, `pumice_top_geared`, both tb tops and the ddr2_char harness (`TEST_SCHED_CORE` on the perf proxy) | pumice rtl/top, dv/tb, harness `ddr2_char_harness.sv` / `ddr2_char_macro.sv` / `ddr2_char_uart_tb_top.sv` |
| granite: records derived from the entry store by two `mc_bank_head_records`; stays on FRFCFS (`SCHED_CORE` parameter, default `MC_SCHED_FRFCFS`); scoria / andesite wrappers updated for the port change, FRFCFS pinned | `granite_core.sv`, `granite.f`, `granite_all.f`, `scoria_scheduler_plane.sv`, `andesite_scheduler_plane.sv` |
| Contract bench rebuilt around a `SCHED_CORE` generate and generic observability ports; test parametrized over both cores; zero-bubble stimulus is now two free-running AW/W streams | `dv/rtl/mc_store_arbiter_macro_tb_top.sv`, `dv/tests/macro/test_mc_store_arbiter_contract.py`, `dv/filelists/mc_store_arbiter_macro.f` |
| pumice BUG-029 (REFpb rotor mirror fed from the FIFO head) found and fixed in the plane | `bug/closed/BUG-029.md`, `mc_scheduler_plane.sv` |
| Docs: `mc_scheduler_plane_v2.md` §5, pumice `CLAUDE.md` scheduler shape, handbook `plane-boundary-registered-snapshots` (consumer-side section) | |

## 2. The core, in one paragraph

Decode (per pair = direction x bank, from the registered record and the
timer's lookahead) -> registered request / class -> round-robin arbiter
(aging overlay, ACT/PRE-vs-column alternation, direction stickiness) ->
registered winner {pair, class} -> fire (live JEDEC re-check: safe bits,
live hit against the open row, forward tCCD, turnarounds, refresh / tRFC
demand blocks). Hold on a closed timer; drop on a class change (the decode
re-presents every cycle, so a drop has no refill cost). The record lags a
pop by one cycle, so the fire stage keeps a one-cycle pop shadow and serves
a just-popped pair from its second record (1 column/cycle on one bank). A
fire raises a next-op hint for its own pair (ACT->COL, PRE->ACT,
last-of-row COL->PRE) when the hop's timer is within the pipe depth; a hop
shorter than the pipe loads the winner register directly. The maintenance /
refresh / init override is the retired core's, with the REF all-idle gate
moved to the live activate-ready bits (tRP-exact) and the read-return wait
made a parameter (default off: it postponed refresh without bound under a
read stream).

## 3. What the bring-up found (each one cost a regression cell)

| finding | mechanism | fix |
|---|---|---|
| comb loop through `wr_commit_ready` | the CAM's commit_ready is a function of this cycle's commit_valid (rate-matched commit); gating the fire on it is a loop | sink room is the ARBITER's check, one cycle before the fire (same split as FRFCFS) |
| single-beat write stream at 50% (board geometry `write_ceiling`, bp 234) | the request register lags a fire by a cycle: after a pair fires its only entry the arbiter re-picked the same pair and the fire stage dropped it, every other cycle | mask the winner's own pair when its request cannot be its next command (row command, or column with `behind_empty`) |
| decode also gated on sink room | two cycles ahead of the rate-matched predicate it halved the same stream | decode checks timers only |
| `fixed_open` timeout PRE never issued; `row_hit_counters` zero; `paging_sweep` runs chopped | the core ignored `mc_page_policy`'s AP override and idle-timeout request | `ap_mode_en/ap_close` own the AP when enabled; timeout PRE is the lowest-priority command |
| `refpb` read back zeros | BUG-029: plane fed the rotor mirror from the FIFO head | push-side op |
| `refresh_credit` (board) 2 REFs across a demand stretch | REF held out of the read-return window without bound | `REF_WAIT_RD_RETURN` parameter, default 0; all-idle on live `bank_act_ready` |
| `static_close` at 23% vs the 49% ceiling | hinted column always beat another bank's ACT, serializing ACT and column | class alternation in the arbiter |

## 4. Gates

| gate | result |
|---|---|
| contract bench, BANK_PICK: baseline + hold + zero-bubble (16/16 steady, 8/8 after a live-gate dip) + post-pop + override | 5/5 PASS |
| contract bench, FRFCFS: baseline + zero-bubble pass; hold / post-pop / override strict-xfail by design | 2 pass, 3 xfail |
| `mc_bank_head_records` fub test (func), mutation "ignore pending in behind_same_row" fails | PASS / fails as intended |
| pumice `make clean-all && make run-all-func-both` on the committed text | 216 passed / 1 skipped default geometry; 216 passed / 1 skipped board geometry (BL4 / 32b beat / x16); common-ip contract 7 pass / 3 xfail and records fub test rerun on the same text; module checksums recorded before and after |
| granite `make clean-all && make run-all-func` (FRFCFS default, records wired) | 6 passed, 1 xpassed (`top_geared[gate-8-12]`, a non-strict xfail) |
| lint -Wall: `mc_bank_pick`, `mc_bank_head_records`, `mc_scheduler_plane` both cores, `pumice_core` both cores, `granite_core` both cores, contract bench both cores | clean (pre-existing `cal_busy_o` UNDRIVEN and PINCONNECTEMPTY excluded) |
| `bin/filelist_registry.py --check` | PASS; `mc_bank_sched` gone from every filelist |

## 5. Performance (pumice-CAM perf proxy, board geometry, 75 MHz, tREFI 585, one generator unless noted)

Programmed timings (board derivation): tRC 5, tRCD 2, tRP 2, tRAS 4, tRFC 11,
tRRD 2, tFAW 4, tWTR 4, tCCD 1, tWR 4, tRTP 2, tRTW 21. Floors at these
timings: col_major rd gap 6 -> 369.2 MB/s, wr gap 8 -> 319.9; streaming 599.9.
FRFCFS numbers are the same harness, same run of this commit (`TEST_SCHED_CORE=0`).

### 5.1 One generator, txn 1024

| family | FRFCFS wr | FRFCFS rd | BANK_PICK wr | BANK_PICK rd | lat wr/rd (cyc) | mism |
|---|---|---|---|---|---|---|
| incremental | 556.1 (Phase 0) | 558.7 (Phase 0) | 574.4 | 571.4 | 48.0 / 50.4 | 0 |
| row_major | 571.9 (Phase 0) | 568.7 (Phase 0) | 577.7 | 576.9 | 48.0 / 50.2 | 0 |
| col_ilv | 307.0 | 353.0 | 459.0 | 457.3 | 52.1 / 51.4 | 0 |
| col_major | 195.0 | 194.9 | 310.9 | 358.7 | 95.8 / 95.9 | 0 |

Command-gap histograms (`PERF_CMD_TRACE=1`, this commit): BANK_PICK col_major
inter-row gap 6 (RD, 1001 of 1024 rows) and 8 (WR, 996) -- the JEDEC floor;
FRFCFS on the same run: 17 (987 rows) for both. The remaining distance to the
369 / 320 floor is refresh (one episode per tREFI = 585 cycles, ~30 cycles
each). Gate check: wr >= 310 PASS (310.9); rd >= 360 is 0.4% short (358.7)
and at the refresh-adjusted floor.

### 5.2 LiteDRAM-equivalent profile (`TEST_TIMING_OVERRIDES="tRTP=1"`, col_major, txn 1024)

| | wr MB/s | rd MB/s | rd inter-row gap |
|---|---|---|---|
| LiteDRAM, same harness (2026-09) | 304 | 386 | 5 (no tRTP counter) |
| BANK_PICK | 311.3 | 387.6 | 5 (1012 of 1024 rows) |

Parity: rd +0.4%, wr +2.4% -- inside the owner's 1-2% criterion for rd, above
it for wr. The one-cycle rd->PRE hop at tRTP = 1 is the direct hint load (a
hop shorter than the pipe).

### 5.3 Four writers + four readers (`TEST_NUM_GEN=4`, txn 256 each)

| family | FRFCFS wr | FRFCFS rd | BANK_PICK wr | BANK_PICK rd |
|---|---|---|---|---|
| incremental | 306.5 | 353.0 | 566.8 | 535.4 |
| row_major | 306.6 | 353.0 | 570.4 | 531.5 |
| col_ilv | 306.6 | 353.0 | 536.3 | 533.9 |
| col_major | 306.6 | 353.1 | 461.2 | 460.3 |

The FRFCFS core sits at one ceiling (307 / 353) for every family with eight
generators; BANK_PICK is 1.5x (col_major) to 1.85x (streaming writes) above
it. mism 0 everywhere. No LiteDRAM multi-generator number exists in this
harness yet (Phase 5).

Model findings in these runs: the pre-existing `tWR` soft violation per
col_major write row (Phase 0 §5; FRFCFS shows it too, 1057 in its run), and
2 `tREFI` soft violations per BANK_PICK run (every run, any length; 0 on
FRFCFS in the same harness). The latter is new to this core and is filed as
a pumice issue (section 6); data is golden in every run.

## 6. Left for later phases

- Phase 3 timing: OOC + build-perf of `mc_bank_pick`; the fire stage carries
  a 16:1 record mux and a 14-bit row compare (`w_hit`) -- measure before
  believing any level count.
- Granite on BANK_PICK is one parameter (`granite_core` `SCHED_CORE`); Phase
  4 replaces its entry store with the FIFO backend behind the same records.
- Mixed same-bank read/write streams: a miss pair yields to the other
  direction's hits until its aging flag lifts the courtesy (sched_age_thresh
  = 0 disables aging). Watch under 1w+1r same-bank traffic.
- `test_pumice_close_drain` still probes FRFCFS internals (built with
  SCHED_CORE=0); a BANK_PICK equivalent (group drain -> one AP) is open.
- The calibrated checker's `tWR` soft violation per col_major write row
  (Phase 0 §5) is pre-existing (FRFCFS too). The 2 `tREFI` soft violations
  per BANK_PICK run are not: pumice ISSUE (see the issue lane) -- find the
  two refresh episodes that exceed tREFI (suspect the first interval after
  init and the drain-to-grant distance under a column stream).
