# TASK-050: granite area list from report 5.10 -- FIFO store, LPDDR2 compile-out, fixed timings, one match set, window variants

> Source: owner, 2026-10-23 -- "please do 1/2/3/4 try 5 and see if it works
> out", on the five-row list that closed section 5.10 of the mem-ctrl
> recovery Phase 3 report (granite BANK_PICK vs LiteDRAM, area). Related:
> recovery plan Phase 4 (the FIFO backend and the storage battery), TASK-049
> (the window families the measurements use), ISSUE-024 (the wall-clock
> engine wait that failed the mixed cell twice under load).

**Priority:** P2
**Status:** closed 2026-10-23 (sim gates green on both backends; board build of the shipped text +0.304 ns, 0 failing endpoints, granite_core 7 403 LUT / 5 316 FF against 9 956 / 5 160 at the 5.10 baseline; the store 3 894 LUT against 5 825 for the entry store with records; report 5.11)
**Owner:** TBD

## What landed

1. **`mc_bank_fifo_store`** (common-ip fub, new): granite's storage backend,
   `granite_core STORE_BACKEND = 1` (default; 0 = `mc_xddr2_entry_store` +
   two `mc_bank_head_records`, kept for A/B). Same ports and data path as
   the entry store (one BRAM, 2-deep prefetch skid, drain queue in commit
   order, B from the skid tag, read tickets at issue). Descriptors are slots
   in a pool; each (direction, bank) keeps a FIFO of slots in arrival order
   and the `mc_head_rec_t` records are read off the fronts and registered.
   A global fill-order FIFO names the slot each W beat belongs to.
   - First cut capped the bank queues at 4 (`BANK_FIFO_DEPTH`). On the board
     geometry one 8-beat AXI burst chops into 8 same-bank entries, so the
     cap blocked the address channel half way through every burst: 23
     percent off at eight threads (429 vs 557 MB/s), 17 percent off on
     one-thread `col_ilv`, and the mixed family did not complete (DRAM
     silent 15 600 cycles). Shipped form: `BANK_FIFO_DEPTH = 0` = pool-deep
     (admission is the pool's, as the entry store's), and the same-row-behind
     flag is one stored bit per queue position, compared at push against the
     bank's registered tail row. Handbook:
     `vault/handbook/design/per-bank-queues-admit-from-the-pool.md`.
   - `granite_core` generate: `g_fifo_store` (heads direct, FR-FCFS vectors
     tied 0, `$error` unless SCHED_CORE = BANK_PICK) / `g_entry_store`.
     Filelists: `common-ip/rtl/filelists/fub/mc_bank_fifo_store.f`, granite
     `granite.f` / `granite_all.f`.
2. **LPDDR2 training plane compiled out of DDR2 builds**: `HAS_LPDDR2`
   plumbed pumice_core -> pumice_top -> pumice_top_geared -> ddr2_char_macro
   -> ddr2_char_harness -> ddr2_char_top (`CHAR_LPDDR2` define, default
   off) and granite_core -> granite_top_geared -> granite_char_macro ->
   granite_char_harness -> granite_char_top (`1'b0`); drives
   `mc_training_plane` HAS_LP_ZQ / HAS_LP_DQ_CAL.
3. **`FIXED_TIMINGS`** (granite_core, geared top, macro, harness, top;
   `GRANITE_FIXED_TIMINGS` env -> define in the ddr2_char `create_project.
   tcl`): the scheduler plane's timers compare against `T_*` constants and
   the TIMINGS CSRs are ignored. Defaults = `ddr2_timings_mc_cycles(75e6)`
   with the board read-path alignment (tRCD 2, tRP 2, tRAS 4, tRC 5, tWR 4,
   tRTP 2, tFAW 4, tRRD 2, tWTR 4, tRTW 20, tCCD 1, tREFI 585, tRFC 11).
   `test_granite_core.py` / `test_granite_top_geared.py` take
   `GRANITE_FIXED_TIMINGS=1` with `T_*` set to the values each test runs on.
4. **One match set**: falls out of item 1 -- the FIFO store compares the two
   heads' rows against the open-row image and nothing else; the records
   modules' N x N same-row matrix is gone from the default build.
5. **Window variants**: `NUM_ENTRIES`, `STORE_BACKEND`, `BANK_FIFO_DEPTH`,
   `FIXED_TIMINGS` on `granite_char_harness`, `granite_char_uart_tb_top` and
   the perf proxy (`TEST_NUM_ENTRIES`, `TEST_STORE_BACKEND`,
   `TEST_BANK_FIFO_DEPTH`, `TEST_FIXED_TIMINGS`); `GRANITE_NUM_ENTRIES` /
   `GRANITE_BANK_FIFO_DEPTH` build knobs. Measured in report 5.11.
6. **Seeds** (owner, same day: "ensure all three agents are seeded the
   same"): `perf_mixed_family.PERF_SEED` / `gen_seed` / `seed_fields` are
   the one seed source for the pumice, granite and LiteDRAM proxies; every
   family record carries `seed` + `gen_seeds` (mixed: `wr_seeds` /
   `rd_seeds`); the grid summary checks parity across the three.
7. Contract battery: `test_mc_store_arbiter_contract` cells are
   core x store (`bank_pick-entry`, `bank_pick-fifo`, `frfcfs-entry`); the
   tb_top takes `STORE_BACKEND`. Granite proxy gained `_host_diag` and a
   store-state probe, dumped on a failed cell (`PERF_ALWAYS_DIAG=1` always).

## Measured (granite perf proxy, board geometry, 75 MHz, wr / rd MB/s, mismatched 0, FIFO store vs entry store)

| family | threads | FIFO store (shipped) | entry store |
|---|---|---|---|
| incremental / row_major / col_ilv / col_major | 1 | 568.2 / 567.5, 576.5 / 572.2, 460.8 / 451.2, 311.1 / 357.7 | identical to the decimal |
| incremental / row_major / col_ilv / col_major | 8 | 556.9 / 555.3, 557.6 / 557.2, 533.5 / 525.9, 459.0 / 457.7 | identical to the decimal |
| random | 8 | 442.1 / 452.9 | 442.1 / 452.9 |
| row_thrash, 2-beat bursts | 1 | 128.7 / 162.9 | 128.7 / 142.9 (the stored flag is the next entry's row, so the last column of a row takes the AP the entry store withheld) |
| mixed (concurrent, 2 threads per bank) | 8 | 98.1 (49.1 / 49.1), 200 290 / 200 299 cycles | 98.1, same cycle counts |

## Gates

granite suite 6 / 1 xfailed on the FIFO store (first cut 6 / 1 xpassed: the
n8/m12 cell passed under the cap), on the entry store, and with
`GRANITE_FIXED_TIMINGS=1`; contract battery 12 / 3 strict xfailed (the
research core's by-design cells); lint of granite_core at FIXED 0 / 1 and
NUM_ENTRIES 1 / 8 (only the pre-existing warning classes), whole-harness
lint of granite_char_top default and with FIXED + NUM_ENTRIES 16 (0 errors);
filelist registry PASS. The mixed cell failed twice under 3-5 parallel sims
("write engine did not complete" with the entry store's exact cycle counts)
and passed alone: ISSUE-024. Board builds, pumice both geometries and the
framework suite: report 5.11.
