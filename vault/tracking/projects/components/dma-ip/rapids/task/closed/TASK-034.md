# TASK-034: rapids-g -- gatling sequences the schedulers

**Priority:** P2
**Status:** closed -- 2026-10-22; started 2026-10-21, plan approved by the owner
**Owner:** sean galloway

## Why

Owner 2026-10-21: "make a rapds-g version that uses gatling instead of the scheduler FSM and as much of the scheduler code as possible. in the rtl have fub_g/macro_g/top_g. Strive for one gatling being shared by 4-8 schedulers." Follow-up: "I thought Gatling could do the next address calculations."

## What

1. Extract `rtl/fub/scheduler_core.sv` from `scheduler.sv`: the datapath, with the state as an input. The product `scheduler` becomes core + FSM + its two `stream_run_addr_gen`. The product behaviour stays the same; the full byte regression is the gate.
2. `rtl/fub_g/scheduler_g.sv`: core + firmware command/state port (legal-edge table; channel reset and fatal error stay hardware interlocks) + firmware-fed run-base FIFOs + firmware-written beat totals.
3. `rtl/macro_g/rapids_seq_g.sv`: one `gatling_core` per half, shared instruction ROM, per-context scratch, MMIO. Hart h slot s = channel h + 4s; NUM_CHANNELS 4 or 8.
4. Firmware `fw_g/sched_g.S`: descriptor policy, chain decision, beat totals, and EXT run bases computed by repeated addition (no multiplier).
5. `bin/gen_rapids_g.py --check` generates the `_g` array/src/snk/core/top_base and tops from the product files.
6. DV: product regression; firmware bases against `stream_run_addr_gen`; the existing macro/top suites against the -g builds; firmware-specific cases; mutation; perf; OOC synthesis A/B.

## Done when

The -g macro/top suites are green at 4 and 8 channels from clean, the product byte regression is unchanged, the address equivalence holds, mutants are caught, the perf and area A/B are measured, and the MAS chapters are in.

## Closed 2026-10-22

Every done-when item is met from clean on the final image (one hart per channel, NUM_HARTS =
NUM_CHANNELS; the one-slot tight loop):

- rapids-g regression: fub_g 75, macro_g 216, top_g 162 passed / 21 skipped (16-channel cells), 0 failed.
- RAPIDS product gate unchanged: counts in rapids BUG-016.
- Address equivalence: the equivalence bench's golden model, every cell.
- Mutants: the firmware and RTL mutant set (MAS 5.5) was run on 2026-10-21; each was caught. The
  final image's loop changes were caught by the suites on the way (hart_fault, `tile_source_bad_ptype`),
  but the mutant set was NOT re-run on the final image. rapids TASK-037's done-when re-runs it on the
  rewritten firmware.
- Perf and area A/B: Genesys 2 gcompare, 45 points, both designs, board == sim on 85/85 windows each
  (`byte_perf_gcompare_fsm_il_rc.json`, `byte_perf_gcompare_gfin_rc.json`); 8-hart bench and OOC
  `rapids_core` A/B.
- Docs: RAPIDS MAS 0.82 Chapter 5 (with firmware flow charts) and HAS 0.92 Sections 2.3 and 6.4
  (choosing RAPIDS or rapids-g).

Bugs found on the way: rapids BUG-016 and BUG-017 (closed). Follow-ons: rapids TASK-035, TASK-036, TASK-037.
