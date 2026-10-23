# TASK-035: An 8-bit descriptor field selects the next-address algorithm (rapids-g)

**Priority:** P3
**Status:** closed -- 2026-10-23; opened 2026-10-21; owner direction, not started; waits on rapids-g (rapids TASK-034)
**Owner:** sean galloway

## Why

Owner 2026-10-21: "Eventually there should be an 8-bit descriptor field that chooses one of many next address algorithms."
In rapids-g the next-address arithmetic is firmware on gatling (rapids TASK-034): today one algorithm, the
EXT run bases of `stream_run_addr_gen` (`rtl/fw_g/sched_g.S`, `gen_init` / `refill`). Firmware makes a new
algorithm a code change rather than an RTL one, so a selector in the descriptor can choose among many.

## What

1. Field location (owner decision). Proposal: chunk 0 bits [224:217], the first eight of the unused
   [255:217], so linear and EXT descriptors both carry it; 0 = today's behaviour (linear, or EXT run bases
   when TYPE = EXT).
2. `scheduler_g`: latch the field and expose it in the sequencer window (a read of chunk 0 [255:192]).
3. Firmware: dispatch `gen_init` / `refill` on the selector, one routine per algorithm; an unknown
   selector is an invalid descriptor (CH_ERROR).
4. The FSM scheduler (product tree) ignores the field (selector 0 only), or refuses non-zero; decide with 1.
5. DV: each algorithm gets an equivalence or golden-model cell, as the EXT bases have against
   `stream_run_addr_gen` (`dv/tests/fub_g/test_rapids_g_equiv.py`).

## Done when

The field is defined in the HAS descriptor format, at least two algorithms are selectable on rapids-g,
each is checked against a model, and selector 0 is bit-identical to today.

## Closed 2026-10-23

Owner chose the proposal as filed: chunk 0 [224:217]; 0 = today's behaviour; 1 = Z-order (Morton) run
bases; RAPIDS (rapids-8ch, rapids-16ch) refuses a non-zero selector as an invalid descriptor (CH_ERROR).
`rapids_pkg` carries `DESC_ALG_LO/HI` and `desc_alg_ok`; `scheduler_core` folds it into the valid
latch, with `desc_alg_max` tied to 0 in `scheduler` and fed from the image (`.equ ALG_MAX`, parsed by
the generator into `FW_ALG_MAX`) in rapids-g. Firmware dispatches `gen_init` / `refill` on R_ALG;
Z-order steps by adding and subtracting stride<<i, no multiplier.

- Z-order cells in the equivalence bench against a Morton golden model; selector 0 runs the existing
  `stream_run_addr_gen` cells unchanged; out-of-range selectors are checked to error on both trees.
- Full gate from `make clean-all`, 2026-10-23 (one run, every area at the full level):
  rapids fub_g 192, macro_g 270, top_g 183 (16-channel cells now run, 0 skipped; `test_rapids_g_regpath`
  failed 3/3 in that run because the new jump-table check in `bin/gen_rapids_g_fw.py` also applied to
  that test's own program; the check was scoped to the scheduler image and the test re-run 3/3 passed),
  fub 1,740, fub_beats 1,302, macro 843, macro_beats 774, top 183, top_beats 54; STREAM fub 510,
  macro 684 (+5 skipped: the 1-channel cells of the multi-channel test, by design), top 69. 0 failed.
- HAS 0.93 Section 5.1 (Next-Address Selector table); MAS 0.83 Table 5.3.4.
