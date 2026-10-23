# TASK-035: An 8-bit descriptor field selects the next-address algorithm (rapids-g)

**Priority:** P3
**Status:** open -- 2026-10-21; owner direction, not started; waits on rapids-g (rapids TASK-034)
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
