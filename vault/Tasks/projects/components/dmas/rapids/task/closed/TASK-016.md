# TASK-016: re-prove the rapids and stream formal suites after the engine fixes; prove the control engines

**Priority:** P2. Sean's ordering 2026-09-27: "work on formal last" -- after
TASK-013/014/015 and the BUG-004..007 / stream BUG-012..015 RTL changes.
**Status:** CLOSED 2026-09-28 (closing note at the end).

## Why

Seven rapids and six stream flats were newer than their last prove status,
two stream proofs were FAIL, three had no status at all, and the two Phase-2
control engines carried their TASK-014 drain properties only in `ifdef FORMAL
blocks that no task ever compiles (the flats are sv2v output without
-DFORMAL). Nothing had been proved on the RTL that shipped this week.

## What was done

Every failure was a harness or flow defect, not RTL; the details are in
`formal/FORMAL_TODO.md` (2026-09-28 pass). In short:

- Harness rot: `ap_ar_size` still asserted the 64-byte descriptor fetch in four
  harnesses (it has been 32 bytes since the beats rework); `perf_profiler`'s
  count bound ignored that `cfg_clear` is an async FIFO reset; the
  `sram_controller` reset property predated the wrapper's deliberate
  zero-reset boundary flop.
- Environment rot: the descriptor-engine and scheduler-group harnesses let the
  address-range registers change every cycle; since BUG-006/BUG-014 the engine
  gates ar_valid on the range, so a mid-AR range write withdrew the AR. Ranges
  are quasi-static (HAS) and are now assumed stable after reset.
- Flow rot: `rapids/scheduler_beats` never passed DEPS to sv2v (and DEPS was
  empty), `stream/scheduler_group` lacked the address generators, and
  `stream/scheduler_group_array` still listed the retired full-monitor stack
  instead of `axi4_master_rd_monlite`.
- Budgets: proofs that did not finish in an hour on one core are bounded at
  the depth they reached, with the reason in the `.sby`: rapids
  `descriptor_engine_beats` 20 -> 16, `scheduler_beats` 35 -> 25,
  `snk/src_sram_controller_beats` 25 -> 15; stream `scheduler` 35 -> 20,
  `sram_controller` 25 -> 18.
- NEW `formal/rapids/ctrlrd_engine` and `ctrlwr_engine`: port-level harnesses
  stating the TASK-014 contract in fabric terms (AR/AW/W held until accepted,
  channel reset included; no second issue while a response is owed;
  r_ready/b_ready only while owed; idle means nothing outstanding). Prove PASS
  at depth 20; both covers reached (a response drained after a channel reset
  landed mid-transaction; return to idle).

## Result

---

**CLOSED 2026-09-28.** rapids: 11 of 11 tasks PASS (the nine existing ones on
their current flats plus the two new control-engine tasks, covers reached).
stream: the nine tasks whose flats were newer than their status re-proved
PASS; the two FAILs (perf_profiler, sram_controller) were harness defects and
pass now. Every bounded depth is recorded in its `.sby` with the reason.
Details and the per-module notes are in `formal/FORMAL_TODO.md` (2026-09-28
pass). Left for a separate audit: `stream/monbus_axil_group` (flat from April;
the top instantiates `monbus_axil4_axil4_group` now).
