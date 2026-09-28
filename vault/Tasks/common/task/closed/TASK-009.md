# TASK-009: Signal-prefix sweep: make r_/w_ truthful across the library

> Migrated 2026-09-27 from `vault/Tasks/common/closed.md` as **COMMON-022** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-10 (Sean: "fix the WRR and any other sv file in
common to properly use prefixes")

Audited every rtl/common module against [[signal-prefixes]] (three violation
classes: w_ assigned with <=, r_ driven combinationally, unprefixed
internals). Fixed 12 files - 8 in common plus, by scope extension, the same
documented bug in its 4 family twins outside common:

- **The handbook's live example, killed in all five homes.** w_rd_data in
  fifo_sync, fifo_async, gaxi_fifo_sync, gaxi_fifo_async and
  gaxi_drop_fifo_sync was a flop wearing a wire's name in the registered/
  BRAM read paths. The generalizing fix: a signal whose storage differs per
  generate branch cannot carry one truthful name - the name moved INTO the
  branches (branch-local r_rd_data driving the port; mux branches drive the
  port straight off the array).
- **Mechanical renames:** w_client_weight (WRR - matching the new DRR/token
  bucket siblings), w_feedback_bit, w_found, w_local_duty/period/repeat,
  w_shift_amount_mod, w_next_lfsr, w_v_data/w_v_count.
- **Audit false positives correctly left:** w_almost_empty_count and
  w_tap_positions - the <= hits were COMPARISON operators.
- **Decisions taken (for the handbook note):** memory arrays keep the bare
  `mem` name (family idiom; latency lives in the read path around them,
  which is now truthfully named); pure slice aliases of registers keep r_
  (`assign r_wr_addr = r_wr_ptr_bin[AW-1:0]` - the value genuinely comes
  out of a flop, and w_ would hide the register from an address-path
  reader).
- **External refs checked BEFORE renaming:** every hit was a regenerated
  sby output dir or a coincidental name elsewhere - nothing to repoint.

Regression: val/common 220, val/cdc 130, val/integ_common 8, val/integ_amba
6 - all green; all gaxi-FIFO tests green. val/amba showed 29 failures, ALL
cocotb_test_block_ready (test_axi_mon_block_ready.py): proven pre-existing
by stashing exactly the 12 changed files and reproducing the identical
wedge on the baseline - it belongs to the in-flight monitor-instrumentation
branch work, not this sweep.

---
