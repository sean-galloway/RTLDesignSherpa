# TASK-014: pit_regmap.py regenerated to match its RDL

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-017** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-24  **Priority:** Medium (filed as High -- corrected, see below)

`rtl/pit_8254/pit_regmap.py` came from the superseded
`bin/peakrdl_to_regmap.py` and contradicted `pit_regs.rdl` on 14 fields across
7 registers: every reserved field `sw='rw'` where the RDL says `sw = r;
hw = na;`, and four PIT_CONTROL fields `'rw'` where PeakRDL emits `'wo'`.
Found by the `.rdl` regen gate ([[TASK-089]]).

Regenerated. Reserved fields marked `rw` drop 26 -> 12 (the rest are genuinely
rw), zero reserved fields left non-`r`, and PIT_CONTROL now reads
bcd/counter_select/mode/rw_mode = `wo`, reserved = `r`. Gated as entry 27 in
`bin/check_rdl_regen.py`, verified to bite.

**The mechanism is real.** `RegisterMap.walk()` calls `sw_writable_mask()` at
`register_map.py:174` (reset-value check) and `nonlatching_mask()` at `:204`
(write/readback), both driven by `sw`. A walk on the old map would have
written read-only reserved bits and expected write-only fields to latch.

**Two corrections to how I filed this.** I filed it **High** on the claim that
`pit_helper.py` consumes it and that regenerating would change DV behaviour.
Neither holds: no test or tbclass loads this regmap, and `pit_helper.py`
itself has zero consumers. So it was a LATENT bug with no current blast
radius, not a live DV defect -- which is also why the fix was low-risk.

`test_apb4_pit_8254.py` is 4 passed before and after. That proves the change
broke nothing; it CANNOT validate the fix, because the tests never read the
regmap. The validation is the field-level comparison against the RDL.

Observation worth its own look some time: five RLB `*_helper.py` files
(pit, hpet, rtc, pic_8259, smbus) have zero consumers, and the hpet/rtc
regmaps are referenced by no DV file either.
