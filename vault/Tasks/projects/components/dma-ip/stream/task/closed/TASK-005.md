# TASK-005: RLB blocks brought under the .rdl regen gate
> **Was `TASK-089` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-24  **Priority:** Medium

The gate covers 26 entries / 18 distinct RDLs now: the 9 from [[TASK-006]]
plus all nine retro_legacy_blocks. All 18 RLB `.sv` reproduce
byte-identically; hpet, pic_8259 and rtc regmaps are gated too.

`<block>_config_regs.sv` is deliberately EXCLUDED -- hand-written wrappers
("Connects PeakRDL to Core"), never emitted by the generator. Including them
would declare hand-written RTL permanently stale, the ddr2_char harness_csr
trap again.

**pit_8254's regmap is excluded as a FINDING, not an omission.** See the RLB
area task filed alongside this: `pit_regmap.py` came from the superseded
`bin/peakrdl_to_regmap.py` and contradicts its own RDL on 14 fields.

Validated: sampled entries dirtied one at a time, every one CAUGHT.

---
