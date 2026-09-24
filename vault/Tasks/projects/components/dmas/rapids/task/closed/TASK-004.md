# TASK-004: Register-map hygiene enforced in RAPIDS DV
> **Was `TASK-057` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-23  **Priority:** P2

All three STREAM lessons audited and ported.

**1. By-name regmap.** The kick sequencer's harness CSRs (0x064-0x07C) were
declared in `rapids_char_harness.sv` but absent from the generator table, so
they had no by-name entry -- which is why two files hardcoded them. Added
KICK_CFG / KICK_MASK / KICK_BASE_LO / KICK_BASE_HI / KICK_STRIDE / GO /
OBS_TARGET to `bin/gen_rapids_harness_regmap.py` (53 -> 60 registers) and
converted BOTH offenders: `dv/test_rapids_char_top_kick.py` and
`host/run_characterization.py`.

Verified in two stages. Offline: all nine field compositions produce words
byte-identical to the old literal writes, including the two-field
`KICK_CFG` case (HALF=1, START_GEN_ON_GO=1 -> 0x3). In simulation: the kick
test is 2 passed / 571.81s with zero `KeyError`s -- a misrouted name raises
`unknown rapids harness register` in `_compose`, and the test asserts
KICK_ENABLE was written exactly once, carried the staged mask, and was the
FINAL write.

Remaining hex literals in RAPIDS DV (`0x2000 + ch*0x100`, `src_addr=0x1000`)
are DATA/memory addresses, not registers, and are correctly left alone.

**2. Kick writes prove a descriptor fetch.** Ported
`assert_descriptors_fetched()` + an `m_axi_desc` AR-monitor callback into
`rapids_beats_top_tb.py`, wired into the source, sink and ext top tests.
RAPIDS is two-half, so unlike STREAM's single map both structures are keyed
by half -- a SRC kick must be proven by a SRC fetch.

Proven in both directions. Live: EXT 1 passed / 270.64s and source+sink
2 passed / 549.13s, each logging "all N kicked descriptors were fetched".
Offline negative test 4/4 -- kicked-but-unfetched raises, zero-kicks raises
(vacuity guard), kicked+fetched passes, and a fetch on the WRONG HALF still
raises, which is what makes the half-keying load-bearing rather than
decorative.

**3. No hand-added registers.** `rapids_regmap.py` is regen-clean: 120
committed vs 120 from a fresh `bin/peakrdl_generate.py` run, with zero
hand-added, zero missing and zero differing entries. RAPIDS does NOT carry
STREAM's 16 hand-stuffed `CHx_CTRL` aliases.

One caveat for [[TASK-088]] (STREAM area): `rapids_regmap.py`'s HEADER is
hand-edited -- a better docstring explaining that the two engine instances
share the layout. The register dictionary is clean, but a byte-for-byte
regen gate would call the file permanently stale on those 21 header lines,
so that manifest entry needs a SEMANTIC (register-dictionary) comparison.

Swept up: both harness regmaps still named `rapids_char_top.sv` as the
decoding RTL, stale since the harness refactor moved the host path into
`rapids_char_harness.sv`.

---
