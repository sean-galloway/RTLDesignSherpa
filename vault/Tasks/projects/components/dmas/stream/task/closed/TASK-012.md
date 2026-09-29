# TASK-012: arm the 26 signal-contract maps that still render VERDICT: NOT CHECKED

**Status:** CLOSED 2026-09-28 (closing note at the end). Was: open 2026-09-27  **Priority:** P3 -- documentation evidence, no RTL
change. Filed from tooling TASK-006 when that global item closed: the shared
emitter in `bin/kmaps/` is done, stream's generator already imports it, and
stream TASK-001 armed the five priority maps (7 IDENTICAL, 1 DIFFERS -- a real
finding). 26 of 37 maps were left with no `rtl_sop=`, so the one criterion that
finds defects (derived cover vs the RTL as written) checks nothing on them.

For each remaining `kmap(...)` call in `docs/gen_signal_contracts_kmaps.py`:

1. `depends_only_on=` if missing: why the function depends on the axes alone.
2. `rtl_sop=`: the RTL expression as a sum-of-products over the axis names.
   A DIFFERS verdict is a finding -- redundant terms (say why they stay), an
   unstated invariant, or a bug -- and goes to this lane's bug list.

Multi-valued maps get item 1 only (no SOP is defined for them; the writer skips
the verdict on purpose). Spec: [[signal-contracts-and-kmaps]]. pumice's
equivalent is pumice TASK-029.

Acceptance: regenerated workbook has no `NOT CHECKED` row; every DIFFERS is
justified in the map's check text or filed as a stream BUG.

---

**CLOSED 2026-09-28.** All 35 two-valued maps carry `rtl_sop=` and all 38
maps carry `depends_only_on=` (the three multi-valued next-state maps get the
dependency argument only, as the spec says). Regenerated workbook: 32
IDENTICAL, 3 DIFFERS, 0 NOT CHECKED, 0 "not stated". The three DIFFERS are
each justified in the map's own check text as a redundant literal kept on
purpose: `w_arb_grant_ack` (the fired and stale arms written out
separately), `sched_wr_valid` (`!commit_zero` kept as the defensive twin of
`issue_rem_nz` under the commits-trail-issues invariant) and the pre-existing
`COMPL packet emission` (`use_mon` redundant given the monitors-off tie-off).
No stream BUG was needed.

What arming found, beyond the verdicts: the generator's citation check had
38 drifted cites, and four maps described RTL that no longer exists --
`m_axi_arvalid`, `w_arb_grant_ack` and the write engine's AW capture now key
on the whole `w_arb_request` (the BUG-012 / rapids BUG-004 closure), the
descriptor fetch `ar_valid` gained the `w_addr_range_valid` gate on the first
fetch, and `w_space_ok` compares `w_effective_space` (the read-side twin of
the write engine's stale-view correction). Those maps, their axis
definitions, the `w_space_ok` sub-term table and the monitor-lite event-loss
arithmetic (`w_lost` after monitor-lite TASK-002) were rewritten to the RTL
as it stands, and every cite in `CITES` points at its current line. The two
SRAM pointer maps that are slices of a three-term enable say so and say why
the third term (`!empty` / `!full`) cannot be false on the cycle that
matters.
