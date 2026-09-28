# TASK-011: Burn down --blindspots, then make it a gate

> Migrated 2026-09-27 from `vault/Tasks/tooling/closed.md` as **TOOL-012** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-08-28 (opened 2026-07-26, measured at `0928fb0b`)
**Priority:** was P2

Opened at 516 findings in three classes. Final state: **0, 0, and 2** -- the
two survivors are tracked as FORMAL-INTEG-COMMON-ORPHANS. The gate itself went
in long ago (`9d0a0c60`); this was the burn-down.

**Be honest about which of these was work and which was arithmetic.**

| class | 516-era | now | what actually happened |
|---|---|---|---|
| tests hand-listing sources | 128 | **0** | real burn-down. 128 -> 12 by earlier passes; the last 12 in `78506f35` -- nine genuinely converted to `get_sources_from_filelist` (plus six missing stub filelists created, since the stub variant runs at gate level), and three that were never hand-listed at all |
| `.sby` dead source paths | 387 | **2** | mostly NOT burn-down. The 387 counted `formal/**/config.sby`, which SymbiYosys GENERATES into every `<task>_prove/` and `<task>_cover/`; none are tracked. Fixed in `ecdf5a3e` to scan tracked files only. Two genuinely dead harnesses remain |
| unregistered filelist | 1 | **0** | `ddr2_char_macro.f` registered |

So the headline "516 -> 2" overstates it. One class was burned down properly,
one was largely a measurement error in the checker, and the checker also
**miscounted the class it was best at**: three of the last twelve tests were
false positives, flagged for the string `verilog_sources = [` when that was a
merge accumulator in a test that already used filelists for its RTL and merely
appended its own `tb_*.sv` harness. That detector now parses with ast and
judges only expressions that flow into `verilog_sources`.

**The lesson worth keeping** is the one this task was created to make, turned on
itself: a check that cannot be trusted to count is as bad as no check. The
`.sby` scan reported REGRESSED locally and PASS in CI for identical commits; the
test scan called three correct tests broken. Both were mutation-tested after
fixing -- break it, see it caught, restore it, see it clear -- which is the
standard the rest of this gate should be held to.

See [[filelists]], TOOL-014 for the three gate blind spots fixed alongside.
