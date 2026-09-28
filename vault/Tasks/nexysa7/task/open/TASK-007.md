# TASK-007: Move ddr2_char_framework into pumice/ (the NEXYS-003 residue)

> Migrated 2026-09-27 from `vault/Tasks/nexysa7/open.md` as **NEXYS-008** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** Low
**Status:** [ ] Open (2026-09-23)

Split out of [[NEXYS-003]] when that closed. This is the ONLY functional work
that was left in it, and it is TIDINESS, not breakage -- `build-perf/rtl/
filelists/` `-f` includes the framework in place today and that is legal, the
tests run, the flow builds.

- `ddr2_char_framework/rtl/*` -> `pumice/rtl/` (flat; keep `bridges/` as-is)
- `ddr2_char_framework/dv/{tb,tbclasses,tests}` -> `pumice/dv/`, then repoint
  `SIM_TESTS` in `build-perf/Makefile` at `$(SELF_DIR)/dv/tests`

Scope decided 2026-09-23: take the FULL move (retire `ddr2_char_framework`,
rename the `filelists.toml` area and `DDR2_CHAR_FRAMEWORK_ROOT`), not the two
literal bullets. The bullets alone leave `dv/filelists` behind -- `filelists.toml`
registers it and the tests reference it by path -- so DV collateral ends up
split across two directories, and it orphans `regen_bridges.sh` from the bridges
it generates. A half-move needing a second move later is worse than either end.

Survey (verified 2026-09-22, repo-cleanup): 76 tracked files; 51 literal
`ddr2_char_framework` paths across 9 filelists; 4 `bin/filelists.toml` lines;
20 embedded Python path strings, three of them OUTSIDE the pumice tree
(`bin/filelist_registry.py:90`, `bin/TBClasses/shared/filelist_utils.py:117`,
`bin/TBClasses/harness/test_device_bus.py:26`). `DDR2_CHAR_FRAMEWORK_ROOT` is
DEAD CONFIG -- defined in two tables, used by zero `.f` files -- so this is ~70
literal edits, not a one-line variable change. Destinations are empty
(`.gitkeep` only); no name collisions.

**Two hazards.**
1. `regen_bridges.sh` is a GENERATOR and breaks on this move: it derives
   `FRAMEWORK_ROOT="$SCRIPT_DIR/.."` then `BRIDGES_DIR="$FRAMEWORK_ROOT/rtl/
   bridges"`. Invoked by BOTH `build-perf/Makefile:41` and
   `flows-litedram-uart/Makefile:37`, and registered as `regen=` in
   `filelists.toml:158`. CRITICAL RULE #0 applies: regenerate the three bridges
   into a SCRATCH tree and diff the ~30 generated files INDIVIDUALLY before
   committing -- a generator that writes nothing also produces no diff, so the
   regen step must prove it ran, not prove it was quiet. (Scar:
   `regen_bridges.sh` once reverted three rounds of work by writing DV.)
2. `char_engine_harness.sv`'s stated rationale describes a different file.
   build-perf has NO `char_engine` reference, so there is no divergent copy to
   reconcile; the genuinely shared piece is `char_engine_block.sv`, which is in
   `ddr2_char_framework/rtl` and moves anyway.

**Acceptance.** Collection counts are not a gate ([[stale-sim-build-false-green]]).
Record the exact invocation AND geometry on both sides -- the pumice suite runs
the same files at two shapes now (`make run-all-func-both`), so a bare test
total is not like-for-like. Pre-move baseline: `fc83c1b3c`, `top/` 188 passed at
BOTH geometries, char board gate 216 passed / 2 xfailed.
