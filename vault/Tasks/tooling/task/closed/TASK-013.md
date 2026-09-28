# TASK-013: source comments still cite pre-migration task IDs

**Priority:** P3. Nothing is broken; the references are stale, not dangling.
**Status:** CLOSED 2026-09-27 -- every area's citations swept except pumice's, which is pumice's own item now
**Owner:** TBD

**What.** The flat-page migration (TOOL-001) renumbered every legacy ID into the
per-lane `TASK`/`BUG`/`ISSUE` namespaces. 232 mappings are recorded in
`vault/Tasks/MIGRATION_MAP.md`. But IDs are also cited from RTL, formal and DV
source, and those citations were NOT swept -- they still name IDs that no longer
exist.

**rtl/amba is DONE** -- the monitor-lite session repointed its six citations in
`a1488f7bd`, each verified against MIGRATION_MAP.md by `<area> <ID>` and keeping the
old id in parentheses (`amba BUG-030 (was AMBA-BLOCKMARGIN)`). Verified here 2026-09-27.

**Remaining citations** (re-measured 2026-09-27; the first pass UNDERCOUNTED
TASK-084 at 5 -- it is 13, and two files were missed entirely):

| File | Cites | Now |
|---|---|---|
| `projects/components/misc/dv/tests/fub/test_axi4_intf_observer.py` (11 lines) | `TASK-084` | amba BUG-036 |
| `projects/components/misc/rtl/axi4_intf_master_observer.sv:483` | `AMBA-MONTRACK` | amba BUG-029 |
| `projects/components/misc/rtl/axi4_intf_slave_observer.sv:494` | `AMBA-MONTRACK` | amba BUG-029 |
| `projects/components/dmas/stream/rtl/macro/stream_core.sv:123` | `[[AMBA-MONTRACK]]` | amba BUG-029 |
| `projects/components/dmas/stream/dv/tests/top/test_stream_top_mon_cfg.py:20` | `[[AMBA-MONTRACK]]` | amba BUG-029 |
| `projects/components/dmas/stream/dv/tbclasses/stream_core_tb.py:39` | `TASK-084` | amba BUG-036 |
| `projects/fpga-systems/Genesys2/stream/build-mon/dv/tests/test_stream_mon.py:365` | `TASK-084` | amba BUG-036 |
| `projects/fpga-systems/Genesys2/stream/stable-obs/MANIFEST.md:49` | `TASK-083` | amba BUG-035 |
| `formal/amba/axi_monitor_addr_check/formal_axi_monitor_addr_check.sv:20,208` | `AMBA-MONBUS-STABILITY` | amba BUG-028 |
| `vault/handbook/design/signal-contracts-and-kmaps.md:275` | `[[AMBA-MONTRACK]]` | amba BUG-029 |
| `vault/handbook/dv/formal.md:82` | `AMBA-MONBUS-STABILITY` | amba BUG-028 |

Roughly 21 citations in 9 files across misc, stream, Genesys2/stream, formal and the
handbook. Only amba ids have been measured at all; other areas' legacy ids
(COMMON-*, TOOL-*, BRIDGE-*, DOCREV-*, RLB-*, CONV-*, MATH-*, NEXYS-*, APBX-*) were
renumbered too and have NOT been searched for.

**bridge TASK-004 / TASK-005 (was BRIDGE-014 / BRIDGE-016) are a SEPARATE problem:
the generator emits the id.** Measured 2026-09-27 after the monitor-lite session
raised it; counts verified independently here.

  279 files cite BRIDGE-014 or BRIDGE-016
  157 of them are GENERATED (134 under projects/components/bridge/rtl/generated/,
      23 under projects/fpga-systems/**/bridges/generated/)
  122 are hand-written
    5 of those 122 are already repointed (ce173c994, monitor-lite)

The generated ones cannot be fixed by editing them -- the next regeneration puts the
old id straight back. The id is written by the generator at six sites, all confirmed
present:

  bridge_pkg/width_utils.py:81                              BRIDGE-016
  bridge_pkg/config_validator.py:200                        BRIDGE-014
  bridge_pkg/config_validator.py:329                        BRIDGE-016
  bridge_pkg/components/bridge_module_generator.py:217      BRIDGE-016
  bridge_pkg/components/bridge_module_generator.py:301      BRIDGE-016
  bridge_pkg/components/axi4_dwidth_converter_component.py:109  BRIDGE-016

**So the fix is a Rule #0 operation, not a sweep**, and it is why this part is filed
rather than done:

1. edit the six generator sites
2. `cd projects/components/bridge/bin && make regen`
3. `python3 bridge_generator.py --bulk bridge_batch.csv --generate-tests`
4. `make clean-all && make run-all-func` against the regenerated tree

Step 2-3 also rewrite `projects/fpga-systems/Genesys2/stream/rtl/bridges/generated/`,
which the STREAM/Genesys owner holds, so it needs coordinating with that session
rather than being run unilaterally. Hand-editing the 157 generated files instead would
be reverted on the next regen -- exactly the inverse failure that
`vault/handbook/design/generated-rtl-discipline.md` records (a hand fix to generated
RTL that came back, unnoticed across 13 files for months).

**Scope note.** The ~21 citations tabled above are amba ids ONLY. Adding bridge's 122
hand-written ones, the real hand-pass scope is ~143 citations, and COMMON-*, TOOL-*,
DOCREV-*, RLB-*, CONV-*, MATH-*, NEXYS-* and APBX-* have still never been searched.

**pumice: the real sweep scope is 173, not 533/651/325/238.** Four wrong numbers were
quoted before this one; the causes are the transferable part and the pumice session
recorded them in MIGRATION_MAP (959d1c276). Verified here 2026-09-27 with `git ls-files`
rather than `grep -r`, which is immune to both bugs below:

| | occurrences |
|---|---|
| `.py` | 104 |
| `.md` | 43 |
| `.sv` | 26 |
| `.rdl` | 0 |
| **real sweep scope** | **173** over 27 distinct legacy ids |
| inside `vault/Tasks` (provenance lines + map rows) | 338 -- NOT debt, this IS the resolution mechanism |

**Why every earlier figure was wrong:**

- **533** -- a `PUMICE-\d+` pattern cannot match `PUMICE-KMAP`, whose suffix is a word.
  Worse, the guard was `assert len(items) == 35` with the 35 derived from the same
  parser, so it confirmed the wrong assumption instead of contradicting it.
- **651** -- counted the tracker's own provenance lines and map rows as debt, i.e. counted
  the fix as the problem.
- **325** -- `grep -r .` emits paths WITHOUT a leading `./`, so a `grep -v '^\./vault/Tasks/'`
  filter matched nothing and the exclusion was inert. The same inert filter also failed to
  exclude `.claude/worktrees/`.
- **238** -- `--exclude-dir=Tasks` dropped BOTH `vault/Tasks` trees, removing the worktree's
  87 tracker citations while keeping its duplicated source.

**The repo contains a GIT WORKTREE, and it doubles every repo-wide count.**
`.claude/worktrees/pumice-ataglance-modes` is a full checkout on its own branch with its
own `vault/Tasks`, `projects/` and `rtl/`; it contributes 152 `PUMICE-*` occurrences.
325 - 152 = 173 exactly. **Run `git worktree list` before quoting any repo-wide count,**
or scope the count with `git ls-files`, which only sees the current worktree's tracked
files.

**Risky fraction is small:** 26 RTL comments. The other 147 are DV and host Python plus
markdown, mechanically safe to rewrite.

**Why it was not swept with the migration.** These are source files in four areas
owned by other sessions, several of which were being actively edited during the
migration. A 15-file comment sweep across RTL, formal and DV while peers hold those
files is how you lose someone's work; and the `[[...]]` forms were never resolved
by the link checker anyway, so nothing newly broke.

**Care required -- a bare ID is ambiguous.** `grep TASK-014` returns 12 files, and
every one means *pumice's* TASK-014 (paging modes retired 2026-09-27), not amba's.
Four areas now have a TASK-015 and several have a BUG-003. Sweep by `<area> <ID>`
against MIGRATION_MAP.md, never by bare ID.

**Completion criteria:**
- [x] Each citation above names an ID that exists, or names the area explicitly
- [x] Other areas' citations swept the same way -- all areas except pumice (below)
- [x] No bare-ID rewrite performed without confirming which area it meant

## Sweep as performed (2026-09-27, tooling session)

Two commits, both pushed:

- `c50be80d7` -- the hand-written half: 1,199 citations in 370 tracked files
  repointed to their migrated ids, keyed `<area> <OLD>` -> `<area> <NEW>` against
  `vault/Tasks/MIGRATION_MAP.md` (annotation form `<area> <NEW> (was <OLD>)`).
  Bare `TASK-nnn` / `PUMICE-nnn` citations with no area were NOT rewritten (the
  sweep skipped them by construction). 19 map rows whose target file no longer
  exists (the nexysa7 area was deleted the same day) were skipped and are listed
  in the scratch sweep log, not rewritten to a dead target. The duplicate
  `DOCREV-001` row was skipped as ambiguous.
- `89536ba8e` -- the generator half: the bridge generator emits 20 tracker-id
  strings into its output, so those were repointed in the generator and EVERY
  bridge regenerated (Rule #0: `make regen`, `--bulk bridge_batch.csv
  --generate-tests`, clean-all + run-all-func, 533 paths in one commit, blobs
  cmp-verified). Genesys bridges were confirmed comment-only by the rapids
  session before the regen was accepted.

Excluded by decision (repo-cleanup session, 2026-09-27): pumice's 173 citations.
Pumice's files are being edited from the pumice session's worktree during its
board campaign; a sweep from here would collide. Deferred, not closed, until
that sweep lands -- the condition is "pumice session sweeps its 173 from its own
worktree and reports the count".

## CLOSED 2026-09-27 -- the global mechanism is done; the unit-specific remainder is filed in the unit lanes

Sean, 2026-09-27: a tooling item is the GLOBAL mechanism and nothing else. If
part of it needs updates inside a unit, that part is an item in the unit's own
lane -- otherwise every agent says "not totally my problem" and it never lands.
Applied here:

- **pumice TASK-030** -- repoint pumice's 173 legacy citations (104 .py, 43 .md,
  26 .sv) against MIGRATION_MAP.md by `<area> <ID>`, the same method used
  everywhere else.

What this item delivered globally: `vault/Tasks/MIGRATION_MAP.md` as the one
key, the map-keyed sweep (skips bare ids and rows whose target no longer
exists), 1,199 citations in 370 files repointed (c50be80d7), and the bridge
generator's 20 emitted ids repointed with every bridge regenerated (89536ba8e).
