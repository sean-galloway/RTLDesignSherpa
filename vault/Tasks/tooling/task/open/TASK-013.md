# TASK-013: source comments still cite pre-migration task IDs

**Priority:** P3. Nothing is broken; the references are stale, not dangling.
**Status:** open 2026-09-27.
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

**pumice is the largest citation cluster, and it is deliberately NOT swept.**
Measured 2026-09-27: **651 `PUMICE-*` occurrences across 173 files** (.md 459, .py 151,
.sv 39, .rdl 2). None of those are the tracker's own provenance lines -- excluding
`vault/Tasks/` leaves the count unchanged at 651. The pumice session reported 533; the
measured figure is higher, and 651 is the number to plan against.

Their reasoning for leaving it here rather than sweeping it, which I agree with: the
references are in live RTL comments and board-measurement records, and rewriting those
to chase a tracker rename costs more than it gains. `MIGRATION_MAP.md` plus each file's
provenance line make an old `PUMICE-NNN` resolvable. If this is swept it should be a
deliberate mechanical pass with its own gate, not a side effect of a migration.

Note the scale relative to the rest of this ticket: pumice alone (651) dwarfs the ~143
hand-written amba and bridge citations tabled above, and `bridge`'s 157 generated ones
need a Rule #0 regeneration rather than editing. A single "sweep the citations" task is
therefore not one job -- it is at least three with different methods.

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
- [ ] Each citation above names an ID that exists, or names the area explicitly
- [ ] Other areas' citations swept the same way (only amba was measured)
- [ ] No bare-ID rewrite performed without confirming which area it meant
