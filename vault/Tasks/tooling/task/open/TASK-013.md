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
