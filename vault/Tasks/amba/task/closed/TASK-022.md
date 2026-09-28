# TASK-022: Every module MUST have a filelist and a registry entry

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-026** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** CLOSED 2026-09-16 -- re-measured; the last open item resolved
itself by the "or drop the module" branch. The entry sat on this page with a
`Not Started` status line and three-week-old numbers, which is why it read as
unfinished.
**Owner:** TBD

**The rule** (authority: `vault/handbook/design/filelists.md`): every module in
`rtl/amba/` has a filelist in `rtl/amba/filelists/`, and the area is registered
in `bin/filelists.toml`. A new module lands with its `.f` **in the same commit**
— not "before the test lands". A module with no filelist has no consumers and is
indistinguishable from dead code the next time someone audits.

**Current state, measured 2026-09-16.** `bin/filelist_registry.py --check`
reports amba at **176 modules / 176 covered / 0 uncovered / 0 broken refs**, and
every other area OK -- overall PASS. `--audit` passes too ("no filelist
hand-lists another area's sources"). Read all three numbers rather than the
PASS: amba now carries **no exemptions at all**, so covered == declared is a
real pass and not an exemption-masked one. The `[exempt]` ledger retains only
`pumice_bank_cmd_picker` / `pumice_bank_sched_core`, both set aside under
`rtl/OLD/` with a stated reason.

The five modules this entry listed as the gap are simply gone from the tree --
no `.sv`, no filelist, no reference anywhere in `rtl/` or `projects/`:

- `gaxi_fifo_async_multi` — dropped
- `gaxi_fifo_sync_multi` — dropped
- `gaxi_skid_buffer_async_multi` — dropped
- `gaxi_skid_buffer_multi` — dropped
- `gaxi_skid_buffer_multi_sigmap` — dropped

**Work:**
- [x] Resolve the five exemptions. **Done** by deletion: all five multi-instance
      wrappers were dropped rather than given consumers, which the item
      explicitly allowed. Verified 2026-09-16 -- absent repo-wide, and no
      `gaxi_*_multi` entries remain in the `[exempt]` ledger.
- [x] Wire `--check` into a gate. **Done** — `.github/workflows/filelist-checks.yml`
      runs on every push and treats `--check` and `--audit` as hard gates, with
      `--blindspots` ratcheted against `bin/blindspots_baseline.json`. (The
      original text here said nothing enforced it and the only workflow was
      `track-clones.yml`; that has not been true for some time. Corrected
      2026-08-17.)
- [x] Also wire `--audit`. Done in the same workflow.

**Why this is worth a gate — both failure modes are silent:**
- `//` is a comment, so a doubled slash in a path silently drops that source.
- Generate-gated submodules (`addr_check`, `monbus_compressor`) are invisible
  to default-parameter elaboration; they compile fine until someone flips the
  parameter.

A stray extra `-I` masks both, which is why "the build passes" is not evidence.

**Reading `--check`:** it prints `PASS` when `declared - covered - exempt` is
empty, so "147 covered" alongside "0 uncovered" on a 152-module area is
expected. Read all three numbers, not the `PASS`.

---


**CLOSED 2026-09-15 — the five exemptions are resolved by deletion (Sean:
"delete gaxi multi if they still exist", and separately: they were test
vehicles for the GAXI BFMs).**

The enforcement half was already done and is unchanged: `--check` and
`--audit` run as hard CI gates in `.github/workflows/filelist-checks.yml`,
with `--blindspots` ratcheted. What remained was the debt this entry called
"a debt entry, not a permanent state" -- five modules carried in `[exempt]`
as "no consumer yet".

Measured before deleting, not assumed: all five sat in `rtl/amba/testcode/`
with zero instantiations in `rtl/` or `projects/`, zero val tests naming
them, zero filelists referencing them, and -- despite
`formal/FORMAL_PRIORITY.md` listing all five as PASSING -- no formal harness
of any kind (no dir, no `.sby`, no `.sv` under `formal/`). That false status
was corrected in the same series.

Deleted: the five `.sv`, the `[exempt]` block, five rows from the gaxi README
mapping table, and two orphaned TBs (`gaxi_buffer_multi.py` 875 lines and
`gaxi_buffer_multi_sigmap.py` 912 lines), whose only "importer" was
`bin/cocotbframework_tree.txt`, a file listing.

**Verification, and the telling part.** `rtl/amba` lint after the deletion:
**PASS, 402 modules, exit 0** -- 183 files, down from 188. The module count
did NOT change, because `rtl/make/area.mk` lints the flattened master
filelist rather than a `find`, and these five were in no filelist. They were
never linted at all. That is precisely the invisibility this entry describes:
"a module with no filelist has no consumers and is indistinguishable from
dead code the next time someone audits."

**Two consequences left for their owners, deliberately not actioned here:**
* the GAXI BFM's signal-map path now has no DUT. `signal_map`/`sigmap`
  appears in exactly one live val test (`test_axi4_master_rd_mon.py`); the
  field-config path is still well covered (`test_gaxi_fifo_sync.py` and 12
  others via `FieldConfig`). If that BFM feature is still wanted, it needs a
  new vehicle.
* `docs/markdown/TestTutorial/gaxi_multi_field_integration.md` (724 lines)
  and `gaxi_field_configuration.md` (777 lines) teach multi-field GAXI using
  the deleted modules as worked examples, and `gaxi_buffer_field.py`,
  `gaxi_buffer_seq.py` and `gaxi_buffer_configs.py` are now a closed orphan
  set. Retiring ~1500 lines of tutorial is a bigger call than the instruction
  covered.

---
