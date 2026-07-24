<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# AMBA tasks — open (not started)

### TASK-026: Every module MUST have a filelist and a registry entry
**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

**The rule** (authority: `vault/handbook/design/filelists.md`): every module in
`rtl/amba/` has a filelist in `rtl/amba/filelists/`, and the area is registered
in `bin/filelists.toml`. A new module lands with its `.f` **in the same commit**
— not "before the test lands". A module with no filelist has no consumers and is
indistinguishable from dead code the next time someone audits.

**Current state is good but unenforced.** `bin/filelist_registry.py --check`
reports amba at 152 modules / 147 covered / 0 uncovered. The 5-module gap is the
`[exempt]` ledger, not a hole:

- `gaxi_fifo_async_multi` — multi-instance wrapper; no consumer yet
- `gaxi_fifo_sync_multi` — multi-instance wrapper; no consumer yet
- `gaxi_skid_buffer_async_multi` — multi-instance wrapper; no consumer yet
- `gaxi_skid_buffer_multi` — multi-instance wrapper; no consumer yet
- `gaxi_skid_buffer_multi_sigmap` — multi-instance wrapper; no consumer yet

**Work:**
- [ ] Resolve the five exemptions: give each a filelist and a consumer, or drop
      the module. "No consumer yet" is a debt entry, not a permanent state.
- [ ] Wire `--check` into a gate. **Nothing runs it today** — not the
      pre-commit hook, not CI (the only workflow is `track-clones.yml`), not a
      Makefile target. A MUST that nothing enforces is a wish. Shared with
      COMMON-010; do the gate once for both areas.
- [ ] Also wire `--audit` (consumers hand-listing `rtl/common` / `rtl/amba`
      sources). amba is the area most likely to be hand-listed by a consumer,
      so the audit matters more here than anywhere else.

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

### TASK-014: Performance Characterization
**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

**Description:**
Characterize resource utilization and performance impact of monitors.

**Metrics to Collect:**
- [ ] Area (LUT, FF, BRAM) per monitor type
- [ ] Timing impact (critical path analysis)
- [ ] Power consumption (if measurable)
- [ ] Comparison: AXI4 vs AXIL vs APB vs AXIS
- [ ] Comparison: With vs without clock gating

**Deliverable:**
- [ ] Performance characterization report
- [ ] Recommendations for resource-constrained designs
- [ ] Optimization opportunities identified

---

### TASK-015: Add Address Range and ID Filtering
**Priority:** P3
**Status:** 🔴 Not Started
**Owner:** TBD

**Description:**
Add optional filtering capabilities to reduce monitor packet traffic.

**Features:**
- [ ] Address range filtering (monitor only specific regions)
- [ ] Transaction ID filtering (monitor only specific masters)
- [ ] Configurable filter enable/disable
- [ ] Runtime filter updates

**Use Case:**
- Reduce packet congestion in high-traffic systems
- Focus monitoring on specific subsystems
- Debug-specific master/slave combinations

---

### TASK-022: Make APB Crossbar Variants Functional
**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD
**Effort:** Medium (2-3 days)
**Dependencies:** None (APB thin crossbar already works)

**Objective:** Get all APB crossbar variants working and tested

**Background:**
- APB thin crossbar (apb_xbar_thin_wrap) is functional and tested
- Buffered/full variants may have issues
- Need comprehensive testing of all variants

**Requirements:**

1. **Verify Thin Variant (Complete)**
   - ✅ test_apb_xbar thin variant PASSED
   - Works as baseline reference

2. **Fix/Verify Buffered Variants**
   - Test apb_xbar with buffering enabled
   - Identify and fix any issues
   - Verify backpressure handling

3. **Full Feature Testing**
   - Multiple masters × multiple slaves
   - Concurrent transactions
   - Address decoding
   - Error responses

4. **Documentation**
   - Document working variants
   - Configuration guidelines
   - Performance characteristics

**Deliverables:**
- [ ] All APB crossbar variants functional
- [ ] Comprehensive test coverage
- [ ] Configuration guide for variant selection
- [ ] Integration examples updated

**Success Criteria:**
- All APB crossbar tests passing
- Documented working configurations
- Clear guidance on variant selection

---

### TASK-024: Write Monitor System Whitepaper
**Priority:** P3
**Status:** 🔴 Not Started (stub created 2026-05-29)
**Owner:** Sean (author) / Claude (assist)
**Deliverable:** `docs/markdown/RTLAmba/monitor_system_whitepaper.md`
> Note (2026-07-22): the 2026-05-29 stub is not present in the current tree; recreate it when this task starts.

**Description:**
2-3 page whitepaper that frames the monitor system as a *design surface*
for SoC integrators -- not a status snapshot of what is in place, but a
guide to which knobs the integrator owns and how to spend them. Different
from `docs/markdown/RTLAmba/overview.md` (which describes the as-built
implementation) and from the per-module specs under `shared/` (which
describe specific blocks). This paper sits one level up: "here is the
spine, here are the axes, here are the tweaks."

**Section outline** (stub already in place):

1. **Identity space allocation** -- UNIT_ID / AGENT_ID / CHANNEL_ID as
   designer-owned. Includes the worked example of allocating UNIT_ID one
   level down so each unit gets up to 16 internal sub-busses to track.
2. **Where to insert monitoring** -- per-port (current default), mid-fabric
   (for localizing fabric-internal violations), root-of-tree (aggregate
   only, trades resolution for area).
3. **Timestamp policy** -- current locked to the monbus_group family's local
   counter. Future direction: hybrid `{global_us[47:0], local_cyc[15:0]}`
   so cross-subsystem correlation and per-wrapper resolution share the
   same 64-bit field. Also a note on PTP / external time-source variant.
4. **Drain path selection** -- err FIFO (IRQ) vs. write FIFO (bulk
   trace), per-packet-type routing via `cfg_*_err_select`.
5. **Packet-type filtering** -- masking strategy, the
   completion+performance congestion pitfall, runtime-reconfigurable
   masks via control APB.
6. **Aggregation topology** -- tree-of-arbiters default, WRR variant for
   skewed traffic, protocol-partitioned groups.

**Out of scope** for the whitepaper (covered elsewhere):
- Packet bit-layout (in `docs/markdown/RTLAmba/includes/monitor_package_spec.md`)
- Per-module port lists / timing (in `docs/markdown/RTLAmba/monitor/{module}.md`)
- Specific test recipes (in the relevant test source).

**Completion checklist** (already mirrored at the bottom of the stub):
- [ ] Pull representative deployment numbers from stream_char on
      Nexys A7 (perf-section figures).
- [ ] One block diagram per section showing as-built vs. tweaked
      configurations side-by-side.
- [ ] Cross-link each section to its per-module spec under `shared/`.
- [ ] Expand the timestamp section into an appendix once the
      hybrid-global scheme is prototyped.
- [ ] Add a verification section pointing at the slave-BFM error-
      injection pattern (`test_bridge_1x2_rd_monitor_error_inject.py`)
      as the template for validating tweaks in simulation.

---


---

## AMBA-CDC-REORG — pull CDC out of amba into a top-level rtl/cdc area
**Status:** open 2026-07-24 — planned, BLOCKED on the running common Kimi review
**Priority:** P1 (Sean)

Sean, 2026-07-24. Create a first-class `rtl/cdc/` area and consolidate the
clock-domain-crossing modules there, out of `rtl/amba/` and `rtl/common/`.

**Modules to move into `rtl/cdc/`:**
- from `rtl/amba/cdc/`: `cdc_2_phase_handshake`, `cdc_4_phase_handshake`,
  `cdc_open_loop`, `cdc_synchronizer`
- from `rtl/common/`: `fifo_async` (the async FIFO)
- from `rtl/amba/gaxi/`: `gaxi_fifo_async`, `gaxi_skid_buffer_async`
- from `rtl/common/` -- the gray/johnson code-conversion modules, so all the
  CDC-adjacent encoding lives in one place for reference (Sean, 2026-07-24):
  `bin2gray`, `gray2bin`, `johnson2bin`, `counter_bingray`, `counter_johnson`

**Everything that must follow the RTL move:**
- [ ] `val/cdc/` must exist (Sean) — move the corresponding tests out of
      `val/common` (fifo_async) and `val/amba` (cdc_*, gaxi async) into it.
- [ ] `docs/markdown/RTLCdc/` book — the moved modules' doc pages leave
      RTLCommon/RTLAmba; add `_book_cdc_index.md`, `index.md`, `overview.md`.
- [ ] **Filelists live with the RTL:** `rtl/cdc/filelists/` (the existing
      convention -- the owning area's `filelists/` dir; `bin/filelists.toml` is
      the REGISTRY/index, not the storage location). Add the cdc area to the
      toml. See [[filelists]] and the AMBA-FILELIST-CONSISTENCY task.
- [ ] Repoint every consumer: `apb5_slave_cdc` instantiates `gaxi_fifo_async`
      and `cdc_synchronizer`; formal harnesses; includes; `-f` includes across
      amba/common/stream.
- [ ] Kimi generates a per-section `overview.md` and the rtl area LINKS to it
      (directive A) -- see the open question below on how, given rtl READMEs
      were just deleted.

**Resolved (Sean, 2026-07-24):**
- **Shared FIFO code stays in common.** Anything used by BOTH the sync and
  async FIFOs / gaxi-fifos -- `fifo_control.sv` and friends -- remains in
  `rtl/common`; `rtl/cdc` depends on `rtl/common` for it. Do not split or
  duplicate it. Only the async-specific modules move.
- **Sequencing confirmed:** do the move AFTER the common Kimi review comes back
  and is integrated. Not before.

**Open design questions -- resolve before moving:**
1. **"Overview linked in the rtl areas" vs "no README in rtl".** We just
   deleted all rtl READMEs. If each section's Kimi `overview.md` must be linked
   FROM the rtl area, what carries the link -- the area `CLAUDE.md`, or a
   single one-line pointer file that is explicitly not a README? Confirm.
3. Does `gaxi_skid_buffer_async` belong in cdc (it is a skid buffer, async
   variant) or stay in gaxi? Confirm the exact gaxi split.

**SEQUENCING (hard):** do NOT start while the common Kimi review runs --
`fifo_async` is in that bundle (part_02) and moving it mid-review invalidates
the result. This is the exact multitask trap Sean flagged. Order: finish the
common review + integrate it, THEN do this reorg as one focused operation,
THEN re-review the new cdc section (DOCREV-009).

---

## AMBA-CLEANUP — move the last misplaced docs out of rtl/amba
**Status:** open 2026-07-24
**Priority:** P2

After the README/PRD purge (commit f7ca848a), two non-`CLAUDE.md`,
non-`known_issues` markdown files remain in the amba RTL tree -- both are
reader-facing/methodology docs that [[doc-placement]] says do not belong there:

- [ ] `rtl/amba/axi4/AXI4_DATA_WIDTH_CONVERTER_SPEC.md` -- a module spec.
      Reader-facing product doc -> `docs/markdown/RTLAmba/` (fold into the
      converter's page or add as its own). Repoint any code-header/doc refs.
- [ ] `rtl/amba/VERIFICATION_ARCHITECTURE.md` -- verification architecture /
      methodology. Method -> `vault/handbook/dv/` if it is practice, or
      `docs/markdown/RTLAmba/` if it is a reader-facing architecture overview.
      Decide which by reading it; repoint refs.

After this, `rtl/amba` should hold only `.sv`, `CLAUDE.md`, and
`known_issues/` bug records -- the same clean shape `rtl/common` now has.
Verify with `find rtl/amba -name '*.md' | grep -v CLAUDE | grep -v known_issues`
returning nothing.

---

## AMBA-FILELIST-CONSISTENCY — normalize where .f lists live
**Status:** open 2026-07-24 — **the RTL-area filelists are already consistent; the actual stragglers are all under projects/ and moved to TOOL-010.** This entry is kept only to record that rtl/amba, rtl/common, rtl/math are clean.
**Priority:** P3

The convention (see [[filelists]]) is: a module's `.f` lives in the owning
area's **`filelists/` dir**, and `bin/filelists.toml` REGISTERS it (the toml is
an index, not storage). Most of the 366 `.f` follow this
(`rtl/amba/filelists/` 118, `rtl/common/filelists/` 56, `rtl/math/filelists/`
38). Sean, 2026-07-24: right now placement is inconsistent. The stragglers:

**Naming -- not called `filelists/`:**
- [ ] `projects/NexysA7/rapids_characterization/flows-rapids-beats/flists/`
      (3 files) -> `filelists/`
- [ ] `projects/components/bridge/rtl/filelists_static/` -> fold into
      `filelists/` (or justify why "static" is a distinct dir)

**Loose `.f` directly beside RTL, no `filelists/` subdir:**
- [ ] `projects/components/retro_legacy_blocks/rtl/rlb_top/rlb_top.f`
- [ ] `projects/components/retro_legacy_blocks/rtl/apb_xbar/apb_xbar_rlb_1to10.f`
- [ ] `projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/ddr2_char_macro.f`

**TB/harness `.f` -- RESOLVED (Sean, 2026-07-24):** a testbench with its own
harness gets its own filelist, co-located WITH the TB (its `filelists/` dir),
not with the RTL. So `*_tb_top.f` under `dv/` are correctly placed in principle;
they just need the same `filelists/`-dir naming. `val/amba/filelists/
monbus_arbiter_grant_hold_dut.f` is a TB list and stays with its TB.

**SCOPE / SEQUENCING (Sean, 2026-07-24):** the RTL-area filelists are ALREADY
consistent -- `rtl/amba/`, `rtl/common/`, `rtl/math/` all use `filelists/`. Every
straggler above is under `projects/` (or a project's `val/`). **Projects are
deferred until the RTL area is complete.** So this task does not start now; it
waits behind the RTL-area work (cdc reorg, amba cleanup). Re-check with
`bin/filelist_registry.py --check` when it runs.
