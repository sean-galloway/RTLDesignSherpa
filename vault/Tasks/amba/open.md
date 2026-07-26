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
**Deliverable:** `docs/markdown/rtl-amba/monitor_system_whitepaper.md`
> Note (2026-07-22): the 2026-05-29 stub is not present in the current tree; recreate it when this task starts.

**Description:**
2-3 page whitepaper that frames the monitor system as a *design surface*
for SoC integrators -- not a status snapshot of what is in place, but a
guide to which knobs the integrator owns and how to spend them. Different
from `docs/markdown/rtl-amba/overview.md` (which describes the as-built
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
- Packet bit-layout (in `docs/markdown/rtl-amba/includes/monitor_package_spec.md`)
- Per-module port lists / timing (in `docs/markdown/rtl-amba/monitor/{module}.md`)
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
**Status:** ✅ DONE 2026-07-25 — every checklist item worked and verified.
Move this block to closed.md.

**Completed 2026-07-25** (commits `dc922a54`, `cd2a2dc3`, `8b2de284`):

- [x] `bin/filelists.toml`: `cdc` area registered. `--check` reports cdc 12
      modules / 12 covered / 0 uncovered, no exemptions needed.
- [x] `.f` for `gaxi_skid_buffer_async` created (it was the one module of twelve
      without one).
- [x] `bin/filelist_registry.py --check` PASS **and `--audit` PASS**. Registering
      the area exposed 27 cross-area hand-listed sources — all pre-existing but
      invisible, since they were intra-area before the move. All 27 converted to
      `-f` includes. Verified behaviour-preserving: `fifo_async.f` resolves to
      the same 14 sources in the same order.
- [x] Moved-module tests run: `val/cdc` 62 passed after `clean-all`;
      `val/amba/test_apb5_slave_cdc` 3 passed; `test_gaxi_buffer_async` 12 passed.
- [x] `val/cdc/` exists — 11 tests git-moved from val/common (7) and val/amba (4),
      plus a four-line Makefile and a conftest that DERIVES its area name rather
      than typing it.
- [x] `docs/markdown/rtl-cdc/` — 8 module pages + cdc.md moved in, with `index.md`,
      `overview.md` and `_book_cdc_index.md`. Casing settled on **rtl-cdc**; the
      empty lowercase `RTLcdc/` is gone. 14 referring pages repathed, 0 broken
      links to any moved page.
- [x] `formal/` — 10 harnesses moved to `formal/cdc/`, 13 files repathed.
- [x] Kimi findings referencing old paths: handled during the round_2 integration
      (the bundle was rebuilt post-move, so `common_meta` flagged the relocation
      itself rather than producing stale-path findings).

**Two things this surfaced that were NOT part of the move:**

1. `test_fifo_async_wavedrom` hand-listed eight `rtl/common` source paths instead
   of taking a filelist, so it had been broken since `c0daf18a` — the one test
   the original path rewrite missed, unnoticed because val/common's suite had not
   been run since. Now takes `rtl/cdc/filelists/fifo_async.f`.
2. The four `apb*_slave_cdc` formal harnesses referenced `cdc_handshake.sv`,
   which exists nowhere and which neither slave instantiates — and they were
   also missing `gaxi_fifo_async` and its whole dependency tree, which the
   slaves DO instantiate. **Fixed 2026-07-25 (`6eab2377`):** each harness's
   `[script]`/`[files]` are now GENERATED from the area's audited filelist, so
   they cannot drift from the closure the cocotb tests compile. 14/17/17/21
   sources, up from 3/4/4/5; all 77 refs resolve and each set elaborates under
   Verilator. The proofs themselves are still unrun — `sby`/`yosys` are not
   installed on this box.

3. Two more stranded tests, same defect as (1): `test_counter_bingray_wavedrom`
   and `test_counter_johnson_wavedrom` sat in val/common hand-listing
   `rtl/common/<dut>.sv`, broken since the move. Confirmed RED, moved to
   val/cdc, put on their filelists. They were missed initially because the move
   swept tests referencing a cdc FILELIST; these referenced a PATH.

**Not blocking, noted:** 387 unresolvable source refs remain in `formal/common/`
`.sby` files, all `math_*` fallout from the earlier arithmetic split. Untouched
here; they want their own task.

---

## AMBA-CLEANUP — move the last misplaced docs out of rtl/amba
**Status:** open 2026-07-24
**Priority:** P2

After the README/PRD purge (commit f7ca848a), two non-`CLAUDE.md`,
non-`known_issues` markdown files remain in the amba RTL tree -- both are
reader-facing/methodology docs that [[doc-placement]] says do not belong there:

- [ ] `rtl/amba/axi4/AXI4_DATA_WIDTH_CONVERTER_SPEC.md` -- a module spec.
      Reader-facing product doc -> `docs/markdown/rtl-amba/` (fold into the
      converter's page or add as its own). Repoint any code-header/doc refs.
- [ ] `rtl/amba/VERIFICATION_ARCHITECTURE.md` -- verification architecture /
      methodology. Method -> `vault/handbook/dv/` if it is practice, or
      `docs/markdown/rtl-amba/` if it is a reader-facing architecture overview.
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
