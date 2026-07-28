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

## AMBA-INTEG-EXAMPLES — the two rtl/integ_amba examples are nine months dead
**Status:** open 2026-07-26
**Priority:** P2 (nothing depends on them, but `make verilator` at rtl/ is RED)

`rtl/integ_amba/examples/apb_peripheral_subsystem.sv` (340 lines) and
`apb_xbar_monitored.sv` (364) do not elaborate: **51 Verilator errors**, all
PINNOTFOUND. They instantiate `apb_monitor` with an interface it no longer has.

| the examples pass | `apb_monitor` actually takes |
|---|---|
| `pclk`, `presetn` | `aclk`, `aresetn` |
| `psel`, `penable`, `pwrite`, `paddr`, `pwdata`, `pready`, `prdata`, `pslverr` | `cmd_valid`/`cmd_ready` + `cmd_pwrite`/`cmd_paddr`/`cmd_pwdata`/`cmd_pstrb`/`cmd_pprot`, and `rsp_valid`/`rsp_ready` + `rsp_prdata`/`rsp_pslverr` |

Both files are **unchanged since the initial commit (2025-11-01)**; `apb_monitor`
was redesigned underneath them. They are its ONLY consumers anywhere in the tree
— no test, no project, no doc references either file.

### Why nobody noticed for nine months

`rtl/integ_amba` had modules but no filelists, no registration and no Makefile,
so it was invisible to `--check` (unregistered) **and** to `--blindspots` (the
orphan scan looks for `.f` files no area covers, and an area with no `.f` at all
has nothing to find). A module can hide by having too little, not just by being
wrong. Registering it (`0c822bd5`) is what surfaced this.

### The shape of the fix

The APB family splits cleanly, and the examples are on the wrong side of it:

- **Bridges** — `apb_master{,_cg,_stub}`, `apb_slave{,_cg,_cdc,_cdc_cg,_stub}`
  and the 8 `apb5_*` equivalents — carry BOTH raw APB (`s_apb_PSEL`, ARM
  uppercase) and `cmd_*`/`rsp_*`.
- **Observers** — `apb_monitor`, `apb5_monitor`, `apb_monitor_addr_check` —
  are cmd/rsp only. That is deliberate: it makes a monitor
  protocol-version-agnostic, since APB4 and APB5 bridges hand it the same shape.
- The monitor is a **sibling, not a submodule**: no bridge instantiates it. You
  tap the bridge's handshake.

So the correct structure is to insert a bridge and tap it:

    raw APB ──> apb_slave ──cmd/rsp──> fabric
                     └── tap cmd_*/rsp_* ──> apb_monitor ──> monbus

`apb_xbar_thin` is raw-APB on both sides (lowercase `s_apb_psel`/`m_apb_psel`),
which is why `apb_xbar_monitored` has raw APB in hand and feeds it straight to a
monitor that stopped accepting it.

### Decide first, then do

1. **Retire** — delete both and the area. They demonstrate an API that is gone
   and nothing uses them. Cheapest and honest.
2. **Rewrite** against the bridge-tap structure above. Worth it only if a worked
   `apb_monitor` integration example is wanted — there is none anywhere else in
   the repo today, which is arguably the entire point of `rtl/integ_amba`.

If rewriting: lint-clean is the floor, and add a smoke test under
`val/integ_amba/` taking its sources from
`rtl/integ_amba/filelists/<module>.f`. Without a test they rot again exactly as
they did — nine months, undetected, because nothing ever compiled them.

**Do not just delete the area registration to make the sweep green.** The
registration is what found this; reverting it re-hides the problem.

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

---

### TASK-027: Split the address-range checker into independent DEBUG and ERROR range sets
**Priority:** P3
**Status:** 🔴 Not Started
**Owner:** TBD

**Context — what shipped first.** `axi_monitor_addr_check` was reworked from a
single-polarity violation checker into an ALLOWLIST checker with two report
paths off **one shared** range set (`cfg_addr_range_low/high/enable`,
`N_ADDR_RANGES`):
- MATCH (addr in a range), gated by `cfg_debug_enable` → `PktTypeAddrMatch (8)` /
  `AXI_ADDR_RANGE_MATCH (0x01)`.
- MISS  (addr in NO range), gated by `cfg_error_enable` → `PktTypeError (0)` /
  `AXI_ERR_ADDR_RANGE (0x0D)`.

Landed + verified: cocotb `test_axi_monitor_addr_check.py` and formal
`formal/amba/axi_monitor_addr_check/` (prove + cover PASS). Wired
`cfg_debug_enable`/`cfg_error_enable` into the `addr_check` instance in
`axi_monitor_base`. **Still tied off** in `dma_slave_monitors.sv` and the STREAM
in-core monitors (`stream_core.sv`, `scheduler_group_array.sv`) — see the
`cfg_addr_*` `1'b0` ties there.

**The evolution requested.** One shared range set couples the two paths (debug
watches exactly the addresses whose *absence* raises an error). Decouple them
into **two independent range sets** so the debug allowlist and the error
allowlist can differ:
- **Debug/match ranges** — their own params + cfg ports; a hit in a DEBUG range
  emits the `AddrMatch` packet.
- **Error ranges** — their own params + cfg ports; an address matching NONE of
  the ERROR ranges emits the `Error`/`ADDR_RANGE` packet.

**Where the params live (per the request): at the monitor core AND the AXI\*
wrapper module level** — threaded the same way `N_ADDR_RANGES` already is, so a
top consumer sets them on `axi4_slave_rd_mon` / `axi4_slave_wr_mon` /
`axi4_master_*_mon` and they flow down through `axi_monitor_filtered` →
`axi_monitor_base` → `axi_monitor_addr_check`.

**Work:**
- [ ] `axi_monitor_addr_check.sv`: replace the single range set with
      `N_DEBUG_ADDR_RANGES` / `N_ERROR_ADDR_RANGES` params + separate
      `cfg_debug_addr_range_{low,high,enable}` and
      `cfg_error_addr_range_{low,high,enable}`. MATCH decision uses the debug
      set; MISS decision uses the error set. Keep the master
      `cfg_addr_check_enable` and the `cfg_debug_enable`/`cfg_error_enable`
      path gates.
- [ ] Thread the two param groups + cfg ports through `axi_monitor_base` →
      `axi_monitor_filtered` → the `axi4_*_mon` wrappers (module-level params
      with sane defaults, e.g. debug set = match-all, error set = match-all so
      the default emits no error).
- [ ] Add **default range values as module params** at the AXI\* wrapper level
      so a consumer can set the allowlists purely by param.
- [ ] Update `val/amba/test_axi_monitor_addr_check.py` for the two range sets
      (drive debug vs error ranges independently; assert a debug-only hit, an
      error-only miss, and an address that is in the debug set but also a valid
      error address).
- [ ] Update `formal/amba/axi_monitor_addr_check/` (anyconst two range sets;
      MATCH membership vs the debug set, MISS non-membership vs the error set).
- [ ] Integration: expose the two range param groups on `dma_slave_monitors.sv`
      and enable them in the STREAM monitor-validation harness; retire the
      `cfg_addr_*` `1'b0` ties in `dma_slave_monitors.sv` /
      `stream_core.sv` / `scheduler_group_array.sv`.

**Related:** TASK-015 (address-range + ID *filtering* to cut traffic) — different
goal (drop mask) but same comparator neighborhood; fold in if done together.

---

---

## BRIDGE-MON-STRESS — three _mon monitor stress tests fail on a memory-bounds read
**Status:** open 2026-07-28 (found by Claude while regenerating bridges for USE_JOHNSON)
**Priority:** P2

`test_bridge_mix_b_mon_monitor`, `test_bridge_mix_c_mon_monitor` and
`test_bridge_mix_d_mon_monitor` fail. The other 28 bridge tests pass.

```
Memory read failed at 0x00000FFC: Read at address 0xFFC with size 8
exceeds memory bounds (size: 4096)
```

A 4096-byte model read at offset 0xFFC with size 8 runs 4 bytes past the end.
Either the stimulus should not generate an 8-byte access at that offset, or the
memory model needs to be sized/masked to tolerate it. The failure is in the
testbench memory model, not in the RTL: no `_mon` variant differs from its
passing non-`mon` sibling in anything that touches addressing.

### Why this surfaced now, and why it is NOT a regression

These three were never being collected. `projects/components/bridge/dv/tests/`
tests do `from monitor_stress_common import ...` — a sibling module — and the
directory was not on `sys.path`, so all six `_mon` tests died at import with
`ModuleNotFoundError` when pytest ran from the repo root. That is fixed (the
directory is now inserted in the area's own `conftest.py`), which is what made
these three visible.

They are unrelated to the USE_JOHNSON regeneration that uncovered them: the
generated adapters gained exactly one line, `.USE_JOHNSON(0)`, which passes the
value `gaxi_fifo_async` was already defaulting to. The generated RTL is
semantically identical.

### Before starting

- Run from inside `projects/components/bridge/dv/tests/`, or rely on the
  conftest fix. Confirm all 31 collect.
- ~66 min for the full bridge suite; the three failures each take ~3 min alone.

---

## BRIDGE-NEXYSA7-REGEN — the five NexysA7 char-framework bridges cannot be regenerated in place
**Status:** open 2026-07-28 (found by Claude during the USE_JOHNSON sweep)
**Priority:** P3

Five generated bridges under the board-characterization frameworks are stale
with respect to the bridge generator:

    projects/NexysA7/ddr2-characterization/ddr2_char_framework/rtl/bridges/generated/bridge_ddr2_char_axil
    projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/generated/bridge_stream_char_axil
    .../bridge_stream_char_axil_mon
    .../bridge_stream_mon_axil
    .../bridge_stream_mon_axil_mon

They carry `Generated by: SlaveAdapterGenerator` and instantiate
`axi4_to_apb_shim`, but they missed the USE_JOHNSON regeneration that updated
the 13 adapters under `projects/components/bridge/rtl/generated/`. Harmless
today -- the shim's `USE_JOHNSON` defaults to 0, which is what the FIFO used
before the parameter existed, so the elaborated hardware is identical. It is a
consistency gap, not a functional one.

### Why it is not a one-liner

**The generator cannot write to the directory it reads from.** Each of these
dirs holds its own `<name>.toml` and `<name>_connectivity.csv` NEXT TO the
generated output. `_emit_bridge_variant` clears/copies into the output dir, so
invoking

    bridge_generator.py --ports <dir>/<name>.toml \
                        --connectivity <dir>/<name>_connectivity.csv \
                        --name <name> --output-dir <parent>

deletes the toml and csv partway through and then dies on
`FileNotFoundError ... <name>.toml` in `shutil.copy2`. All five fail the same
way, leaving a half-regenerated tree. (Tried on 2026-07-28; restored with
`git checkout -- projects/NexysA7/`, which recovers cleanly because the configs
are tracked.)

`projects/components/bridge/` avoids this because `bin/bridge_batch.csv` keeps
configs in `bin/test_configs/` and writes to `../rtl/generated` -- separate
trees.

### The fix

Move each config out of its output dir (a `configs/` sibling, mirroring the
components layout), then add these five to a batch CSV so `make regen` covers
them. Do NOT hand-edit the adapters to add `.USE_JOHNSON(0)` -- that is the
partial-regeneration anti-pattern CRITICAL RULE #0 exists to prevent.

These are board flows; verify on hardware or in the flow's own sim before
trusting the regenerated output.

---

## AMBA-MONITOR-PKG-PAGES — five packages have RTL but no doc page
**Status:** open 2026-07-28 (found while reorganizing rtl/amba/monitor)
**Priority:** P3

`docs/markdown/rtl-amba/index.md` listed four package pages -- `apb_pkg.md`,
`axi_pkg.md`, `monitor_pkg.md`, `monitor_network_pkg.md` -- none of which have
ever existed. That section is rebuilt: it now links the four real package pages
and names the packages whose RTL exists with no page.

Still to write, if wanted:

    rtl/amba/includes/apb_pkg.sv
    rtl/amba/includes/apb5_pkg.sv
    rtl/amba/includes/axi_pkg.sv
    rtl/amba/includes/monitor_pkg.sv
    rtl/amba/includes/monitor_common_pkg.sv

`monitor_network_pkg` has NO RTL either -- it is a phantom. Do not write it.

### Resolved: the whitepaper references, and the replacement

**A new architecture document now exists:**
`docs/markdown/rtl-amba/monitor/monitor_system_architecture.md` -- written
2026-07-28 at Sean's request. It covers the overarching architecture and
capabilities: the 128-bit packet as the single currency, the four-stage
detect/shape/filter/transport pipeline, error/debug/perf packet production for
protocols AND for custom blocks (the arbiters are the worked example, with a
step-by-step for instrumenting your own block via PROTOCOL_CORE), the three
capture strategies compared (bulk trace / compressed trace via monbus_compressor
/ on-chip counting via monbus_pkt_tally), and the perfmon window buckets. Every
number in it was checked against the RTL.

It is NOT a restoration of the deleted whitepaper -- see below.

Four pages (`monitor_amba4_pkg.md`, `monitor_amba5_pkg.md`,
`monitor_arbiter_pkg.md`, `monitor_package_spec.md`) linked
`../monitor_system_whitepaper.md`. That file was **deliberately deleted** on
2026-07-18 in `ca8e12cd`: *"Remove the dated MonitorSystem whitepaper
(superseded by the full monitor docs + the forthcoming RTL library PDFs)."*
The `.md`, a `.docx`, a `.pdf`, its style yaml and its generator script all went
with it.

So the links were leftovers from an intentional removal, not a page waiting to
be written. They are gone; the four pages no longer promise it. **Nothing to
restore -- do not re-add the whitepaper.** If a design-surface view (identity
allocation, timestamp policy, drain paths, aggregation topology) turns out to be
missing from the per-module docs, it belongs in `monitor_package_spec.md`, which
is what superseded it.

---

## CDC-FORMAL-STALE — the 4-phase handshake formal proof runs against a pre-rename DUT copy
**Status:** open 2026-07-28 (found by kimi round 10, verified)
**Priority:** P2

`formal/cdc/cdc_handshake/` proves `formal_cdc_handshake.sv`, which compiles
`cdc_handshake_formal.sv` -- a Yosys-compatible copy of the DUT. That copy was
taken before the module became `cdc_4_phase_handshake` and gained parameters:

| | parameters |
|---|---|
| `cdc_handshake_formal.sv` (proved) | `DATA_WIDTH` |
| `rtl/cdc/cdc_4_phase_handshake.sv` (live) | `DATA_WIDTH`, `SYNC_STAGES`, `TIMEOUT_CYCLES`, `FAST_PATH` |

So the proof says nothing about the timeout path (`TIMEOUT_CYCLES > 0` asserting
`src_timeout`) or the fast path (`FAST_PATH=1`, dst accepting when `dst_ready`
is already high) -- the two most recent additions, and the two most likely to
carry a protocol bug.

The doc now scopes its claim
(`docs/markdown/rtl-cdc/cdc.md`, "Verification status"), so nothing currently
overclaims. The work is:

1. Refresh `cdc_handshake_formal.sv` from the live module (it exists because
   Yosys cannot take the `reset_defs.svh` macros -- keep that transformation,
   change nothing else).
2. Extend `formal_cdc_handshake.sv` with properties for the two new parameters.
3. Re-run and confirm the existing properties still pass.

Note the harness is ALSO single-clock/single-reset by construction, which is a
separate and already-documented limitation -- it cannot express the asymmetric
reset hazard. Fixing that is a bigger job and is not this task.

Not a false alarm about the filename: the reviewer flagged
`formal_cdc_handshake.sv` vs `cdc_handshake_formal.sv` as a possible
transposition. Both files exist and both names are correct --
`formal_cdc_handshake.sv` is the harness (`cdc_handshake.sby` has
`prep -top formal_cdc_handshake`) and `cdc_handshake_formal.sv` is the DUT copy.
Confusing, but not wrong.
