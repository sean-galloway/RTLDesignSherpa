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
- APB thin crossbar (apbx_xbar_thin_wrap) is functional and tested
- Buffered/full variants may have issues
- Need comprehensive testing of all variants

**Requirements:**

1. **Verify Thin Variant (Complete)**
   - ✅ test_apbx_xbar thin variant PASSED
   - Works as baseline reference

2. **Fix/Verify Buffered Variants**
   - Test apbx_xbar with buffering enabled
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

`rtl/integ_amba/examples/apb4_peripheral_subsystem.sv` (340 lines) and
`apbx_xbar_monitored.sv` (364) do not elaborate: **51 Verilator errors**, all
PINNOTFOUND. They instantiate `apb4_monitor` with an interface it no longer has.

| the examples pass | `apb4_monitor` actually takes |
|---|---|
| `pclk`, `presetn` | `aclk`, `aresetn` |
| `psel`, `penable`, `pwrite`, `paddr`, `pwdata`, `pready`, `prdata`, `pslverr` | `cmd_valid`/`cmd_ready` + `cmd_pwrite`/`cmd_paddr`/`cmd_pwdata`/`cmd_pstrb`/`cmd_pprot`, and `rsp_valid`/`rsp_ready` + `rsp_prdata`/`rsp_pslverr` |

Both files are **unchanged since the initial commit (2025-11-01)**; `apb4_monitor`
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

- **Bridges** — `apb4_master{,_cg,_stub}`, `apb4_slave{,_cg,_cdc,_cdc_cg,_stub}`
  and the 8 `apb5_*` equivalents — carry BOTH raw APB (`s_apb_PSEL`, ARM
  uppercase) and `cmd_*`/`rsp_*`.
- **Observers** — `apb4_monitor`, `apb5_monitor`, `apb_monitor_addr_check` —
  are cmd/rsp only. That is deliberate: it makes a monitor
  protocol-version-agnostic, since APB4 and APB5 bridges hand it the same shape.
- The monitor is a **sibling, not a submodule**: no bridge instantiates it. You
  tap the bridge's handshake.

So the correct structure is to insert a bridge and tap it:

    raw APB ──> apb4_slave ──cmd/rsp──> fabric
                     └── tap cmd_*/rsp_* ──> apb4_monitor ──> monbus

`apbx_xbar_thin` is raw-APB on both sides (lowercase `s_apb_psel`/`m_apb_psel`),
which is why `apbx_xbar_monitored` has raw APB in hand and feeds it straight to a
monitor that stopped accepting it.

### Decide first, then do

1. **Retire** — delete both and the area. They demonstrate an API that is gone
   and nothing uses them. Cheapest and honest.
2. **Rewrite** against the bridge-tap structure above. Worth it only if a worked
   `apb4_monitor` integration example is wanted — there is none anywhere else in
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
here; they want their own task. *(They got one: paths mechanically repaired
2026-08-09, 5 modules spot-verified prove+cover PASS; the full re-run is
MATH-006 in vault/Tasks/math. The TOOL-012 blindspots baseline can be
lowered accordingly.)*

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
- [ ] `projects/components/retro_legacy_blocks/rtl/apbx_xbar/apbx_xbar_rlb_1to10.f`
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
`axi4_to_apb4_shim`, but they missed the USE_JOHNSON regeneration that updated
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

`docs/markdown/rtl-amba/index.md` listed four package pages -- `apb4_pkg.md`,
`axi_pkg.md`, `monitor_pkg.md`, `monitor_network_pkg.md` -- none of which have
ever existed. That section is rebuilt: it now links the four real package pages
and names the packages whose RTL exists with no page.

Still to write, if wanted:

    rtl/amba/includes/apb4_pkg.sv
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

## AMBA-MONTRACK — in-core monitor under-counts bursts when its table caps
**Status:** open 2026-08-05  **Found:** STREAM Genesys 2 monitor cosim

The in-core `axi4_master_rd_mon` does not track every burst it sees. Measured on
the STREAM harness, external observer vs in-core, same traffic, same window:

| cones compiled | table | observer | in-core | tracked |
|---|---|---|---|---|
| 1 (perf only)  | 16 | 4096 | 3513 | 86% |
| 5 (mon build)  | 16 | 4096 | 3073 | 75% |

Reproduce: `test_stream_mon_perf.py::obs_equiv` (5 cones) and the pre-migration
`test_stream_char.py::obs_equiv` with `SIM_AR_OUTSTANDING=2` (1 cone). Both fail;
this is NOT a migration regression and predates the shared harness.

**Mechanism.** A table slot frees on `event_reported`, not on RLAST
(`axi_monitor_trans_mgr`: `w_can_cleanup = event_reported` for
COMPLETE/ERROR/ORPHANED). While the table is capped, `block_ready` throttles the
upstream handshake, but commands that get through while capped are simply not
tracked -- documented as "lossy-but-honest" in [[monitor-configuration]]. More
compiled cones means more packets owed per transaction, more time capped, more
loss. Hence 86% -> 75% from cone count alone, at identical depth.

**Why it matters more than it looks.** A missed burst is a missed MATCH. On a
coverage run the symptom is a tuple that reads as "never observed" when it did
occur and the monitor was full. That is the exact wrong failure mode for a
board campaign whose goal is observing lots of matches under specific patterns
-- it produces confident false negatives.

Related and separate: `rw_perf` fails `RD AR->firstR histogram total 255 !=
burst count 256`, byte-identical on both trees. A one-burst histogram
off-by-one, independent of the loss above.

**ANSWERED 2026-08-05: depth closes it completely.**

| table | observer | in-core | tracked |
|---|---|---|---|
| 16 | 4096 | 3073 | 75% |
| **40** | 4096 | **4096** | **100%** -- `obs_equiv` PASSES |

So the loss is not inherent to the monitor: it is capping, and a table that
never caps tracks everything. Sizing is the lever for BOTH failure modes -- the
wedge (fixed by the floor of 16) and the loss (needs enough depth that the
table never fills at the sustained match rate).

**RESOLVED 2026-08-06: 40 slots is NOT affordable. Timing, not area.**

|  slots | WNS        | LUTs (325T)     | in-core tracking |
|---|---|---|---|
|  16    | **+1.018 ns** | 81393 (39.9%) | 3073/4096 (75%) |
|  40    | **-25.183 ns** | 131663 (64.6%) | 4096/4096 (100%) |

A 25 ns miss on a 10 ns period -- the path is over THREE times the clock, not a
marginal overshoot. `monitor_trans_cam` performs three combinational ID lookups
plus a free-slot priority encode across every entry, so the critical cone scales
with depth; 64.6% utilisation then adds routing congestion. Depth buys tracking
completeness and spends timing, steeply and nonlinearly.

So the board ships 16: saturation is RECOVERABLE (no more permanent wedge) but
tracking is ~75% under 5 compiled cones. Closing the completeness gap requires
one of:

1. **Pipeline the CAM lookup.** The real fix -- decouples depth from the
   combinational cone. `monbus_cam_pipe` already exists as precedent for the
   monbus CAM; the trans CAM has no pipelined variant.
2. **Fewer cones per bitstream.** Tracking loss scales with cones (86% at 1 cone
   vs 75% at 5, same depth). A coverage bitstream compiling only the classes it
   is matching would track them completely, at the cost of more bitstreams --
   the flavor split already established for error vs all-except-error.
3. **Floorplanning.** A pblock around the monitor CAMs, as was done for
   `pblock_compressor` on the stream_char timing knife-edge.

**The tension this creates.** The board runs `AR_MAX_OUTSTANDING=2` explicitly
to keep the trans_mgr CAM small enough to close timing with every cone built.
The sizing change decouples table depth from that knob, so `AR=2` + a larger
`MON_TRANS_MARGIN` can give 40 slots without touching the datapath -- but the
CAM timing arc scales with DEPTH, not with AR, so a 40-deep CAM reintroduces
exactly the pressure `AR=2` was avoiding. Completeness vs timing closure is a
real trade here and only synthesis settles it.

**Remaining open questions:**
- Should coverage builds compile only the cones being matched, trading breadth
  per bitstream for completeness within one?
- Should the monitor expose a dropped-command counter, so loss is visible
  instead of silent? Today nothing distinguishes "not observed" from "not
  tracked".

Fixed separately on 2026-08-05: the WEDGE (not the loss). Tables below 16 got
`cmd_entry_reserve()==0` and no recovery guarantee, so the first overrun hung
the monitored bus permanently -- live in the shipping monitor bitstream at
4ch x AR=2 = 12 slots. `stream_core` now sizes
`MAX(16, NUM_CHANNELS*Ax_MAX + MON_TRANS_MARGIN)`. See [[monitor-sizing]].

## AMBA-BLOCKMARGIN — block_ready margin covers 1 allocator, not 3 (root cause of the tracking loss)
**Status:** open 2026-08-08  **Supersedes the mechanism in** [[AMBA-MONTRACK]]

`block_ready` is computed from `active_count`, a REGISTERED pop-count that lags
true occupancy by one cycle (axi_monitor_trans_mgr.sv:1082, deliberately -- the
former accumulator could underflow to 0xFF). The comment says the lag is
"absorbed by block_ready's BLOCK_MARGIN". It is not, on any table >= 16:

```
BLOCK_MARGIN = (CMD_ENTRY_RESERVE > 0) ? (CMD_ENTRY_RESERVE - 1) : 3
             = 1   for MAX >= 16        (CMD_ENTRY_RESERVE = 2)
             = 3   for MAX <  16        (legacy flat margin)
```

THREE independent allocators can fire in the same cycle -- `addr_wants_alloc`,
`data_wants_alloc`, `resp_wants_alloc`, each with its own `*_alloc_oh` out of
monitor_trans_cam. One cycle of stale occupancy therefore admits up to three
allocations against a margin of one.

**The legacy margin of 3 was exactly right.** The saturation-recovery refactor
replaced it with `CMD_ENTRY_RESERVE - 1` and regressed it to 1 on precisely the
tables the reserve was added to protect.

**Why the data drop is a symptom, not the defect.** Every data beat belongs to a
command that was already accepted; if that command got a slot, its beats MATCH
and never need allocation. Unmatched data can only exist when a command was
accepted WITHOUT being allocated -- i.e. when block_ready failed to stop it. So
the observable loss (unmatched data/resp beats discarded at a full table,
because they cannot be backpressured -- a monitor must never stall returning
data) is downstream of a command that should never have been admitted.

**Measured.** val/amba/test_axi_monitor_trans_mgr.py::phase_saturation_recovers,
depth 8: after fill `active_count=8, block_ready=0`; 32 unmatched data beats
driven; `peak=8`, final 7 -- all 32 discarded. At the harness level obs_equiv
reports observer 4096 vs in-core 3073, IDENTICAL at drain 2,000 and 200,000
clocks, so it is loss and not backlog. At 40 slots the margin is still 1 but
occupancy never nears full (8 max outstanding), so nothing is lost -- the bug
only bites on genuine saturation.

**Fix candidates:**
1. `BLOCK_MARGIN = max(3, CMD_ENTRY_RESERVE - 1)` -- restores the legacy cover
   while keeping the reserve. Cheapest, and the margin then matches the number
   of allocators by construction rather than by coincidence.
2. Derive block_ready from the COMBINATIONAL `w_occupancy` instead of the
   registered `r_active_count`, removing the lag entirely. Costs the timing the
   registration was added to buy -- measure before choosing.
3. Gate `data_wants_alloc` / `resp_wants_alloc` on free slots and count the
   rejects, so loss becomes visible instead of silent (still no counter today).

Whichever is taken, add an assertion that occupancy never exceeds
`MAX_TRANSACTIONS` AND that no command is accepted without an allocation -- the
second is the invariant that actually failed here.

**Credit:** found by the user's observation that "if the cmds are stopped
correctly, there won't be data to drop", which reframed a documented
"lossy-but-honest" behaviour as a flow-control defect.

---

### TASK-060: `axi4_dma_observer` does not elaborate — `o_cmd_block` unconnected
**Priority:** P1
**Status:** 🔴 Not Started (found 2026-08-10)
**Owner:** TBD

`rtl/amba/shared/axi4_dma_observer.sv` instantiates `axi_perf_latency_hist`
twice (`u_rd_lat_hist` line ~1037, `u_wr_lat_hist` line ~1066) without
connecting its `o_cmd_block` output. Verilator treats PINMISSING as an error:

```
%Warning-PINMISSING: axi4_dma_observer.sv:1037: Cell has missing pin: 'o_cmd_block'
%Error: Exiting due to 4 warning(s)
```

**The module does not build**, so `val/amba/test_axi4_dma_observer.py` cannot
run at all — it was the single failure in a 249-test GATE sweep of the shared
area (2026-08-10). Vivado only warns on a missing pin, which is why the board
flows that instantiate this module still build and nobody noticed.

**Do not treat this as a tie-off.** `o_cmd_block`'s own port comment says it is
exported "so the command channel can be held off instead of losing the sample",
and names this exact case as where it matters most: the histogram FIFO is
`MAX_OUTSTANDING` **per channel** while the transaction table beside it blocks
at `MAX_TRANSACTIONS` **across all channels**, so one channel can be inside the
table's limit and past this one. A dropped sample is silent — no error, no flag,
and the surviving latencies are misattributed as well as undercounted.

**The pattern already exists.** `projects/components/misc/rtl/axi4_intf_observer.sv`
is this module's renamed successor and handles it correctly: `rd_hist_block` /
`wr_hist_block` nets, tied to `1'b0` in the `gen_no_hist` branch, feeding a
sticky `o_hist_sample_lost` output cleared with `i_meter_clear`. It does NOT
backpressure the observed bus — correct for an observer — it makes the loss
visible instead.

**Work:**
- [ ] Decide: mirror the successor (add `o_hist_sample_lost`), or explicitly
      discard with `.o_cmd_block ()` and accept silent sample loss.
- [ ] If the port is added, update the four instantiators —
      `axi4_intf_observer.sv`, `stream_mon_harness.sv:1853`,
      `stream_char_harness.sv:1665`, `harness_csr.sv` — or they inherit the
      same PINMISSING break.
- [ ] Re-run `val/amba/test_axi4_dma_observer.py` (currently unrunnable).

**Note:** the owner said 2026-08-10 not to change this module pending their own
look; recorded here rather than fixed.

---

### TASK-061: splitter `block_ready` duplicates transactions instead of blocking them
**Priority:** P2
**Status:** 🔴 Not Started (found 2026-08-09, doc qc round_1)
**Owner:** TBD

In `rtl/amba/shared/axi_master_rd_splitter.sv` the downstream valid is not
gated by `block_ready`, while both the upstream ready and the FSM capture are:

```systemverilog
309:  if (fub_arvalid && m_axi_arready && !block_ready)   // FSM capture: gated
394:  IDLE: m_axi_arvalid = fub_arvalid;                  // downstream valid: NOT gated
409:  fub_arready = m_axi_arready && !block_ready;        // upstream ready: gated
```

With `block_ready=1`, `fub_arvalid=1`, `m_axi_arready=1`: the slave accepts the
AR, the upstream handshake never completes, the FSM never captures — so the same
AR is re-presented and re-accepted every cycle. **Duplicated downstream
transactions, not blocked ones.** `axi_master_wr_splitter.sv` has the same
structure on AW.

**Latent, not live:** nothing in `rtl/` or `projects/` instantiates either
splitter. `pumice_wr_splitter.sv` refers to "the old shared
axi_master_wr_splitter" and replaces it. The existing tests pass because they
never assert `block_ready` — the "who would notice if this library module were
wrong?" shape from [escape-analysis](../../handbook/dv/escape-analysis.md).

**Work:**
- [ ] Gate `m_axi_arvalid` (and `m_axi_awvalid`) with `!block_ready` in IDLE,
      or document that `block_ready` must never be asserted mid-transaction.
- [ ] Add a test that asserts `block_ready` and counts downstream ARs/AWs —
      no current test does, which is why this is a doc-review find.
- [ ] Fix `docs/markdown/rtl-amba/shared/axi_master_rd_splitter.md`, which
      claims `block_ready` "prevents new transactions during error conditions".

---

### TASK-063: splitter defect cluster round 2 — BRESP consolidation, RLAST pass-through, silent split-FIFO drop
**Priority:** P2 (latent — nothing instantiates either splitter; pumice wrote its own)
**Status:** Not Started (found 2026-08-12, shared doc qc re-round)
**Owner:** TBD

Three more defects in the same two modules TASK-061 covers, found by the
fresh shared qc round and confirmed by inspection:

1. **`axi_master_wr_splitter` drops the final split's BRESP.**
   `r_consolidated_resp_status` folds each split's response in one cycle
   AFTER its B handshake, but the FINAL split's response is forwarded
   upstream in that same cycle — so `fub_bresp` reflects splits 1..N-1
   only. resp1=OKAY, resp2=SLVERR upstreams as OKAY: an error on the last
   split reads as success. (The page's own worked example describes the
   intended, correct behavior.)
2. **`axi_master_rd_splitter` passes every split's RLAST upstream**
   (`assign fub_rlast = m_axi_rlast`). An N-way split delivers N RLAST
   pulses; a generic AXI master terminates at the first one. Either
   consolidate RLAST (mirror the write side's WLAST regeneration) or
   pin the beat-counting-consumer restriction as the contract — decide,
   then make docs and RTL agree. Docs now state the restriction.
3. **Both splitters silently drop split-info records when the FIFO
   fills** — `wr_ready` unconnected, push ungated by full. Sizing is
   currently a correctness requirement; a full-FIFO stall (or at least
   a sticky overflow flag) would make it fail loud.

Round_3 additions, both verified against the source (2026-08-13):

4. **Consolidation state is not fenced per transaction.** The IDLE accept
   (`fub_awvalid && m_axi_awready && !block_ready`, line ~373) has no
   `!r_waiting_for_responses` term, and acceptance overwrites the single
   consolidation state set (`r_original_txn_id`, counts, flags). T1's final
   split AW handshakes -> IDLE with responses in flight; T2 accepted next
   cycle resets to pass-through; T1's split responses then forward raw
   upstream (3 B's for 2 AWs), or fold into T2's consolidation if T2 is
   split (T1 never answered — deadlock). `m_axi_bid` is never checked in
   consolidation mode.
5. **Leading W data defeats WLAST regeneration.** W is pure pass-through
   while `r_data_splitting` arms only when the first split AW handshakes;
   AXI4 permits W-before-AW, so early W beats carry the original wlast and
   are never counted.

Fix together with TASK-061 in one pass over the splitter pair, with a
testbench that actually asserts block_ready, drives error responses on
the last split, fills the FIFO, overlaps two split transactions'
response windows, and leads with W data — none of the current collateral
exercises any of these.

### TASK-064: converter read-path PSLVERR loss + peakrdl held-req contract
**Priority:** P2
**Status:** Not Started (found 2026-08-13, shared qc round_3; WSTRB sibling defect FIXED same day)
**Owner:** TBD

Two remaining converter-family defects (the third from this round — WSTRB
dropped, PSTRB constant all-ones from a blocking-order guard in
`axi4_to_apb4_convert` — is FIXED and regression-locked by the shim suite's
`partial_strobe_write_test`, mutation-proven RED on pre-fix RTL):

1. **`axi4_to_apb4_convert` loses PSLVERR from non-final APB slices on
   width-converted reads.** `w_resp_rd = (w_pslverr) ? 2'b10 : 2'b00` uses
   only the in-flight response; the accumulated `r_pslverr` feeds only
   `w_resp_wr`. A 2:1 read whose first slice errors returns RRESP=OKAY with
   partially-bad data. Fix needs per-AXI-beat accumulation for R (the
   burst-wide `r_pslverr` would over-mark subsequent beats).
2. **`peakrdl_to_cmdrsp` holds `regblk_req` >= 2 cycles** (IDLE accept cycle
   + WAIT_ACK) against a documented 1-cycle strobe. Whether the PeakRDL
   passthrough cpuif re-executes per held cycle needs settling against the
   generated regblock's req/ack contract; idempotent plain registers would
   mask a double-access in every current test. Decide the contract, then fix
   RTL or re-document. Docs updated to state the held behavior meanwhile.

### TASK-062: `sdpram_slave_axil_axil` runs on the board with no simulation
**Priority:** P2
**Status:** 🔴 Not Started (found 2026-08-10)
**Owner:** TBD

`rtl/amba/shared/sdpram_slave_axil_axil.sv` is instantiated on hardware —
`projects/NexysA7/stream_characterization/flows-stream-bridge/rtl/stream_char_harness.sv:1229`
(debug_sram, 64-bit AXIL write + AXIL read) plus the instrumentation filelists —
and **no test references it**.

Of the four protocol-permutation wrappers only `sdpram_slave_axi4_axi4` has a
test (`val/amba/test_sdpram_slave.py`). `sdpram_slave_axi4_axil` and
`sdpram_slave_axil_axi4` are untested too, but neither is instantiated anywhere
in the repo, so they are latent; this one is deployed.

The shared `sdpram_core` IS exercised through the axi4_axi4 wrapper, so the RAM
itself has coverage. What is unverified is the wrapper glue — the AXI4↔AXIL
handshake and width adaptation — which is exactly where a permutation wrapper
goes wrong.

**Work:**
- [ ] Test `sdpram_slave_axil_axil` at the width the board uses (64-bit).
- [ ] Decide on the other two: test them, or drop them if nothing will consume
      them ("no consumer yet" is a debt entry, not a permanent state — see
      TASK-026).
