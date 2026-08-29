<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# AMBA tasks — open (not started)

## AMBA-MONRATE-INTERMITTENT — axi_monitor completion-RATE thresholds fail ~3/run under -n24
**Status:** open 2026-08-28 — NOT root-caused. Filed for a fresh agent.
**Priority:** P2 — blocks reading val/amba as a clean signal, so every shared
DV-framework change has to be A/B'd instead of just run.
**Related — READ BOTH FIRST, this is a THIRD distinct cause in the same
family, and both known ones are already ruled out below:**
* [[VAL-XDIST-INTERMITTENT]] (this page) — concurrent deletion of the shared
  `val/amba/local_sim_build` root. Signature is
  `FileNotFoundError: RTL source not found`.
* AMBA-WAVEDROM-FLAKY (closed.md) — runners drawing a random per-run seed.

### Symptom

Full `val/amba` at `-n 24` reports a small, non-empty failure set that is
NOT STABLE between runs. Observed across four full runs:

| run | result | failing |
|---|---|---|
| 1 (seed unpinned) | 1 failed / 742 passed | `test_axi_monitor_trans_mgr_wr_bank[64-4-1]` |
| 2 (seed unpinned) | 1 failed / 742 passed | `test_axi4_monitor[8-64-16-True-True-combined]` |
| 3 (SEED=1234) | 3 failed / 740 passed | `test_axi4_monitor[8-64-16-True-True-combined]`, `test_axi_mon_block_ready[axi4_master_wr_mon-12]`, +1 |
| 4 (SEED=1234) | 3 failed / 740 passed | `test_axi4_monitor[4-64-8-True-True-addr64]`, `test_axi_mon_block_ready[axi4_master_wr_mon-12]`, +1 |

The assertion is a STATISTICAL THRESHOLD, not a functional check:

    ❌ FAIL: Got 16 completions (16.0%), expected >= 20 (20%)

`test_axi_mon_block_ready[axi4_master_wr_mon-12]` was stable across runs 3
and 4; the `test_axi4_monitor` parameter MOVED. So at least part of the set
is genuinely nondeterministic and part may be a real always-failing test
that only shows up at `-n 24` — separating those two is step one.

### Already ruled out — do not re-check these

* **Random seed.** `val/amba/test_axi4_monitor.py:547` does
  `'SEED': os.environ.get('SEED', str(random.randint(0, 100000)))`, so the
  AMBA-WAVEDROM-FLAKY pattern is present and was the obvious suspect.
  Pinning `SEED=1234` did NOT stabilise it: runs 3 and 4 above used the
  same pinned seed and still disagreed on which parameter failed.
* **sim_build collisions.** Names are fully unique — they carry both the
  xdist worker id and every parameter, e.g.
  `test_gw11_axi_monitor_combined_iw8_aw64_mt16_axi4_rd` and
  `test_{worker_id}_axi_monitor_trans_mgr_wr_bank_mt{N}_nb{N}_wq{N}`.
* **Concurrent deletion of `local_sim_build`** (the VAL-XDIST-INTERMITTENT
  cause). Nothing deleted the build root during these runs, and the
  signature is different — a threshold assertion, not `FileNotFoundError`.
* **A shared-framework change.** These runs were the A/B for a GAXISlave
  change (RDS-DV c220c19/aacb90d) that is provably inert here: nothing in
  `val/` or `bin/TBClasses/` passes its `ready_policy` kwarg. Runs 3 and 4
  are exactly that A/B — same counts with and without it.
* **Serial execution.** `test_axi_monitor_trans_mgr_wr_bank` passes 5/5
  serially from a clean build (367s wall, genuinely simulated), both with
  and without the framework change. Only `-n 24` shows the failures.

### Leads worth chasing

1. **Resource pressure tripping a safety monitor.** The monitor TBs log
   `Safety limits: {'max_test_duration_minutes': 30, 'max_memory_mb': 2048,
   'progress_timeout_minutes': 5, 'max_cpu_percent': 95,
   'enable_safety_monitoring': True, ...}`. At 24 workers CPU is pinned and
   memory is contended, so a duration/progress/CPU guard aborting a run
   would look exactly like a completion shortfall. Check whether an abort
   path reduces the completion count rather than failing loudly, and sweep
   `-n` (24 / 12 / 8 / 4) to see if the failure rate tracks worker count.
2. **The threshold itself.** ">= 20% completions" with an observed 16% may
   simply be too tight for a congested monitor — CLAUDE.md documents AXI
   Monitor packet congestion, and warns never to enable `cfg_compl_enable`
   and `cfg_perf_enable` together. Check what the failing configs enable.
3. **Is the count a rate or a race?** 16 vs 20 completions is a small
   absolute number; confirm whether the test drains completions for a fixed
   wall/sim window that a loaded machine can shorten.

### Definition of done

Either a mechanism + fix that makes `val/amba -n 24` reproducibly clean, or
a documented reason each affected test cannot be deterministic at that
width plus a concrete guard (pinned seed, widened bound with rationale,
serial marker, or reduced default `-n`). Silently loosening the threshold
to make it pass is NOT acceptable — the point of the assertion is to catch
monitor congestion regressions.

Reproduce with:

    source env_python
    SEED=1234 python3 -m pytest val/amba/ -q --tb=short -n 24


## VAL-XDIST-INTERMITTENT — ROOT-CAUSED 2026-08-28: concurrent deletion of local_sim_build
**Status:** root cause PROVEN; remaining item is the durable fix below
**Related:** AMBA-WAVEDROM-FLAKY (closed same day) -- same *family*
(nondeterministic val/amba result), DIFFERENT cause. That one was a random
per-run seed; this one is not seed-related at all.

CAUSE: `val/amba/local_sim_build/` is a single shared build root, and
deleting from it while a run is in flight destroys that run's build.

REPRODUCED ON THE FIRST ATTEMPT. Start the parallel set; 3 seconds in, run
`rm -rf val/amba/local_sim_build/*monbus_axil4_axil4*`:

    1 failed, 17 passed
    FAILED val/amba/test_monbus_axil4_axil4_group_compressed
    raise FileNotFoundError(f"RTL source not found: {src}")
    make: *** [.../Vtop___024root__DepSet_...o] Error 1

Same test and same `FileNotFoundError: RTL source not found` signature as
the 12-failure occurrence earlier that day.

NOT THE CAUSE -- each ruled out by experiment, recorded so nobody re-checks:
  * seed nondeterminism. The compressed suite DOES draw a random seed
    (`SEED: random.randint(...)`, exactly the AMBA-WAVEDROM-FLAKY pattern),
    which made it the obvious suspect -- but a sweep of eight seeds
    (1/42/1234/99999/7/4347/55555/31337) passes 8/8. Worth pinning for
    reproducibility; it is not this bug.
  * sim_build name collision between xdist workers. Both implicated tests
    embed PYTEST_XDIST_WORKER in their build directory name.
  * parallelism itself. Forty consecutive `-n 12` runs, each preceded by a
    clean `rm -rf`, all passed.
  * source mutation during a run. Touching the RTL mid-run changes nothing;
    Verilator has already built.

HOW THE THREE OCCURRENCES FIT:
  1, 2 -- I had overlapping `rm -rf` globs and background pytest jobs in
    flight (two killed with TaskStop mid-run). Directly matches the repro.
  3 -- my own command was sequential (`rm -rf; pytest`), so the deleter was
    NOT mine. This is a SHARED WORKTREE with concurrent sessions and the
    build root has no per-session scoping, so another session running or
    cleaning val/amba collides with mine.

DURABLE FIX, DONE (was "not taken" here until 2026-08-28 -- the note went
stale, and the stale note is how this nearly got re-solved):
`bin/TBClasses/shared/utilities.py` no longer hardcodes the build root.

  * `sim_build_root(tests_dir)` honours `SIM_BUILD_ROOT`. Unset keeps the
    historical `<tests_dir>/local_sim_build`, so nobody is broken by
    default; when set, the per-AREA structure is preserved beneath it
    (`<root>/<area>/local_sim_build`) rather than flattened -- flattening
    would trade a cross-session collision for a cross-area one, since
    build-dir names are only unique within an area.
  * `sim_build_path(tests_dir, name)` creates the dir and writes a
    `.sim_busy` marker naming session, pid and start time.
  * `sim_build_is_busy(path)` reads that marker, so a cleaner can tell
    "another session is building here RIGHT NOW" from "leftover from a run
    that ended" -- the distinction whose absence caused occurrences 1-3.

WHAT REMAINS is adoption, and it is not automatic:

  * Nothing sets `SIM_BUILD_ROOT`, so every session still lands in the
    shared root by default. Markers written today read `session=shared`.
    Defaulting it in `env_python` was considered and REJECTED: any
    per-invocation key (`$$`) gives each shell a fresh root, so every run
    recompiles from scratch -- test_stream_perf.py measures ~220 s cold vs
    ~35 s warm, ~185 s of duplicate compile per case. The shared root is
    correct for model reuse. Set `SIM_BUILD_ROOT` deliberately when two
    agents must be fully isolated and the recompile is worth paying for.
  * The markers are advisory. Nothing consults `sim_build_is_busy()` yet,
    so a blunt `rm -rf` still ignores them.

INTERIM DISCIPLINE, free: never `rm -rf` a broad `local_sim_build/*` glob
while anything might be running -- including another session -- and scope
cleanups to the exact build directory the run will use.

That discipline was violated repeatedly on 2026-08-28 by an agent running
the stream cosims: every run was launched as `rm -rf .../local_sim_build;
make sim`, unconditionally, ignoring the markers. Which is the argument
for not relying on discipline at all -- cleanup belongs in the make
target, where it is written once and can consult the markers, rather than
in whatever ad-hoc shell command each caller types. See CLEANUP-IN-MAKE.

DONE 2026-08-28, the other half of the problem: TBBase now LOGS THE SEED
for every TB. Most val/ runners default SEED to `random.randint(...)` --
correct for a stress runner -- but the seed appeared nowhere, so a failure
under a random seed could not be replayed: rerunning drew a NEW seed, the
test passed, and a real bug read as flaky. That is precisely how these
intermittents kept getting rerun away. One line in TBBase covers every
TB-derived testbench; the log now carries
`SEED=<n> (reproduce with: SEED=<n> pytest <test>)`, verified by replaying
a logged seed and getting the same value back.

The first version of that log line ALSO claimed a missing SEED meant "NOT
reproducible", which was wrong -- most TBs default it themselves
(axi_monitor_tb uses 42), so those runs are repeatable, just not
steerable. Corrected: an alarming-but-inaccurate warning is one people
learn to scroll past.

## TASK-026: Every module MUST have a filelist and a registry entry
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
**Dependencies:** None

**Objective:** Get all APB crossbar variants working and tested

**Background (STALE — see note):** written when `apbx_xbar_thin` was the
only proven variant. As of 2026-08-27 all five generated variants
(1to1/2to1/1to4/2to4/2to2_mixed) pass 8/8 and lint clean, and thin has
been deleted. **This task looks complete; it needs closing or rescoping
rather than doing.**

**Requirements:**

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

## AMBA-INTEG-EXAMPLES — CLOSED 2026-08-27: resolved by deletion, plus the residue it left
**Status:** CLOSED (option 1, "Retire", taken -- see the decision list in the
original text below)

The RTL was deleted in `01d1c3e6` ("removed old integ_* code that was used for
bfm development"), which took BOTH `rtl/integ_amba/` and `rtl/integ_common/`.
Sean asked whether it was already gone; it was -- but the deletion left residue
in four places, and no tooling flagged any of it (deletion 2026-08-19, found 2026-08-27):

  * `bin/filelists.toml` still declared both areas, pointing at directories
    that no longer existed;
  * `docs/markdown/rtl-integ-amba/` and `rtl-integ-common/` -- two whole doc
    books, 11 pages total, documenting deleted modules;
  * `docs/markdown/index.md` linked both books in two places, one of them
    still saying "2 modules -- currently not building, see
    AMBA-INTEG-EXAMPLES";
  * `docs/DOCUMENTATION_INDEX.md` listed integration examples as repo
    structure item 3.
  The review pipeline was still bundling both books, so a future qc round
  would have spent units reviewing docs for code that does not exist.

ROOT CAUSE, and the reason this is worth reading: `filelist_registry.py
--check` PASSED the whole time. `rglob("*.sv")` on a missing directory yields
nothing, so a dead area reports "[OK] 0 modules, 0 uncovered" and passes
forever. That is the SAME blind-spot class this registry was built to close,
one level up -- the original task said "a module can hide by having too little,
not just by being wrong"; it turns out an AREA can hide by not existing.
Fixed: --check now fails on an rtl_root that is not a directory, mutation-
verified with an injected ghost area (FAIL, exit 1) and the clean tree still
PASS.

Original analysis kept below for the record.

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

`apbx_xbar_thin` was raw-APB on both sides (lowercase
`s_apb_psel`/`m_apb_psel`), which is why `apbx_xbar_monitored` had raw APB in
hand and fed it straight to a monitor that stopped accepting it.

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

## AMBA-MONTRACK — CLOSED 2026-08-26 (root cause was [[AMBA-BLOCKMARGIN]], fixed + measured)
**Status:** CLOSED  **Found:** STREAM Genesys 2 monitor cosim

CLOSURE: the loss mechanism was never capping per se -- it was commands
ADMITTED against stale occupancy with no free slot (the BLOCKMARGIN
margin-of-1 defect), whose un-backpressureable data beats were then
discarded. With cmd_entry_reserve=4 (margin 3, all three same-cycle
allocators covered; landed 16e4c18b, verified 2026-08-26):
  * unit level: test_axi_mon_block_ready asserts NO untracked
    admissions on every wrapper (31/31 with trans_mgr suite);
  * harness level: obs_equiv PASSES on today's tree -- in-core RD
    prod=8192 = observer 8192, WR 8192 = 8192, all three histogram
    totals match (rd firstR 511, rd RLAST 511, wr AW->B 512).
The remaining open questions dissolve: a dropped-command counter is
unnecessary when no command can be admitted untracked (block_ready now
throttles honestly -- loss became flow control); the fewer-cones-per-
bitstream idea is moot for completeness (still valid as a congestion
knob, see monitor-configuration). The pipelined trans-CAM idea remains
a real FUTURE scalability lever (depth >16 at 100 MHz) but is a feature,
not a defect -- not tracked here. Original analysis kept below.

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

## AMBA-BLOCKMARGIN — CLOSED 2026-08-26 (fix landed 2026-08-20 in 16e4c18b; verified + reconciled today)
**Status:** CLOSED  **Supersedes the mechanism in** [[AMBA-MONTRACK]]

CLOSURE: cmd_entry_reserve() returns 4 on tables >= 16 since 16e4c18b
(2026-08-20), which makes the derived BLOCK_MARGIN exactly 3 -- covering
all three allocators in the stale cycle while keeping the recovery
contract (margin <= reserve-1). Verified 2026-08-26 on clean rebuilds:
test_axi_monitor_trans_mgr + test_axi_mon_block_ready 31/31, which
enforce BOTH requested invariants (assert_no_untracked_admissions -- no
command admitted without an allocation -- and peak_occupancy <= depth);
formal ap_cmd_entry_cap proves the command cap. The stale
axi_monitor_base.sv comment block that still described reserve=2 as
current and the fix as "left as is" (written before 16e4c18b, never
reconciled) is rewritten to the post-fix truth -- that comment was the
last place the pre-fix narrative survived, and the monitors doc book
would have been re-corrupted from it. Cost accepted: 4 reserved slots
per table >= 16 (12 usable command slots at depth 16, 60 at 64).

Original analysis kept below for the record.

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

**FIX CANDIDATE 1 IS WRONG — MEASURED 2026-08-17.**

`BLOCK_MARGIN = max(3, CMD_ENTRY_RESERVE - 1)` was implemented and it BREAKS
saturation recovery. The margin must satisfy two constraints simultaneously:

  (a) >= 3, to cover the three allocators that can fire in the one stale cycle
  (b) <= CMD_ENTRY_RESERVE - 1, or `block_ready` can never RE-ASSERT

With `CMD_ENTRY_RESERVE = 2` on tables >= 16 these are unsatisfiable. At
margin 3 on a 16-slot table `block_ready` needs `active_count < 13`, while the
reserve only guarantees 2 free slots -- so occupancy parks at 14 and the gate
never recovers. `test_axi_monitor_trans_mgr` catches it directly:

    block_ready never re-asserted after traffic stopped
    (active_count stuck at 14/16) -- peak=16 block_ready=0

That is the permanent wedge the reserve was added to prevent, which is a worse
failure than the tracking loss it was meant to fix. Reverted; the reasoning is
now recorded in `axi_monitor_base.sv` beside the localparam so the next person
does not re-try it.

**THE ACTUAL FIX: raise `CMD_ENTRY_RESERVE` to 4** (in `monitor_common_pkg`),
so both constraints can hold at margin 3. That costs 4 slots of capacity per
table rather than 2 and touches every wrapper's effective depth, so it wants
sizing review alongside -- it is not a one-liner, and this task should stop
describing it as one.

**Fix candidates (original):**
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

### TASK-070: mon_cg monbus_valid held through gating -- FIXED 2026-08-26, residual CLOSED same day
**Priority:** was P2 -- CONFIRMED then fixed; residual documented below

CONFIRMED by directed test before the fix: park a completion packet
(monbus_ready low), idle into gating, raise ready -- the ungated consumer
accepted the SAME packet 30 times in 30 cycles off the frozen valid, at
both idle counts. Fix (all 12 wrappers: axi4 + axi5 + axil4): (1)
w_monbus_valid ORed into user_valid -- a pending packet is outstanding
work, holds the block awake and re-wakes it within a cycle; (2) external
monbus_valid masked with !cg_gating -- covers the knife-edge where gating
asserts on the same edge the packet arrives (1-cycle wake), so a consumer
can never sample a valid the reporter's stopped clock could not retire.
The mask only defers valid's rise, never truncates a visible valid,
because once w_monbus_valid is high gating cannot engage.

Directed test = val/amba/test_mon_cg_gating.py phase 6 (park, watch
gating, release, record packet VALUES -- a count cannot tell one packet
re-delivered N times from N distinct packets draining). 24/24 gating +
36/36 functional green after clean rebuild.

RESIDUAL CLOSED (same day, after the monitor-stack dive): no port
export was needed. The wrappers already receive the CAM occupancy as
active_transactions (filtered's active_count), and CAM entries stay
valid until their packet is marked into the reporter FIFO -- the
registered count then lags one cycle further, meeting monbus_valid's
assertion. ORing (|active_transactions) into user_valid therefore covers
the entire retire -> FIFO -> output emission window with an existing
port. Phase 6 tightened to assert len(delivered) == 1 (was <= 3, which
tolerated the stranded phase-5 packet surfacing in phase 6's drain);
tightened test RED against the wrapper-only fix (2 deliveries: the
0x8000 stranded packet + the 0xA000 phase packet), GREEN after the
occupancy term: gating 24/24, functional 36/36, clean rebuilds. One
sequencing subtlety: w_monbus_valid alone is NOT redundant with the
occupancy term -- the threshold/perf/debug bypass packets never come
from CAM entries, so both terms are needed. w_output_busy export NOT
needed; nothing further owed here. Docs updated to the closed contract
(no idle-count advisory).

## AMBA-COMPTP — CLOSED 2026-08-27: SKID_DEPTH 2 -> 3 recovers 1 record/cycle
**Status:** CLOSED (measured 0.670 -> 1.000; one localparam)
**Priority:** was P3

FIX: `localparam int SKID_DEPTH = 2` -> `3` in monbus_compressor.sv. That
one line feeds both the credit guard and the skid instance, so nothing
else changed. r_credit is [2:0] and w_skid_count is [3:0] (headroom), and
gaxi_skid_buffer takes 2..8 inclusive, so 3 is legal -- see
[[skid-depth-contract]].

WHY 3 EXACTLY: the credit round trip is 3 cycles -- present at T, CAM
result T+1, REGISTERED skid rd_valid and pop T+2, credit visible again
T+3 -- so N credits sustain N/3 records/cycle. Depth 2 predicts 0.667 and
phase 4 measured 0.670 (134/200); depth 3 predicts and measured exactly
1.000 (200/200). Depth 4 would buy nothing: the input handshake caps at 1.

WHY THE CREDIT CEILING COULD NOT BE RAISED ALONE (the constraint that
made this a skid change rather than a guard change): monbus_cam_pipe has
NO result_ready -- results are autonomous -- and skid_wr_ready is
connected but never consulted. The credit guard is therefore the only
thing guaranteeing a landing slot for every in-flight result. More
credits than skid entries = a result arriving at a full skid, silently
dropped.

COST: one skid entry, P_W = 382 bits (hit + idx + old_data + delta_ts +
event_data + src_ts60 + packet).

TIMING: deepening the skid does NOT reopen the 65-bit format-C path the
skid exists to break -- it adds an entry, it does not shorten a cone.
Regression 61/61 clean. A synthesis run on the target part is still the
honest confirmation for a design that fought for 100 MHz once; flagged
rather than claimed.

The phase-4 assertion is now a LOWER bound only (>= 0.98). 1.0 is the
handshake ceiling, so nothing can legitimately exceed it and any drop is
a regression -- the two-sided bound had done its job by firing here.

CLOSED TOO (2026-08-28): the credit invariant is now asserted.
test_monbus_compressor.py phase 0 checks `pipe_res_valid |-> skid_wr_ready`
every cycle -- a CAM result presented while the skid is full is a silently
dropped record, and skid_wr_ready is connected but never consulted.

An in-RTL `ifdef FORMAL` property was the obvious home and would have been
DECORATION: there is no formal proof for the compressor, so it would never
run. The check lives in the testbench, where monbus_compressor is the
toplevel so its internals are reachable, and it fails loudly rather than
skipping if they are not.

Two things it took to make the check real, both worth remembering:
  * IT RUNS FIRST. Breaking the invariant desyncs the slot stream, so the
    golden comparison already caught it -- as a four-minute
    SimTimeoutError with nothing pointing at the cause. Ordered before
    phase 1, it names the cause in seconds.
  * IT NEEDED CONSUMER BACK-PRESSURE. The first version drove with
    out_ready high, so the skid drained as fast as it filled, the credit
    never neared its ceiling, and it reported violations=0 against a
    DELIBERATELY BROKEN guard -- stimulus that could not expose the bug.
    Stalling the consumer backs the skid up. Mutation-verified after the
    fix: ceiling raised above SKID_DEPTH gives peak credit 5 and 2
    result-at-full-skid violations; the good RTL gives peak 3 and 0.

The compressor's Tier-1 input rate is **0.67 records/cycle**, not the
1 record/cycle both the RTL header and monbus_compressor.md claimed.
Measured, not argued: val/amba/test_monbus_compressor.py phase 4 holds
in_valid high across a long same-template run and counts input
handshakes -- 134 in 200 cycles, stable.

MECHANISM. The CAM result path is credit-gated at SKID_DEPTH=2 while the
credit round trip is ~2 cycles: present at T -> CAM result T+1 ->
gaxi_skid_buffer rd_valid is REGISTERED so it appears T+2 -> pop T+2 ->
credit decrement visible T+3. Two credits against a 2-cycle round trip
stalls the input one cycle in three.

WHY NOT JUST FIXED. Recovering 1/cycle needs either >=3 credits or a
fall-through result interface, and that skid is exactly what keeps the
65-bit format-C ed_delta path off the stage-1 commit path -- which was
the 100 MHz critical path this design already fought once. Trading it
back for a third more throughput is a timing decision that wants a
synthesis run, not a one-line parameter bump.

DONE MEANWHILE: both texts now state the measured 2/3, and phase 4
asserts 0.60 <= rate <= 0.72 so the claim and the hardware cannot drift
apart again. The UPPER bound is deliberate -- if a future change
improves the credit round trip, the test fires and says to re-measure
and update all three places together.

### TASK-062: CLOSED 2026-08-28 -- stale as filed; the real gap was inside sdpram_core
**Status:** CLOSED

AS FILED, stale. Tests for all three untested wrappers landed 2026-08-13,
three days after the task was written (2026-08-10). Measured, not assumed:
all four permutations build and pass (12 cases), and the shared suite in
sdpram_slave_mixed_tb is substantive -- single beat, write burst, read
burst, random fill, bulk clear, plus a valid/ready monitor.

THE REAL GAP, found while checking Sean's "all sdpram modules should have
tests": sdpram_core has FIVE modules' worth of coverage but a parameter
that selects between TWO WRITE IMPLEMENTATIONS, and only one was ever
built.

  * `USE_WSTRB=1` -> `g_wstrb`, the byte-enable loop (infers distributed
    RAM);
  * `USE_WSTRB=0` -> `g_fullword`, the single full-word write that
    block-RAM inference wants, which IGNORES fub_wstrb by construction.

Only sdpram_slave_axil_axil even exposes the parameter; the other three
wrappers take the default. So `g_fullword` had never been elaborated, let
alone simulated -- and separately, NO test had ever driven a partial write
strobe, so the byte-enable behaviour the parameter exists for was
unproven in BOTH modes.

Fixed: a phase_partial_strobe in the shared TB that asserts each branch's
real contract (merge under USE_WSTRB=1, whole-word overwrite under 0), and
a USE_WSTRB=0 row on the axil_axil test. Mutation-verified by forcing both
configs down the byte-enable path: only the ws0 row fails, with the
specific message. All 12 cases green.

TWO TEST BUGS OF MINE, caught before commit and worth recording:
  * the sim_build tag omitted the new axis, so the ws0 and ws1 rows at the
    same dw/depth/level would have SHARED A BUILD DIR -- the second run
    reusing the first build and reporting a pass for RTL it never
    simulated;
  * the phase was VACUOUS at DATA_WIDTH=256. Fixed 64-bit constants masked
    into a 256-bit word leave the upper bytes zero in both the seed and the
    new value, so the masked-off region was identical either way and the
    check could not tell honoured strobes from ignored ones. Caught by
    reading the LOGGED VALUES, not the pass/fail -- every dw256 row was
    green and proving nothing. Patterns now fill the width, and an explicit
    guard fails the phase if seed and new ever agree outside the strobed
    bytes.

NOT taken: exposing USE_WSTRB on the other three wrappers. That is an RTL
API change, and the core's both branches are now covered through
axil_axil. Raise it if a caller needs block-RAM inference on an AXI4
write side.
### TASK-065: SPLIT axi4_intf_observer into master + slave versions; retire the original and dma_slave_monitors
**Priority:** P1
**Status:** 🔴 Not Started
**Owner:** TBD

**GOAL — say it first, because it sets every sizing decision:** exercise ALL
FOUR axi4 monitor flavours in the **stream `build-mon` configuration**:

    axi4_master_rd_mon   axi4_master_wr_mon
    axi4_slave_rd_mon    axi4_slave_wr_mon

The monitors are the DUT here, not instrumentation. That has consequences:

- In `build-mon` the taps must be **ON** (`ENABLE_MON_TAPS=1`) — a monitor with
  its taps off is not under test. Which means the table MUST be sized so
  `block_ready` never drops, because with taps on the wrapper's gate is live
  and a saturated table corrupts the bus (see the 49->367 replay below). The
  ID slice / `NUM_BANKS` work exists to make that sizing closeable.
- In `build-perf` the taps stay **OFF**: no instrumentation in the datapath,
  no gate, nothing to saturate.
- Success = all four modules driven under heavy traffic with monbus/tally
  evidence per flavour, not merely "the build runs".

**Mechanism:** `axi4_intf_observer` (ex-`axi4_dma_observer`) is SPLIT INTO TWO
MODULES — a master version and a slave version. **The original goes away**;
this is a replacement, not a second instance added alongside it. Two observers
because one role cannot exercise the other role's monitors.

- master version — wraps `axi4_master_rd_mon` / `axi4_master_wr_mon`, hangs off
  the STREAM ports. (This is what today's `axi4_intf_observer` already does
  internally, so it is the closer descendant of the original.)
- slave version — wraps `axi4_slave_rd_mon` / `axi4_slave_wr_mon`, hangs off
  the DMA slaves.
- When both exist, DELETE `axi4_intf_observer` and repoint `u_dma_observer` in
  `stream_harness.sv` at the master version. No module keeps the old name: a
  block that instantiates master monitors must not be reachable under a name
  that reads as role-neutral, which is how the slave side ended up hand-rolled
  as `dma_slave_monitors` in the first place.
- **Parallel snoop**, not series pass-through. Each observer carries its own
  AXIL monbus group feeding its **own** tally module.
- A monitor OBSERVES. It must never drive the datapath handshake.

**Step 0 — the hang fix, independent of the rest.** Retire
`dma_slave_monitors` and instantiate `axi4_dma_slaves` raw in
`stream_harness.sv` (`u_dma_slaves`). That alone restores the 8-channel perf
build.

**Why (measured, from the ch3 wedge in build-perf):**
`dma_slave_monitors` (commit `ee07c71a`, 2026-08-09 — inside the regression
bracket: `f22fafb9` passes 8ch, HEAD hangs) splices slave monitors INLINE on
the DMA-slave bus with a single un-sliced `MAX_TRANSACTIONS(16)` table, while
STREAM runs 8 channels x 8 outstanding = 64 concurrent. The table saturates,
`w_block_ready` drops (first at 6977.92 us), and
`axi4_slave_rd_mon.sv:491` masks only the OUTWARD `s_axi_arready` while the
core underneath still sees the ungated `s_axi_arvalid` and accepts. STREAM,
never having seen a handshake, holds the same AR on the bus and the core
accepts it again — every cycle.

Counted at both ends over 0..7030 us:

| tap | AR handshakes, id 3 |
|---|---|
| `harness.f_rd_ar` (what STREAM sees) | 49 |
| `u_rd_pattern_gen.fub_axi_ar` (what the slave sees) | 367 |

Each replay is a well-formed 16-beat burst (15.97 beats/AR), so every
per-transaction property passed. What broke was CONSERVATION, which nothing
was watching. Nothing in `build-perf` even reads these monitors, and
`slvmon_regs.rdl` defaults `MON_EN=1`, so they came up enabled and unread.

**Enabling work already landed (uncommitted at time of writing):**
- ID-filter restore, 15 files — `1e6b1d9d` had removed the per-tap ID slice
  (`ID_FILTER_ENABLE` / `ID_MATCH_BASE` / `ID_MATCH_COUNT`); restored
  byte-identical to `1e6b1d9d^`. 4 taps x 2 channels verified via
  `test_axi_mon_id_slice[0,2,4,6]`.
- `USE_WDATA_ORDER_Q` (`axi_monitor_trans_mgr.sv`, default 0) — AW-order queue
  replacing the WID-less O(N^2) oldest-select. Push slot on AW handshake, pop
  on W-last. 9 passed off, 9 passed on.
- `NUM_BANKS` (default 1) — same-bank guards on `pick_oldest` and the rank
  update (elaboration constants, so cross-bank comparators are never built),
  per-bank survivor counts, plus `addr/data/resp_alloc_mask` on
  `monitor_trans_cam` so an ID can only allocate inside its own bank.
- Both parameters plumbed wrapper -> `axi_monitor_filtered` -> `axi_monitor_base`
  -> `trans_mgr` across all 12 wrappers.

**Open work:**
- [ ] Step 0 above (fixes the hang on its own).
- [x] **DONE 2026-08-14.** Split into `axi4_intf_master_observer.sv` (taps
      `axi4_master_{rd,wr}_mon`) and `axi4_intf_slave_observer.sv` (taps
      `axi4_slave_{rd,wr}_mon`), both in `projects/components/misc/rtl/`.
      Naming is the owner's: `axi4_intf_<role>_observer`, not
      `axi4_intf_observer_<role>`.

      **They are OBSERVERS: every AXI4 port is an INPUT** (46 of them, zero
      outputs on the observed bus), including both halves of each handshake so
      a beat is recognisable from the wire alone. The only outputs are the
      AXIL monbus egress, the APB config slave, and status. This settles the
      "parallel snoop vs taps ON" contradiction in this task's own text: the
      observers no longer sit in the path at all.

      `stream_harness.sv` rewired accordingly — what used to run
      `rd_* -> u_dma_observer -> f_rd_*` is now a direct assign, with the
      observer watching those wires. The instrument can no longer gate the
      DMA. Both observers lint clean; the rewired harness elaborates with 0
      errors.

      Filelists created for both, and they now pull their own tap closure
      (`axi4_<role>_{rd,wr}_mon.f` + `axi_perf_latency_hist.f`) — the old
      filelist did not, so it could not stand alone and lint needed the taps
      added by hand.
- [x] **DONE 2026-08-14.** DELETED `axi4_intf_observer.sv` + its filelist, and
      repointed every caller: `stream_harness.sv` (instantiation + 3 comments),
      `harness_csr.sv` (2), `stream_harness.f`, `monbus_group.f`,
      `dma_slave_monitors.f`, both NexysA7 harness filelists, the host/DV
      Python (`obs_addrs.py`, `host_bus_meters.py`, `host_reg_walk.py`,
      `test_stream_mon{,_perf}.py`, `val/amba/test_axi_mon_block_ready.py`),
      `build-perf/Makefile`, five `docs/markdown/rtl-amba` pages, and the
      pumice / rapids task pages. `grep axi4_intf_observer` over `*.sv`/`*.f`
      returns nothing; the only surviving mentions are this task page's own
      historical record.
- [ ] **Egress mismatch — THIS IS THE BLOCKER for instantiating the slave
      observer (confirmed against the harness 2026-08-16).** `stream_harness`
      wires the slave monbus path as `m_axil_*` (AXIL write master -> bridge
      master `slave_monbus_wr` -> `u_slave_tally`), which is what
      `dma_slave_monitors` provides via `monbus_axil4_axil4_group`. Both new
      observers inherit `monbus_axil4_axi4_group` from the original, so they
      expose `m_axi_*` (AXI4 burst master) instead. The slave observer cannot
      take `u_dma_slaves`' place until the group is parameter-selected:
      declare both port sets and generate-select so the port list is stable.

      **The rest of that swap is mapped and mechanical.** Replace
      `dma_slave_monitors u_dma_slaves` (harness ~1692-1775) with
      `axi4_dma_slaves`, carrying the same `s_axi_*` / CRC / beat-count /
      busy connections, and add the slave observer snooping the SAME
      `f_rd_*` / `f_wr_*` nets. Those are the nets the MASTER observer
      already snoops -- one bus, both roles, which is exactly what exercises
      all four monitor flavours. Non-AXI ports to carry over from the old
      instance: `cam_clear` (csr_cam_clear), `s_apb_*` (slvmon_apb_*),
      `s_axil_*` (se_*), `m_axil_*` (slmon_*), `irq_out`,
      `cfg_base_addr`/`cfg_limit_addr` (0x000C0000 / 0x000FFFFF).
- [ ] **Generate the CAM NUM_BANKS times** (generate loop of
      `monitor_trans_cam`, depth MAX_TRANSACTIONS/NUM_BANKS each) so each
      instance closes timing. Currently only the age/rank logic is banked;
      one full-depth CAM is still instantiated. See the GAP note above.
- [ ] Then synthesise to confirm convergence at N=64/B=4 (16 per CAM), and
      run that config against observer traffic.
- [ ] `stream_harness.sv:1956` currently passes `NUM_RD_PORTS(1)`/
      `NUM_WR_PORTS(1)` with `ENABLE_MON_TAPS=0`; confirm against the intended
      4x2 topology.

**WHY 4x — TIMING, not capacity.** The observers are instantiated with params
set so the **CAM is GENERATED 4 TIMES**. Each generated CAM is then small
enough to close timing (16 entries measured at WNS +1.018 ns; a single table at
40 entries is -25.183 ns and will not close, 72 never). The 4x is a timing
measure that happens to also give enough slots; do not describe it as sizing.

**CAM replication: DONE.** `monitor_trans_cam` is now instantiated inside a
`generate` loop, NUM_BANKS times, each of depth MAX_TRANSACTIONS/NUM_BANKS
(`g_cam_bank` in `axi_monitor_trans_mgr.sv`). Per-bank one-hots are stitched
back into the flat N-wide vectors, so everything downstream is unchanged, and
allocation is confined by construction (`*_wants_alloc` gated on
`bank_of(id) == gb`). At NUM_BANKS=1 it is a single CAM of depth N -- the
original design. Verified: NUM_BANKS=1 passes (3 passed), lint clean.

The age/rank logic (`pick_oldest` + the rank update, the two O(N^2) structures)
is banked by the same-bank guards, and `USE_WDATA_ORDER_Q` removes the
WID-less cross-ID oldest-select that would otherwise have forced a global
compare.

**RESOLVED 2026-08-14 — it was (b), a real defect, and it is FIXED.**

The recorded `test_axi4_master_wr_mon[8-32-32-1-4-16-4-8-4-func]` failure does
NOT reproduce: that test passes at NUM_BANKS=1 and 4, with the order queue on
and off, across 10 seeds each (30/30). It was never sensitive to the defect —
the test could not even express NUM_BANKS until this session (it now takes
`NUM_BANKS` / `USE_WDATA_ORDER_Q` from the environment and puts both in the
`sim_build` name, so a banked run cannot silently reuse an unbanked binary).

The defect is real and was found by inspection, then proven directly.
`pick_oldest` compares SAME-BANK ONLY, justified by "candidates come from an
ID-matched vector, and every entry with a given ID lives in one bank". True
for the read path (`w_data_cand_open` <- `data_match_oh`) and for
`addr_update_oh` (<- `addr_match_oh`); FALSE for the WID-less write path,
whose candidate set `w_data_state_pred_oh` is a state predicate spanning every
bank. So at NUM_BANKS=B the write select returned one winner PER BANK and a
single W beat advanced up to B transactions — the issue #41 double-count,
reintroduced across banks. Measured at N=16/B=4: one W beat advanced slots 0
and 4 together.

**Why nothing saw it:** `val/amba/test_axi_monitor_trans_mgr.py` hardcodes
`IS_READ: '1'`, so the entire transaction-manager regression exercises the
read path only. "trans_mgr passes at 8-32-16" was never evidence about writes
at any bank count.

**Fix (owner's design, 2026-08-14): a common WID FIFO.** Push the AWID on the
AW handshake, pop on W-LAST; the head AWID keys the write-data candidate set.
That puts the write path back inside the ID-matched world `pick_oldest`
assumes — every candidate shares one ID, therefore one bank, so the same-bank
compare is exact by construction rather than by luck. Replaces the slot-index
queue that `USE_WDATA_ORDER_Q` used to select (same parameter name, new
implementation, so no wrapper re-plumbing).

Carries a REPO-WIDE bus requirement, recorded in
[[valid-ready-contracts]]: **W must not lead AW.** Same-cycle AW+W stays
supported via the empty-queue bypass; W strictly before its AW has no AWID to
attribute it to and is treated as a stray. This is the restriction commercial
VIPs commonly impose.

`NUM_BANKS>1` on a write monitor now REFUSES to elaborate without
`USE_WDATA_ORDER_Q=1` (`$error`) — the combination has no correct behaviour to
fall back to. Covered by
`val/amba/test_axi_monitor_trans_mgr_wr_bank.py::test_banked_write_without_widq_is_refused`
alongside the attribution check itself (5 passed: nb1/nb4 x wq, plus the board
sizing N=64/B=4, plus the refusal).

TIMING at N=64/B=4 remains unverified — that is still a synthesis question,
untouched by this fix.

**SECOND BANKING DEFECT, found by the wq=1 sweep and FIXED 2026-08-14.** The
same-cycle AW+W bypass reads a LOCAL MIRROR of the CAM's allocation pick, and
the mirror scanned for the lowest free slot GLOBALLY. Under banking the CAM
allocates inside the ID's bank, so the mirror named a slot in a different bank
and the bypass bound the W beat to an entry that was never allocated:

```
0 completion packet(s), expected 1 -- the same-cycle W beat was lost
1 spurious error packet(s) (codes=['0x4']) -- B after a lost W beat
                            fabricates EVT_PROTOCOL 'response before data'
```

That is the exact failure `95c9490a` originally fixed, back again via banking.
Fix: mask the mirror scan with `w_addr_bank_mask` (all ones at NUM_BANKS=1, so
the unbanked path is bit-identical). Verified `test_axi_monitor_wr_same_cycle`
+ `test_axi4_master_wr_mon` at wq1/nb4, wq1/nb1, wq0/nb1 — 5 passed each; the
pre-fix RED at wq1/nb4 is the mutation evidence.

**The pattern worth carrying forward:** banking invalidated TWO separately
documented invariants — "candidates come from an ID-matched vector"
(`pick_oldest`) and "the CAM allocates the lowest free index" (the bypass
mirror). In both cases the comment asserting the invariant survived the change
while the property it described did not.

**That audit is now DONE and comes back clean.** All six `pick_oldest` call
sites were re-read against B>1: `w_widq_cand_oh` (head AWID, ID-matched — the
fix), `w_addr_pend_oh` (<- `addr_match_oh`), `w_data_cand_open`/`_any` (<-
`data_match_oh`), and `w_resp_cand_open`/`_any` (<- `resp_match_oh`) are all
ID-matched and therefore same-bank by construction. The one non-ID-matched
set, `w_data_state_pred_oh`, is now unreachable when banked (elaboration
guard). The allocation mirror was the only other flat-table assumption and is
bank-masked. No further sites outstanding.

**FORMAL COVERAGE GAP (found 2026-08-14, still open).** The banked
configurations are not proved. `formal/amba/axi_monitor_trans_mgr/*.sby` has
no `NUM_BANKS` / `USE_WDATA_ORDER_Q` override, so the flattened DUT is built
at the parameter defaults (`NUM_BANKS=1`) and every monitor proof runs the
UNBANKED design only. That is not a small hole: `ap_bypass_alloc_mirror`
asserts precisely the invariant that banking broke a second time (see the
same-cycle bypass mirror below), and it passes — because at NUM_BANKS=1 the
invariant is still true. Banking needs its own proof configuration, or the
properties that encode "one flat table" assumptions have to be re-read against
B>1 by hand every time.

**Consequence of ID banking (the constraint that follows):** every transaction
sharing an ID lands in one CAM, so per-ID concurrency is capped by the
GENERATED CAM's depth, not by the total:

    MAX_TRANSACTIONS/NUM_BANKS >= (IDs per bank) * (outstanding per ID)

8ch x 8 outstanding over 4 banks = 16/bank -> `MAX_TRANSACTIONS=64,
NUM_BANKS=4`, and 16 is the depth measured to close (WNS +1.018 ns; 40 entries
= -25.183 ns). Undersize it and entries are refused, not mis-tracked:
`test_axi_monitor_trans_mgr` reports "four outstanding AR(id=2) occupy 2
slot(s), expected 4" at N=8/B=4, and passes at N=16/B=4.

**Debug collateral:** `projects/fpga-systems/Genesys2/stream/build-perf/dv/tests/GTKW/ch3-sram-counts.gtkw`
(110 signals across the three SRAM pointer pairs and both engines) against the
pinned `local_sim_build/ch3-hang.fst`.

## OBS-PORTS — the observers fan telemetry out as ports instead of owning it

**Status:** open 2026-08-16 (found while wiring both observers into stream_harness)

`axi4_intf_{master,slave}_observer` each declare 60 outputs, and only 33 are a
real interface (APB slave response, AXIL slave read, the dump master, irq).
The rest -- bus meters, latency histograms, perf counters, FIFO counts,
compressor stats -- are TELEMETRY fanned out as top-level ports. Wiring the
slave observer into `stream_harness` required tying off **70 pins** on that one
instance, and every one of them is a Verilator PINMISSING error if forgotten.

**This contradicts the block's own design note.** Its header argues it "owns
its configuration rather than taking 29 cfg_* ports that the harness tied off",
and that owning the APB window is "what lets ONE harness source serve both
builds". Config was internalized; STATUS never was, so the harness still has to
know the block's internals to read anything out of it.

**Wanted:** telemetry readable through the observer's OWN regblock (`obs_regs`,
already instantiated behind `s_apb_*`), not through ports.

- Add status fields to `obs_regs.rdl` for the meter buckets, histogram
  bins/totals, perf counters, FIFO counts and compressor stats.
- Regenerate via `bin/peakrdl_generate.py` ONLY -- the wrapper emits RTL, docs
  and regmap in lockstep; raw `peakrdl regblock` desyncs the regmap
  ([[feedback_peakrdl_generate_bin]]).
- Wire the internal nets to the regblock and DELETE the telemetry ports.
- Repoint the readers: `harness_csr.sv` currently mirrors the observer's perf
  outputs into its own CSR space (the "RFC Stage E external observer perf
  readback" path), and the host reads them there. With the regblock owning
  them, the host reads the observer's APB window directly, by name via
  `obs_addrs.py` ([[feedback_registers_by_name]]).

**Why it matters beyond tidiness:** 70 tie-offs per instance is 70 chances to
forget one, and a forgotten OUTPUT is silent -- it reads as PINMISSING only
because Verilator escalates it. The `_cg` wrappers shipped for months with an
unconnected `debug_block_ready` for exactly this reason, hidden behind
`-Wno-PINMISSING`.

**Do this BEFORE the 8-channel build.** Two observers x 70 ports is also
routing and area on a 325T that is already the reason build-mon is 4 channels.

## AMBA-HISTCH1 — CLOSED 2026-08-26: NUM_CHANNELS=1 channel decode guarded
**Status:** CLOSED (fixed same day it was filed; the pumice consumer-path
retirement proceeds independently -- this fix is defensive for every
other NUM_CHANNELS=1 instantiation and cannot conflict with it)

CLOSURE: the three channel decodes are now
`(NUM_CHANNELS > 1) ? id[CW-1:0] : '0` -- exactly the fix the filing
prescribed. Mutation-proven: new latency_hist_ch1_odd_id_test (odd-ids
counted 0/4 on the unguarded RTL under Verilator; 4/4 fixed, plus a
mixed-id bin-exact check) and a NUM_CHANNELS x IS_READ parametrization
of val/amba/test_axi_perf_latency_hist.py (was ch8-only -- structurally
blind to this). The old RTL also failed the pre-existing interleave
phase on a ch1 build (cmd id=1's push vanished out-of-bounds), so the
bug was reachable from existing stimulus, just never built at ch1.
8/8 val cases green. The timestamp-FIFO sizing contract note below
(MAX_OUTSTANDING vs consumer admission domain) remains true and stays
documented in the module's o_cmd_block comment.

`rtl/amba/shared/axi_perf_latency_hist.sv` derives
`CW = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1` and then indexes every
per-channel array with `id[CW-1:0]`. At `NUM_CHANNELS=1` that makes the
channel index ID BIT 0 into a ONE-entry array:

- Simulation (Verilator): out-of-bounds accesses silently vanish — only
  even-ID commands are counted. Deterministic: an LFSR-id run counted
  33/64 transactions (the even-id subset), byte-identical across configs.
- Synthesis: the index truncates instead, so odd/even ids ALIAS onto the
  single entry — same-cycle push/pop hit the same registers, the occupancy
  count corrupts, and `r_burst_active` churn produces multiple "first
  beat" events per burst. This is the likely mechanism behind the pumice
  board's EXTRA-returns side of PUMICE-011 (168409 vs 64000).

Fix when touched: `w_ch_* = (NUM_CHANNELS > 1) ? id[CW-1:0] : '0;` for the
cmd/data/resp decodes. NUM_CHANNELS>1 instantiations (the stream observers
at 8) are unaffected. Also note the timestamp-FIFO sizing contract the same
investigation surfaced: with `o_cmd_block` unconsumed, MAX_OUTSTANDING must
cover the consumer's WHOLE admission domain or samples are silently lost
(the module's own comment documents the degradation; the char macro ran at
8 vs an ~10+ deep engine pipeline and lost up to 6/64 samples even with
single-id traffic).
