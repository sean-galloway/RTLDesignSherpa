<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — open (not started)


## TOOL-002: Migrate the remaining method docs out of bin/ into the handbook
**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

`CLAUDE.md` now states the handbook is the single source of truth for skills and
methods, and that methodology does not live next to the code. Seven files in
`bin/` still do. They were deliberately left when the Kimi migration was scoped
to Kimi only — this is the follow-through, not new work.

- [ ] `bin/DOC_GENERATION.md` — the doc pipeline how-to
- [ ] `bin/HEADER_TOOL_USAGE.md`
- [ ] `bin/markdown_to_word_instructions.md`
- [ ] `bin/md_to_docx_install.md`
- [ ] `bin/md_to_docx_usage.md`
- [ ] `bin/SIGNAL_CONTRACTS_KMAPS.md`
- [ ] `bin/SIGNAL_NAMING_AUDIT.md`

Method content moves into the relevant handbook note (mostly
[[doc-pipeline]] and [[signal-contracts-and-kmaps]]); each file is reduced to a
short pointer, as `bin/review/README.md` already is. Do not delete outright —
someone landing in `bin/` should still be redirected.

**Known inconsistency to resolve as part of this:** `doc-pipeline.md` currently
calls `bin/DOC_GENERATION.md` the "canonical how-to", which contradicts the rule
one note away. Whichever way it resolves, the two must agree.

**Distinguish artifacts from documentation.** Files the code *reads* are not
documentation and stay put — `bin/review/REVIEWER_BRIEF.md` and
`docs/kimi_humanization_style_guide.md` are loaded verbatim as prompts. Check
before moving anything.

---

## TOOL-003: One gate that runs filelist_registry --check and --audit
**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

Shared deliverable for COMMON-010 and AMBA TASK-026 — build it once here rather
than twice in the areas.

`bin/filelist_registry.py --check` is currently run by **nothing**: not the
pre-commit hook (which does check `.sv` declaration order, so the hook exists
and is the obvious home), not CI (`track-clones.yml` is the only workflow), not
a Makefile target. Every module having a filelist is a stated MUST that nothing
verifies.

- [ ] Add `--check` to the pre-commit hook, scoped to commits touching `.sv` or
      `.f` so it does not tax unrelated commits.
- [ ] Add `--audit` (consumers hand-listing `rtl/common` / `rtl/amba` sources).
- [ ] Decide whether a CI workflow is also wanted, given the repo currently has
      almost no CI.
- [ ] Make the failure message name the offending module and the area's
      `filelists/` dir, so the fix is obvious without reading the tool.

**Gotcha to preserve:** `--check` exits PASS when `declared - covered - exempt`
is empty, so a gate that only inspects the exit code will not notice the
`[exempt]` ledger growing. Either fail on new exempt entries or report the
counts. See [[filelists]].

---

## TOOL-004: Finish validating the cloud bootstrap on a genuinely clean box
**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

`bin/install_tools.sh` and `bin/cloud_bootstrap.sh` were written and partly
verified on 2026-07-23, but two paths have never executed:

- [ ] **The oss-cad-suite download.** Only `--no-formal` was exercised; the
      workstation already had the suite, so the ~2 GB fetch, the GitHub-API tag
      resolution, and the tarball layout assumption (`oss-cad-suite/bin/...`)
      are all unproven. If the release asset naming has changed, the resolver
      builds a 404 URL.
- [ ] **A clean-box run end to end.** Every step was verified individually
      (apt has Verilator 5.020 on Ubuntu 24.04; `CocoTBFramework` resolves from
      PyPI at 0.6.1; sv2v and Verible download and execute) but never in
      sequence on a machine that had none of it.
- [ ] The `val/common` smoke test at the end of `cloud_bootstrap.sh` has not
      been observed passing from a cold start.

Verified and not in doubt: the pinned-Verilator shim resolves to 5.020 even
with oss-cad-suite on PATH. That was the part most likely to be silently wrong.

---

## TOOL-005: env_python hardcodes /mnt/data/tools
**Priority:** P3
**Status:** 🔴 Not Started
**Owner:** TBD

`env_python` works unmodified in a sandbox *provided* tools install to
`/mnt/data/tools`. If they land anywhere else, `install_tools.sh --prefix`
prints three `export PATH` lines the user must paste, and the ordering matters
(the pinned Verilator must be prepended LAST so it beats oss-cad-suite's 5.045).

That is a footgun: paste them in the wrong order and you silently simulate on
5.045, which is exactly what the pin exists to prevent.

Make `env_python` honour a `RTLDS_TOOLS_PREFIX` (defaulting to
`/mnt/data/tools`) so the prefix is set once and the ordering is not the user's
problem. See [[cloud-sandbox]].

---

## TOOL-006: Triage the 18 Dependabot vulnerabilities on the default branch
**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

Every push prints: *"GitHub found 18 vulnerabilities on
sean-galloway/RTLDesignSherpa's default branch (14 high, 4 moderate)."* It has
been printing that all session and is tracked nowhere, which is how a warning
becomes wallpaper.

- [ ] Read the Dependabot alerts and classify: real exposure vs transitive dev
      dependency that never runs on untrusted input.
- [ ] Bump what is safe to bump; `requirements.txt` is pinned, so each bump is
      a deliberate edit and needs a regression run behind it.
- [ ] Record anything deliberately not fixed, with the reason. An accepted risk
      that is written down is fine; an unread alert is not.

Note the alerts are against `main`, and the working branch has moved on — check
whether any are already fixed by the current pins before doing work.

---

## TOOL-007: Two real gaps in the RDS-DV arbiter BFM
**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

Found while fixing COMMON-012. Both belong in the RTLDesignSherpa-DV repo, not
here; file them there and reference this task.

- [ ] **`ArbiterCompliance.analyze_round_robin_compliance()` is a stub.** It
      returns a hardcoded `{'rr_efficiency': 1.0, ...}` regardless of the
      observed grant sequence — see `components/shared/arbiter_compliance.py`.
      It is the one check whose name promises to catch a rotation defect, and
      it cannot. A clean report from it is not evidence of anything. Either
      implement it against the grant history the monitor already records, or
      make it return `{'status': 'not_implemented'}` so callers cannot mistake
      it for a pass. `detect_burst_behavior()` is stubbed the same way
      (`bursts_detected: 0` hardcoded).
- [ ] **`ArbiterMaster` cannot saturate via a profile.** Its
      `_setup_default_profiles` defines a private set (`default`, `fast`,
      `slow`, `disabled`, `manual`) that is not wired to `FlexConfigGen`, whose
      `DEFAULT_PROFILES` already contains `backtoback` = `[(0,0)]` = zero delay.
      Even `fast` carries a 1-3 cycle `inter_request_delay`, so all-clients-up
      never sustains and arbiter tests silently under-stress. Workaround in use:
      `force_client_request(c, enable=True)`. Wire the shared catalogue in, or
      add a saturating profile.

Why this matters beyond tidiness: the combination of these two is what let a
round-robin arbiter that starved half its clients pass its own testbench. See
[[randomization]].

---

## TOOL-010: Project-area cleanup — apply the RTL-area pattern to projects/
**Priority:** P2
**Status:** 🔴 Not Started — **DEFERRED until the RTL area is complete** (Sean)
**Owner:** Sean (pumice push) / TBD

Once `rtl/` is clean (doc placement, CDC reorg, filelist consistency), apply the
same passes to `projects/`. "We will look into the projects once the RTL area is
complete" (Sean, 2026-07-24). This is the umbrella; each project below is a unit
of work.

**Per project, the same three passes done on rtl/common and rtl/amba:**
- doc placement ([[doc-placement]]): README → link, standalone guides →
  `docs/markdown/`, style guides/methodology → `vault/handbook/`, no PRD/spec
  docs loose in the tree. (README rollout is tracked broadly as DOCREV-007;
  this is the per-project execution.)
- filelist consistency ([[filelists]]): every `.f` in the owning dir's
  `filelists/`; a TB with its own harness gets its own filelist WITH the TB.
- verify `bin/filelist_registry.py --check` (all three counts) still resolves.

**Concrete known stragglers (from the 2026-07-24 survey):**
- [ ] **bridge** — `rtl/filelists_static/` → `filelists/` (or justify "static")
- [ ] **rapids_char** (NexysA7) — `flows-rapids-beats/flists/` → `filelists/`
- [ ] **retro_legacy_blocks** — loose `rtl/rlb_top/rlb_top.f` → `filelists/`
      subdir. (`rtl/apbx_xbar/apbx_xbar_rlb_1to10.f` is gone: deleted
      2026-09-14 along with the hand-rolled crossbar it listed, which was
      replaced by the generated `apbx_xbar_1to10.sv`.)
- [ ] **ddr2_char** (NexysA7) — loose `rtl/ddr2_char_macro.f` → `filelists/`;
      the `dv/` harness `.f` get a `filelists/` dir WITH the TB
- [ ] **pumice** — `dv/tb/*_tb_top.f` → a `filelists/` dir with the TB.
      **⚠️ PUMICE PUSHES FROM SEAN'S WORKSTATION, not this environment**
      (Sean, 2026-07-24) — make the pumice changes but do NOT push them; Sean
      pushes pumice from the workstation. See Tasks/pumice.
- [ ] the remaining components (converters, delta, hive, misc, apbx_xbar,
      dmas/{stream,rapids}, memory-controllers/{ddr3,ddr4}) get the same
      treatment as they are reached.

**Gate:** RTL area first (Tasks/INDEX.md sequencing). Do not start until the
cdc reorg + amba cleanup land.

---

## TOOL-011: Tests resolve filelists through the toml registry, not hardcoded paths
**Priority:** P2
**Status:** 🔴 Not Started
**Owner:** TBD

Every test hardcodes its filelist location:

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path='rtl/common/filelists/fifo_async.f')

So moving a module's `.f` (e.g. the CDC reorg: common/amba -> rtl/cdc) forces an
edit to every test that names the old path. That is the repo's #1 silent-failure
trap -- a missed test path resolves to nothing and the test "passes" against no
DUT. It made the CDC reorg touch ~10 test files it should not have had to.

**Fix:** resolve the filelist by MODULE NAME through `bin/filelists.toml` /
`bin/filelist_registry.py`, which already answers "which filelist provides
module X" (`--find MODULE`). The test names the module, the registry returns the
`.f`; location is the registry's concern, not the test's.

- [ ] Add a `filelist_for(module)` helper to `TBClasses/shared/filelist_utils`
      that calls the registry (or reads the toml) and returns the `.f` path.
- [ ] `get_sources_from_filelist` gains a `module=` mode: given a module name,
      resolve via the registry instead of a literal `filelist_path`.
- [ ] Migrate tests from `filelist_path='...'` to `module='...'`. A module move
      then updates only the toml, never the tests.
- [ ] Keep `filelist_path=` working for the harness/consumer cases that assemble
      a specific `.f` rather than one module.

**Payoff, concretely:** had this existed, the CDC reorg would have moved 12 `.sv`
+ their `.f` + one toml area, and touched ZERO test files. It is the structural
fix for the fragility [[filelists]] describes.

## TOOLING-KMAP — emit CONTRACT TABLES (proofs), not K-map pictures
**Status:** open 2026-08-06; SCOPE CHANGED 2026-08-28 — the output FORM
changes, not just its rigour. Sean, after reviewing the emitted maps: "all
of the kmaps so far are unacceptable as there is no way to discern what
signals map to what... it should list out the signals that have strict
relationships (like if a=0 then b[1:0] is always 2'b10) then use these terms
in a table going through each possible value, then marking the ones that are
illegal, and marking the legal combinations with what the output should be.
This isn't necessarily the form a traditional kmap is, but it works in the
real world where more than 3-4 expressions are at play."

So the deliverable is a THREE-PART CONTRACT TABLE (term list -> invariants ->
decision table), spec and rationale in
[[signal-contracts-and-kmaps]]. Items 1-4 below survive but are re-aimed:
item 1 becomes the term list (structural, not a footnote), item 2's
don't-cares now also cover ILLEGAL rows with the invariant that excludes
them, item 3's sufficiency argument becomes the invariant list, and item 4
(implicants) matters MORE, because the table deliberately gives up the
grid's visual adjacency and mechanical derivation is what replaces it.

NEW item 0, ahead of the rest: teach the emitter the table form and add an
invariant checker -- evaluate each declared invariant over the full space and
FAIL the run if a row it calls impossible is actually reachable. A wrong
invariant must not silently delete a real case.

Audit of both `gen_signal_contracts_kmaps.py` (stream) and pumice's merged
`gen_pumice_signal_contracts.py`: the grids are
Gray-ordered and computed from cited RTL -- genuinely good -- but they stop
short of proving anything. `grep -ciE "implicant|minimal|quine|espresso"` finds
nothing in either generator; every "cover" hit is prose inside a
`CHECK BY INSPECTION` string. See [[signal-contracts-and-kmaps]] for the six
criteria; the emitter satisfies two.

Work, in the order that pays:

1. **Axis derivation table.** `kmap()` takes `varnames` as bare strings. Take
   `(name, expr, cite)` triples instead and emit them above the grid. An axis
   that is itself a composite expression hides the logic the map claims to show.
2. **Don't-care support.** Let `fn` return `None`/`X`; render as `X`, styled
   distinctly, and require a `reason=` citation per unreachable region. Today
   unreachable cells get a real 0/1 plus a prose aside -- which both hides bugs
   and blocks legal grouping.
3. **Sufficiency field.** A required `depends_only_on=` argument explaining why
   the mapped function ignores every other input. Fail the run if it is empty.
   Without it a paged map is a slice with no stated invariant.
4. **Implicant derivation.** Quine-McCluskey is fine at <= 6 variables (our cap).
   Emit the minimal sum-of-products, then DIFF it against the mirrored RTL
   expression and label the result identical / RTL-redundant / RTL-differs.
   The third case is the defect finder.
5. **Promote to bin/.** Both generators carry a private copy of this machinery
   (was /TOOLING_TODO.md item 1; that file's backlog folded into this area
   2026-08-09 and the promotion now lives ONLY here). Do this AFTER 1-4 so
   one implementation gets the improvements, not two.

Acceptance: a workbook where every map states its axis equations, its
sufficiency argument, its don't-cares with citations, and a derived-vs-RTL
verdict.

## TOOL-014 — Scripts book link rot + DOCUMENTATION_INDEX refresh
**Status:** open 2026-08-09 (migrated from /TOOLING_TODO.md item 3, found
2026-07-22 during the assets move; re-verified still broken at migration)
**Priority:** P3

`docs/markdown/Scripts` has pre-existing broken image/file links, untouched
by the images_scripts_uml -> Scripts/assets move (all moved links verified
at the time):
- `wavedrom_troubleshooting.md` -> `assets/wavedrom/*.svg` — dir never
  existed here (18 references, still broken 2026-08-09)
- `cheat_sheet.md` -> `../rtl/_wavedrom_svg/*.svg` — dir gone
- `generate_uml.md` -> `../../puml_img/CocoTBFramework*.png` — UML renders
  gone; the tool lives in RDS-DV now, so the page may belong there entirely
- `md_to_docx.md` -> diagram.json examples — illustrative snippets; possibly
  fine as-is, mark as examples

Triage each: repoint, regenerate, or prune when the Scripts book gets its
pass (the docs-review area has "Scripts overview: write it" pending — do
these together). Related: `docs/DOCUMENTATION_INDEX.md` still catalogs the
pre-cleanup docs/ layout — refresh or retire it now that the handbook exists
(owner flagged 2026-07-22; its TESTING.md entry was repointed to the
handbook when /TESTING.md was retired 2026-08-09).

---

## TOOL-016 — Twelve component conftests stamp TEST_LEVEL into os.environ, which kills every per-cell depth export
**Status:** open 2026-09-09 (found while leveling the bridge suite, BRIDGE-007)
**Priority:** P2. Any Pattern B area that has a real REG_LEVEL grid runs
every cell of a FULL run at full depth and every cell of a GATE run at
gate depth -- the grid exists in pytest collection only.

**Mechanism.** `cocotb_test.simulator.set_env` applies `extra_env` and
then copies EVERY `os.environ` entry over it, so the process environment
beats the per-cell value a wrapper exports. A "REG_LEVEL -> TEST_LEVEL
bridge" block -- `os.environ['TEST_LEVEL'] = _reg_level.upper()` at
conftest import, written for wrappers that exported nothing -- was copied
into thirteen conftests. The bridge's copy is removed (this task's
evidence), converters followed on 2026-09-10, then retro_legacy_blocks, pumice
(all three areas), misc and apbx-xbar on 2026-09-11. Five remain, all
rapids:

    projects/components/dmas/rapids/dv/tests/{fub,fub_beats,macro,macro_beats,top_beats}/conftest.py

**Evidence.** First leveled bridge FULL run, 2026-09-09: 216 cells, the
gate/func/full triple of every test, all logging `level=full` with
identical wall-clock. Removing the stamp and re-running one test at
REG_LEVEL=FULL gave gate/func/full cells at 1/4/16 offsets.

**Everything in scope is converted.** The five rapids areas are all that is
left and they are out of scope until that suite is green again ([[feedback_rapids_out_of_scope]]). Originally, and true then: Measured 2026-09-10
with `check_test_levels.py`: every area except the bridge reports
`depth:not-exported` on nearly every test -- their wrappers export nothing,
so the stamp is the ONLY thing mapping REG_LEVEL onto a depth. Deleting it
alone would drop those tests to the default and quietly shrink every FULL
run, which is the failure its own comment was written to prevent (pumice
fub, 91 tests -> 79).

**What does NOT work, so nobody tries it twice.** Re-stamping the cell's
own value into `os.environ` from the wrapper, just before `run()`, so that
what cocotb_test copies over `extra_env` is the cell's value. It looks
airtight and it is not: measured on the bridge with the stamp re-added, the
wrapper printed `extra_env=gate os.environ=gate` immediately before `run()`
and the simulation still logged `TEST_LEVEL=full` on all three cells, 16
offsets per pair in each. The same three cells with the stamp REMOVED ran
gate/func/full at 1/4/16. The mechanism behind that is not understood; what
is settled is that only removing the stamp works.

**What to do per area, in ONE commit.** Both halves together:
1. Give every wrapper `@pytest.mark.parametrize("test_level", reg_level_grid())`
   and `**level_env(test_level)` in its `extra_env`, from
   `TBClasses.shared.test_levels` (one implementation; the checker
   recognises it).
2. Give the area a depth profile its TBs read via `current_level()` -- the
   bridge's `dv/tbclasses/bridge_levels.py` is the model.
3. THEN delete the conftest stamp.
4. `check_test_levels.py <area>` clean, and confirm from the TB banner that
   sibling cells log DIFFERENT `TEST_LEVEL=<x>` and different wall-clock. A
   grid that expands is not a grid that runs.
5. Clean FULL run for that area before moving on.

`projects/components/bridge` is the worked example, converted end to end.
rapids is out of scope until its suite is green again. Handbook:
[[test-runner]] (the cocotb_test precedence note), [[test-review]].

**converters, converted 2026-09-10.** Eighteen wrappers. Eleven already
exported a depth and none of it reached the simulator, which is exactly the
half-state this task describes: the grid expanded and every cell ran at the
same depth. The seven with no axis at all -- the AXI2APB4 shim, the
AXI4-to-APB4 RRESP witness, the data upsize and downsize converters, the
downsize smoke test, the PeakRDL adapter and the UART bridge error witness --
each got a REG_LEVEL grid, a per-cell `level_env` export and a depth profile
its cocotb body reads. `func` was set to the counts each file already used, so
the conversion adds gate and full around existing coverage rather than
redefining it. Then the stamp went, in the same commit.

Step 4 measured, not assumed. Grid: 60 / 113 / 171 tests at GATE / FUNC /
FULL. Depth reaching the simulator: the three sibling cells of
`test_dnsize_quick` logged 3, 12 and 48 transactions, and the RRESP witness
drove 1, 3 and 8 beats.

Two findings fell out of the conversion, both of the kind [[BRIDGE-007]] is
for. The downsize smoke test discarded its scenario's pass/fail return, so it
could not fail on a data mismatch. The RRESP witness pinned `testcase=` to a
single cocotb test; it now runs a level-selected list of per-slice error cases
through one test and reports every mismatching beat, because which subset
fails is the diagnosis -- driving RRESP from the in-flight slice fails the
first-slice cases, while a stuck accumulator fails the clean beats that follow
an errored one. That second case did not exist before and is the coverage the
level axis actually bought: at full the run now shows OKAY on beats 2, 4 and 6
immediately after SLVERR beats.

**misc, converted 2026-09-11 (`79cc245eb`).** Four wrappers.
`test_dma_address_gen` already exported a per-cell TEST_LEVEL and its TB
already had a gate/func/full table -- the stamp overrode both, the exact
half-state this task describes. The grid did not move either: 48 cells at
GATE, FUNC and FULL alike. All four wrappers now take `reg_level_grid()` and
export `level_env()`; the three with no depth knob got one (counts, never
burst geometry), and the observer's register test is graded by SECTION
instead -- gate proves the bus, the capability contract and the reset values,
func adds the config round-trip, full adds the read-only sweep. A register
test still has tiers if you look for them.

Step 4 measured. Grid 48 / 96 / 144. Sibling cells of one test: dma_address_gen
drove 16 / 64 / 256 linear addresses, rd_pattern_gen 8 / 16 / 48 stability
bursts, wr_crc_check 2 / 4 / 12 back-to-back writes, the observer's traffic
test 16 / 32 / 96 productive beats, and its register test stopped at three
distinct tiers. Clean run: FULL 144 (8:48), FUNC 96 (4:36), GATE 48 (4:07),
no failures, no reruns.

Two findings fell out, both in the observer wrapper. Its sim_build key was
`{dut}_{testcase}`, but testcase is runtime-only and does not change the
build, so the same RTL compiled four times per observer -- and a level axis
made it twelve (24 directories for 2 distinct RTL configurations). The key is
now toplevel + a parameter digest + the xdist worker. And it was the only
wrapper in the area passing no LOG_PATH and no per-cell results file, so its
grading would have left nothing to check; both are per cell now, and that is
where the tier evidence above came from.

**apbx-xbar, converted 2026-09-11 (`d2b61e553`).** The one area whose stamp
was INERT rather than load-bearing: nothing there read TEST_LEVEL, so the
grid sat at 9 cells for GATE, FUNC and FULL alike and removing the stamp
alone would have changed nothing. That made it DV design work -- six
hand-rolled testbenches with no tbclasses, each with its scenario counts
written as literals.

Each cocotb body now takes its COUNTS from a per-file table and the crossbar
shape (master/slave fan-out, burst geometry, poll loops) stays fixed.
`timeout_time` had to scale with them: it is evaluated at import, inside the
simulator with TEST_LEVEL already set, and 1to1 allowed 40 us for ~122
transactions, so a full run against a gate-sized timeout would have failed as
a timeout rather than as a bug. `func` reproduces each test's previous counts
exactly, so gate and full bracket the old coverage instead of redefining it.

`test_apbx_xbar_2to2_mixed` has no count to scale -- it is a contract test
(four master/slave pairings, sideband gating, the APBX-002 decode-miss
regression). It grades by SECTION with the decode-miss round count as the
knob, since repeating a miss is what would expose state it left behind.

Step 4 measured. Grid 9 / 18 / 27. Transactions per level, derived and logged
by each test: 1to1 38 / 122 / 274, 2to1 80 / 204 / 468, 1to4 140 / 336 / 784,
2to4 180 / 464 / 1108; timing measured 3 / 5 / 16 transfers and 2to2_mixed
ran 0 / 1 / 4 decode-miss rounds. FULL 27, FUNC 18, GATE 9, no failures.

Three things were already broken. Every summary line added a hand-summed
constant matching no set of loops (1to1 +60 against 82 fixed transactions,
2to1 +70 against 144, 1to4 +160 against 296, 2to4 +250 against 364) -- all
derived now. conftest carried three dead fixtures, one of which
(`xbar_test_level`) encoded a second, conflicting level model with its own
transaction-count table that would have tripled every test if anyone had
requested it. And `timing` imported the same helper twice while
`2to2_mixed` never imported pytest at all.


<!-- Moved from vault/Tasks/amba/ 2026-09-14: the root cause is the pytest-xdist runner deleting local_sim_build concurrently, which hits every area, not amba RTL -->
## VAL-XDIST-INTERMITTENT — OPEN on the durable fix (root cause proven 2026-08-28: concurrent deletion of local_sim_build)
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
