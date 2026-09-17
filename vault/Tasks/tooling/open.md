<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — open (not started)

## TOOL-017: `lint-<component>` is advertised but cannot run for two areas
**Priority:** P3
**Status:** 🔴 Not Started -- and MOVED BACK TO OPEN 2026-09-16. It was filed on
the closed page while its own status said Not Started and no fix was recorded.
Re-checked against the tree today and it still reproduces exactly as described:
`retro_legacy_blocks` has an `rtl/Makefile` but NO `lint-all` target, and
`apbx_xbar` has no `rtl/` directory at all, while the template at
`projects/components/Makefile` delegates unconditionally to
`$(MAKE) -C $(1)/rtl lint-all`.
**Owner:** TBD

`projects/components/Makefile` generates a lint target per component and
advertises them in `make help`:

    make lint-retro_legacy_blocks  Lint Retro Legacy Blocks RTL

Both of these fail immediately, measured 2026-09-14:

    $ make lint-retro_legacy_blocks
    make[1]: *** No rule to make target 'lint-all'.  Stop.
    make: *** [Makefile:463: lint-retro_legacy_blocks] Error 2

    $ make lint-apbx_xbar
    make[1]: *** apbx_xbar/rtl: No such file or directory.  Stop.
    make: *** [Makefile:463: lint-apbx_xbar] Error 2

The template at `Makefile:456` delegates to `$(MAKE) -C $(1)/rtl lint-all`.
stream, rapids, bridge and converters each have an `rtl/Makefile` providing
`lint-all`; **retro_legacy_blocks and apbx_xbar do not**, and apbx_xbar has no
`rtl/` directory under that name at all.

**Why it matters rather than being cosmetic.** A gate that cannot run is not a
gate, and this one is advertised in `help`, so the natural assumption is that
the area is linted. It is not: [[RLB-015]] sat unverified for days partly
because the reporter concluded "retro_legacy_blocks has no lint target, so
nothing is measured" -- the right conclusion from the wrong premise. The area
IS lintable; every block has a working top filelist and
`verilator --lint-only -Wall --timing -f <filelist>` runs clean today.

**Fix options, in order of preference:** give the two areas an `rtl/Makefile`
with a `lint-all` that loops their top filelists (the sweep in RLB-015's
closure is a working prototype); or have the template discover filelists
directly and drop the per-area Makefile requirement; or, at minimum, stop
advertising targets that cannot run.

**SAME ROOT CAUSE, WORSE SYMPTOM, found 2026-09-14: the whole component
regression cannot run either.** `projects/components/Makefile` line 31 lists
the component as `apbx_xbar`, but the directory was renamed to the hyphenated
house style and is `apbx-xbar` on disk. It is the FIRST entry in `COMPONENTS`,
and the loop at `Makefile:259` ends each iteration with `|| exit 1`, so:

    $ make clean-all && make run-all-full-parallel
    ==> Testing apbx_xbar (FULL, 48 workers)
    make[1]: *** apbx_xbar/dv/tests: No such file or directory.  Stop.
    make: *** [Makefile:259: test-all-full-parallel] Error 1

That aborts before a single test of ANY component executes. So the documented
whole-repo command -- `make clean-all && make run-all-full-parallel`, which is
the standing instruction for every area -- has been exiting 2 without testing
anything, and the failure is 3 lines into a long log where it reads like
progress. It affects all six `test-all-*` targets, which share the loop.

**FIXED 2026-09-14** (Sean: "I fixed the apbx-xbar a couple of weeks ago.
That is the correct reference" -- the hyphenated directory is canonical, so
the Makefile was simply the stale side).

The history is a two-step rename that half-landed. `f28581b3d`
("refactor(apbx_xbar): rename apb4_xbar -> apbx_xbar", 2026-08-12) touched the
Makefile; `95f7006fc` ("...+ hyphenated dir", the SAME DAY) renamed the
directory to `apbx-xbar`. The Makefile kept step 1's name and was never
advanced to step 2b's, so `COMPONENTS` has pointed at a path that stopped
existing hours later. An earlier note here blamed f28581b3d for the rename;
that was wrong -- f28581b3d is the commit that was left BEHIND by it.

Fix applied: `apbx_xbar` -> `apbx-xbar` in `COMPONENTS`, plus the matching
`make lint-apbx_xbar` help line (the `lint-$(1)` template derives its target
name from COMPONENTS, so the advertised name moves with it). Only PATH
references changed -- the SystemVerilog modules stay `apbx_xbar_*`.

**The lint half of this entry stays OPEN.** `lint-apbx-xbar` now resolves the
path but still fails, for the separate reason above: apbx-xbar has no
`rtl/Makefile` providing `lint-all`. Same for retro_legacy_blocks.

Same lesson as the lint half: a gate that cannot run is not a gate. This one
additionally reported a non-zero exit that is easy to read as "the suite ran
and something failed" rather than "nothing ran at all".

**CLOSED 2026-09-15 — and the scope was SIX areas, not two.**

The entry named retro_legacy_blocks and apbx_xbar. Measuring every component
found four more, each broken differently, which is why a survey beat reasoning
from the template:

| area | what was actually wrong | now |
|---|---|---|
| retro_legacy_blocks | no `rtl/Makefile` at all | PASS, 84 modules |
| apbx-xbar | had a Makefile; `verible` target died on a shell syntax error | PASS, 21 modules |
| misc | no `rtl/Makefile` | PASS, 57 modules |
| pumice | no `rtl/Makefile` | PASS, 52 modules |
| stream | Makefile referenced `filelists/stream_all.f`, which never existed | PASS, 76 modules |
| rapids | same, `filelists/rapids_all.f` | PASS, 69 modules |
| converters | ran, but `|| true` per file and no `--top-module` — gated nothing | PASS, 65 modules |
| bridge | already a real gate (filelist-driven, `--top-module`, waivers) | left alone |

**The fix was not new lint logic.** `rtl/make/area.mk` already did exactly what
this entry asked for, and the four `rtl/` areas use it through a four-line
Makefile. Each component got the same four-line Makefile plus the
`filelists/<area>_all.f` master that `area.mk` (and stream's and rapids' own
Makefiles) had always expected. The 180-to-295-line per-area Makefiles are gone.

Verified per area with `make -C projects/components lint-<component>`; the
counts above are modules linted each as its own top.

**`area.mk` needed one change**, because it looked for a module's own filelist
only at a flat `filelists/<mod>.f`, which never matches an area that nests them
(`gpio/filelists/`, `filelists/core/`, `filelists/top/`). It now falls back to a
recursive search, flat-first so existing areas are unchanged. Proven against a
baseline captured BEFORE the edit: common 218, cdc 20, math 174, amba 402,
exit 0 — identical after, with per-module resolution now also working
(46/14/172/149 via own filelist).

**Three defects fell out of having a gate that actually runs:**

1. **An RTL bug in `axi4_slave_rom`** (misc). It had no ROM size parameter and
   derived one from the whole address space -- `ROM_ADDR_WIDTH = AXI_ADDR_WIDTH
   - $clog2(BYTES_PER_WORD)` = 29, so `2**29` entries, ~34 Gbit at 64-bit data.
   Verilator refuses to elaborate it ("vector of over 1 billion bits") and no
   flag suppresses it -- `--max-num-width` caps number width, not array depth.
   Nothing in the repo instantiates the module or overrides that width, which is
   why nobody noticed: the old per-file gate never elaborated anything. Fixed by
   giving the ROM a real `ROM_ADDR_WIDTH` parameter (default 12) and indexing it
   from the low address bits.

2. **`filelist_registry.py` audited its own generated output.** `area.mk` writes
   a flattened filelist to `<area>/rtl/lint_reports/` on every run, and
   `area_filelists()` did a bare `rglob("*.f")` with no tracked-file filter.
   retro_legacy_blocks declares the whole `rtl/` tree as `filelist_dirs`, so the
   auditor picked that artifact up; a flattened list hand-lists every source by
   definition, so `--audit` reported 29 cross-area sources and the pre-commit
   hook blocked EVERY commit until the untracked file was deleted -- a red gate
   no commit could fix. Now filtered through the existing `_git_ignored()`, the
   same rule `--blindspots` already used ("if git does not track it, it is not
   ours to register"). Verified with the artifact PRESENT, not merely deleted.

3. **`flatten_filelist.py` had no cycle guard.** A filelist that `-f` includes
   itself recursed until `RecursionError`, naming neither the file nor the
   cycle. That is easy to write by accident -- generate a master by globbing its
   own directory and it includes itself, which is exactly what I did to misc.
   It now exits 2 naming the chain.

**The top-level `Makefile` carried a third, worse copy of this defect** and was
fixed too: all ten project lint targets ended `|| true` so none could fail, each
was wrapped in a `[ -f .../Makefile ]` guard that printed "not found" and then
exited 0, `lint-apbx_xbar` still pointed at the pre-rename `apbx_xbar/` path,
and `lint-shims`/`lint-hive` named areas that do not exist. A target that
reports success for a missing area is worse than one that errors.

**Bridge was NOT converted, and should not be.** Its Makefile is a genuine
gate -- it loops its filelists, lints each with `--top-module`, counts failures
and carries real lint waivers -- so converting it would have thrown away the
waivers to make it resemble the others. It is slow (53 filelists, each flattened
then linted, ~7 min) and buffers into its own log, so it looks hung from the
outside. It is not; I killed it twice on that mistaken reading before probing at
the right level, which is the lesson: a make with no visible children is not
evidence of a hang until you have walked down to the level that would show them.

**But bridge WAS broken, in a fourth way, and it was hiding behind the same
`|| true` this task removed.** `make -C projects/components lint-all` still
exited 2 after every area passed, because `lint-all = verilator verible` and
bridge's `verible` recipe died with `/bin/sh: Syntax error: ";" unexpected`.

Cause: these Makefiles `-include $(REPO_ROOT)/makefiles/common.mk` and **that
file does not exist** -- there is no `makefiles/` directory in the repo, and
`print_success`/`print_warning` are defined nowhere. `-include` is silent by
design, so every `$(call print_success,...)` expanded to EMPTY. On its own
recipe line that is harmless, which is why nobody noticed; inside a continued
shell block it leaves a bare `;` between `cat ...;` and `else`, and the shell
refuses to parse it. So bridge's verilator half passed, printed its tick, and
the area still returned 2.

The same defect sat in **delta**, and only became visible once the top-level
`|| true` came off -- removing the mask is what turned a latent break into a
failing target. Fixed in both by replacing the four in-shell `$(call print_*)`
calls per file with plain `echo`s; the calls left on their own recipe lines are
harmless and were not touched. Verified: bridge `verible` exit 0, delta
`lint-all` exit 0, and no in-shell `$(call print_*)` remains anywhere.

apbx-xbar had this too -- it is why `lint-apbx-xbar` failed at
`Makefile:49: verible` rather than for the reason this entry originally
recorded -- but its Makefile was replaced wholesale, so the bug went with it.

---



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
**Priority:** P2 -> P3 (re-scoped)
**Status:** MOSTLY DONE, re-scoped 2026-09-16. Three of the four items landed
without this entry being updated, so it still read as untouched work.
**Owner:** TBD

Shared deliverable for COMMON-010 and AMBA TASK-026 — build it once here rather
than twice in the areas.

**The premise below was true when filed and is FALSE now** -- kept because the
re-scope only makes sense against it. It read: "`--check` is currently run by
nothing: not the pre-commit hook, not CI (`track-clones.yml` is the only
workflow), not a Makefile target."

Measured 2026-09-16, all three clauses are wrong:

- `.github/workflows/filelist-checks.yml` runs `--check`, `--audit` and
  `--blindspots --ratchet` as hard gates on push, PR and dispatch, plus
  `check_doc_examples.py` and `check_test_dut_family.py`.
- `.git/hooks/pre-commit` runs the same three locally, gated on staged
  `.f/.sv/.svh/.sby/.toml` or `test_*.py` -- a deliberate superset of the
  ".sv or .f" this entry asked for, because `.sby` and `test_*.py` are the
  blindspot carriers.

- [x] Add `--check` to the pre-commit hook, scoped. **Done**, and scoped wider
      than asked (see above).
- [x] Add `--audit`. **Done** -- the hook loops `for check in --check --audit`,
      and CI runs it as its own step.
- [x] Decide whether a CI workflow is also wanted. **Done, decided yes.**
- [ ] PARTIAL -- make the failure message name the offending module **and the
      area's `filelists/` dir**. `cmd_check` prints `uncovered module: {m}` and
      the area name, but never the directory the `.f` belongs in, so the fix
      still is not obvious without reading the tool. One f-string.
- [ ] NOT DONE, and this is the substantive half -- fail (or delta-report) when
      the `[exempt]` ledger GROWS. `cmd_check` line ~436 is
      `missing = sorted(m for m in declared - covered if m not in exempt)`, so
      an exempt module is silently subtracted and a new exemption passes every
      gate. `--blindspots --ratchet` does NOT cover this: it ratchets
      unregistered `.f`, hand-listed tests and dead `.sby` paths, a different
      class. Validating [[TASK-026]] on 2026-09-16 required reading the ledger
      by hand for exactly this reason.

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
**Status:** open 2026-09-09 (found while leveling the bridge suite, BRIDGE-007).
**RE-MEASURED 2026-09-16 -- the "everything in scope is converted" claim below
was WRONG; stream and pumice are not converted.**
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

**Measured 2026-09-16, per area, with the step-4 checker itself**
(`python3 bin/review/check_test_levels.py <dir>` -- note its glob is NOT
recursive, so it takes the leaf directory holding `test_*.py`; pointing it at an
area root silently reports "0 of 0 compliant", which reads like a pass and is
not one):

| area | compliant | state |
|---|---|---|
| bridge | 72 / 72 | converted |
| converters | 23 / 23 | converted |
| misc | 4 / 4 | converted |
| apbx-xbar | 6 / 6 | converted |
| retro_legacy_blocks | 14 / 14 | converted |
| stream | **17 / 17** | **CONVERTED 2026-09-17 (a33e68181)** |
| **pumice** | **13 / 34** | **NOT converted** |
| rapids | 0 / 17 | stamp still present |

**stream CONVERTED 2026-09-17 (`a33e68181`), 4 / 17 -> 17 / 17.** Thirteen
wrappers plus two TBs; the other four already passed. Both halves landed
together, as this task requires.

*The find that justified it.* `test_stream_core.py` and `test_stream_top.py`
read TEST_LEVEL at COLLECTION time, when no per-cell environment exists, so both
were pinned to their `gate` branch at every REG_LEVEL -- their func and full
configs had never been generated. stream_core's full config selects
`timing_profile: 'mixed'`, which its own comment calls the regression sentinel
for the `axi_write_engine` WLAST/drain bug. That sentinel had never run. Both
generators now take the level as an argument and union across
`reg_level_grid()`, so the axis COMPOSES with each file's existing grid rather
than multiplying it: cells went GATE 221 -> 190, FUNC 315 -> 328, FULL 804 ->
861, and FUNC coverage is preserved or additive everywhere (verified by diffing
loop conditions against HEAD -- every new conditional gates only at GATE).

*Two traps worth recording for the next area.* The checker's helper escape hatch
(`check_test_levels.py:275`) requires BOTH `reg_level_grid` AND `level_env` in
the source; importing only the former leaves the file falling through to
`has_grid()`, which needs an inline REG_LEVEL plus a 'GATE'/'FULL' literal. And
`grid_levels()` reads assignments to the NAME `test_level`, so a runtime depth
read written as `test_level = os.environ.get('TEST_LEVEL', 'gate')` inside a
cocotb body reports as `depth:pinned-grid(gate)` -- rename the local and the
finding clears.

*Step 4 is COMPLETE; step 5 was NOT RUN.* All nine edited files have been
executed since editing, one cell at a time:

| file | runtime evidence |
|---|---|
| `latency_bridge` | num_beats 8 -> 64 across levels, clean builds |
| `regs` | 0 vs 160 vs 400 write/readback checks per level |
| `mon_cfg` | three distinct section banners; aliasing restored to FUNC |
| `mon_classes` | passing cell, 21 s |
| `monbus` | passing cell, 19 s |
| `stream_core` | passing gate cell, 33 s |
| `test_stream_top_advanced` | passing cell, 81 s |
| `test_stream_top` | passing cell, 123 s |
| `performance_profile` | passing cell, 201 s |

Depth genuinely VARIES, not merely labels: `regs` performs 0 / 160 / 400
write/readback checks and `mon_cfg` runs one / two / three sections by level.

NOT obtained: a FULL-level `stream_core` cell (`params17`, 4 channels x 3
transfer sizes x mixed timing), and step 5's clean 861-cell FULL run. NINE
simulator jobs were killed by the harness citing low memory, on a machine
reporting ~175 GB available with ZERO kernel OOM records and no process above
725 MB; several died before their build started. Concurrency, macro-vs-top,
build parallelism, cell count and per-launch machine state were each proposed
and refuted by measurement -- and the "small cells survive" boundary was wrong
too, since 81 s, 123 s and 201 s cells all passed afterwards. No mechanism was
established. Whoever runs step 5 should expect it to be the binding constraint,
not the conversion.

*A green checker is not a passing suite.* During this conversion one misplaced
line -- `self.log` called before `super().__init__()` in `StreamCoreTB` -- broke
EIGHT test files while the checker still read 17/17, because it parses
statically and never executes. It was found by running tests, not by the tool.
Three other self-inflicted defects surfaced the same way: `_run_regs` never
receiving its `test_level`, a NameError from renaming assignments without their
references, and an aliasing cross-check wrongly demoted out of FUNC.


**The previous claim confused "stamp removed" with "converted."** Stream and
pumice no longer carry the `os.environ['TEST_LEVEL']` stamp, which is what a
grep for it shows -- but neither ever got the other half. Zero of stream's 17
wrappers use `reg_level_grid()` or `level_env()`, and the checker reports
`depth:not-exported, depth:never-read` across them. That is the half-state THIS
TASK WARNS ABOUT, in the paragraph it replaced: deleting the stamp alone drops
those tests to the default and quietly shrinks every FULL run. Both areas are
sitting in it now.

**stream is the actionable piece and it is NOT rapids-blocked.** It has zero
open known issues (`known_issues/` holds only `resolved/`), so the
[[feedback_rapids_out_of_scope]] gate does not apply to it. Size: 17 wrappers
(fub 7, macro 5, top 5) plus a `stream_levels.py` modelled on the bridge's, and
7 of its TBs already reference `test_level`, so the depth knobs mostly exist and
need wiring rather than inventing -- the same favourable start `misc`'s
`dma_address_gen` had. The cost is step 5, a clean FULL run for the area.

**rapids remains genuinely blocked:** five active known issues, three of them
data-path (`drain_size_gt1_source_beat_drop`, `sink_data_path`,
`sink_sram_control`, plus `desc_arsize_exceeds_bus_width` and
`char_harness_sink_selfcheck_no_beats`). Grading depth against a suite that
drops beats would be meaningless.

*Original text, true when written 2026-09-10: every area except the bridge
reported `depth:not-exported` on nearly every test -- their wrappers export
nothing, so the stamp was the ONLY thing mapping REG_LEVEL onto a depth.
Deleting it alone would drop those tests to the default and quietly shrink every
FULL run, which is the failure its own comment was written to prevent (pumice
fub, 91 tests -> 79).*

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


## TOOL-019: delta's lint runs, passes, and gates nothing

**Priority:** P3
**Status:** 🔴 Not Started
**Owner:** TBD

The last area still on the old per-file lint template. `make lint-delta`
exits 0 always, because the recipe lints each `.sv` individually and ends
every invocation with `|| true`:

    verilator --lint-only ... $file > lint_reports/... 2>&1 || true; \
    verible-verilog-lint ... $file > lint_reports/... 2>&1 || true; \

Three `|| true` remain in `projects/components/delta/rtl/Makefile`; every
other area has zero. It also never elaborates -- no `--top-module`, no
filelist -- so it would not catch what the same defect hid in misc
(axi4_slave_rom could not elaborate at its own defaults; see [[TOOL-017]]).

**Why it was left out of TOOL-017.** The fix applied everywhere else was a
four-line `rtl/make/area.mk` include plus `filelists/<area>_all.f`. delta has
**one** `.sv` (`delta_axis_flat_4x16.sv`), **zero** filelists, and no entry in
`bin/filelists.toml`, so converting it means inventing both a filelist and a
registry area for a single-module stub. That is a judgement call about an area
that may not warrant one, not a mechanical conversion, so it was filed rather
than guessed at.

delta is not in `COMPONENTS`, so `make -C projects/components lint-all` does
not cover it; only the top-level `lint-delta` / `lint-projects` do. Its shell
syntax error (empty `$(call print_*)`) WAS fixed under TOOL-017 -- it surfaced
the moment the masking `|| true` came off the top-level target -- so the target
runs today. It just does not gate.

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
