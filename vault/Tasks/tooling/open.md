<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — open (not started)

### TOOL-012: Burn down --blindspots, then make it a gate
**Priority:** P2
**Status:** open 2026-07-26 (measured at `0928fb0b`)

`filelist_registry.py --blindspots` exists now and reports **516 findings**. The
check is the easy part; this task is the backlog it revealed and the gate that
keeps it at zero.

| n | class | shape of the fix |
|---|---|---|
| 387 | `.sby` harnesses with dead source paths, across 149 files | nearly all math-split fallout. Generate `[script]`/`[files]` from the area's filelist, as the four `apb*_slave_cdc` harnesses now are (`6eab2377`) |
| 128 | tests building their own `verilog_sources` array | swap to `get_sources_from_filelist`. Three of these were silently BROKEN when found, so treat each as suspect, not cosmetic |
| 1 | unregistered filelist: `ddr2_char_macro.f` | one line in `filelists.toml`, same as `flows-stream-monitor` in `50e4335d`. It is a real module (wraps the AXI4 char engines + pumice controller) |

**Why this matters more than the count suggests.** Every one of these is a place
where `--check` and `--audit` report PASS over something they cannot see. That
is exactly how `rtl/cdc` sat uncovered, how three wavedrom tests stayed broken
for a day, and how four formal harnesses went without `gaxi_fifo_async` and its
whole dependency tree.

**Order:** the 128 tests first — they are the class that hides *broken* things,
not merely uncovered ones. The 387 harness paths are one mechanical pass over
`formal/common/math_*` once someone confirms where the math sources moved.

**Then gate it.** Nothing runs `--check`, `--audit` or `--blindspots` today, in
a hook or in CI, which is the root cause of all of the above. Wire all three in
together once `--blindspots` reaches zero; gating on a check that already fails
teaches people to skip it. See [[filelists]].

---

### TOOL-002: Migrate the remaining method docs out of bin/ into the handbook
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

### TOOL-003: One gate that runs filelist_registry --check and --audit
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

### TOOL-004: Finish validating the cloud bootstrap on a genuinely clean box
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

### TOOL-005: env_python hardcodes /mnt/data/tools
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

### TOOL-006: Triage the 18 Dependabot vulnerabilities on the default branch
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

### TOOL-007: Two real gaps in the RDS-DV arbiter BFM
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

### TOOL-010: Project-area cleanup — apply the RTL-area pattern to projects/
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
- [ ] **retro_legacy_blocks** — loose `rtl/rlb_top/rlb_top.f`,
      `rtl/apb_xbar/apb_xbar_rlb_1to10.f` → `filelists/` subdirs
- [ ] **ddr2_char** (NexysA7) — loose `rtl/ddr2_char_macro.f` → `filelists/`;
      the `dv/` harness `.f` get a `filelists/` dir WITH the TB
- [ ] **pumice** — `dv/tb/*_tb_top.f` → a `filelists/` dir with the TB.
      **⚠️ PUMICE PUSHES FROM SEAN'S WORKSTATION, not this environment**
      (Sean, 2026-07-24) — make the pumice changes but do NOT push them; Sean
      pushes pumice from the workstation. See Tasks/pumice.
- [ ] the remaining components (converters, delta, hive, misc, apb_xbar,
      dmas/{stream,rapids}, memory-controllers/{ddr3,ddr4}) get the same
      treatment as they are reached.

**Gate:** RTL area first (Tasks/INDEX.md sequencing). Do not start until the
cdc reorg + amba cleanup land.

---

### TOOL-011: Tests resolve filelists through the toml registry, not hardcoded paths
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
