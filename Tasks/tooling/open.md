<!-- Managed by the `tasks` convention: see /Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — open (not started)

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

### TOOL-008: Redo the Makefiles from scratch
**Priority:** P1
**Status:** 🔴 Not Started — spec re-captured from Sean 2026-07-23 (see below)
**Owner:** Sean (spec) / TBD (implementation)

**History.** Sean wrote an extensive design for this. That document was never
committed here and did not survive the workstation loss on 2026-07-23 — not in
the tree, not in any local or remote branch, not in reflog/stash/dangling
objects, not in any surviving session transcript. A prior session promised to
file this task and did not. The requirements below were **re-dictated by Sean on
2026-07-23** after the loss; they are his words paraphrased, not reconstructed by
inference. If the original doc resurfaces, reconcile against it — it was longer
than this.

---

#### R1 — Every Makefile figures out its own thread count. No hardcoded numbers.

**This is the requirement that killed a machine.** The hardcoded worker counts
assume a big host; on a smaller one they oversubscribe until it dies. Sean had
to hard-kill the workstation on 2026-07-23 because of this.

Measured 2026-07-23 (host `nproc` = **8**):
- **`-n 48` is hardcoded in 28 files.** `test_targets.mk` alone has **70**
  occurrences; `env_python` has 2; each of `val/{amba,common,integ_amba,
  integ_common}/Makefile` and ~20 `projects/**/dv/tests/**/Makefile` have 1-2.
  On this 8-core box that is a **6x oversubscription** by default.
- Other files pick different numbers with no rationale: `-n 24`, `-n 2`,
  `PYTEST_WORKERS := 8` (stream `performance_tests/Makefile`).
- Exactly **one** place does it right and nothing else copies it:
  `projects/components/Makefile:58-59` —
  `FAST_JOBS ?= 4` / `FAST_WORKERS ?= $(shell echo $$(( $$(nproc) / $(FAST_JOBS) )))`.
- The number is also baked into non-Makefile files that must be swept with them:
  `bin/aggregate_test_results.py`, and the docs
  `docs/handbook/dv/test-runner.md` (2), `projects/components/MAKEFILE_GUIDE.md`,
  `projects/components/MAKEFILE_HIERARCHY.md`.

Derive from `nproc` in ONE place, overridable by env var. Remember these are
Verilator sims — each worker is a compile+sim process, so the right divisor is
not necessarily 1-per-core; whatever the rule is, it lives in the master
Makefile and nowhere else.

#### R2 — One consistent target grammar, everywhere.

```
make run-<all|testroot>-<gate|func|full>-<serial|parallel>
```

- **testroot** is the test file with `test_` and `.py` stripped:
  `test_grey2bin.py` → `make run-grey2bin-func-parallel`.
- `all` means every test in scope for the Makefile you are standing in.
- Today the targets are hand-written and combinatorial instead —
  `val/amba/Makefile` is **2074 lines / 229 targets**, `val/common/Makefile`
  **1245 / 131**, root `Makefile` **976 / 83**, `projects/components/Makefile`
  **613 / 35**. Adding a module means hand-editing several targets across
  several files and nothing checks that you did.

**Open question for Sean:** the dictated grammar ended
`-<serial|parallel>-<serial|parallel>` — the same axis twice. Assumed a typo and
recorded once. If it was intentional (e.g. an outer dir-level axis and an inner
pytest-level axis, which the existing `PARALLEL_DIRS` in the stream/rapids
Makefiles hints at), say so and this gets corrected before implementation.

#### R3 — Discover tests by globbing. Do not enumerate them.

Targets are generated from globbing `test_*.py`, so a new test is runnable the
moment it lands. This is what makes R2 maintainable and kills the combinatorial
hand-written target lists.

#### R4 — One master Makefile; every other Makefile is ~4 lines.

All logic lives in the master (include/`.mk`). A leaf `Makefile` in
`val/common/`, `projects/**/dv/tests/fub/`, `macro/`, `top/` etc. sets its few
locals and includes the master. Today those leaf Makefiles are "completely
different" from each other across `common/`, `amba/`, and the `projects/` areas
— same job, divergent implementations, which is how the thread handling drifted
in the first place.

---

**Measured state of the problem (2026-07-23), as the starting evidence:**
- **124 Makefiles** in the repo (excluding `venv/`): 36 under
  `projects/components/`, 18 under `projects/NexysA7/`, 60 under `formal/`,
  5 under `val/`, plus the 3-tier roots.
- The regression Makefiles are **enormous and hand-maintained** — line/target
  counts under R2 above.
- The hand-written target set is combinatorial — every protocol crossed with
  `-parallel`, `-gate`, `-func`, `-full`, plus per-module variants
  (`run-apb5-master`, `run-apb5-slave`, `run-apb5-monitor`, `run-apb5-cg`,
  `run-apb5-cdc`, `run-apb5-stub`, ...). This is exactly what R2+R3 replace.
- The `fub/` / `macro/` / `top/` split repeats across `dmas/stream`,
  `dmas/rapids`, `pumice`, `misc`, `timing_characterization` — each with its own
  divergent Makefile doing the same job. These are the R4 four-liners.
- The existing three-tier description lives in
  `projects/components/MAKEFILE_HIERARCHY.md` and `MAKEFILE_GUIDE.md`
  (both dated 2025-10-24, pre-dmas-reorg). Per the handbook rule these are
  methodology living next to code and should end up as handbook notes —
  coordinate with TOOL-002.

**Related work already tracked, do not duplicate:**
- TOOL-003 wants a gate running `filelist_registry --check/--audit`; a Makefile
  rewrite is the natural home for it, since the filelists are what a
  regenerated target set would key off.
- [[test-runner]] and [[running-regressions]] document the current
  Makefile → pytest → cocotb_test.run → Verilator stack and the
  `REG_LEVEL` vs `TEST_LEVEL` distinction. Any rewrite must keep those
  semantics or update both notes in the same change.
