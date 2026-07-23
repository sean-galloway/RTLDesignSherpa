<!-- Managed by the `tasks` convention: see /Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# Tooling tasks — active (in progress)

### TOOL-001: Migrate the remaining areas into /Tasks/<area>/
**Priority:** P2
**Status:** 🟡 In Progress (2026-07-22) — amba pilot done; 13 areas pending.
**Owner:** Claude (assist) / Sean (review)

**Goal:** Move every remaining per-component TASKS.md / TODO.md into the central
`/Tasks/<area>/` structure so all project status is visible from one place, and
retire the scattered files. Use the `tasks` skill's "Migrating an area"
procedure for each so they all come out identical.

**Areas still pending** (tracked at their old files until moved):
- [x] common — rtl/common/TASKS.md (DONE 2026-07-23 -> Tasks/common/)
- [ ] stream — dmas/stream/TASKS.md + TODO_RFC_StageE_datapath_perfmon.md
- [ ] rapids — dmas/rapids/TASKS.md + docs/rapids_beats_mas/TODO.md
- [ ] bridge — bridge/TASKS.md
- [ ] bch — bch/TASKS.md
- [ ] delta — delta/TASKS.md
- [ ] hive — hive/TASKS.md
- [ ] retro-legacy — retro_legacy_blocks/TASKS.md + rtl/{ioapic,pm_acpi,smbus}/TODO.md
- [ ] memory-controllers — ddr3-lpddr3 / ddr4-lpddr4 TASKS.md (pumice DONE 2026-07-23 -> Tasks/pumice/)
- [ ] nexysa7 — timing_characterization/TASKS.md + cdc_counter_display CDC_DEMO_TODO.md
- [ ] formal — formal/FORMAL_TODO.md
- [ ] coverage — val/COVERAGE_TODO.md
- [ ] tooling — TOOLING_TODO.md (this area's own backlog; migrate alongside)

**Per area (see `tasks` skill):** fence-aware split of the source into task
blocks → classify open/active/closed/dropped by REAL repo state (not the stale
Status marker) → write INDEX + the four pages → repoint inbound refs → delete
originals → verify block count + links against the original.

**Open decisions to confirm with Sean before starting the batch:**
1. Is open/active/closed/dropped the right lifecycle split?
2. Area granularity: group the 3 memory-controllers vs split; retro-legacy
   sub-blocks (ioapic/pm_acpi/smbus) as one area vs several?

---

### TOOL-008: Redo the Makefiles from scratch
**Priority:** P1
**Status:** 🟡 In Progress (2026-07-23) — proof of concept built, **awaiting
Sean's full validation run before anything is pushed or swapped in**
**Owner:** Sean (spec + validation) / Claude (implementation)

**Proof of concept, 2026-07-23 — not yet validated by a real regression:**
- `make/tests.mk` — the master. ~180 lines carrying all logic.
- `val/amba/Makefile.poc` — the four-line leaf, deliberately named `.poc` so the
  existing 2074-line `val/amba/Makefile` keeps working untouched. Run it with
  `make -f Makefile.poc <target>`.

Structurally verified: worker count derives to **7** on an 8-core/15 GB box
(was a hardcoded 48); **119** test roots discovered by glob; **2160** targets
generated (120 selectors x 3 levels x 6 variants); serial emits no `-n`,
parallel emits `-n 7 --dist=loadgroup`, waves prepends `WAVES=1`.

**NOT yet verified: a green end-to-end test run through the new path.** Nothing
here may be swapped in, and TOOL-008 may not close, until Sean has run the full
suite through it. Structural verification is not a passing regression — see
[[running-regressions]] on how a run gets more optimistic than the code
deserves.

**Worker-count rule as implemented:** `JOBS = min(nproc, MemTotalGB /
GB_PER_WORKER)`, `GB_PER_WORKER ?= 2`, both overridable
(`make JOBS=16 ...`). The memory ceiling is deliberate and is the one that
would actually have prevented the machine death — Verilator elaboration is
RAM-hungry and swap is what makes a box stop responding; a cores-only rule
would not have caught it. Open to being reduced to cores-only if Sean prefers.

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
make run-<all|testroot>-<gate|func|full>[-serial|-parallel][-waves]
```

- **testroot** is the test file with `test_` and `.py` stripped:
  `test_grey2bin.py` → `make run-grey2bin-func`.
- `all` means every test in scope for the Makefile you are standing in.
- **The mode and waves suffixes are OPTIONAL** (Sean, 2026-07-23: "serial is
  optional like waves"). Bare `run-<x>-<level>` is parallel without waves, so
  the common case types shortest. This also resolves the earlier open question
  about the dictated grammar ending in the serial|parallel axis twice — it is
  one optional mode suffix plus one optional waves suffix, matching the
  `-gate` / `-gate-waves` / `-gate-serial` shape `test_targets.mk` already uses.
- Six variants per level, all generated, none enumerated: bare, `-parallel`,
  `-serial`, `-waves`, `-parallel-waves`, `-serial-waves`.
- Today the targets are hand-written and combinatorial instead —
  `val/amba/Makefile` is **2074 lines / 229 targets**, `val/common/Makefile`
  **1245 / 131**, root `Makefile` **976 / 83**, `projects/components/Makefile`
  **613 / 35**. Adding a module means hand-editing several targets across
  several files and nothing checks that you did.

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

---

### TOOL-009: Python version mismatch breaks EVERY Verilator build on this box
**Priority:** P0 — blocks all simulation, and blocks TOOL-008 validation
**Status:** 🟡 Diagnosed 2026-07-23, root-caused and reproduced; fix not applied
**Owner:** Sean (decide the fix) / Claude (apply)

**Symptom:** every test fails at link time with
`undefined reference to Vtop::Vtop(char const*)`. Not an RTL or testbench
problem, and **not** caused by the TOOL-008 Makefile rewrite — it reproduces
under raw `pytest` with no make involved at all.

**The chain, each link verified by execution:**

1. `/usr/bin/python3` is a symlink to **python3.10** (3.10.12).
2. The venv was built from `/usr/bin/python3.11`, which on this box is
   **3.11.0rc1** — a release candidate, not a release (`venv/pyvenv.cfg`).
3. `cocotb_test/simulator.py:215` sets `PYTHONHOME = sysconfig prefix` for the
   simulator subprocess. Inside a venv that is the **venv** prefix (3.11).
4. Verilator's `share/verilator/include/verilated.mk:20` hardcodes
   `PYTHON3 = /usr/bin/python3` — baked in when Verilator was configured, so it
   is **3.10**.
5. Building `Vtop__ALL.cpp` runs that 3.10 interpreter with `PYTHONHOME`
   pointing at a 3.11 stdlib. It dies:
   `AssertionError: SRE module mismatch` (from `import re`).
6. The recipe is `... $^ > $@`, so the shell has **already truncated**
   `Vtop__ALL.cpp` before the interpreter fails. Result: a **zero-byte**
   amalgamation.
7. Empty `.cpp` -> 824-byte `Vtop__ALL.o` -> archive with no `Vtop` symbols ->
   the link errors above.

**Proof of the fix:** `make -f Vtop.mk PYTHON3=<venv>/bin/python3 Vtop__ALL.cpp`
produces a correct 522-byte file, and `test_amba_clock_gate_ctrl` then
**passes**. Nothing else was changed.

**Why it looks like a flaky/stale-build problem and is not.** `--reruns 3` and
xdist retries re-enter the same broken build dir and fail identically — the
five `*_results.xml` files in one `local_sim_build/` dir are that. `clean-all`
does not help: a fresh dir reproduces it 2/2. Do not chase this as a stale
artifact; see [[running-regressions]].

**Fix options, in preference order:**
- [ ] **Rebuild the venv on the interpreter `/usr/bin/python3` resolves to**
      (3.10.12), so `PYTHONHOME` and Verilator's hardcoded `PYTHON3` agree.
      Robust, survives a Verilator reinstall, no root needed. Confirm nothing
      in the stack actually requires 3.11 first.
- [ ] Or repoint `/usr/bin/python3` at 3.11 — needs root and changes system
      behaviour for everything else on the box.
- [ ] Or patch `verilated.mk:20` to `PYTHON3 ?= /usr/bin/python3` and export
      `PYTHON3` from `env_python` (make lets the environment win over `?=`).
      Cheapest, but it edits a file under `~/tools` that a Verilator reinstall
      silently reverts — if chosen, `bin/install_tools.sh` must apply it.

**Do not build a venv on a release candidate.** 3.11.0rc1 should not be the
base for anything; whichever option is chosen, pin a released interpreter.
Belongs with TOOL-004 — this is exactly the class of gap "validate the
bootstrap on a genuinely clean box" exists to catch, and the rebuilt
workstation shipped it.
