# TASK-009: Redo the Makefiles from scratch

> Migrated 2026-09-27 from `vault/Tasks/tooling/closed.md` as **TOOL-008** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P1
**Status:** Closed 2026-09-20 — Sean signed off. R1-R4 all hold, validated
by real regressions, not by structure.

**Closed with two items carried forward, deliberately not buried:**
1. `Genesys2/stream/rtl/bridges/dv/tests/Makefile` (3 hardcoded `-n`) and the
   pumice `dv/tests` Makefiles were outside this sweep. Neither is a defect in
   what landed; both need the same four-line treatment when their owners get
   to them.
2. c74e22c76 stopped reading `coverage_workers` (24) and `coverage_reruns`
   (5/2), so a coverage run now uses the derived width with 3 reruns. The
   intent was memory headroom during instrumented runs; `GB_PER_WORKER=4`
   restores it host-aware rather than pinning a number. Seven other toml keys
   are now read by nothing. **Still an open decision** — tracked here rather
   than lost, because the task that created it is closing.
**Owner:** Sean (spec + validation) / Claude (implementation)

**Where it actually stands (2026-09-18).** The proof of concept this entry used
to describe is gone: there is no `Makefile.poc` anywhere, and `val/amba/Makefile`
is the 5-line leaf (the 2074-line original is retired). `make/tests.mk` is live
at 312 lines and **26 Makefiles** include it across `val/`, `projects/components/`,
`projects/fpga-systems/` and `projects/asic-trials/`.

| requirement | state |
|---|---|
| R1 derive the thread count | DONE — `JOBS = min(nproc, MemGB/GB_PER_WORKER)`; derived **48** on a 48-core/188 GB host, **7** on the 8-core box |
| R2 one target grammar | DONE — `run-<all\|testglob>-<gate\|func\|full>[-serial\|-parallel][-waves]`, generated not enumerated |
| R3 discover by glob | DONE — `TESTS := $(sort $(wildcard test_*.py))`; a new test is runnable the moment it lands |
| R4 one master, 4-line leaves | DONE — leaves are 4-5 lines; `val/Makefile`, `projects/components/Makefile` and the per-component dispatchers forward and carry no test logic |

**The blocker this entry named is satisfied — by runs, not by structure.**
A whole-area FULL regression went through `clean-all` + `run-all-full-parallel`
on 2026-09-18: 861 cells, `fub` 123 passed, `macro` 680 passed + 3 skipped,
`top` 52 passed + 3 xfailed. And `make test-val-common-gate` — a generated
target — ran 77 passed in 37 s through the delegated path.

**The last R1 hole was the generated targets themselves** (c74e22c76).
`test_targets.mk` hand-built `cd <dir> && pytest ... -n 48 test_*.py` for every
environment, re-implementing tests.mk and pinning the worker count. The
generator now emits `$(MAKE) -C <dir> run-all-<level>-<mode>`: 113 target names
unchanged, hardcoded `-n` 59 -> 0, raw `cd` recipes 93 -> 0, delegations 8 -> 101.

**What is left, and why it is not closed:**
1. Sean's sign-off — the Done-when is his validation, not a session's.
2. Two areas outside this sweep: `Genesys2/stream/rtl/bridges/dv/tests/Makefile`
   (3 hardcoded `-n`, stream is owned elsewhere) and the pumice `dv/tests`
   Makefiles (skipped by standing instruction).
3. A decision c74e22c76 forces: delegation stopped reading `coverage_workers`
   (24) and `coverage_reruns` (5/2), so coverage now runs at the derived width
   with 3 reruns. The intent was memory headroom during instrumented runs.
   `GB_PER_WORKER=4` would restore it host-aware rather than pinning 24.
   Seven other toml keys (`pytest_flags`, `test_pattern`, `reruns`,
   `reruns_delay`, `coverage_extra_env`, ...) are now read by nothing; their
   values are reproduced by tests.mk, which is why delegating was safe, but
   unread config rots and should be deleted once (3) is decided.

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

### R1 — Every Makefile figures out its own thread count. No hardcoded numbers.

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
  `vault/handbook/dv/test-runner.md` (2), `projects/components/MAKEFILE_GUIDE.md`,
  `projects/components/MAKEFILE_HIERARCHY.md`.

Derive from `nproc` in ONE place, overridable by env var. Remember these are
Verilator sims — each worker is a compile+sim process, so the right divisor is
not necessarily 1-per-core; whatever the rule is, it lives in the master
Makefile and nowhere else.

### R2 — One consistent target grammar, everywhere.

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

### R3 — Discover tests by globbing. Do not enumerate them.

Targets are generated from globbing `test_*.py`, so a new test is runnable the
moment it lands. This is what makes R2 maintainable and kills the combinatorial
hand-written target lists.

### R4 — One master Makefile; every other Makefile is ~4 lines.

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
