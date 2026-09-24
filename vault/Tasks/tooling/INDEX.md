<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# Tooling tasks

**Next ID: TOOL-021** — never recycle a number, even when its task closed.

Repo tooling, scripts, and process work.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 1 | in progress right now |
| [open.md](open.md) | 7 | accepted, not started |
| [closed.md](closed.md) | 14 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

## Active

- **TOOL-001** — Migrate the remaining areas into /vault/Tasks/<area>/ (amba pilot,
  pumice, common and docs-review done; awaiting Sean's sign-off on lifecycle
  split + area granularity for the batch).

## Open

- **TOOL-016** (P2) — twelve component conftests stamp `TEST_LEVEL` into
  `os.environ`; cocotb_test lets the environment override `extra_env`, so
  every cell of a leveled run executes at REG_LEVEL's depth. Bridge fixed;
  misc, rlb, apbx-xbar, converters, rapids, pumice remain.
- **TOOL-004** — finish validating the cloud bootstrap: the oss-cad-suite
  download path and a clean-box run have never executed.
- **TOOL-007** — two RDS-DV arbiter-BFM gaps: a stubbed round-robin compliance
  check and no saturating profile. Together they let a starving arbiter pass.
- **TOOL-010** — project-area cleanup: apply the RTL-area pattern to
  `projects/`. Sequenced behind the RTL-area work per the master Tasks INDEX.
- **TOOL-011** — tests resolve filelists through the toml registry, not
  hardcoded paths.
- **TOOLING-KMAP** — emit contract tables (term list, invariants, decision
  table) rather than K-map pictures; add an invariant checker.
- **VAL-XDIST-INTERMITTENT** — root cause proven (concurrent deletion of
  `local_sim_build`); open on adoption: nothing sets `SIM_BUILD_ROOT` and the
  `.sim_busy` markers are advisory.

## Note

This area's historical backlog (/TOOLING_TODO.md) was folded in and the file
deleted 2026-08-09: item 1 (kmap promote to bin/) was already subsumed by
TOOLING-KMAP step 5, item 2 (skills strategy) closed as TOOL-013, item 3
(Scripts link rot) opened as TOOL-014.

## Closed

- **TOOL-008** (P1) — Makefiles redone: one `make/tests.mk`, four-line leaves,
  host-derived worker count, glob-discovered targets. Closed 2026-09-20 after an
  861-cell FULL regression through the new path. Two items carried forward in
  the entry: the stream-bridges and pumice Makefiles, and a coverage-tuning
  decision (`GB_PER_WORKER=4` vs the retired `coverage_workers`).
