<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# Tooling tasks

**Next ID: TOOL-015** — never recycle a number, even when its task closed.

Repo tooling, scripts, and process work.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 2 | in progress right now |
| [open.md](open.md) | 10 | accepted, not started |
| [closed.md](closed.md) | 2 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

## Active

- **TOOL-008** (P1) — redo the Makefiles from scratch. Live in `val/amba`
  (`make/tests.mk` + four-line `val/amba/Makefile`): worker count derived
  from cores and RAM (was a hardcoded 48 on an 8-core box — this killed a
  machine), glob-discovered tests, 2160 targets from ~180 lines. **Blocked on
  Sean's full validation run** — nothing swapped in or pushed until then.
- **TOOL-001** — Migrate the remaining areas into /vault/Tasks/<area>/ (amba pilot,
  pumice, common and docs-review done; awaiting Sean's sign-off on lifecycle
  split + area granularity for the batch).

## Open

- **TOOL-003** — one gate that actually runs `filelist_registry --check`.
  Shared deliverable for COMMON-010 / AMBA TASK-026; today nothing runs it.
- **TOOL-002** — migrate the 7 remaining method docs out of `bin/` into the
  handbook, per the single-source-of-truth rule in CLAUDE.md.
- **TOOL-004** — finish validating the cloud bootstrap: the oss-cad-suite
  download path and a clean-box run have never executed.
- **TOOL-006** — triage the 18 Dependabot vulnerabilities on `main`.
- **TOOL-005** — `env_python` hardcodes `/mnt/data/tools`; make the prefix a
  variable so the PATH ordering is not the user's problem.
- **TOOL-007** — two RDS-DV arbiter-BFM gaps: a stubbed round-robin compliance
  check and no saturating profile. Together they let a starving arbiter pass.
- **TOOL-010** — project-area cleanup: apply the RTL-area pattern to
  `projects/`. Sequenced behind the RTL-area work per the master Tasks INDEX.
- **TOOL-011** — tests resolve filelists through the toml registry, not
  hardcoded paths.
- **TOOL-012** — burn down `--blindspots`, then make it a gate.
- **TOOL-014** — Scripts book link rot + DOCUMENTATION_INDEX refresh/retire.

## Note

This area's historical backlog (/TOOLING_TODO.md) was folded in and the file
deleted 2026-08-09: item 1 (kmap promote to bin/) was already subsumed by
TOOLING-KMAP step 5, item 2 (skills strategy) closed as TOOL-013, item 3
(Scripts link rot) opened as TOOL-014.
