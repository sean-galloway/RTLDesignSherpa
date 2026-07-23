<!-- Managed by the `tasks` convention: see /Tasks/INDEX.md. -->

# Tooling tasks

Repo tooling, scripts, and process work.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 1 | in progress right now |
| [open.md](open.md) | 5 | accepted, not started |
| [closed.md](closed.md) | 0 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

## Active

- **TOOL-001** — Migrate the remaining areas into /Tasks/<area>/ (amba pilot,
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

## Note

This area's own historical backlog still lives in
[/TOOLING_TODO.md](../../TOOLING_TODO.md) and migrates here as part of TOOL-001.
