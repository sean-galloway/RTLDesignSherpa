<!-- Managed by the `tasks` convention: see /Tasks/INDEX.md. -->

# AMBA tasks

Canonical task tracker for `rtl/amba/` (AXI4/AXI5, APB, AXI-Stream, the
monitor subsystem, monbus). Migrated 2026-07-22 from `rtl/amba/PRD/TASKS.md`.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 3 | in progress right now |
| [open.md](open.md) | 4 | accepted, not started |
| [closed.md](closed.md) | 18 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing (won't do / superseded) |

## Active

- **TASK-023** — Complete RTLAmba documentation + waveform integration (P0)
- **TASK-013** — Integration examples (~90%)
- **TASK-025** — Update formal proofs for the monitor logic (12/12 infra green;
  perfmon / cam_clear / cone-drop properties still pending)

## Open

- **TASK-014** — Performance characterization
- **TASK-015** — Address range + ID filtering
- **TASK-022** — Make APB crossbar variants functional
- **TASK-024** — Monitor system whitepaper (P3)

## Lifecycle

A task moves `open → active → closed` (done) — or to `dropped` if it ends
without completing — by **cutting** its `### TASK-NNN` block from one page and
pasting it into the next; never copy, or the same task lives in two states.
Each block keeps its `**Status:**` line updated with the date (and, when
dropped, a one-line reason). New AMBA tasks get the next `TASK-NNN` number and
start in `open.md` (or `active.md` if you're starting immediately).

## Related

- Enforcement authority: [/GLOBAL_REQUIREMENTS.md](../../GLOBAL_REQUIREMENTS.md)
- Subsystem: [rtl/amba/CLAUDE.md](../../rtl/amba/CLAUDE.md),
  [rtl/amba/PRD/PRD-AMBA.md](../../rtl/amba/PRD/PRD-AMBA.md),
  [rtl/amba/KNOWN_ISSUES/](../../rtl/amba/KNOWN_ISSUES/)
- Standing plans kept as their own docs: `rtl/amba/PRD/TASK-008-*`,
  `TASK-016-*` (implementation notes, not lifecycle items)
