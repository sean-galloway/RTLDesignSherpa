<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# scoria-ddr3-lpddr3 — tasks

**Next ID: TASK-004** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — advanced scheduling / refresh modes survey.

- **TASK-003** — decide the fate of `scoria_powerdown_ctrl` and
  `scoria_dfi_signal_pack`: complete modules that nothing instantiates, so the
  tree implies power-down support the controller does not have.

- **TASK-002** (ACTIVE) — author the scoria HAS. v0.1 is written; the PRD stub says it
  is waiting on a locked HAS. Starts from `docs/design-requirements.md`, the delta
  analysis against JESD79-3F / JESD209-3C / DFI v3.1, and closes when the three open
  decisions in it (DFI revision, write-leveling ownership, package split) are settled
