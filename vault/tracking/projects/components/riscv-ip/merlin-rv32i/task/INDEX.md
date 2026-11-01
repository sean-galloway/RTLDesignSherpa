<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/riscv-ip/merlin-rv32i — tasks

**Next ID: TASK-003** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-002** — follow-ups from the TASK-001 final review (hazard idex_rd_wen doc, unit-test symmetry cases, docstring nits, MERLIN_ROOT into formal_flat.mk)

(none)

## Active

(none)

## Closed

- **TASK-001** — implement merlin per PRD v0.2 (5-stage pipelined RV32I:
  pipeline registers, hazard/forwarding unit, EX branch resolve + flush;
  rv32ui + directed hazard suite + spike lockstep + riscv-formal retire).
  Outcome: core/DV/formal green, GTKW verified, HAS/MAS skeletons committed.
  Commit range: Task 1 through Task 7.
