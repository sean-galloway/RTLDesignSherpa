<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/riscv-ip/common-rv32i — tasks

**Next ID: TASK-004** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

- **TASK-003** — the `bin/apps/core_drills` app: design doc accepted 2026-11-28 (all decisions as recommended); building merlin modes 1-2 and peregrine's predictor drill (mode 3)

## Closed

- **TASK-001** — rv32i_alu: one adder and one shifter (ISSUE-001 row 1); -205..-306 LUT per core, suites and riscv-formal green
- **TASK-002** — riscv-arch-test 3.10.0 rv32i_m/I signatures against spike on kestrel, merlin and gatling (39/39, 39/39, 156/156); shared harness in dv/arch_test
