<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/riscv-ip/common-rv32i — issues

**Next ID: ISSUE-002** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed: it resolves INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

(none)

## Closed

- **ISSUE-001** — riscv-ip FPGA microarchitecture review (2026-11-18, closed 2026-11-21): ALU one adder + one shifter (common-rv32i TASK-001), merlin control-only resets + registered forwarding selects + load-to-branch interlock (merlin-rv32i TASK-003, TASK-004), gatling PC file in LUTRAM (gatling-rv32i TASK-004), kestrel board 75 -> 80 MHz with the 0.2 ns budget in the XDC; report in assets/issue001_fpga_uarch/
