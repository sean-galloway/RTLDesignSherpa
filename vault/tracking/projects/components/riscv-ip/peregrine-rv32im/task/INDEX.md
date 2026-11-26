<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/riscv-ip/peregrine-rv32im — tasks

**Next ID: TASK-007** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-004** — hive HIVE-C `CORE_FLAVOR=peregrine` swap, peregrine's system bring-up (PRD §7 item 6, hive PRD §10.3).
- **TASK-005** — bus error handling: load/store access faults on AXI SLVERR/DECERR from the uncached port and amber (PRD §3/§4.3, amended to not built 2026-11-25); not scheduled.

## Active

(none)

## Closed

- **TASK-006** — 75 MHz (owner floor 2026-11-26): `peregrine_top` closes 13.333 ns on xc7a100t-1 (+0.300 `MUL_DSP=0`, +0.099 `MUL_DSP=1`, 0.2 ns uncertainty in). No load forwarded WB->EX (+6.4% kernel CPI), registered interrupt decision, three amber `l1_control` timing changes. Closed 2026-11-26.
- **TASK-003** — the peregrine book *Simplified RV32IM: peregrine -- speculation and traps* v0.1 (78 pp). Closed 2026-11-25; drill mode 3 moved to riscv-ip/common-rv32i TASK-003.
- **TASK-002** — `peregrine_has` and `peregrine_mas` books v0.1 (HAS 121 pp, MAS 197 pp), as built. Closed 2026-11-25; the PRD mismatches they found were amended, error handling filed as TASK-005.
- **TASK-001** — peregrine RV32IM core: RTL, DV and targeted formal per PRD 0.2. Closed 2026-11-25: all seven stages done; amber is the D$, 18.5 ns (54.1 MHz) on xc7a100t-1, riscv-formal 52/52 on both `MUL_DSP` builds, targeted core/top properties, a bounded M-unit reference proof.
