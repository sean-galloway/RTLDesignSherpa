<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/riscv-ip/peregrine-rv32im — tasks

**Next ID: TASK-008** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 6 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open


## Active


## Closed

- **TASK-007** — interruptible M instructions: cancel in flight, one instruction of progress after `mret` (from ISSUE-001, owner 2026-11-27). Closed 2026-11-27: latency bound 40 cycles (measured 38, was up to 271 behind 8 divides), FULL 100/100, riscv-formal 52/52 both builds, 75 MHz +0.273 / +0.466.
- **TASK-005** — bus error handling: load/store/instruction access faults on AXI SLVERR/DECERR (uncached port, amber fill, I$ fill), a failed dirty write-back as platform interrupt 16 with CSR `mbuserr` (0x7C0), and a parameterized uncached window (owner decisions 2026-11-27). Loads and stores fault at WB, precise (owner 2026-11-27). Closed 2026-11-27; amber's part is cache-ip/amber-mesi-l1 TASK-008.
- **TASK-006** — 75 MHz (owner floor 2026-11-26): `peregrine_top` closes 13.333 ns on xc7a100t-1 (+0.300 `MUL_DSP=0`, +0.099 `MUL_DSP=1`, 0.2 ns uncertainty in). No load forwarded WB->EX (+6.4% kernel CPI), registered interrupt decision, three amber `l1_control` timing changes. Closed 2026-11-26.
- **TASK-003** — the peregrine book *Simplified RV32IM: peregrine -- speculation and traps* v0.1 (78 pp). Closed 2026-11-25; drill mode 3 moved to riscv-ip/common-rv32i TASK-003.
- **TASK-002** — `peregrine_has` and `peregrine_mas` books v0.1 (HAS 121 pp, MAS 197 pp), as built. Closed 2026-11-25; the PRD mismatches they found were amended, error handling filed as TASK-005.
- **TASK-001** — peregrine RV32IM core: RTL, DV and targeted formal per PRD 0.2. Closed 2026-11-25: all seven stages done; amber is the D$, 18.5 ns (54.1 MHz) on xc7a100t-1, riscv-formal 52/52 on both `MUL_DSP` builds, targeted core/top properties, a bounded M-unit reference proof.

## Dropped

- **TASK-004** — moved to compute-eng-ip/hive TASK-001 (owner 2026-11-27).
