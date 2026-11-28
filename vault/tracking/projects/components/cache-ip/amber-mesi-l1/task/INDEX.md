<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/amber-mesi-l1 — tasks

**Next ID: TASK-009** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 8 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open


## Active


## Closed

- **TASK-008** — bus error reporting: a failed fill answers the CPU request with an error bit and installs nothing; a failed dirty write-back drops the line and latches its address in a sticky status (`wb_err_*`), behind `BUS_ERR_EN` (default 0). Filed 2026-11-27 from riscv-ip/peregrine-rv32im TASK-005. Closed 2026-11-27.
- **TASK-006** — read fills install E behind `READ_FILL_E` (default 0; peregrine sets 1, as the only coherent master). The fabrics return no IsShared, so the rule is not unconditional. Formal `ap_fill_install_rule`; peregrine kernels -0.08% cycles. Closed 2026-11-26.
- **TASK-007** — amber closes 75 MHz on xc7a100t-1: `amber_top` +0.560 at 13.333 ns (+0.100 at 13.0), `peregrine_top` 13.333 ns; five timing changes in `l1_control` / `l1_snoop_resp`, 1-cycle hit kept. Closed 2026-11-26.
- **TASK-004** — CPU-side clean-all request, for peregrine's `fence.i` (riscv-ip/peregrine-rv32im PRD P10). Closed 2026-11-24: `MAINT_EN=1` maint op, WriteClean walk, response after the last B (da9e8df71); peregrine `fence_i` and `Zifencei` pass at `CACHE_EN=1`.
- **TASK-005** — pipelined hit path on the CPU port, for peregrine's MEM stage (PRD P13 option (b)). Closed 2026-11-24: read hit 1 cycle / issue every cycle, write hit 1 / 2 (was 4 / 3); HIT_RUN_MAX=8 bounds snoop wait to 9; common-ip FULL 255/255, amber FULL 121/121, formal cover/live/safety PASS, OOC WNS +0.342 ns.
- **TASK-003** — Genesys2 Vivado build of the post-restructure amber hierarchy. Closed 2026-11-01: bitstream green, WNS +0.083 ns, 0/404,557 failing endpoints, undriven-net warnings pre-existing; on-board run available on demand.
- **TASK-002** — restructure amber RTL into planes (mem-ctrl doctrine): CPU / coherence-core / fabric planes, ACE isolated as a swappable fabric plane so a CHI plane can replace it later.  Closed 2026-11-01: planes landed, fabric contract doc + CHI stub in place; full regression is the restructure plan's Task 6.
- **TASK-001** — amber_pair_harness on `monbus_axil4_group_1wr` (the
  write-only group swap): drain tie-offs deleted, error window strapped to a
  dead null window, tally ingest unchanged. DV green modulo the pre-existing
  BUG-003 seed flake (2026-10-25)
