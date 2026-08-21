<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# AMBA tasks

Canonical task tracker for `rtl/amba/` (AXI4/AXI5, APB, AXI-Stream, the
monitor subsystem, monbus). Migrated 2026-07-22 from `rtl/amba/PRD/TASKS.md`.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 1 | in progress right now |
| [open.md](open.md) | 9 | accepted, not started |
| [closed.md](closed.md) | 21 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing (won't do / superseded) |

## Active

- **TASK-025** — Update formal proofs for the monitor logic. 12/12 proofs pass
  and the real bug they surfaced (active_count underflow) is fixed; still open:
  the val/amba monitor-path sweep, perfmon-window / cam_clear properties, and
  the `ENABLE_*_LOGIC=0` cone-drop configs.

## Open

- **TASK-026** — every module MUST have a filelist + registry entry. Coverage
  is already good; the gap is that **nothing enforces it**. Shared gate with
  COMMON-010.
- **TASK-014** — Performance characterization
- **TASK-015** — Address range + ID filtering
- **TASK-027** — Split the address-range checker into independent DEBUG and
  ERROR range sets, with params at the monitor + AXI\* wrapper module level
- **TASK-022** — Make APB crossbar variants functional
- **TASK-024** — Monitor system whitepaper (P3)
- **TASK-060** — CLOSED 2026-08-21: module deleted with the observer rework (successors in misc); `o_cmd_block`
  unconnected on both `axi_perf_latency_hist` instances, so its test cannot run
  at all. Vivado only warns, which is why the board flows still build. (P1)
- **TASK-061** — splitter `block_ready` duplicates transactions instead of
  blocking them; downstream valid is ungated while upstream ready and the FSM
  capture are. Latent — nothing instantiates either splitter. (P2)
- **TASK-062** — `sdpram_slave_axil_axil` is on the board with no simulation
  behind it; only the axi4_axi4 wrapper of the four has a test. (P2)

## Lifecycle

A task moves `open → active → closed` (done) — or to `dropped` if it ends
without completing — by **cutting** its `### TASK-NNN` block from one page and
pasting it into the next; never copy, or the same task lives in two states.
Each block keeps its `**Status:**` line updated with the date (and, when
dropped, a one-line reason). New AMBA tasks get the next `TASK-NNN` number and
start in `open.md` (or `active.md` if you're starting immediately).

## Related

- Enforcement authority: [/GLOBAL_REQUIREMENTS.md](../../../GLOBAL_REQUIREMENTS.md)
- Subsystem: [rtl/amba/CLAUDE.md](../../../rtl/amba/CLAUDE.md),
  [rtl/amba/PRD/PRD-AMBA.md](../../../rtl/amba/PRD/PRD-AMBA.md),
  [rtl/amba/KNOWN_ISSUES/](../../../rtl/amba/KNOWN_ISSUES/)
- Standing plans kept as their own docs: `rtl/amba/PRD/TASK-008-*`,
  `TASK-016-*` (implementation notes, not lifecycle items)
