<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dma-ip/rapids — issues

**Next ID: ISSUE-008** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 7 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Closed

- **ISSUE-007** — MONCAP reads nothing on observer-only rapids builds (closed
  2026-10-09: gen_moncap captures the observers' monbus when GEN_MON=0, with
  record-contiguous arbitration; both observer protocols board-decodable, sim
  27 words / 9 records AXI+AXIS)

- **ISSUE-005** — SCHED_CONFIG.COMPL_EN now gates the scheduler's and descriptor engine's CORE Completion packets at the group; OFF and ON states tested (closed 2026-09-29)

- **ISSUE-006** — under memory latency the sink keeps only ~12 beats in flight per channel (closed 2026-09-28: the generator feeds one channel at a time; the window is one channel's AW_MAX_OUTSTANDING x burst)
- **ISSUE-004** — one board config reports zero ingress starvation where every other reports ~200 (closed 2026-09-28: re-measured and ILA-traced, no anomaly)
- **ISSUE-001** — after TASK-082, snkGB/s reports ingress latency, not datapath rate (closed 2026-09-27; outlier moved to ISSUE-004)
- **ISSUE-003** — monitor registers answer normally when the monitors are not built (closed 2026-09-27)
- **ISSUE-002** — backpressure runs record meter numbers that cannot mean anything
