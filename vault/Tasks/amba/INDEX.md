<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# AMBA tasks

**Next ID: TASK-098** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-001` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly/risk/question not yet diagnosed | `ISSUE-001` |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../INDEX.md) for the full definitions.


Canonical task tracker for `rtl/amba/` (AXI4/AXI5, APB, AXI-Stream, the
monitor subsystem, monbus). Migrated 2026-07-22 from `rtl/amba/PRD/TASKS.md`.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 1 | in progress right now |
| [open.md](open.md) | 8 | accepted, not started |
| [deferred.md](deferred.md) | 0 | accepted, parked on a named condition |
| [closed.md](closed.md) | 65 | done (kept for history) |
| [dropped.md](dropped.md) | 1 | ended without completing (won't do / superseded) |

*Re-measured again 2026-09-16 and corrected: the table claimed 11 open / 58
closed against an actual 10 / 63. Two things caused it. Entries were added and
moved without the table following, and -- the subtler one -- a count that matches
only `TASK-nnn` and `AMBA-*` headings silently MISSES entries filed under other
ID forms. `OBS-PORTS` is one such entry and went uncounted for exactly that
reason. Match any `ID-number` or all-caps-name heading at `##`/`###`, and read
the number rather than trusting this table.*

*Counts re-measured 2026-09-14 by matching task-ID headings, not by hand. They
had drifted in both directions, because entries in this area sit at BOTH `##`
and `###` and any count that assumes one level is wrong. Two separate fixes
landed the same day: six entries whose bodies said CLOSED were moved OUT of
`open.md`, and five whose bodies said "open" or "NOT fixed" were moved BACK IN
from `closed.md` (TASK-078, -083, -084, -085, -095). A scan that only reads `##` misses
TASK-077, -075, -074, -073, -014, -015, -022, -024 — eight real open items,
several of them defects. (A ninth, CONV-001, has since moved to the converters
area as CONV-010, where it belongs.)*

## Active

- **TASK-025** — Update formal proofs for the monitor logic. 12/12 proofs pass
  and the real bug they surfaced (active_count underflow) is fixed; still open:
  the val/amba monitor-path sweep, perfmon-window / cam_clear properties, and
  the `ENABLE_*_LOGIC=0` cone-drop configs.

## Open

- **AMBA-MONRATE-INTERMITTENT** — `val/amba` at `-n 24` fails ~1-3 tests per
  run and the failing set is NOT stable, on completion-RATE thresholds in the
  axi_monitor family (`Got 16 completions (16.0%), expected >= 20 (20%)`).
  NOT root-caused; filed for a fresh agent with the evidence and the leads.
  A third distinct cause in the same family as VAL-XDIST-INTERMITTENT and the
  closed AMBA-WAVEDROM-FLAKY — **both of those causes are already ruled out**
  (seed pinning does not stabilise it; sim_build names are unique). Blocks
  reading val/amba as a clean signal, so shared-framework changes currently
  have to be A/B'd.

- **TASK-072** — lighten the gate-heavy monitor modules. Scoped 2026-08-31:
  `bus_transaction_t`'s three 32-bit phase TIMERS are write-only repo-wide
  (96 bits x N of dead flops; the real timing lives in `axi_monitor_timeout`),
  the three timestamps are read only as differences, and `addr_hit_any` is a
  global OR that couples every CAM bank to every other -- which is what
  Genesys2 `build-mon` is failing setup on.
- **TASK-027** — CLOSED 2026-08-31: the monitors own the mechanism, the
  customer owns the policy (how ranges are defined is the integrator's call).
- **TASK-065** — CLOSED 2026-08-31: nothing left to delete; exposed a
  host/RTL regmap mismatch on the `slvmon_apb` window instead.
- **TASK-026** — every module MUST have a filelist + registry entry. Coverage
  is already good; the gap is that **nothing enforces it**. Shared gate with
  COMMON-010.
- **TASK-014** — Performance characterization
- **TASK-015** — Address range + ID filtering
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
  [rtl/amba/KNOWN_ISSUES/](../../../rtl/amba/KNOWN_ISSUES/)
- Standing plans kept as their own docs: `rtl/amba/PRD/TASK-008-*`,
  `TASK-016-*` (implementation notes, not lifecycle items)
