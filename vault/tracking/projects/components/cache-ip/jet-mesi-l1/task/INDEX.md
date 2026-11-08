<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/jet-mesi-l1 — tasks

**Next ID: TASK-004** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-003** ([page](open/TASK-003.md)) — give jet its hit latency back: data-array address lead under the BRAM sync-read array (6 -> 5), then v3 classify/tag-read overlap (-> 3..4). Filed 2026-11-08 from the FPGA review sweeps.

## Active

(none)

## Closed

- **TASK-001** — implement jet per the 2026-10-28 design spec (J1–J7 ruled):
  jet_pkg + jet_mshr + jet_wb_buffer + jet_rsp_seq + jet_control, DV ladder,
  formal liveness at tiny geometry, FULL soak grids, Genesys2 pair-rig
  measurement sweep. Closed 2026-11-03: all seven phases done; J7 measured on
  silicon (−16.6% thrash / −31.5% write-storm run cycles vs amber, hit 3 vs 4
  cycles, fill BW +18–37.5%; MSHR grid flat — the rig tops out at 2
  outstanding misses). Follow-ups: ISSUE-001 (90 MHz cone, jet v2), ISSUE-002
  (jet_monlite drop limit).
- **TASK-002** — restructure jet RTL into planes (mem-ctrl doctrine): CPU / coherence-core / fabric planes, ACE swappable for a future CHI plane. Coordinate with amber TASK-002.  Closed 2026-11-01: planes landed (with `jet_ace_top` carrying the J7 `jet_monlite` / MSHR stream), fabric contract doc + CHI stub in place; full regression is the restructure plan's Task 6.
