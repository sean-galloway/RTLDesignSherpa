<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# granite-ddr2-lpddr2 — tasks

**Next ID: TASK-010** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one
state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 6 | done (kept for history) |
| [dropped/](dropped/) | 1 | ended without completing |
| [deferred/](deferred/) | 2 | parked pending a named condition |

## Open

None.

## Active

None.

## Closed

- **TASK-007** — narrow AXI beats on a host as wide as the controller: the
  plane had no narrow support at all (the chopper steps by full beats). Fixed
  by `mc_axi4_narrow_pack` in `mc_axi4_plane` (`NARROW_EN` 1; all four
  controllers); 1020 -> 0 mismatched, every AxSIZE clean, full width unchanged.
  The post-mismatch write "hang" is the harness's sticky any_error. CLOSED
  2026-11-02. [closed/TASK-007.md](closed/TASK-007.md).

- **TASK-003** — granite at 100 MHz and ahead of LiteDRAM through the same
  harness: 100 MHz closes with the merge default, DDR2-400 board point
  772/774 of 800 streaming, LiteDRAM tally 42 / 18 / 0. Item 6's residuals
  went to TASK-007 (narrow beats) and TASK-009 (1:4 board first word).
  CLOSED 2026-11-02. [closed/TASK-003.md](closed/TASK-003.md).

- **TASK-008** — Ocelus observability on granite and pumice (`HAS_MON`, default 0):
  lite port monitors + `mc_monlite` internal errors/debug -> one AXI-Lite packet
  writer, `MON_*` CSRs at 0x200. RTL + sim; board not wired. CLOSED 2026-11-01.
  [closed/TASK-008.md](closed/TASK-008.md).

- **TASK-006** — store combining behind `STORE_MERGE_EN` (default 1 since 2026-10-29): the
  close_page pair walk doubles both ways and matches pumice, open_page pair
  at 3-4 threads +14..25 percent. The board corruption was a WRITE reaching
  the DFI head before its data (merged-B drain bubble, stale head record,
  own-fill fdone) with the scheduler's timers running from the commit; fixed
  in the store and the pick, held-WRITE asserted 0 in sim, 64/64 board cells
  clean. CLOSED 2026-10-29. [closed/TASK-006.md](closed/TASK-006.md).

- **TASK-001** — granite first build: wrappers dissolved, `granite_core`
  composed from common-ip, CSR baseline, Nexys A7 at 75 MHz. The split-burst
  wedge it carried was fixed under MC-003. CLOSED 2026-10-29.
  [closed/TASK-001.md](closed/TASK-001.md).
- **TASK-002** — bank queues as gaxi_age_fifo_sync (PEEK 2) carrying the pool
  age; landed 3a1479820, cycle-identical, controller worst path 0.34 -> 0.93
  ns. Residual (where the aged class sits in the select, `HAS_AGE` 0) folded
  into TASK-003 item 5. CLOSED 2026-10-29. [closed/TASK-002.md](closed/TASK-002.md).

## Dropped

- **TASK-005** — the simple AXI aggregator in granite's AXI plane (`HALF_AGG`)
  -- DROPPED 2026-11-03, superseded by TASK-006's store combiner, which merges
  on the DRAM address across IDs and threads with no hold. Block and
  parameters deleted (text at dd27f9bda). [dropped/TASK-005.md](dropped/TASK-005.md).

## Deferred

- **TASK-004** — granite 100 MHz timing margin: the remaining levers (LA=3 pick
  split, plane pblock, registered read-issue strobe; directives, replication and
  the pick trim measured and not levers) -- DEFERRED 2026-10-29, pending a build
  that no longer closes at 100 MHz with the shipped directives, or a product
  point above 100 MHz. [deferred/TASK-004.md](deferred/TASK-004.md).
- **TASK-009** — the DFI 1:4 board point's first DQ word of each read run is
  sampled before the device drives it (PHY side, ahead of the controller)
  -- DEFERRED 2026-11-02, pending 1:4 as a product point; four board
  experiments listed. [deferred/TASK-009.md](deferred/TASK-009.md).
