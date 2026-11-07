<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# memory-controllers — bugs

**Next ID: BUG-003** — never recycle a number, even when its item closed.

A DEFECT with a reproduction in the shared `common-ip` RTL, affecting more than
one controller. If you cannot state the expected behaviour, it is an ISSUE, not
a bug. A defect confined to one controller is filed in that controller's lane.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started (the BUG-000 template is not counted) |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

None.

## Active

None.

## Closed

- **BUG-001** — `mc_wr_intake` drops write responses: the store's `wr_done`
  strobe has no ready and the 4-deep B FIFO's `wr_ready` is unconnected, so a
  host holding `bready` low across more than four completions loses Bs
  silently. Both controllers. Fixed 2026-11-06: `wr_done` has a ready and the
  outstanding-B bound is applied at admission (a drain-side hold tripped tRP).
  Closed 2026-11-07. [closed/BUG-001.md](closed/BUG-001.md).
- **BUG-002** — `mc_dfi_cdc` (async branch) crosses a write burst's staged
  token and its data in two independent async FIFOs; the token can resolve a
  dfi_clk cycle before the data, so the serializer drives `dfi_wrdata` one
  cycle late against `t_phy_wrlat`. Two-clock builds only; neither board.
  Fixed 2026-11-06 (token launched a cycle after its data; granite derives the
  write-data FIFO depth for CDC builds). Closed 2026-11-07. [closed/BUG-002.md](closed/BUG-002.md).
