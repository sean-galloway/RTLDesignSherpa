<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# memory-controllers — bugs

**Next ID: BUG-005** — never recycle a number, even when its item closed.

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
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

None.

## Active

None.

## Closed

- **BUG-004** — `mc_global_timers` enforced a programmed window N as N+1 MC
  cycles (pumice TASK-034 had measured it and kept it as the contract). The
  host's tRRD of 2 became 3 cycles, 30 ns against the part's 10 ns: every
  close-page stream whose column needs its own ACT ran at one ACT per 3 cycles
  and the DUAL_ISSUE row lane never fired (its column lands inside the
  exclusion), 238 MB/s on the granite board's bank_interleave preset against a
  400 floor. Fixed 2026-11-18: the readiness compares open one cycle earlier
  (N is N, as the bank timers since MC-003), formal re-pinned with exact-N
  covers, host `rtw_guard` 6 -> 7 so the PHY-measured tRTW spacing holds, model
  `rank_ok_lag` 1 -> 0. Board (100 MHz SKU): bank_interleave 238 -> 387 MB/s on
  every row-hit cell, close_page interleaved / row_thrash / random +8 .. +67, the
  SKU's cells flat, 0 mismatched; one corner cell lost (close_page mixed 145 ->
  111 union, predicted by the model, carried in MC-021). Closed 2026-11-18. [closed/BUG-004.md](closed/BUG-004.md).

- **BUG-003** — the board host's DDR2 ns table carried tRRD 7.5 ns (the
  JESD79-2F 1 KB-page value) for a 2 KB-page x16 part whose tRRD is 10 ns.
  Fixed 2026-11-16 in `pumice_device.py` and the pumice char-perf proxy's part
  table, pinned by a host test (2 / 2 / 3 MC cycles at 75 / 100 / 200 MHz).
  The fix showed the checker's tFAW case had only ever bound on the
  inconsistent table (four rounded tRRDs cover tFAW at every legal point of
  this part); it now runs on a synthetic set. Closed 2026-11-16.
  [closed/BUG-003.md](closed/BUG-003.md).
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
