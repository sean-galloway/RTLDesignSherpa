<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/utility-ip/converters — bugs

**Next ID: BUG-010** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 9 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Closed

- **BUG-009** — beat-level R interleave across IDs now supported: per-ID
  reassembly layer in the read converter (demux by RID, shared beat pool,
  one-outstanding-burst-per-ID reservation, burst-at-a-time feeding of the
  untouched axi_data primitives); interleave + burst-OOO regressions
  RED-verified against the pre-fix RTL; closed 2026-10-04

- **BUG-008** — dwidth converter split-fold assumes in-order B across IDs
- **BUG-001** — axi_data_dnsize burst-tracking LAST: early LAST on TRACK_BURSTS
- **BUG-002** — the dnsize and upsize test files are decorative: 22/22 configs fail when asserted
- **BUG-003** — dnsize DUAL buffer: dropped beats and misplaced LAST
- **BUG-004** — downsize converters truncate AWLEN/ARLEN on long bursts
- **BUG-005** — dwidth rd RRESP fold used bitwise OR; SLVERR|EXOKAY inflated to DECERR
- **BUG-006** — axi4_to_axil4_wr: parked burst AW deadlocked a pending single-beat W
- **BUG-007** — converters RTL used manual async reset, against the components mandate
