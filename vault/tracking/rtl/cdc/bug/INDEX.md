<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# cdc — bugs

**Next ID: BUG-005** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

## Active

None.

## Closed

- **BUG-004** — `glitch_free_n_dff_arn` had no `ASYNC_REG` attribute on its
  synchronizer array. Found 2026-11-05 under memory-controllers ISSUE-001;
  attribute added 2026-11-06; confirmed 2026-11-07 on a routed granite Nexys A7
  build (120 flops all carry it, 0 SRL, every stage pair in one slice).
  [closed/BUG-004.md](closed/BUG-004.md).

- **BUG-001** — cdc_4_phase_handshake FAST_PATH acknowledged a transfer the receiver never took
- **BUG-002** — fifo_async wavedrom scenarios hand-drove dut.read against a live BFM
- **BUG-003** — STALE — the 4-phase handshake formal proof ran against a pre-rename DUT copy
