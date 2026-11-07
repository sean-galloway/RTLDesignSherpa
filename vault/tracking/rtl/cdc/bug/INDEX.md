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
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

## Active

- **BUG-004** — `glitch_free_n_dff_arn` has no `ASYNC_REG` attribute on its
  synchronizer array, so every `gaxi_fifo_async` pointer crossing is unclassified
  by Vivado's CDC report and may be split across slices. Found 2026-11-05 under
  memory-controllers ISSUE-001. Attribute added 2026-11-06; awaiting a board report_cdc. [active/BUG-004.md](active/BUG-004.md).


## Closed

- **BUG-001** — cdc_4_phase_handshake FAST_PATH acknowledged a transfer the receiver never took
- **BUG-002** — fifo_async wavedrom scenarios hand-drove dut.read against a live BFM
- **BUG-003** — STALE — the 4-phase handshake formal proof ran against a pre-rename DUT copy
