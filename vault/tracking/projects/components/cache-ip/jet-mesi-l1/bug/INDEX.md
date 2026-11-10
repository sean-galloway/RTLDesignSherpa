<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/jet-mesi-l1 — bugs

**Next ID: BUG-004** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what
correct looks like. If you cannot state the expected behaviour, it is an
ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

(none)

## Closed

- **BUG-001** ([page](closed/BUG-001.md)) — jet_mshr `set_full_o` compares claims against WAYS cast to MW+1 bits: constant-true at MSHR_COUNT=2, WAYS=4 (every s128w4_m02 FULL cell fails to build). Filed 2026-11-09 from the first FULL run of the pushed RTL; closed 2026-11-09.
- **BUG-002** ([page](closed/BUG-002.md)) — jet_wb_buffer indexes `r_data` with `{slot, beat}` into a VICTIM_DEPTH*FILL_BEATS store: one bit too wide at VICTIM_DEPTH=1 (every *_v1 FULL cell fails to build), wrong at non-pow2 depths. Filed 2026-11-09; closed 2026-11-09.
- **BUG-003** ([page](closed/BUG-003.md)) — jet_pair_fabric loses the buffer-free clear when a trailing absorption's BVALID lands during the peer's F_REPLAY_R (guard not owner-qualified): that direction is never granted again, rig hang (SEED=54355, s128w4 m16v1 fifo). P1. Filed 2026-11-09; closed 2026-11-09.
