<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# memory-controllers — issues

**Next ID: ISSUE-009** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed, spanning more than one
controller (the shared `common-ip` RTL, or pumice and granite together). It
RESOLVES INTO a bug, a task, or a recorded no-action. A problem confined to one
controller is filed in that controller's own lane.

Each item is **its own file**, `<ID>.md`, inside the directory for its
state. Moving an item between states is `git mv`, so an item is in
exactly one state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started (the ISSUE-000 template is not counted) |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 6 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-008** -- a rare one-cycle draw survives refresh alignment: one
  board row in 263 differed by a cycle at the same `REF_ALIGN` offset
  (`defaults row_major_bl4`, 269,754 vs 269,753). Filed 2026-11-25 from
  MC-022's board check. [open/ISSUE-008.md](open/ISSUE-008.md).

- **ISSUE-007** -- the `bank_interleave` row-hit cells at the phase-exact
  counters sit at the 583 MB/s ceiling with a per-pass draw a step below it
  (566 on five to seven of eighteen cells, ~520 on one, the cells differing
  run to run; single-direction passes, so not the direction register); the
  model is 585 flat. Filed 2026-11-22 from MC-020 decision 1.

## Closed

- **ISSUE-005** -- the open-page mixed cell's slow attractor: the direction
  register's 255 / 255 cap alternation (272 / 272) where the fast mode, taken
  on the refresh phase at GO, runs 311 / 522; whether the pick core should
  take the fast mode deterministically. Filed 2026-11-19 from MC-021 step 8.
  2026-11-22, at the phase-exact counters: the model's preference inverted
  (fast at both GO phases on `defaults` and `open_page`) where the board stays
  slow (three of three, two of three).
  Closed 2026-11-24 into MC-024: read priority is one mode on every run
  (297 / 455 x3 on both open-page presets); the power-on register keeps the
  race by decision. [closed/ISSUE-005.md](closed/ISSUE-005.md).

- **ISSUE-006** -- the SKU model ran `defaults` (the hybrid page policy) as plain
  open page. Closed 2026-11-20 into a model term: the RTL's page policy
  (`page_mode` 4 the hybrid, 0 the flat close-on-drain the board's open_page
  writes), with which `defaults mixed_bl8` is one mode at all 40 GO phases as
  the board's five runs were, the by-mode compare 57 / 0, every `defaults` cell
  within 1.2 percent, and the demand PREs MC-019 found on the lane are in the
  model. [closed/ISSUE-006.md](closed/ISSUE-006.md).
- **ISSUE-002** -- the board's `bank_interleave` map at 233-258 MB/s against the
  SKU model's 778. Closed 2026-11-17: a model configuration error -- the host's
  preset is the interleaved map AND close page (PAGE_POLICY_CLOSE), the model
  ran it open; corrected, the model is 389 against 232-238 and the proxy
  reproduces the board exactly. The remaining gap is ISSUE-003's hop cost on
  eight banks (ACT -> ACT 3 cycles against t_rrd 2, two empty slots per column
  pair), resolved into MC-021.
- **ISSUE-003** -- `close_page` pays ~2.5 MC cycles per dependent hop above the
  SKU model. Closed 2026-11-17, measured: the ACT after an auto-precharge fires
  two cycles after `bank_act_ready_i` rises (the decode's registered request
  plus the winner register), the hinted ACT -> column lands at tRCD exactly;
  ACT -> ACT 10 / 9 against the model's 7.7 / 6.7. Resolved into MC-021 (a
  `hop_lag` model term, then the RTL question).

- **ISSUE-004** -- the SKU model's `mixed` read turns ran four times the batch
  cap. Closed 2026-11-17: the RTL's rotor rule was the model's; the store in
  front of it was not (the mixed cap at every push keeps each direction at six
  beats, a pushed beat is a head four cycles later), so the waiting direction's
  ACT rides unopposed. Three admission terms added to the model; `mixed`
  286 / 286 against the board's 272 / 272, every other SKU cell unchanged.
- **ISSUE-001** -- the pumice/granite microarchitecture was ASIC-shaped for an
  FPGA target. Closed 2026-11-08: 12 of 17 resolution rows done (MC-004..MC-010,
  e1ebaacf7 .. a4e9c03f1), 4 deferred with the measurement that says why
  (5, 7, 14b, 15). pumice closes 75 MHz on the FPGA SKU (38,970 LUT, +0.230)
  and runs the board at 75 MHz; granite closes its 75 MHz board point and sits
  on the noise floor at the 100 MHz push profile.
