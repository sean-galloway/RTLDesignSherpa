<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Refresh Controller (`refresh_ctrl`)

**Module:** `refresh_ctrl.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_mem_cmd_scheduler`
**Status:** Implemented — FSM-free tREFI/pending/drain accumulator with a REFab/REFpb selector and REFpb bank rotor.

> Refresh **recovery** (tRFC) is not this block's job: the arbiter
> (`pumice_cmd_arbiter`) loads a down-counter from `TIMINGS_RFC_REFI.tRFC` on
> each fired REF and blocks ACT/REF picks until it expires — see
> [ch02/07](07_scheduler.md). `refresh_ctrl` only meters *when* refreshes are
> owed.

> Scope note: this module is `refresh_ctrl`. It is a compact, FSM-free
> accumulator design — three registered counter blocks plus a bank rotor,
> all strict-flopped at the outputs. It tracks the tREFI interval, keeps a
> JEDEC-capped count of postponed refreshes, meters how many REF commands
> the scheduler should burst back-to-back, and (for LPDDR2 REFpb) rotates a
> target bank across grants.
>
> Features that earlier drafts of this chapter described as current
> architecture are **not implemented** and are not part of this module:
> DARP per-bank age selection, periodic ZQCS piggyback, per-rank PASR mask
> propagation, self-refresh coordination, LPDDR2 temperature (MR4) scaling,
> per-rank REFab round-robin, a multi-state FSM, and per-(rank, bank)
> `refresh_req`/`refresh_gnt` handshake arrays. Refresh does not use a
> bank-machine handshake: it raises a single `refresh_req_o` and wins
> against other scheduler commands by priority inside
> `pumice_cmd_arbiter`. Those retired features are collected under
> [Open Questions / Future Work](#open-questions--future-work).

---

## Purpose

`refresh_ctrl` owns DRAM refresh scheduling. It produces:

- `refresh_req_o` — a single request line that elevates refresh to highest
  priority in the scheduler. Strict default: high while any refresh is
  pending; the v3 postpone/pull-in credits (section 2b) reshape when it
  asserts.
- `pending_refreshes_o` — the count of postponed refreshes (JEDEC max 8).
- `refresh_drain_active_o` — a hint that the scheduler should keep granting
  REF back-to-back to work down a burst quota.
- `refresh_kind_o` / `refresh_bank_o` — the REFab-vs-REFpb selector and, in
  REFpb mode, the target bank produced by the bank rotor.
- `obs_*` — observability taps on internal state for future CSR readout.

This is the heart of the controller's correctness story: get refresh wrong
and DRAM forgets data. The design is deliberately simple — three registered
counter blocks and a bank rotor, with no control FSM.

---

## Synthesis Parameters

| Parameter    | Default             | Effect                                                            |
|--------------|---------------------|-------------------------------------------------------------------|
| `NUM_BANKS`  | 8                   | Number of banks the REFpb rotor cycles through (`0..NUM_BANKS-1`) |
| `BA_W`       | `$clog2(NUM_BANKS)` | Width of `refresh_bank_o` / the bank rotor (derived)              |

The module imports `pumice_pkg::*` and uses the standard reset macros
(`reset_defs.svh`). Clock is `mc_clk`; reset is `mc_rst_n` (active-low).

---

## Behavioral Blocks

There is no FSM. The module is four registered blocks feeding a strict-flop
output stage.

### 1. tREFI Counter (`r_refi_cnt`)

A 16-bit down-counter that measures the refresh interval in MC cycles.

- Only ticks when `enable_i` is high (`enable_i` comes from
  `init_sequencer` — refresh is gated off until init completes). While
  `enable_i` is low, the counter is held reloaded at `t_refi_i`.
- When it reaches 0 (`w_refi_expired`), it reloads `t_refi_i` and that
  expiry event drives one increment of the pending accumulator.

### 2. Pending Accumulator (`r_pending`)

A 4-bit count of postponed refreshes, capped at `MAX_PENDING = 8` (the
JEDEC ceiling of postponed refreshes).

- A tREFI expiry (while enabled) adds 1, saturating at 8. At saturation the
  RTL comment flags a looming DRAM data-retention violation — the workload
  has blocked refresh longer than JEDEC allows. With pull-in credit banked
  (below), an expiry consumes a credit instead of adding to the backlog.
- A grant retires a pending refresh if any (`w_grant_accept`); a grant with
  no backlog banks a pull-in credit (`w_grant_early`).
- A simultaneous expiry and grant net to zero change.

### 2b. JEDEC +-8 Credits (`REF_CTRL.postpone_limit` / `pullin_limit`, v3)

Two 4-bit CSR knobs shape when the request line asserts; 0/0 is the strict
baseline (request the moment anything is pending), bit-identical to v2.

- **Postpone** (`postpone_limit`, clamped to 7): while demand persists,
  `refresh_req_o` is withheld until the backlog EXCEEDS the limit. The
  clamp guarantees the saturating backlog (8) can always exceed it, so the
  retention ceiling forces refresh even under unbroken demand.
- **Pull-in** (`pullin_limit`, clamped to 8): once idle is confirmed,
  refreshes run AHEAD of tREFI, banking up to the limit in `r_pullin`;
  each later expiry consumes a credit, giving a following demand burst a
  refresh-free window.
- **Idle confirmation**: `demand_i` (scheduler CAM occupancy) blinks off
  for a few cycles between bursts; a 16-cycle hysteresis counter
  (`IDLE_CONFIRM`) keeps micro-gaps from releasing postponed refreshes or
  triggering pull-ins mid-stream.
- `refresh_req_o` is therefore
  `idle ? (backlog > 0 || credit < pullin_limit) : (backlog > postpone_limit)`,
  registered.

### 3. Drain Quota (`r_burst_remaining`)

A 4-bit counter that meters how many REFs the scheduler should issue
back-to-back once refresh wins arbitration.

- When the previous burst is fully drained (`r_burst_remaining == 0`) and
  there is pending work (`r_pending > 0`), it (re)loads
  `min(refresh_burst_i, r_pending)`. If that clamp evaluates to 0 it loads
  1 instead, so a burst always makes forward progress.
- Each accepted grant decrements it.
- `w_drain_active = (r_burst_remaining > 0) && (r_pending > 0) &&
  refresh_req_o` is exported as `refresh_drain_active_o`. While it is high,
  the scheduler should keep granting REF back-to-back rather than yielding
  to reads/writes. The `refresh_req_o` term is load-bearing: a postponed
  backlog (request withheld) must not open the drain window, or the
  arbiter's drain preemption would defeat the postpone credit entirely.

`refresh_burst_i` is a 4-bit input (1..8) that sets the desired drain count
per request cycle.

### 4. REFpb Bank Rotor (`r_bank_rotor`)

Selects the target bank for LPDDR2 per-bank refresh.

- On each accepted grant, if `refpb_mode_i` is set, the rotor increments and
  wraps `0..NUM_BANKS-1`.
- In REFab mode (`refpb_mode_i == 0`) it is held at 0.
- `refresh_bank_o` is the registered rotor value; it is only meaningful in
  REFpb mode.
- `r_grants_total` (16-bit) counts total accepted grants for observability.

`refresh_kind_o` is simply the registered copy of `refpb_mode_i`
(0 = REFab, 1 = REFpb), forwarded to the scheduler / `dfi_cmd_formatter`.

All final outputs are strict-flopped (registered) in a single output stage.

---

## Interface

### Parameters and Clocking

| Signal     | Direction | Width | Description                          |
|------------|-----------|-------|--------------------------------------|
| `mc_clk`   | input     | 1     | Memory-controller clock              |
| `mc_rst_n` | input     | 1     | Active-low asynchronous reset        |

### Inputs

| Signal            | Width | Description                                                                 |
|-------------------|-------|-----------------------------------------------------------------------------|
| `t_refi_i`        | 16    | Refresh interval in MC cycles (tREFI). Reload value for `r_refi_cnt`.        |
| `refresh_burst_i` | 4     | Desired drain count per request cycle (1..8). Loads the burst quota.        |
| `refpb_mode_i`    | 1     | 0 = REFab, 1 = REFpb (LPDDR2). Selects `refresh_kind_o` and enables the rotor. |
| `enable_i`        | 1     | From `init_sequencer` (init done). Gates the tREFI counter and accumulation. |
| `postpone_limit_i`| 4     | `REF_CTRL.postpone_limit` — defer under demand, clamped to 7. 0 = strict.    |
| `pullin_limit_i`  | 4     | `REF_CTRL.pullin_limit` — run ahead on confirmed idle, clamped to 8. 0 = off. |
| `demand_i`        | 1     | Scheduler CAM occupancy (any read/write waiting). Feeds the idle hysteresis. |
| `refresh_grant_i` | 1     | Pulsed by the scheduler when it issues a REF on the DFI bus.                 |

### Outputs

| Signal                   | Width   | Description                                                        |
|--------------------------|---------|--------------------------------------------------------------------|
| `refresh_req_o`          | 1       | Credit-shaped request (see 2b), registered.                        |
| `pending_refreshes_o`    | 4       | Current postponed-refresh count (0..8).                            |
| `refresh_drain_active_o` | 1       | Burst quota owed, pending nonzero AND request asserted — keep granting REF. |
| `refresh_kind_o`         | 1       | Registered `refpb_mode_i` (0 = REFab, 1 = REFpb).                   |
| `refresh_bank_o`         | `BA_W`  | REFpb target bank from the rotor (valid in REFpb mode).            |

### Observability (`obs_*`, future CSR readout)

| Signal                  | Width  | Source                                            |
|-------------------------|--------|---------------------------------------------------|
| `obs_refi_cnt_o`        | 16     | Current `r_refi_cnt` value                        |
| `obs_drain_remaining_o` | 4      | Current `r_burst_remaining` value                 |
| `obs_bank_rotor_o`      | `BA_W` | Current `r_bank_rotor` value                      |
| `obs_grants_total_o`    | 16     | Total accepted grants (`r_grants_total`)          |
| `obs_pullin_credit_o`   | 4      | Current pull-in credit (`r_pullin`)               |

These are wired out for future CSR/telemetry hookup; no CSR block consumes
them yet.

---

## Timing / Behavior

- **Reset.** All registers clear to 0. `refresh_req_o`,
  `refresh_drain_active_o`, `refresh_kind_o`, `refresh_bank_o`, and every
  `obs_*` output reset to 0.
- **Init gating.** With `enable_i` low, `r_refi_cnt` is held at `t_refi_i`
  and no pending refreshes accumulate — refresh is inert until
  `init_sequencer` releases `enable_i`.
- **Single-cycle latency.** Because there is no FSM, request/drain/bank
  outputs simply track the counter state one flop behind. When tREFI
  expires, `r_pending` rises the next cycle and `refresh_req_o` follows the
  cycle after (output flop stage).
- **Grant handshake.** The module never blocks on a grant. It exports its
  request and drain hint; the scheduler decides when to pulse
  `refresh_grant_i`, and the module bookkeeps against those pulses.
- **Priority, not handshake.** Refresh wins against other scheduler
  commands by priority in `pumice_cmd_arbiter`; there is no per-bank
  `refresh_req`/`refresh_gnt` array and no bank-machine handshake.

---

## Verification Notes (cocotb test plan)

| Scenario                                                                                    | What it proves                                           |
|---------------------------------------------------------------------------------------------|----------------------------------------------------------|
| `enable_i` low: `t_refi_i` loaded, no ticks, `r_pending` stays 0, `refresh_req_o` stays low | Init gating                                              |
| `enable_i` high: `r_refi_cnt` counts down and reloads on expiry                             | tREFI countdown + reload                                 |
| One tREFI expiry with no grant: `r_pending == 1`, `refresh_req_o` asserts                   | Pending accumulate + request                             |
| Withhold grants across 8+ expiries: `r_pending` saturates at 8, does not overflow           | JEDEC max-8 postpone cap                                 |
| Expiry and grant in the same cycle: `r_pending` unchanged                                   | Simultaneous tick+grant net-zero                         |
| Grants with pending > 0: `r_pending` decrements; `refresh_req_o` drops at 0                 | Grant accounting                                         |
| `refresh_burst_i = N` with `r_pending >= N`: quota loads N, `refresh_drain_active_o` high    | Drain quota load + active hint                           |
| `refresh_burst_i > r_pending`: quota clamps to `r_pending`                                   | Burst clamp (no overcount)                               |
| `refresh_burst_i` clamp resolves to 0 but pending > 0: quota loads 1                         | Forward-progress floor                                   |
| Grants during drain: `r_burst_remaining` counts down; `refresh_drain_active_o` deasserts at 0| Drain metering                                           |
| REFab mode (`refpb_mode_i = 0`): `refresh_bank_o` stays 0, `refresh_kind_o == 0`             | REFab selector + rotor held                              |
| REFpb mode (`refpb_mode_i = 1`): `refresh_bank_o` rotates `0..NUM_BANKS-1` across grants     | REFpb bank rotor wrap                                    |
| `obs_*` taps track internal counters                                                        | Observability wiring                                     |

---

## Open Questions / Future Work

The following were described in earlier SWAG/HAS drafts but are **not
implemented** in `refresh_ctrl`. They are recorded here as possible future
scope, not as current behavior:

- **DARP per-bank age selection.** REFpb currently uses a plain round-robin
  bank rotor. An age-aware selector (refresh the oldest idle non-masked
  bank first, falling back to oldest-first) would need bank-state and
  last-refresh-age inputs the module does not have today.
- **Periodic ZQCS piggyback.** No ZQCS interval counter or ZQCS sequencing
  exists. If added, it could piggyback on the refresh window (all banks
  idle) rather than triggering a separate bus-blocking event.
- **Per-rank PASR mask propagation.** No PASR bank/segment masks, no
  MR16/MR17 propagation. LPDDR2 partial-array self-refresh is unsupported.
- **Self-refresh coordination.** No `sr_entry_req`/`sr_entry_gnt` handshake
  with a power-state block; the tREFI counter is not paused for self-refresh.
- **LPDDR2 temperature scaling.** No MR4-driven tREFI derating. `t_refi_i`
  is the single reload value regardless of temperature class.
- **Per-rank REFab round-robin.** Single-rank only; there is no rank
  pointer or per-rank REF dispatch. `NUM_BANKS` (banks), not ranks, is the
  only structural parameter.
- **Multi-state FSM / per-bank handshake.** The design is FSM-free and uses
  a single priority-based request rather than per-(rank, bank)
  `refresh_req`/`refresh_gnt` arrays. Any of the above features would likely
  reintroduce sequencing state.
