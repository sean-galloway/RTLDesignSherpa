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

# Bank Timer (`scoria_bank_timer` + `scoria_bank_timers`)

**Module:** `scoria_bank_timer.sv`, `scoria_bank_timers.sv`
**Location:** `rtl/fub/`
**Category:** JEDEC timing
**Parent:** `scoria_scheduler_layer`
**Status:** complete, sim-verified

---

## Purpose

`scoria_bank_timers` is a thin wrapper that stamps one `scoria_bank_timer` instance for every `(rank, bank)` pair and fans the scheduler's command-event strobes to the addressed instance. `scoria_bank_timer` tracks a single bank's JEDEC timing constraints with preset/decrement countdown timers and a row-open register. There is no FSM; the per-command `safe_*` outputs are combinational off the timer flops.

## Parameters

### `scoria_bank_timers`

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_RANKS` | int | 1+ | 1 | ranks per channel |
| `NUM_BANKS` | int | 4..16 | 8 | banks per rank |
| `ROW_WIDTH` | int | — | 14 | row address width |
| `RKW` | int | derived | `$clog2(NUM_RANKS)` or 1 | rank index width |
| `BKW` | int | derived | `$clog2(NUM_BANKS)` | bank index width |
| `BANK_LA` | int | 0+ | 0 | advisory lookahead depth passed to each timer |

: Table 2.13.1: Bank timers wrapper parameters

### `scoria_bank_timer`

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `ROW_WIDTH` | int | — | 14 | row address width |
| `TW` | int | — | 8 | timer counter width |
| `LA` | int | 0+ | 0 | advisory lookahead depth in cycles |

: Table 2.13.2: Single bank timer parameters

## Interface

### Wrapper event and readiness ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `evt_act_i` | in | 1 | activate event |
| `evt_rd_i` | in | 1 | read event |
| `evt_wr_i` | in | 1 | write event |
| `evt_pre_i` | in | 1 | precharge event |
| `evt_ap_i` | in | 1 | auto-precharge qualifier |
| `evt_rank_i` | in | `RKW` | event rank |
| `evt_bank_i` | in | `BKW` | event bank |
| `evt_row_i` | in | `ROW_WIDTH` | event row |
| `bank_act_ready_o` | out | `NUM_RANKS*NUM_BANKS` | per-bank safe to activate |
| `bank_rdwr_ready_o` | out | `NUM_RANKS*NUM_BANKS` | per-bank safe to read/write |
| `bank_pre_ready_o` | out | `NUM_RANKS*NUM_BANKS` | per-bank safe to precharge |
| `bank_row_active_o` | out | `NUM_RANKS*NUM_BANKS` | per-bank row-valid flag |
| `bank_open_row_o` | out | `NUM_RANKS*NUM_BANKS*ROW_WIDTH` | per-bank open row |
| `bank_state_o` | out | `NUM_RANKS*NUM_BANKS` | derived `bank_state_e` |

: Table 2.13.3: Bank timers wrapper interface

The wrapper also exports lookahead readiness twins (`bank_act_ready_la_o`, `bank_rdwr_ready_la_o`, `bank_pre_ready_la_o`) and observability flags.

### Single-timer ports

| Signal | Direction | Width | Description |
|---|---|---|---|
| `t_rcd_i` | in | `TW` | ACT-to-RD/WR spacing |
| `t_rp_i` | in | `TW` | PRE-to-ACT spacing |
| `t_ras_i` | in | `TW` | min ACT-to-PRE spacing |
| `t_rc_i` | in | `TW` | same-bank ACT-to-ACT spacing |
| `t_wr_i` | in | `TW` | WR-to-PRE recovery |
| `t_rtp_i` | in | `TW` | RD-to-PRE recovery |
| `set_act_i` | in | 1 | load tRCD/tRAS/tRC and open row |
| `set_rd_i` | in | 1 | load tRTP into preblk timer |
| `set_wr_i` | in | 1 | load tWR into preblk timer |
| `set_pre_i` | in | 1 | explicit precharge |
| `set_ap_i` | in | 1 | auto-precharge qualifier on RD/WR |
| `row_i` | in | `ROW_WIDTH` | row to open |

: Table 2.13.4: Single bank timer command inputs

## Microarchitecture internals

### Five timers

Each timer is an 8-bit saturating down-counter that reloads on its trigger event and counts to zero.

| Timer | Loaded on | Value | Gates |
|---|---|---|---|
| `r_rcd` | `set_act_i` | `t_rcd_i` | `safe_rd_o`, `safe_wr_o` |
| `r_ras` | `set_act_i` | `t_ras_i` | `safe_pre_o` |
| `r_rc` | `set_act_i` | `t_rc_i` | `safe_act_o` |
| `r_rp` | `set_pre_i` or auto-PRE fire | `t_rp_i` | `safe_act_o` |
| `r_preblk` | `set_rd_i` (`t_rtp_i`) / `set_wr_i` (`t_wr_i`) | tRTP / tWR | `safe_pre_o` |

: Table 2.13.5: Bank timer countdowns

### Safe equations

```text
safe_act_o = !r_row_valid && (r_rp == 0) && (r_rc == 0)
safe_rd_o  =  r_row_valid && (r_rcd == 0) && !r_ap_pending
safe_wr_o  = safe_rd_o
safe_pre_o =  r_row_valid && (r_ras == 0) && (r_preblk == 0) && !r_ap_pending
```

`safe_wr_o` is literally assigned `safe_rd_o`. Read/write recovery is handled by `r_preblk`, not by the read/write-safe term.

### Auto-precharge pending

A read or write with `set_ap_i` sets `r_ap_pending`. The auto-precharge fires when the recovery and tRAS windows have both elapsed:

```text
w_ap_fire = r_ap_pending && (r_preblk == 0) && (r_ras == 0)
```

On `w_ap_fire`, the row closes, `r_ap_pending` clears, and `r_rp` reloads from `t_rp_i` — all without a separate scheduler PRE command.

### Lookahead twins

With `LA = 4` in the scheduler build, the advisory outputs predict readiness `LA` cycles ahead:

```text
safe_act_la_o  = !r_row_valid && (r_rp <= LA) && (r_rc <= LA)
safe_rdwr_la_o =  r_row_valid && (r_rcd <= LA) && !r_ap_pending
safe_pre_la_o  =  r_row_valid && (r_ras <= LA) && (r_preblk <= LA) && !r_ap_pending
```

The lookahead deliberately never predicts `row_valid` or the auto-precharge close. It can only under-report safety; the arbiter re-checks the live `safe_*` outputs at its final stage.

### Observability and derived state

`bank_state_e` is derived purely for observability:

```text
if (r_row_valid)  state = (r_rcd != 0) ? BANK_ACTIVATING : BANK_ACTIVE
else              state = (r_rp  != 0) ? BANK_PRECHARGING : BANK_IDLE
```

No downstream logic depends on `state_o`. Additional observability flags expose `r_rcd != 0`, `r_preblk != 0`, `r_ras != 0`, and `r_ap_pending`.

## FSM policy

There is no state machine. The block is timers plus a row-open register, with combinational safe outputs.

## Timing

`safe_*` outputs are combinational from the timer flops, so they reflect the effect of a command issued on the previous cycle after one clock edge. The wrapper adds only wiring; there is no extra pipeline stage.

## Notes

- **No FSM means no multi-cycle lag.** The previous design double-registered readiness behind a 3-state FSM, which let refresh and columns slip into stale bank state.
- **Lookahead is advisory.** It is safe to trust a "not safe" lookahead, because the arbiter re-checks the live outputs. A "safe" lookahead can be invalidated by a reload from a command the scheduler issues in the meantime.
- **Rank/bank decoding.** The wrapper uses a decoded select rather than an indexed array access, so an out-of-range rank cannot address past the stamped instances.
