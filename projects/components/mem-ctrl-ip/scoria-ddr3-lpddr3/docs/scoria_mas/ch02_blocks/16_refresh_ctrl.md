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

# Refresh Controller (`scoria_refresh_ctrl`)

**Module:** `scoria_refresh_ctrl.sv`
**Location:** `rtl/fub/`
**Category:** maintenance / refresh
**Parent:** `scoria_scheduler_layer`
**Status:** complete and sim-verified; formal-retention proof green in `formal/scoria/refresh_ctrl`

---

## Purpose

`scoria_refresh_ctrl` keeps the DRAM rows alive. It is a credit machine, not an FSM: a `tREFI` interval counter ticks, a pending accumulator tracks how many refreshes are owed, and a request line stays raised until the scheduler grants enough of them back. The block supports DDR3 all-bank refresh, LPDDR3 per-bank refresh with a device-mirror rotor, JEDEC's plus-or-minus-eight postpone/pull-in window, and the TASK-001 Mode A elastic and Mode B temperature-compensated refresh policies.

The core is inherited from pumice, proven there, and re-derived here for scoria's REFpb interval arithmetic and the TASK-001 modes. The RTL is the authority; this page documents the logic as it exists.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_BANKS` | int | 8..16 | 8 | banks per rank; determines the REFpb rotor wrap |
| `BA_W` | int | — | `$clog2(NUM_BANKS)` | bank-address width, drives `refresh_bank_o` |

: Table 2.16.1: Refresh controller parameters

## Interface

### Timing, mode, and configuration

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mc_clk` | in | 1 | controller clock |
| `mc_rst_n` | in | 1 | active-low reset |
| `enable_i` | in | 1 | refresh engine enable; driven by the init sequencer once initialization completes |
| `t_refi_i` | in | 16 | `tREFI` reload value, runtime CSR |
| `trefi_pb_i` | in | 16 | per-bank `tREFI` for REFpb mode; 0 means derive `t_refi_i >> 3` |
| `refresh_burst_i` | in | 4 | refreshes to issue per drain window, 1..8 |
| `refpb_mode_i` | in | 1 | 0 = all-bank `REFab`, 1 = per-bank `REFpb` (LPDDR3) |
| `refi_reload_i` | in | 1 | immediate counter reload; DV/bring-up pulse only — tie 0 in production |

### Credit-window and demand-aware policy

| Signal | Direction | Width | Description |
|---|---|---|---|
| `postpone_limit_i` | in | 4 | postpone bound from CSR; internally clamped to `POSTPONE_MAX` |
| `pullin_limit_i` | in | 4 | pull-in bound from CSR; internally clamped to 8 |
| `demand_i` | in | 1 | scheduler has read/write work waiting |
| `elastic_en_i` | in | 1 | Mode A elastic refresh enable |
| `pullin_idle_streak_i` | in | 8 | consecutive no-demand cycles before pull-in is allowed |
| `postpone_demand_streak_i` | in | 7 | consecutive demand cycles before the postpone threshold engages |
| `tcr_en_i` | in | 1 | Mode B temperature-compensated refresh enable |
| `trefi_derate_i` | in | 2 | 0 = 1x, 1 = 2x, 2 = 4x; encoding 3 clamps to 2 |

### Arbiter handshake and refresh outputs

| Signal | Direction | Width | Description |
|---|---|---|---|
| `refresh_req_o` | out | 1 | request to the scheduler; held until granted |
| `refresh_grant_i` | in | 1 | scheduler grant pulse |
| `grant_was_pb_i` | in | 1 | the granted command on the wire this cycle was a `REFpb` |
| `refresh_drain_active_o` | out | 1 | high during a burst-drain window; scheduler keeps granting REF back-to-back |
| `refresh_kind_o` | out | 1 | 0 = `REFab`, 1 = `REFpb` |
| `refresh_bank_o` | out | `BA_W` | per-bank refresh target; the device-mirror rotor output |
| `pending_refreshes_o` | out | 4 | current pending backlog |

### Observability

| Signal | Direction | Width | Description |
|---|---|---|---|
| `obs_refi_cnt_o` | out | 16 | live interval countdown |
| `obs_drain_remaining_o` | out | 4 | burst drain counter remaining |
| `obs_bank_rotor_o` | out | `BA_W` | rotor bank pointer |
| `obs_grants_total_o` | out | 16 | total refresh grants since reset |
| `obs_pullin_credit_o` | out | 4 | pull-in credits banked |
| `obs_postpone_events_o` | out | 16 | Mode A telemetry: refreshes actively postponed |
| `obs_pullin_events_o` | out | 16 | Mode A telemetry: pull-in grants |

: Table 2.16.2: Refresh controller ports

## Microarchitecture internals

### tREFI counter and effective interval

`r_refi_cnt` counts down from the effective interval. On expiry the machine either consumes one pull-in credit or increments the pending accumulator. The effective interval depends on the refresh mode and, in Mode B, the temperature derate:

```text
w_refi_eff       = refpb_mode_i ? (trefi_pb_i != 0 ? trefi_pb_i : t_refi_i >> 3)
                                : t_refi_i
w_derate_shift   = tcr_en_i ? (trefi_derate_i > 2 ? 2 : trefi_derate_i) : 0
w_refi_eff_derated = w_refi_eff >> w_derate_shift
```

The derate shift is applied to the reload value only. A CSR change mid-interval takes effect on the next reload; the running counter is never rescaled.

### Credit accumulator

`r_pending` is a saturating 4-bit counter with a ceiling of `MAX_PENDING = 8`. Each `tREFI` tick adds one unless a pull-in credit is available; each grant subtracts one. When `r_pending` reaches 8, further tREFI ticks are silently dropped — a data-retention hazard — so the request logic is deliberately biased to start asking before the ceiling.

`r_pullin` tracks refreshes performed ahead of their tREFI tick. A grant issued while `r_pending` is 0 and `r_pullin` is below 8 banks a credit instead of retiring a pending refresh.

### Postpone and pull-in limits

The JEDEC window permits ±8 refreshes, but the controller clamps the programmed postpone limit to `POSTPONE_MAX = MAX_PENDING - 2 = 6`:

```text
w_post_eff = (postpone_limit_i > 6) ? 6 : postpone_limit_i
w_pull_eff = (pullin_limit_i  > 8) ? 8 : pullin_limit_i
```

With the old clamp of 7, the busy-side request `r_pending > w_post_eff` first asserted at `r_pending == 8`, exactly the value at which the accumulator saturates and drops further ticks. Any latency between request and grant — finishing a burst, precharging banks, tRFC — then ate real refreshes. The deliberate 7→6 reduction gives one full `tREFI` of headroom before the JEDEC 8-postponed ceiling. The pull-in limit is clamped to 8, matching the JEDEC window.

### Idle confirmation and the three-case request

Demand is CAM occupancy, which can blink off for a few cycles between bursts. Treating those micro-gaps as idle would release postponed refreshes mid-stream and trigger pull-ins, so idle is confirmed only after a sustained no-demand streak. Mode A makes the threshold sweepable; when disabled, the inherited 16-cycle confirmation is used.

The request equation has three cases:

```text
if (w_idle)
    req = (r_pending > 0) || (r_pullin < w_pull_eff)
else if (elastic_en_i && r_demand_streak < postpone_demand_streak_i)
    req = (r_pending > 0)           // sporadic demand: strict
else
    req = (r_pending > w_post_eff)  // sustained demand: postpone threshold
```

When `elastic_en_i` is low, the equation reduces bit-for-bit to the v3 behavior. The demand streak is a saturating 7-bit counter reset on any no-demand cycle.

### Drain burst

When the previous burst is fully drained and `r_pending` is non-zero, `r_burst_remaining` loads `min(refresh_burst_i, r_pending)`. The drain window stays open while `r_burst_remaining > 0`, `r_pending > 0`, and `refresh_req_o` is asserted. Each grant decrements the remaining count. The drain is gated on the registered request so a postponed backlog does not accidentally open a preemption window.

### REFpb rotor

`r_bank_rotor` mirrors the device's internal per-bank refresh counter. It advances only when `grant_was_pb_i` is true, and it holds through `REFab` mode changes. Keying the advance off the granted command rather than `refpb_mode_i` keeps the mirror synchronized across mode boundaries; the device's counter persists, and clearing the controller's copy would desynchronize it.

### Why a credit machine and not an FSM

A refresh controller could be drawn as a state machine with states for "counting", "requesting", "draining", and "recovering". This block deliberately is not. The interval counter, pending accumulator, pull-in bank, drain quota, and rotor are all independent counters whose next-state functions are evaluated together each cycle. There is no central state to sequence them because their interaction is purely arithmetic: the request line is a combinational function of the counters, and the grant pulse is just another term in the counter updates. That structure matches the inherited pumice block, keeps the formal-property surface small, and makes Mode A/B additions pure data-path changes.

## FSM policy

There is no FSM. The block is a credit/state-counter machine: one counter for the interval, one saturating accumulator for pending refreshes, one counter for pull-in credits, and a handful of comparators that decide when to raise `refresh_req_o`. Mode selects are data, not control — they change the values loaded into counters and the bank address driven to the scheduler, but they do not add states.

The only sequential state beyond the counters is the registered output stage, which copies the combinational request and counter values into the output flops each cycle.

## Timing

The `tREFI` counter reloads with `w_refi_eff_derated` on every expiry and on an asserted `refi_reload_i`. Recovery timing after a refresh is owned by the arbiter: it loads `t_rfc_i` for `REFab` and `t_rfc_pb_i` for `REFpb` into its own recovery counter. Refresh is request-and-wait; it never preempts host traffic.

The request-to-grant latency is unbounded by design. The credit window absorbs scheduler back-pressure: the pending counter keeps ticking upward while the request is held, and the pull-in credit bank absorbs the opposite case where the bus is free before the next `tREFI` tick.

## Notes

- **Formal proof:** The retention and accounting properties are green in `formal/scoria/refresh_ctrl`. The proof must be re-derived when the interval arithmetic changes — REFpb mode, Mode B derate, or any future ceiling change. Carrying the all-bank proof forward unchanged would prove the wrong thing while appearing green.
- **`refi_reload_i` is a DV/bring-up knob:** it immediately reloads the counter with the current CSR value, saving the one stale interval that otherwise occurs after a `t_refi_i` change. Tie it to 0 in production; when tied low it has no effect, so the default build is bit-identical to a design without it.
- **Refresh is an ordinary bank occupant:** bank timers own the banks during refresh. A refresh request waits its turn in the scheduler like any other command, and the drain window only biases scheduling within the maintenance class.
- **Postpone clamp trap:** A CSR value above 6 still clamps to 6. Firmware cannot program the controller all the way to the JEDEC ceiling; the headroom is intentional.
- **REFpb mode-change trap:** The rotor must advance only on `grant_was_pb_i`, not on `refpb_mode_i`. A grant decided as `REFab` but counted as per-bank, or vice versa, desynchronizes the mirror and causes the controller to precharge the wrong bank ahead of each device refresh.
- **Telemetry semantics:** `obs_postpone_events_o` counts interval ticks that add to `r_pending` while the elastic postpone branch is actively withholding the request; `obs_pullin_events_o` counts grants issued when `r_pending` is zero. Both saturate at 0xFFFF rather than wrapping.
