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

# Global Timers (`scoria_global_timers`)

**Module:** `scoria_global_timers.sv`
**Location:** `rtl/fub/`
**Category:** JEDEC timing
**Parent:** `scoria_scheduler_layer`
**Status:** complete, sim-verified, formal-proven

---

## Purpose

`scoria_global_timers` tracks the command-spacing constraints that span banks or ranks: per-rank `tFAW` and `tRRD`, and global `tWTR`, `tRTW`, and `tCCD`. It is pure counters; there is no FSM. The outputs are registered readiness flags consumed by the command arbiter.

## Parameters

| Parameter | Type | Range | Default | Meaning |
|---|---|---|---|---|
| `NUM_RANKS` | int | 1+ | 1 | ranks per channel |
| `NUM_BANKS` | int | 4..16 | 8 | banks per rank |
| `RKW` | int | derived | `$clog2(NUM_RANKS)` or 1 | rank index width |
| `BKW` | int | derived | `$clog2(NUM_BANKS)` | bank index width |

: Table 2.14.1: Global timers parameters

## Interface

### Timing CSRs and events

| Signal | Direction | Width | Description |
|---|---|---|---|
| `t_faw_i` | in | 8 | tFAW window |
| `t_rrd_i` | in | 8 | ACT-to-ACT spacing per rank |
| `t_wtr_global_i` | in | 8 | write-to-read turnaround |
| `t_rtw_i` | in | 8 | read-to-write turnaround |
| `t_ccd_i` | in | 8 | CAS-to-CAS spacing |
| `evt_act_i` | in | 1 | activate event |
| `evt_act_rank_i` | in | `RKW` | rank of the activate event |
| `evt_rd_i` | in | 1 | read event |
| `evt_wr_i` | in | 1 | write event |

: Table 2.14.2: Global timers inputs

### Readiness and observability

| Signal | Direction | Width | Description |
|---|---|---|---|
| `tfaw_window_ok_o` | out | `NUM_RANKS` | at least one tFAW slot is free |
| `trrd_window_ok_o` | out | `NUM_RANKS` | tRRD satisfied |
| `twtr_global_ok_o` | out | 1 | tWTR satisfied |
| `trtw_window_ok_o` | out | 1 | tRTW satisfied |
| `tccd_window_ok_o` | out | 1 | tCCD satisfied |
| `obs_faw_nz_o` | out | `NUM_RANKS` | tFAW counter non-zero |
| `obs_trrd_nz_o` | out | `NUM_RANKS` | tRRD counter non-zero |
| `obs_twtr_nz_o` | out | 1 | tWTR counter non-zero |
| `obs_trtw_nz_o` | out | 1 | tRTW counter non-zero |
| `obs_tccd_nz_o` | out | 1 | tCCD counter non-zero |

: Table 2.14.3: Global timers outputs

## Microarchitecture internals

### tFAW

Each rank maintains a 4-deep sliding window of countdowns. On an ACT, the slot with the smallest remaining count is loaded with `t_faw_i`. `tfaw_window_ok_o[r]` is high when at least one slot in rank `r` is at zero.

### tRRD

Each rank has a single countdown that reloads on every ACT to that rank.

### tWTR, tRTW, tCCD

These are global single counters. `tWTR` reloads on a write, `tRTW` on a read, and `tCCD` on any column command (`evt_rd_i || evt_wr_i`).

### Next-state alignment

The module computes one next-state function for each counter family and feeds both the counter flops and the readiness flops from that same function. This is the fixed-form structure inherited from pumice with the one-cycle-lag defect removed.

The readiness outputs are computed as early comparators rather than as `w_*_nxt == 0`, so the late event signals drive only one-bit mux selects:

```text
tfaw_ok_nxt = on_ACT ? (any_free_other || (t_faw_i == 0)) : any_free_all
trrd_ok_nxt = on_ACT ? (t_rrd_i == 0) : (r_trrd_cnt <= 1)
twtr_ok_nxt = on_WR ? (t_wtr_global_i == 0) : (r_twtr_cnt <= 1)
trtw_ok_nxt = on_RD ? (t_rtw_i == 0) : (r_trtw_cnt <= 1)
tccd_ok_nxt = on_COL ? (t_ccd_i == 0) : (r_tccd_cnt <= 1)
```

### Output flops

The readiness flops reset to all-ones, so every window starts ready:

```systemverilog
tfaw_window_ok_o <= '1;
trrd_window_ok_o <= '1;
twtr_global_ok_o <= 1'b1;
trtw_window_ok_o <= 1'b1;
tccd_window_ok_o <= 1'b1;
```

## FSM policy

No FSM. The block is counters and comparators.

## Timing

The outputs are registered, so a command accepted in cycle `N` closes the relevant window in cycle `N+1`. The next-state derivation guarantees that the readiness flop and the counter flop agree on the same cycle, not one cycle apart.

## Notes

- **The fixed-form warning is mandatory.** pumice's original version published readiness one cycle late: the registered status flop sampled the current counter state instead of the next state, so the flags permitted `tCCD` and `tRTW` violations for one cycle after the command that should have closed them. The fix computes one next-state function and feeds both the counter and its status flop from it. A fresh behavioral reimplementation would reintroduce the defect, because the behavioral description does not mention the flop. Copy the module. This is the warning from HAS Chapter 3.1, restated here as a design note.
- **Consumers no longer compensate.** The arbiter previously added `!(w_fire_out && r_do_rd)` terms and stopped using `tccd_ok_i` to close its own blind spot. With the fixed global timers, those compensations are no longer required; the formal environment assumes only the published outputs.
- **Formal proof.** The block is proven in `formal/scoria/global_timers/scoria_global_timers.sby`.
