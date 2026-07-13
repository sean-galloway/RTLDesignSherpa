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

# Bank Timers and Cross-Bank Timers

Per-bank JEDEC timing is tracked by an **FSM-free** `bank_timer` per (rank, bank); cross-bank / bus-turnaround timing is tracked by `global_timers`. There is no multi-state bank machine in this design.

## `bank_timer`

### Purpose

Track one DRAM bank's JEDEC "safe" timing. RTL: `rtl/fub/bank_timer.sv`. It is **not a state machine** — it is a set of preset/decrement countdown timers plus a trivial row-open register and a single auto-precharge bit. The arbiter drives one `set_*` strobe per issued command; each timer loads its config value on its trigger, free-runs decrementing (saturating at 0), and reports its constraint as "safe" when the count is 0.

Because the per-command `safe_*` outputs are a purely combinational AND of the relevant timers behind a **single register stage** (the counter), a just-issued command is reflected one cycle later with no multi-stage lag. This was the point of retiring the old 3-state FSM, whose double-registered state was the root cause of the refresh-vs-ACT and column-vs-PRE hazards.

### Instantiation

`pumice_bank_timers` (`rtl/fub/pumice_bank_timers.sv`) stamps one `bank_timer` per `(rank, bank)` pair — for the default (`NUM_RANKS=1`, `NUM_BANKS=8`) that is 8 instances. It routes the arbiter's `evt_*` event strobes to the addressed bank and fans the per-bank readiness back out to the arbiter.

### Timers

Each timer loads on its event, counts down, and saturates at 0:

| Timer        | JEDEC     | Loaded on           | Gates             |
|--------------|-----------|---------------------|-------------------|
| `r_rcd`      | tRCD      | ACT                 | `safe_rd`/`safe_wr` |
| `r_ras`      | tRAS      | ACT                 | `safe_pre`        |
| `r_rc`       | tRC       | ACT                 | `safe_act`        |
| `r_rp`       | tRP       | explicit PRE or auto-PRE fire | `safe_act` |
| `r_preblk`   | tRTP (RD) / tWR (WR) | RD / WR    | `safe_pre` only   |

The timer config inputs (`t_rcd_i`, `t_rp_i`, `t_ras_i`, `t_rc_i`, `t_wr_i`, `t_rtp_i`) are controller-cycle, command-relative values supplied by the scheduler layer from CSRs.

### Row State (minimal — not an FSM)

Two elements track row occupancy:

- `r_row_valid` + `r_open_row` — set on ACT (captures `row_i`), cleared on an explicit PRE or when an auto-precharge completes.
- `r_ap_pending` — a single bit set from the `set_ap_i` qualifier on a RD/WR. When both `r_preblk` and `r_ras` reach 0, the auto-precharge "fires" (`w_ap_fire`): the row closes internally and tRP loads — with no scheduler PRE and no extra states.

### Combinational Safe Outputs

The readiness outputs are combinational off the timers (single register stage behind):

- `safe_act_o = !r_row_valid && (r_rp == 0) && (r_rc == 0)` — bank precharged, tRP since PRE, tRC since last ACT.
- `safe_rd_o = r_row_valid && (r_rcd == 0) && !r_ap_pending` — row open, tRCD met, not auto-precharging.
- `safe_wr_o = safe_rd_o` — same condition.
- `safe_pre_o = r_row_valid && (r_ras == 0) && (r_preblk == 0) && !r_ap_pending` — row open, tRAS and tRTP/tWR met, not auto-precharging.

Open-page behavior falls out naturally: RD/WR only load `r_preblk` and (optionally) the auto-PRE bit, so column commands stream to an open row. The tCCD / tWTR / tRTW turnaround constraints are enforced globally in `global_timers` and ANDed by the arbiter, not here.

### Observability State

For debug only, `state_o` is derived combinationally from the timers into a `bank_state_e` value (`BANK_IDLE`, `BANK_ACTIVATING`, `BANK_ACTIVE`, `BANK_PRECHARGING`). No downstream logic depends on it — it is purely an observation output alongside the `obs_*_nz` timer-nonzero flags.

### Refresh Interaction

There is no per-bank refresh handshake. The arbiter serializes refresh: on a refresh request it precharges active banks one per cycle (using `safe_pre` / `bank_row_active`), then issues `REF` once no bank has an open row. The `bank_timer` participates only through its standard row-open and `safe_pre` outputs.

---

## `global_timers`

### Purpose

Enforce the cross-bank and shared-bus turnaround constraints that a single bank cannot see locally. RTL: `rtl/fub/global_timers.sv`. Implemented once (not per bank) because these constraints are inherently global.

### Tracked Constraints

| Constraint | Description                                            | Scope        |
|------------|--------------------------------------------------------|--------------|
| `tFAW`     | At most 4 ACTs in any rolling tFAW window              | per-rank     |
| `tRRD`     | Minimum gap between any two ACT commands               | per-rank     |
| `tWTR`     | Write-to-read data-bus turnaround                      | global       |
| `tRTW`     | Read-to-write data-bus turnaround                      | global       |
| `tCCD`     | Column-to-column spacing                               | global       |

### Interface

The timers consume the arbiter's `evt_act` (with `evt_act_rank`), `evt_rd`, and `evt_wr` strobes and produce the readiness window signals the arbiter ANDs into its pick:

- `tfaw_window_ok_o` / `trrd_window_ok_o` — per-rank vectors, gate `ACT`.
- `twtr_global_ok_o` / `trtw_window_ok_o` / `tccd_window_ok_o` — gate column commands.

tFAW / tRRD are kept per-rank because they are device-local activate-stagger limits; the data-bus turnaround windows (tWTR / tRTW / tCCD) are global because the DQ bus is shared across ranks.
