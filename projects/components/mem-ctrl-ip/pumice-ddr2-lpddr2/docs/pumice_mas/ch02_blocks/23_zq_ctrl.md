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

# ZQ Calibration Controller (`pumice_zq_ctrl`)

**Module:** `pumice_zq_ctrl.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `pumice_training_layer`
**Status:** implemented and FUB-tested (LPDDR2); inert for DDR2 builds — no ZQ pin

> This FUB never emits a DRAM command. It raises a request, and on grant the
> arbiter issues the command from the FUB's payload verbatim. LPDDR2 has no
> ZQCS/ZQCL opcode, so both calibrations are MRW writes to MR10
> (OP = `8'h56` for ZQCS, `8'hAB` for ZQCL) — the FUB packs the MR index and
> OP into its row output and stops there.

---

## Purpose

Periodic ZQ calibration for LPDDR2, as maintenance traffic. JESD209-2F
§5.13.3 expects ZQCS (short) at regular intervals and ZQCL (long) to
re-establish the ±15% RON window after calibration has been deferred too
long. The block is a port of `scoria_zq_ctrl` to LPDDR2 semantics: wait the
programmed interval, ask for the bus, hold the post-grant quiet window,
start the next interval. It is deliberately small.

The run condition is `zq_en_i && init_done_i && (memtype_i ==
MEMTYPE_LPDDR2) && interval != 0`, so the block is completely inert for DDR2
builds. LPDDR2-S4 wants all banks precharged for ZQ and LPDDR2-N allows
Idle-or-Active; the conservative all-banks-idle grant contract the arbiter
enforces satisfies both.

## Parameters

| Parameter    | Default | Meaning                    |
|--------------|---------|----------------------------|
| `MR10_INDEX` | 10      | MR index for ZQ calibration; lands in `zq_row_o[13:8]`. |

## The Four FSM States

`r_state` is 2 bits. Unlike the FSM-free `refresh_ctrl`, this block has a
genuinely sequential lifecycle — wait, ask, hold, and a deferred-wait state
for the placement policy:

```text
ZQ_IDLE  — counting down r_interval to the next calibration
ZQ_REQ   — requesting the arbiter, waiting for grant
ZQ_HOLD  — granted; holding the post-grant quiet window before reload
ZQ_DEFER — interval expired but demand is high, holding off (Mode C)
```

- **`ZQ_IDLE`** decrements `r_interval`. On zero: if `zq_defer_en_i &&
  demand_i`, enter `ZQ_DEFER`; otherwise `ZQ_REQ`. The counter seeds from
  `t_zqcs_interval_i` at reset (not zero) so the first interval is full
  length even if enable comes up late — same latent-coupling removal
  scoria made.
- **`ZQ_REQ`** holds `zq_req_o` until `zq_grant_i`, then loads `r_hold`
  with `t_zqcs_i` or `t_zqcl_i` (selected by `r_is_zqcl`), bumps
  `r_total`, and enters `ZQ_HOLD`. While waiting with `demand_i` high,
  `r_overdue` sets — a request that withdrew itself under load would
  starve silently, so the starvation is made visible.
- **`ZQ_HOLD`** counts `r_hold` to zero, then returns to `ZQ_IDLE` and
  reloads `r_interval`. The hold itself does not block traffic; the block
  just declines to start the next interval early. The actual bus-quiet
  enforcement is the arbiter's job (below).
- **`ZQ_DEFER`** exits to `ZQ_REQ` when demand drops, when
  `zq_defer_en_i` is cleared, or when `overdue_max_i != 0 && r_defer_cnt
  >= overdue_max_i`. Any exit with `r_defer_cnt != 0` requests **ZQCL**
  instead of ZQCS — that is the escalation path. `r_overdue` is set the
  whole time the block sits deferred.

## Interface

### Run gating and configuration (from `CAL_*` CSRs via the training layer)

| Signal              | Direction | Width | Description                                           |
|---------------------|-----------|-------|-------------------------------------------------------|
| `mc_clk`            | in        | 1     | controller clock                                       |
| `mc_rst_n`          | in        | 1     | active-low reset                                       |
| `zq_en_i`           | in        | 1     | periodic ZQ enable (`CAL_CTRL.zq_en`)                  |
| `init_done_i`       | in        | 1     | scheduler init complete                                 |
| `memtype_i`         | in        | 1     | `MEMTYPE_LPDDR2` required                               |
| `t_zqcs_interval_i` | in        | 32    | MC cycles between calibrations; 0 disables              |
| `t_zqcs_i`          | in        | 16    | post-grant hold, ZQCS                                   |
| `t_zqcl_i`          | in        | 16    | post-grant hold, ZQCL                                   |
| `zq_defer_en_i`     | in        | 1     | Mode-C deferral under sustained demand                  |
| `overdue_max_i`     | in        | 13    | max deferral cycles; 0 = no cap                         |
| `demand_i`          | in        | 1     | scheduler has read/write work (tied 0 in the layer today — see Notes) |

### Arbiter handshake and telemetry

| Signal            | Direction | Width | Description                                           |
|-------------------|-----------|-------|-------------------------------------------------------|
| `zq_req_o`        | out       | 1     | request; high in `ZQ_REQ`                               |
| `zq_grant_i`      | in        | 1     | arbiter grant (single cycle)                            |
| `zq_op_o`         | out       | —     | always `OP_MRS` — LPDDR2 ZQ is pure MRW                 |
| `zq_bank_o`       | out       | 3     | 0; the MR index lives in the row field                  |
| `zq_row_o`        | out       | 18    | `{4'd0, MR10_INDEX[5:0], OP[7:0]}` — MRW row packing    |
| `zq_is_zqcl_o`    | out       | 1     | 1 = the current request is a ZQCL                       |
| `cal_busy_o`      | out       | 1     | high in `ZQ_HOLD`; the bus-quiet window                 |
| `obs_zqcs_total_o`| out       | 16    | calibrations issued since reset (`CAL_STATUS.zqcs_total`) |
| `obs_overdue_o`   | out       | 1     | interval expired without grant, or deferred (`CAL_STATUS.zq_overdue`) |

## Timing / Behavior

One grant per calibration. The interval reloads at the end of `ZQ_HOLD`, so
grant-to-next-request spacing is `t_zqcs_interval_i + hold` cycles.
`t_zqcs_interval_i` counts mc_clk cycles; convert from the JEDEC tZQCS
interval at the MC frequency.

Traffic blocking is the arbiter's job, not this FUB's: `cal_busy_o` from
the training layer folds into the arbiter's `w_out_safe` term, which blocks
every demand-class fire during the hold window. That keeps the BUG-003
discipline intact — `w_fire_out == cmd_valid_o && cmd_ready_i` holds by
construction, and the new gate never touches the pick cone.

MR10 writes are transient commands: they flow through the arbiter
maintenance path and are never shadowed into the `mode_register` FUB, same
rule `init_sequencer`'s ZQ step follows today.

## Verification Notes (cocotb test plan)

Verified by `dv/tests/fub/test_pumice_zq_ctrl.py`: interval expiry →
request, grant → hold → reload, Mode-C deferral under sustained demand,
overdue expiry selects ZQCL, `zq_row_o` MRW packing (`MR10` + `0x56`/`0xAB`),
`obs_zqcs_total_o` accounting, and DDR2-inert behavior
(`memtype_i != MEMTYPE_LPDDR2` never requests).

## Notes

- **ZQ never preempts.** It raises `zq_req_o` and waits, matching the
  family doctrine that maintenance is request-and-wait traffic.
- **`demand_i` is tied off in the layer today.** The training layer grounds
  `demand_i` (`1'b0`), so the `ZQ_DEFER` entry condition (`zq_defer_en_i &&
  demand_i` at interval expiry) can never fire: expiry goes straight to
  `ZQ_REQ`, the ZQCL escalation path is unreachable, and `obs_overdue_o`
  never sets. Mode-C and the overdue cap are dormant until something wires
  this port to the scheduler's demand indicator. The RTL keeps the FSM so
  the policy is one wire away.
- **Overdue is a starvation indicator, not an error.** High `obs_overdue_o`
  under load says calibration is losing arbitration; it should be bounded
  by `overdue_max_i` or the workload starves ZQ entirely.

## Open Questions / Future Work

- **Demand wiring.** `demand_i` grounded in `pumice_training_layer`; feed it
  from the scheduler's demand indicator to make Mode-C placement live.
- **Multi-rank.** Single-rank today; the rank loop for a shared ZQ resistor
  is a documented `generate` hook.
