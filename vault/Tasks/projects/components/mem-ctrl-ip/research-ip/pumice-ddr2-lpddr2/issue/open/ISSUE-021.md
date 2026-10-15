# ISSUE-021: mc_training_plane ties ZQ demand to 0 — defer/ZQCL/overdue policy unreachable

> Source: mc_init_plane work (Task 5), 2026-10-15.
> Related: TASK-042 (runtime ZQ), `mc_lpddr2_zq_ctrl` header (Mode-C
> placement policy).

**Priority:** P2
**Status:** open
**Owner:** TBD

## Finding

`common-ip/rtl/macro/mc_training_plane.sv:125` instantiates
`mc_lpddr2_zq_ctrl` with `.demand_i(1'b0)`. The ZQ FSM's Mode-C policy is
entirely demand-gated:

- `ZQ_DEFER` is only entered from `ZQ_IDLE` when `zq_defer_en_i && demand_i`
  — with demand tied 0 the state is **unreachable**.
- `r_is_zqcl` is only set on `ZQ_DEFER` exits, so **ZQCL never issues** in the
  composed plane; every interval expiry issues ZQCS regardless of
  `t_zqcl_i`/`zq_overdue_max_i`.
- `obs_overdue_o` only rises while waiting for grant under demand
  (`ZQ_REQ && demand_i`) or inside `ZQ_DEFER` — with demand tied 0 it is
  **constant 0** and `zq_overdue_max_i` is dead config.

The fub carries the full policy and is now fub-verified
(`common-ip/dv/tests/fub/test_mc_lpddr2_zq_ctrl.py`); the plane composition
silently drops half of it.

## Options

1. Add a `demand_i` input to `mc_training_plane` (sourced from the scheduler
   plane's `|rd_sch_valid || |wr_sch_valid` at the cores, the same shape the
   page-policy `demand_i` uses) and wire it through.
2. Drop the defer/ZQCL/overdue knobs from the plane's port list if the
   products decide they never want Mode-C (then also strip the CSRs).

Owner decision needed. Until then the shipped behavior is: periodic ZQCS at
`zq_interval_i`, no deferral, no ZQCL, no overdue.
