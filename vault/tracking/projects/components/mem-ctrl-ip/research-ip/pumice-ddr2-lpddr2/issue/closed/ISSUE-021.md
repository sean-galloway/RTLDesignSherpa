# ISSUE-021: mc_training_plane ties ZQ demand to 0 — defer/ZQCL/overdue policy unreachable

> Source: mc_init_plane work (Task 5), 2026-10-15.
> Related: TASK-042 (runtime ZQ), `mc_lpddr2_zq_ctrl` header (Mode-C
> placement policy).

**Priority:** P2
**Status:** closed 2026-10-29 (option 1 taken, owner's call; see the closing entry)
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

## Resolution (2026-10-29, owner: "do the recommended" = option 1)

`mc_training_plane` gained `demand_i`, wired to the ZQ block's `demand_i`
in place of the `1'b0`. Both cores drive it from the store's scheduler
request vectors, `(|w_wr_sch_v) || (|w_rd_sch_v)`, the same term the
scheduler plane derives its own `w_demand` from for the page policy and
refresh postpone. The plane is instantiated only by `granite_core`,
`pumice_core` and its TB (scoria and andesite carry their own ZQ blocks;
scoria's does not use demand), so the change is those four files plus the
test. For DDR2 builds `HAS_LP_ZQ` is 0 and nothing is instantiated, so the
shipped DDR2 bitstreams are untouched; LPDDR2 builds now get the Mode-C
policy their CSRs already describe.

The plane test (`test_mc_training_plane.py`) drives the port and pins the
policy at the plane boundary: deferral under demand with `zq_overdue_o`
high and no request, release on loss of demand as ZQCL (`{MR10, 0xAB}`),
the `zq_overdue_max` cut as ZQCL with demand still high, and the knob's
OFF state (`zq_defer_en=0`, demand held: ZQCS at the interval, overdue 0).
6/6 on a clean build. The earlier test's "pinned at 0" case is now simply
the no-demand case. Regressions: common-ip fub+macro, granite top func,
pumice top func-parallel (results in the commit).
