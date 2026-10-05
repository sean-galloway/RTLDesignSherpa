# TASK-005: RS decoder flags f = 2t erasure blocks uncorrectable

**Priority:** P2
**Status:** open 2026-10-04
**Owner:** TBD

The erasure path corrects f = 8 (t) erasures on the board and refuses
f = 17 (2t+1) by inspection, but the boundary case **f = 16 = 2t is flagged
uncorrectable on every block** — the design intent (and the B-stage logic)
say it should correct: `w_b_bad_final` is forced clean on `w_er_t_zero`
(`rs_decoder_core.sv`, BE_* FSM), i.e. f = 2t is meant to pass the solve
stage, and the code bound `2*mu + f <= 2t` allows it.

Found by the `erasure` sequence on the Genesys 2 (`seq_erasure.py`),
`f=16` run: `ok/corr/unc = 0/0/16, sym=0, data_err=True, crc_ok=True`.

## Evidence

- `rs_decoder_core.sv` BE stage: `w_b_bad = w_kes_deg_err || (w_kes_deg >
  w_budget) || ((w_kes_deg == 0) && (w_er_f == 0))`, with
  `w_budget = (T2 - f) >> 1` and `w_b_bad_final = w_er_t_zero ? 1'b0 :
  w_b_bad`. At f = 2t the budget is 0 and t_zero forces the verdict clean,
  so the uncorrectable must come from downstream.
- Final verdict (`w_uncorrectable_final`): `r_sv2_correct && (r_sv2_bad ||
  (r_sv2_roots != r_sv2_deg) || r_sv2_den_zero || !w_rechk_zero)`. One of
  the four terms fires for the f = 2t combined locator (degree 16,
  LAM_N = T2+1 arrays): likely candidates are the C-stage `bad` carried
  from the combined degree against a t-sized threshold, a Forney
  `den_zero` on the combined locator's derivative, or the second-syndrome
  re-check on the shortened profile RS(252,236).

## Scope

- Reproduce in the component DV first: extend
  `dv/tests/fub/` (or the erasure unit's own coverage) with a directed
  f = 2t case; the board found it, the sim must keep it.
- Identify which verdict term fires (status skid fields are readable per
  block; the erasure unit's `o_deg_c`/`o_f_over` too).
- Fix where the fix belongs: if the C-stage threshold assumes deg <= t for
  the erasure build, it must use the combined-degree bound (T2) under
  ERASURE_SUPPORT; re-run the full board `erasure` sequence (f = 8 / 16 /
  17) plus the dual-solver agreement.
- Do NOT relax the f = 2t+1 refuse-by-inspection path to make this pass;
  that case is correct today.

## Notes

- Everything else about the erasure flow is verified on the Genesys 2
  (TASK: 2026-10-04 board bring-up): f = 8 corrected 16/16 with A=B
  solver agreement, f = 17 refused 16/16.
- The BCH tree has no erasure path (D5 open), so this is RS-only.
