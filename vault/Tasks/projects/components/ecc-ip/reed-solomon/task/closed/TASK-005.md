# TASK-005: RS decoder flags f = 2t erasure blocks uncorrectable

**Priority:** P2
**Status:** closed 2026-10-08 — not a decoder defect; the decoder was correct
the whole time. The 2026-10-04 run's erasure flags never reached the decoder:
the symptom pattern (f = t corrects, f = 2t uncorrectable on every block,
f = 2t+1 refuses) is exactly errors-only decoding of an unmarked stream. The
run happened inside the uncommitted unified-injector migration window, when
the host regmap still wrote INJ_CFG.mark at bit 2 while the hardware had
already moved it to bit 3 (the 2-bit -> 3-bit mode-field widening).
f433fcaec (2026-10-05) committed the consistent flip — RDL, generated
regblock, and host regmap all move mark 2 -> 3 — which is the fix; the task
stayed open only because no board run re-executed the erasure sequence after
that commit. Closed with an era-exact Genesys 2 A/B: the stashed 2026-10-04
bitstream PASSES the same `init erasure` sequence with current host code, as
does a fresh current-main image.

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

## Resolution 2026-10-08

Attempted the task's scope in order; every step came back green on current
main, and the era-exact A/B on the board localizes the original failure to
the migration-window INJ_CFG.mark bit mismatch, not any RTL:

- Component DV: `dv/tests/fub/test_rs_decoder_core.py` includes the directed
  (0, 2t, corrupt) cell; at the exact board geometry RS(252,236) t=8 S=4 it
  passes at gate level. The board geometry was not in the matrix — added as a
  permanent profile so the sim keeps what the board found.
- Harness sim (`test_rs_loop_uart_erasure`, real UART bridge, unmodified
  host programs, TB-default ENABLE_COMPARE=1 so riBM-vs-Euclid agreement is
  real): f = 8 / 16 / 17 all PASS, both with the current injector and with
  the pre-#89 injector restored — the injector change is not the variable.
- Genesys 2, fresh image from current main (WNS +1.168 ns): `init erasure`
  blocks=16 — f=8 corr 16/16, f=16 corr 16/16 (sym=256), f=17 unc 16/16.
- Genesys 2, era-exact 2026-10-04 bitstream (stashed before the rebuild):
  the SAME sequence now PASSES identically. The failure was never in the
  decoder core — with the mark sideband dead, f=16 errors-only is
  uncorrectable on every block by definition, while f=8 corrects and f=17
  refuses, which is precisely the recorded symptom. The era image already
  contained the unified injector; what it ran against was the era HOST
  regmap, and the migration-window record shows the flip: f433fcaec moves
  INJ_CFG.mark from bit 2 to bit 3 in the RDL, the generated regblock, AND
  the host regmap in one commit — the stale-bit window is the defect, the
  commit is the fix, and it post-dates the failing run by hours.

## Notes

- Everything else about the erasure flow is verified on the Genesys 2
  (TASK: 2026-10-04 board bring-up): f = 8 corrected 16/16 with A=B
  solver agreement, f = 17 refused 16/16.
- The BCH tree has no erasure path (D5 open), so this is RS-only.
