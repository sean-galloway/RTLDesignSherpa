# TASK-013: math: Vedic (Urdhva-Tiryagbhyam) multiplier family — implement, then characterize on G2 and/or ASAP7

**Priority:** P3
**Status:** open
**Owner:** TBD

Filed 2026-10-31 (owner direction in session): the Vedic-multiplier claim
gets settled on *our* flows, not on the literature's baselines. Feeds from
TASK-012 (mining the Vedic-ALU collection); the three imported papers are
entries 22–24 in
`projects/components/riscv-ip/references/microarchitecture-papers.md`
(Deshpande & Mahajan 2014; Saha et al. 2011; Kaje & Nayak 8×8 FPGA).

## Scope

1. **Implement** `math_multiplier_vedic_ut_008` (8×8, per Kaje & Nayak's
   FPGA write-up), then `math_multiplier_vedic_ut_032` (per Deshpande &
   Mahajan / Saha et al.). House rules: shared-primitive adders where
   sensible, family test in val/math with golden-model parity like every
   other multiplier family, doc page under `docs/markdown/rtl-math/` with
   a `## References` section citing entries 22–24.
2. **Characterize on the Genesys 2 (Vivado)** at matched widths against the
   repo's best-in-class: `math_multiplier_dadda_tree_032`,
   `math_multiplier_wallace_tree_csa_032` (and the behavioral `*` baseline
   for honesty). Metrics: LUT/FF/DSP count, Fmax, and (if the board rig
   allows) a power delta. Verdict recorded on the rtl-math doc page:
   does UT beat, match, or lose to Dadda/Wallace on our flow.
3. **Alternative or addition (owner pick at scoping):** run the same
   comparison through the asic-trials ASAP7 flow instead of / as well as
   the G2 board — the literature's wins were mostly ASIC std-cell claims,
   so ASAP7 is the ground truth those papers were actually arguing about.

## Done when

- Both widths exist, are tested to family standard, and are filed in the
  registry.
- Characterization numbers (G2 and/or ASAP7 per the scoping pick) are
  committed with the verdict on the doc page.
- The verdict is written back into entry 22 of the riscv-ip
  microarchitecture reading list (claim confirmed / refuted / mixed).
