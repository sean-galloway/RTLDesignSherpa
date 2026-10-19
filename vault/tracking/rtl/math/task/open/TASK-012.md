# TASK-012: math: mine the Vedic-ALU paper collection for usable arithmetic nuggets

**Priority:** P3
**Status:** open
**Owner:** TBD

Owner-provided folder (2026-10-17): `/home/seang/Downloads/Vedic-ALU/` —
seven PDFs. The question: does any technique in them earn a place in
`rtl/math` (or honestly converge with something already there)? This is a
mining task, not an implementation task: triage, compare against the
existing families, record verdicts. `rtl/math` already carries Wallace /
Dadda / carry-save / prefix adders, SRT + multiplicative dividers, and the
IEEE fp32/bf16/fp8 families — the bar is "measured, structural, and not
already what we have."

## Inventory

On-topic for `rtl/math`:

- `Ancient_Indian_Vedic_Mathematics_based_3.pdf` — Deshpande & Mahajan,
  "Ancient Indian Vedic Mathematics based 32-Bit Multiplier Design for High
  Speed and Low Power Processors," *IJCA* 95(24), June 2014. Urdhva-
  Tiryagbhyam ("vertically and crosswise") 32-bit multiplier in VHDL, speed
  and power claims vs conventional arrays.

Off-topic here (one-line verdict each is enough; pointer, not analysis):

- `more_papers_by_dr.rashmi_mahajan/Detection_of_an_Intruder_and_Protect.pdf`
  — IJEECS 7(3); security application, no arithmetic.
- `.../Dynamic_Partial_Reconfiguration_Implemen.pdf` — DPR *implementation of
  AES*; reconfigurable-compute context belongs to compute-eng's CGRA
  ambition, not `rtl/math`.
- `.../Internal_dynamic_partial_reconfiguration.pdf` and
  `.../High_Speed_Dynamic_Partial_Reconfigurati.pdf` — both *Indian J. Sci.
  Technol.* 3(4), Apr 2010; DPR methodology, same pointer as above.
- `.../Performance_Enhancement_of_AES_Algorithm.pdf` — AES enhancement; only
  skim for constant/GF(2^8) multiplier tricks (likely none new — MixColumns
  constants are shift/XOR).
- `.../Electronic_Glove_for_Troops_to_Interpret.pdf` — IJEAT 9(4), 2020;
  gesture interface, no arithmetic.

## What to look for (the nugget questions)

1. **Urdhva-Tiryagbhyam structure.** The 2×2-bit Vedic kernel recursed as a
   binary tree is structurally a carry-save partial-product array in
   disguise — compare honestly against `math_multiplier_wallace_tree_*` /
   `math_multiplier_dadda_*`: different reduction order? better critical
   path for FPGA DSP-less builds? If it is the same structure with a
   Sanskrit name, say so — that is still a worth-recording finding (the
   repo's convergent-thinking citation rule), and the comparison table is
   the deliverable.
2. **Nikhilam sutra** (all-from-9-and-last-from-10): multiplication of
   operands near a convenient base. In binary this converges with Booth-
   style recoding / near-power-of-two fast paths — check whether it offers
   anything over a radix-4 Booth arrangement the library does not already
   get from its Dadda/Wallace trees.
3. **Duplex squaring** (the Vedic squaring sutra): the library has no
   dedicated squarer. Is a duplex-based `math_squarer_*` structurally
   cheaper than multiply-by-self through the tree multipliers? Squarings
   feed Newton iterations (the fp32 sqrt's reciprocal-sqrt refinement and
   the bf16 reciprocal family), so a real win has immediate consumers.
4. **Low-power structuring.** The 2014 paper's power claims — any operand
   isolation / gating structure applicable to the existing
   `math_adder_*` / `math_multiplier_*` families, or FPGA-irrelevant?
5. **Side papers:** skim only; record the one-line verdicts above, plus
   anything that surprisingly touches arithmetic.

## Constraints and conventions

- The folder is in `~/Downloads` (ephemeral). Record verdicts here as you
  go so the findings survive the folder. If anything is adopted, archive
  the PDF into `rtl/math/references/` per the standing convention
  (`Topic__AuthorYear.pdf`, verified open-access copy, indexed in that
  dir's `README.md`, citation lines in the consuming module's
  `docs/markdown/rtl-math/` page). If the folder disappears mid-task, ask
  the owner before treating an unarchived paper as adopted.
- Any new module follows the family/generator conventions of `rtl/math`
  (filelists, `val/math` cocotb tests, golden-model discipline per the
  fp_testing/bf16_testing base classes).
- Educational benefit over IP, per the area's ethos: a measured negative
  result ("Vedic tree == carry-save array at N=32, here's the data") is a
  perfectly good close.

## Done when

- Every PDF in the folder carries a one-line verdict in this file's
  inventory (nugget / no-action / out-of-scope-with-pointer).
- The on-topic findings are recorded: sutra → repo-family mapping, the
  honest structural comparison vs Wallace/Dadda/carry-save, and a
  go/no-go per nugget with expected measured deltas.
- Each adopted nugget has its paper archived + indexed in
  `rtl/math/references/` per convention (or a recorded reason not to), and
  any new module has a filed follow-on task — this task closes on the
  mining, not the RTL.
