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

# Solver Options

The key-equation solver is the one block with two implementations, selected
by `KES_ALGO` (PRD D11). They have identical ports and produce the same
error-locator and error-evaluator polynomials up to a common nonzero scale
factor -- which is harmless, because Chien search finds the same roots and
Forney takes the ratio of the two polynomials.

| | riBM (`"RIBM"`, default) | modified Euclidean (`"EUCLID"`) |
|---|---|---|
| Algorithm | reformulated inversionless Berlekamp-Massey, Sarwate and Shanbhag 2001 | Sugiyama's Euclidean algorithm with cross-multiplication in place of division (Shao et al. 1985), every polynomial kept top-aligned so no shifter is needed |
| Array | 3t + 1 processing elements, 2 registers each | four register arrays: R and Q of 2t + 1 symbols, the shifted locator pair of 2t + 3 |
| GF multipliers | 2 per element: 6t + 2 (50 at t = 8) | 2 per coefficient of each pair: 8t + 8 (72 at t = 8) |
| Iterations | exactly 2t | data-dependent, t + 1 .. 2t (2t + 1 at t <= 2 when a leading syndrome is zero), plus one cycle for the finishing check |
| Evaluator produced | the high half of S(x)Lambda(x); Forney uses X^(1 - b - 2t) | the textbook S(x)Lambda(x) mod x^2t; Forney uses X^(1 - b). The Forney block's `OMEGA_HIGH_HALF` constant follows `KES_ALGO`; nothing else in the decoder changes |
| Critical path per iteration | one multiply and one XOR, no feedback across the array | cross-multiply feeding a degree comparison that drives the swap: longer |
| Control | discrepancy select and gamma update | two nominal degree counters, the normalise / cross / swap rule |
| Readability | dense; the reformulation is not obvious from the textbook | the textbook algorithm, recognisable step by step |
| Fallback | -- | the degree-computationless variant (Baek and Sunwoo 2006) removes the counters at the cost of a wider element |

: Table 3.1: The two key-equation solvers

riBM is the default because its per-iteration critical path is shorter and
does not cross the array, which is what sets the decoder's clock at high t.
Euclid is kept for readability and as the cross-check: both are bit-exact
against `dv/tbclasses/rs_model.py`, which runs both solvers on every block
of its validation and requires identical decoder output (900 of 900 blocks
on six profiles), and the decoder core test runs the same profiles with
either solver selected.

Nothing else in the decoder knows which solver produced Lambda. Syndromes,
Chien, Forney, the block buffer and the corrector are the same modules in
both builds.
