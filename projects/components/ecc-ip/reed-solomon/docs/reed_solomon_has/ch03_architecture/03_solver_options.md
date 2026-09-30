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
| Algorithm | reformulated inversionless Berlekamp-Massey, Sarwate and Shanbhag 2001 | Sugiyama's Euclidean algorithm in the inversionless cross-multiplying systolic form of Shao et al. 1985 |
| Array | 3t + 1 processing elements | 2t processing elements |
| GF multipliers | 2 per element: 6t + 2 (50 at t = 8) | 4 per element: 8t (64 at t = 8) |
| Iterations | exactly 2t | at most 2t; may stop early when the remainder degree falls below t |
| Critical path per iteration | one multiply and one XOR, no feedback across the array | cross-multiply feeding a degree comparison that drives the swap: longer |
| Control | discrepancy select and gamma update | two degree counters and the swap rule |
| Readability | dense; the reformulation is not obvious from the textbook | the textbook algorithm, recognisable step by step |
| Fallback | -- | the degree-computationless variant (Baek and Sunwoo 2006) removes the counters at the cost of a wider element |

: Table 3.1: The two key-equation solvers

riBM is the default because its per-iteration critical path is shorter and
does not cross the array, which is what sets the decoder's clock at high t.
Euclid is kept for readability and as the cross-check: both are verified
against the same golden model on the same blocks, and the equivalence test is
direct -- identical Chien root sets and identical Forney values for every
corrected block.

Nothing else in the decoder knows which solver produced Lambda. Syndromes,
Chien, Forney, the block buffer and the corrector are the same modules in
both builds.
