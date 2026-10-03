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

The key-equation solver is the block whose algorithm is not yet chosen (PRD
D11). Three candidates are attractive for a binary BCH decoder. They all
invert the same key equation from the t odd syndromes to the error-locator
polynomial Lambda(x). Because there is no Forney stage, the locator is the
only polynomial the Chien search needs.

| | inversionless BM (`"RIBM"`) | modified Euclidean (`"EUCLID"`) | step-by-step / PGZ (`"SMALL_T"`) |
|---|---|---|---|
| Algorithm | reformulated inversionless Berlekamp-Massey, Sarwate and Shanbhag 2001; seeded with the t odd syndromes | Sugiyama's Euclidean algorithm with cross-multiplication in place of division (Shao et al. 1985) | Massey 1965 step-by-step correction, or the Peterson-Gorenstein-Zierler direct matrix solve for small t |
| Array | 3t + 1 processing elements, 2 registers each | four register arrays: R and Q of 2t + 1 symbols, the shifted locator pair of 2t + 3 | control-heavy but small datapath: one or a few GF multipliers and a syndrome update loop |
| GF multipliers | 2 per element: 6t + 2 | 2 per coefficient of each pair: 8t + 8 | O(t^2) logic or a single iterative multiplier |
| Iterations | exactly 2t | data-dependent, t + 1 .. 2t | one per located error position, up to t |
| Critical path per iteration | one multiply and one XOR, no feedback across the array | cross-multiply feeding a degree comparison that drives the swap: longer | depends on implementation; often dominated by syndrome-update MUX tree |
| Control | discrepancy select and gamma update | two nominal degree counters, the normalise / cross / swap rule | position counter, syndrome-test loop, error-counter update |
| Readability | dense; the reformulation is not obvious from the textbook | the textbook algorithm, recognisable step by step | the simplest conceptually for very small t |
| Best fit | general t; the default if no consumer names a small-t profile | a cross-check and a readable alternative | t <= 8 (flash pages often sit here); smallest area at tiny t |

: Table 3.1: Key-equation solver candidates

No default is selected at revision 0.1. The choice is D11. Two solvers
agreeing as the cross-check, per the RS D11 philosophy, is the recommended
verification posture: the golden model runs every candidate on every block
and requires identical roots, and the RTL is built with whichever algorithm
the first consumer's rate and area target prefers.

Nothing else in the decoder knows which solver produced Lambda. Syndromes,
Chien, the block buffer and the corrector are the same modules in every
candidate build.
