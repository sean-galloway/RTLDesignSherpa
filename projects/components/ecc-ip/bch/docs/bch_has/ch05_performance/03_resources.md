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

# Resources

All resource numbers are **TBD**. The PRD requires (R5) that no number be
claimed before it is measured in an out-of-context synthesis fixture per the
repository's practice. Chapter 6.5 is the plan that replaces this table with
measurements.

## GF primitives per core

The BCH core reuses the reed-solomon GF primitives (`gf_mul_const`,
`gf_mul`, `gf_inv`) without duplicating them. The counts below are the
expected structural forms once the RTL exists; they are not measured.

| Primitive | Encoder | Decoder | Formula (target) |
|---|---:|---:|---|
| `gf_mul_const` | 2t | 2t + t | generator taps + syndrome constant multiplies |
| `gf_mul` | 0 | solver-dependent | BM: 6t + 2; Euclid: 8t + 8; small-t: O(t^2) or fewer |
| `gf_inv` | 0 | 0 or 1 | binary BCH needs no Forney inverse; a small-t solver may use one |
| GF symbol registers | 2t | t + solver array | encoder 2t parity; decoder t odd syndromes + locator |

: Table 5.5: GF primitive counts (analytic placeholder)

## Storage

| Item | Size | Formula |
|---|---|---|
| block FIFO | TBD | (n + latency, rounded up) x B bits, plus erasure bit if enabled |
| output FIFO | TBD | (2k + latency, rounded up) x (B + 1): corrected bit, hit, last |
| re-check syndromes | t cells | a second `syndrome_unit` over the corrected stream |
| log / antilog tables (`gf_inv`) | 2 x 2^m x m | LUT ROM at small m, BRAM or Itoh-Tsujii at large m |
| skid buffers | 2 (encoder), 3 (decoder), 2 deep | stage boundaries |

: Table 5.6: Storage (placeholder)

## Order of magnitude

A `gf_mul_const` at m = 8 is at most 8 XOR trees of up to 8 inputs; a
`gf_mul` is an m x m AND array with reduction. The total arithmetic cost
scales with t and m, and with the D6 throughput choice. The first
out-of-context run will say where the BCH decoder lands on the target parts.

## Scaling

- m grows: every multiplier grows from m x m, and the log/antilog tables
  scale as 2^m x m.
- t grows: syndrome cells, solver array and Chien lanes all grow linearly
  with t.
- Shortening: n is smaller than 2^m - 1, so the Chien walk and buffers are
  shorter but the arithmetic width is unchanged.
- Bits per beat B (D9): syndrome and Chien datapaths scale with B; the
  solver is unaffected.
