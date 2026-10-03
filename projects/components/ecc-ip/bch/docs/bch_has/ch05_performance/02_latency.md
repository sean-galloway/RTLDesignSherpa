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

# Latency

All latency numbers are **TBD**. The exact values depend on PRD D6
(throughput architecture), D9 (bits per beat), D11 (solver algorithm), and
the pipeline depth chosen during micro-architecture.

## Encoder

| From | To | Cycles |
|---|---|---|
| first data bit in | first data bit out | pipeline only |
| k-th data bit in | first parity bit out | pipeline + 1 |
| k-th data bit in | last parity bit out | pipeline + (n - k) / B |

: Table 5.3: Encoder latency (placeholder)

## Decoder

| Phase | Cycles | Notes |
|---|---|---|
| receive the block | n / B | t odd syndromes complete with the last bit |
| key equation | <= 2t (BM) or data-dependent (Euclid / small-t) | skipped when the syndromes are all zero |
| Chien walk + bit flip + re-check | n / B | one or more positions per cycle |
| drain | k / B | the data bits leave while the next block is walked |
| pipeline | TBD | descriptor skids, solver handoff, verdict stage, output FIFO |
| first bit in to first bit out | TBD | dominated by 2n/B plus solver and pipeline |
| **first bit in to last bit out** | TBD | dominated by 2n/B + k/B plus solver and pipeline |

: Table 5.4: Decoder latency (placeholder)

For a shortened code the n above is the shortened length.

## Buffer sizing

The block FIFO must hold the current block while the next arrives during
the Chien walk. Its depth is TBD and will be sized once D6 and D9 are fixed.
The output FIFO holds a block's data bits while it waits for its verdict and
the next block's while that one is walked. The release-on-verdict rule costs
this second buffer and extra first-bit latency; it is the price of never
emitting an altered bit on an uncorrectable block.
