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

All figures analytic at revision 0.1, one symbol per beat.

## Encoder

| From | To | Cycles |
|---|---|---|
| first data symbol in | first data symbol out | pipeline only: about 3 (unpack, skid, pack) |
| k-th data symbol in | first parity symbol out | pipeline + 1 |
| k-th data symbol in | last parity symbol out | pipeline + 2t |

: Table 5.3: Encoder latency

## Decoder

| Phase | Cycles | Notes |
|---|---|---|
| receive the block | n | syndromes complete with the last symbol |
| key equation | 2t (riBM) or <= 2t (Euclid) | skipped when the syndromes are all zero |
| Chien + Forney + corrector | n | one position per cycle; the buffer drains in step |
| pipeline | about 6 | unpack, skid, solver handoff, Forney, corrector, pack |
| **first symbol in to last symbol out** | **about 2n + 2t + 6** | 527 for RS(255,239) |
| first symbol in to first symbol out | about n + 2t + 6 | 277 |

: Table 5.4: Decoder latency

For a shortened code the n above is the shortened length (204 for DVB). For
S symbols per beat, divide the n terms by S; the 2t solver term does not
shrink.

## Buffer sizing

The block buffer must hold the current block while the next arrives during
the Chien walk: depth = n + 2t + pipeline symbols, rounded up to a power of
two -- 512 for the reference profile, 1024 for RS(544,514).
