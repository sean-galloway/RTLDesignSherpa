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
| Chien + Forney + re-check walk | n | one position per cycle; the block is released only after its verdict |
| drain | k | the data symbols leave while the next block is walked |
| pipeline | about 8 | descriptor skids, solver handoff, the correct-stage register, the verdict stage, output FIFO |
| first symbol in to first symbol out | about 2n + 2t + 6 | 532 for RS(255,239) |
| **first symbol in to last symbol out** | **about 2n + 2t + k + 6** | 771 |

: Table 5.4: Decoder latency

For a shortened code the n above is the shortened length (204 for DVB). For
S symbols per beat, divide the n terms by S; the 2t solver term does not
shrink.

## Buffer sizing

The block FIFO must hold the current block while the next arrives during
the Chien walk: depth = n + 2t + 8 symbols, rounded up to a power of two --
512 for the reference profile, 1024 for RS(544,514). The output FIFO holds a
block's data symbols while it waits for its verdict and the next block's
while that one is walked: depth = 2k + 8 rounded up, at 2m + 2 bits per entry
(received symbol, correction, hit, last) -- 512 x 18 for the reference profile.
The release-on-verdict rule costs this second buffer and the extra n cycles
of first-symbol latency; it is the price of never emitting an altered symbol
on an uncorrectable block.
