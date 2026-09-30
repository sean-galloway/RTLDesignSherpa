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

# Throughput

All figures analytic at revision 0.1.

## Sustained rate

Both cores consume one beat per cycle when not back-pressured. With
`SYMBOLS_PER_BEAT = S`, that is S symbols, S x m bits, per cycle.

| Core | Sustained | Gap | Notes |
|---|---|---|---|
| Encoder | k symbols in per k + 2t cycles | 2t cycles per block while parity drains, unless the consumer buffers 2t symbols upstream | output rate is n/k times the input rate |
| Decoder | one block per n cycles | none once pipelined; the next block arrives during the previous block's Chien walk | output rate is k/n times the input rate |

: Table 5.1: Sustained throughput, S = 1

For the reference profile at S = 1 and a 200 MHz clock: 1.6 Gbit/s coded on
the wire, 1.5 Gbit/s of data. At S = 8 (a 64-bit bus, m = 8) the same clock
gives 12.8 Gbit/s coded, which is where the 802.3-class profiles live.

## What scales with S

| Block | Scaling | Reason |
|---|---|---|
| encoder LFSR | S symbols advance per cycle | the LFSR update is applied S times in one cycle (or unrolled) |
| syndrome cells | S-fold Horner step | each cell absorbs S symbols per cycle |
| Chien cells | S positions per cycle | replicated, or the step constant becomes alpha^(-S) with S evaluators |
| Forney | up to S corrections per cycle in the worst case | S inverses, or a small queue and a one-per-cycle Forney with a stall on dense errors |
| block buffer | width x S | depth unchanged in beats |
| key-equation solver | unchanged | it works on the 2t syndromes, not the stream |

: Table 5.2: Scaling with symbols per beat

The Forney row is the one to watch: with S > 1 a block with errors in
adjacent positions may need more than one correction in a cycle. The cheap
design stalls the drain for the extra cycles (rare, bounded by t per block);
the expensive one replicates the inverse.
