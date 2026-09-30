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
| Encoder | ceil(k/S) beats in per ceil(k/S) + ceil(2t/S) cycles | ceil(2t/S) cycles per block while parity drains, unless the consumer buffers that many beats upstream | output rate is n/k times the input rate |
| Decoder | one block per ceil(n/S) + 1 cycles | the verdict stage is one entry deep, so a block's successor cannot enter the correct stage until its verdict is written; otherwise none, the next block arrives during the previous block's Chien walk | output rate is k/n times the input rate |

: Table 5.1: Sustained throughput

Measured in simulation, back-to-back timing at both ends:

| Profile | S | Encoder, cycles per block | Decoder, cycles per block (steady state) |
|---|---|---|---|
| RS(255,239) | 1 | 255 | 255.5 |
| RS(255,239) | 4 | 64 | 67.5 |
| RS(255,239) | 8 | 32 | 36 |
| RS(204,188) | 8 | 26 | 30 |
| RS(21,19) | 4 | 6 | 10.2 |
| RS(15,11) | 3 | 6 | 9.2 |
| RS(252,236) on the board | 4 | 63 | 69.3 |

: Table 5.1a: Measured cycles per block

For the reference profile at S = 1 and a 200 MHz clock: 1.6 Gbit/s coded on
the wire, 1.5 Gbit/s of data. At S = 8 (a 64-bit bus, m = 8) the same clock
gives 12.8 Gbit/s coded, which is where the 802.3-class profiles live.

## What scales with S

| Block | Scaling | Reason |
|---|---|---|
| encoder LFSR | S symbols advance per cycle | S single steps unrolled; the taps are constant, so it is one XOR network |
| syndrome cells | S-fold Horner step | S unrolled steps per cell, the state after the beat's count taken |
| Chien cells | S positions per cycle | one register set per cell, S lane constants alpha^(iu), the step constant alpha^(iS) |
| Forney | S corrections per cycle | S lane sums, S inverses and S multiplies |
| block and output FIFOs | width x S | depth in beats |
| key-equation solver | unchanged | it works on the 2t syndromes, not the stream |

: Table 5.2: Scaling with symbols per beat

The Forney row is the cost to watch: the cores as built take the S-inverse
form, so a correction can land in every lane of a beat in the same cycle and
the walk never stalls. The alternative -- one inverse and a stall of up to
t cycles per block on dense errors -- is the trade to revisit if the
characterisation shows the inverses dominating at large S.
