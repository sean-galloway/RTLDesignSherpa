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

# Data Flow

## Encoder

One beat in, one beat out, with the output stream (n/k) longer than the input.
The exact shape depends on PRD D6 (throughput architecture) and the D9
bits-per-beat decision.

1. A beat of `BITS_PER_BEAT` data bits arrives with `in_valid`; the core
   accepts it when the encoder can take it (`in_ready`).
2. Each bit enters the LFSR (updating the parity registers) and is passed
   straight to the output mux -- systematic encoding means the data are not
   delayed by the code, only by the pipeline.
3. On the k-th bit (`in_last`), the mux switches to the parity registers
   and emits the n - k parity bits over the following cycles, then raises
   `out_last`; the LFSR clears for the next block.
4. While parity drains, `in_ready` is low: the encoder cannot start a new
   block until the previous block's parity has left. A consumer that wants
   full-rate back-to-back blocks provides an input FIFO of at least n - k
   bits upstream, or accepts the gap.

## Decoder

One beat in, one beat out, with a block of latency in between.

1. Received bits are written to the block buffer and fed to the syndrome
   unit. Erasure flags, if enabled, are recorded alongside each bit.
2. On `in_last` the t odd syndromes are complete. If all are zero the block
   is clean: the solver is skipped and the buffer drains through the corrector
   unchanged, status = ok.
3. Otherwise the key-equation solver runs. If the resulting locator degree
   exceeds t, or is zero, the block is already known to be uncorrectable.
4. Chien search steps through bit positions 0 .. n-1, one (or more, per D6)
   per cycle, while the buffer reads out the same positions. At each root the
   corrector flips the bit.
5. On the last position the verdict is final: uncorrectable if the root count
   differs from the degree, or if a re-check over the corrected stream shows a
   non-zero syndrome. That last check catches blocks with more than t errors
   whose wrong locator still has the right number of roots.
6. The block is released only once its verdict exists. Corrections are
   applied on the way out, and not at all when the block is uncorrectable, so
   an uncorrectable block leaves exactly as it arrived. The status ports hold
   the verdict for every beat of the block and `out_last` marks its k-th bit.
7. The next block's bits arrive during steps 3-6 and the one after that is
   being solved while this one is walked; the buffers are sized for that
   overlap, so the decoder sustains one block per n cycles in the serial case.

## Block boundaries

The core does not count bits to find a block: `in_last` is the boundary,
and the core checks it. A block shorter or longer than the configured n (or
k on the encoder side) is reported as a framing error in status and the core
resynchronises on the next `in_last`. A shortened code (`N_BITS` < 2^m - 1)
is handled by the core treating the missing leading bits as zero in the
syndromes and by offsetting the Chien positions; the consumer sees only the
shortened block.

## Multiple bits per beat

With `BITS_PER_BEAT = B > 1` every stage works a beat per cycle: the
encoder LFSR advances by the beat's bit count, the syndrome cells take B
Horner steps, and the Chien cells evaluate B positions from one set of
registers, each lane a constant multiply away from the beat's first
position. The solver works on the t odd syndromes and is unaffected. Blocks
are still delimited by `last`; a per-beat keep mask is needed for partial
final beats (the open D9 sub-question).
