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

One beat in, one beat out, with the output stream 2t/k longer than the input.

1. A beat of `SYMBOLS_PER_BEAT` data symbols arrives with `in_valid`; the
   core accepts it when the encoder can take it (`in_ready`).
2. Each symbol enters the LFSR (updating the parity registers) and is passed
   straight to the output mux -- systematic encoding means the data are not
   delayed by the code, only by the pipeline.
3. On the k-th symbol (`in_last`), the mux switches to the parity registers
   and emits the 2t parity symbols over the following cycles, then raises
   `out_last`; the LFSR clears for the next block.
4. While parity drains, `in_ready` is low: the encoder cannot start a new
   block until the previous block's parity has left. A consumer that wants
   full-rate back-to-back blocks provides an input FIFO of at least 2t
   symbols upstream, or accepts the 2t-cycle gap.

## Decoder

One beat in, one beat out, with a block of latency in between.

1. Received symbols are written to the block buffer and fed to the syndrome
   cells. Erasure flags, if enabled, are recorded alongside each symbol.
2. On `in_last` the syndromes are complete. If all are zero the block is
   clean: the solver is skipped and the buffer drains through the corrector
   unchanged, status = ok.
3. Otherwise the key-equation solver runs 2t iterations. If the resulting
   locator degree exceeds t (or the Chien search finds fewer roots than the
   degree), the block is uncorrectable: it drains uncorrected with status =
   uncorrectable, so the consumer sees the block and the verdict together.
4. Chien search steps through positions 0 .. n-1, one per cycle, while the
   buffer reads out the same positions. At each root, Forney supplies the
   error value and the corrector applies it. `out_last` carries the status.
5. The next block's symbols may be arriving during steps 3-4; the buffer is
   sized for that overlap, so the decoder sustains one block per n cycles.

### Figure 3.2: Decoder timeline, one symbol per cycle

![Decoder timeline](../assets/mermaid/rs_decoder_timeline.png)

For the reference profile a block takes about 2n + 2t cycles from first
symbol in to last symbol out (about 526 for RS(255,239)), and the next block
overlaps the second half, so sustained throughput is one block every n
cycles.

## Block boundaries

The core does not count symbols to find a block: `in_last` is the boundary,
and the core checks it. A block shorter or longer than the configured n (or
k on the encoder side) is reported as a framing error in status and the core
resynchronises on the next `in_last`. A shortened code (`N_SYMBOLS` <
2^m - 1) is handled by the core treating the missing leading symbols as zero
in the syndromes and by offsetting the Chien positions; the consumer sees
only the shortened block.

## Multiple symbols per beat

With `SYMBOLS_PER_BEAT = S > 1` the encoder LFSR advances S symbols per
cycle and the syndrome and Chien cells are replicated or fed S-way (chapter
5.1); the solver, which works on the 2t syndromes, is unaffected. Blocks are
still delimited by `last`; a block whose length is not a multiple of S ends
with a partial final beat, marked by a per-symbol keep mask in the data
beat.
