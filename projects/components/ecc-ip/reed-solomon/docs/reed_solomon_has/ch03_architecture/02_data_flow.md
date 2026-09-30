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
   locator degree exceeds t, or is zero, the block is already known to be
   uncorrectable.
4. Chien search steps through positions 0 .. n-1, one per cycle, while the
   buffer reads out the same positions. At each root, Forney supplies the
   error value. Every corrected symbol, data and parity alike, is fed to a
   second syndrome unit; the received data symbols and their corrections go
   to the output FIFO as separate fields.
5. On the last position the verdict is final: uncorrectable if the root count
   differs from the degree, if a derivative was zero at a root, or if the
   re-computed syndromes are not all zero. That last check is what catches the
   blocks with more than t errors whose wrong locator still has the right
   number of roots; the degree and root checks alone miscorrect some of them.
6. The block is released only once its verdict exists. Corrections are
   applied on the way out, and not at all when the block is uncorrectable, so
   an uncorrectable block leaves exactly as it arrived. The status ports hold
   the verdict for every beat of the block and `out_last` marks its k-th.
7. The next block's symbols arrive during steps 3-6 and the one after that is
   being solved while this one is walked; the buffers are sized for that
   overlap, so the decoder sustains one block per n cycles.

### Figure 3.2: Decoder timeline, one symbol per cycle

![Decoder timeline](../assets/mermaid/rs_decoder_timeline.png)

For the reference profile the first data beat of a block emerges about
2n/S + 2t cycles after its first beat arrived (the block is received, solved,
and walked to its verdict before release), and the block then drains in k/S
cycles while the next block is walked, so sustained throughput is one block
every n/S cycles -- measured at 252 to 257 cycles per RS(255,239) block at
S = 1, 64.5 at S = 4 and 33 at S = 8 (n/S = 32).

## Block boundaries

The core does not count symbols to find a block: `in_last` is the boundary,
and the core checks it. A block shorter or longer than the configured n (or
k on the encoder side) is reported as a framing error in status and the core
resynchronises on the next `in_last`. A shortened code (`N_SYMBOLS` <
2^m - 1) is handled by the core treating the missing leading symbols as zero
in the syndromes and by offsetting the Chien positions; the consumer sees
only the shortened block.

## Multiple symbols per beat

With `SYMBOLS_PER_BEAT = S > 1` every stage works a beat per cycle: the
encoder LFSR advances by the beat's symbol count (S single steps unrolled,
the state after the count-th taken), the syndrome cells take S Horner
steps, and the Chien and Forney cells evaluate S positions from one set of
registers, each lane a constant multiply away from the beat's first
position. The solver works on the 2t syndromes and is unaffected. Blocks
are still delimited by `last`; `keep` is low-aligned and only a block's
last beat may be partial.

Where the partial beats fall differs between the cores. The encoder passes
data beats through as received and appends the parity in ceil(2t/S) beats,
so its output may carry a partial beat at the end of the data and another
at the end of the parity; a consumer that needs contiguous packing puts a
beat packer at the outlet, which is the adapters' job (chapter 4.2, 4.3).
The decoder drops the parity lanes, so its output is k symbols in ceil(k/S)
beats with only the final beat partial.
