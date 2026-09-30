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

# System Requirements

What a consumer must provide, and what it gets.

## The consumer provides

- **Block boundaries.** `in_last` on the k-th data symbol (encoder) or n-th
  coded symbol (decoder) of every block. The consumer's scheduler, framer or
  job control already knows where blocks end; the core checks and reports,
  it does not infer.
- **Room for the rate change.** The encoder emits n symbols for every k it
  takes; the decoder emits k for every n. The consumer's downstream (encoder)
  or upstream (decoder) absorbs the difference, or provides a FIFO of 2t
  symbols so the encoder's parity drain does not stall its input.
- **A single clock** and the repository's active-low asynchronous reset.
- **Erasure knowledge**, if `ENABLE_ERASURES`: which symbols are known bad,
  per symbol, with the data.
- **Configuration at build time.** The profile is parameters; nothing about
  the code is set at run time in the bare core.

## The consumer gets

- Systematic encoding: data pass through unchanged and in order, parity
  follows.
- A per-block verdict on the decoder: ok, corrected (with count),
  uncorrectable, framing error -- valid with the last symbol of the block,
  so the consumer can act on the block it has just received.
- Data as received on an uncorrectable block, never silently altered.
- Determinism: no run-time state survives a block except the counters; the
  same input block yields the same output block every time.

## Environment

- SystemVerilog-2012, synthesisable, no assertions in RTL (properties live in
  `formal/`), lint-clean under Verilator per the repository gate.
- Filelists under `rtl/filelists/`, registered in `bin/filelists.toml`, one
  per top, from the first module.
- Python golden model dependencies (`reedsolo`, `galois`) are DV-only.
