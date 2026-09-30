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

# Purpose and Scope

## Purpose

The Reed-Solomon codec adds symbol-level forward error correction to a data
path. An encoder appends 2t parity symbols to every block of k data symbols;
a decoder, given the n = k + 2t received symbols, corrects up to t symbol
errors -- or e errors and f erasures with 2e + f <= 2t -- and reports what it
did. A symbol is m bits, so a single corrupted symbol may carry m corrupted
bits: RS is the code for channels whose errors come in bursts and for
memories whose failures take out a whole device or a whole nibble at once.

The component exists so that a Sherpa consumer -- a memory controller, a
compute engine, a serial link -- can drop a proven codec into its own
datapath instead of building one. That is why the deliverable is a CORE with
plain valid/ready streaming ports at both ends (PRD D9): the consumer keeps
its own interfaces and the codec is a block inside them.

## Scope

In scope:

- `rs_encoder_core` and `rs_decoder_core`: systematic RS(n, k) over GF(2^m),
  parameterised in m, t and shortening
- the GF(2^m) primitive layer they are built from, written so the planned
  BCH component can reuse it
- optional boundary adapters for standalone use: AXI-Stream at either end,
  or an AXI4 read or write engine with a job interface at either end,
  chosen independently per end
- an optional scrambler / pseudo-randomizer stage behind a parameter
- the configuration registers, status and counters of the standalone tops
- verification against a software golden model, and FPGA characterisation

Out of scope (PRD section 6 and D7):

- BCH: its own component, `ecc-ip/bch/`
- soft-decision, list and folded RS decoding
- concatenation with convolutional or LDPC codes, and interleaving beyond a
  symbol-address permutation at the boundary
- any mid-stream insertion of the codec into a fabric (chapter 2.3 says why)

## Where this document stands

No RTL exists at revision 0.1. Everything here is derived from the PRD's
decisions, the FUB catalog's block hierarchy and the standards in
`References/`. Where a number appears it is analytic -- a cell count from the
algorithm, a latency from the pipeline -- and is labelled so. Measured
throughput, timing and resources arrive with the first synthesis run
(chapter 6.5) and will replace the estimates in chapter 5.
