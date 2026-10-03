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

The Binary BCH codec adds bit-level forward error correction to a data path.
An encoder appends parity bits to every block of k data bits; a decoder, given
the n = k + (n - k) received bits, corrects up to t bit errors anywhere in the
block. The arithmetic is over GF(2^m), but the code is binary: every error
value is 1, so correction is a simple bit flip and no error-value computation
is needed. A binary BCH code is the choice for channels whose errors are
independent bit flips or multi-bit failures without a fixed symbol framing,
such as raw flash pages and memory arrays.

The component exists so that a Sherpa consumer -- a memory controller, a
compute engine, a serial link -- can drop a proven codec into its own
datapath instead of building one. That is why the deliverable is a CORE with
plain valid/ready streaming ports at both ends (PRD D9 direction): the
consumer keeps its own interfaces and the codec is a block inside them.

## Scope

In scope:

- `bch_encoder_core` and `bch_decoder_core`: systematic binary BCH(n, k) over
  GF(2^m), parameterised in m, t and shortening
- the GF(2^m) primitive layer imported from the reed-solomon component
  (PRD D7), used but not duplicated
- optional boundary adapters for standalone use: AXI-Stream at either end,
  or an AXI4 read or write engine with a job interface at either end,
  chosen independently per end
- the configuration registers, status and counters of the standalone tops
- verification against a software golden model, and FPGA characterisation

Out of scope (PRD section 6 and D12):

- soft-decision, list and folded BCH decoding
- concatenation with convolutional or LDPC codes, and interleaving beyond a
  bit-address permutation at the boundary
- any mid-stream insertion of the codec into a fabric (chapter 2.3 says why)
- a scrambler / randomizer inside the codec (D12: out unless a named standard
  consumer needs one)

## Where this document stands

No RTL exists at revision 0.1. Everything here is derived from the PRD's
decisions and the standards in `References/`. Where a number appears it is an
analytic placeholder -- a cell count from the algorithm, a latency bound from
the pipeline -- and is labelled so. Measured throughput, timing and resources
arrive with the first synthesis run (chapter 6.5) and will replace the
estimates in chapter 5.
