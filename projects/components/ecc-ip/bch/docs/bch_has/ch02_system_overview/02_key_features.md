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

# Key Features

## Decided (PRD section 3)

- **Valid/ready core at both ends** (D9 direction). `bch_encoder_core` and
  `bch_decoder_core` present the house streaming contract: valid, ready,
  data, a `last` flag on the final bit of a block; the decoder adds a
  per-block status out. A consumer instantiates the core and nothing else.
- **Optional adapters, selectable per end** (D9 direction). `INTAKE_IF` and
  `OUTLET_IF` each `NONE` (default), `AXIS` or `AXI4`, independently, so
  AXIS-in/AXI4-out and the other pairings are one core with different
  adapters generated. Only the adapters selected exist in the netlist.
- **GF primitives imported, not copied** (D7). `gf_pkg`, `gf_mul`,
  `gf_mul_const` and `gf_inv` are taken from the reed-solomon component's
  `rtl/gf/` tree. Nothing BCH-specific lives in the RS tree.
- **Bits per beat is a new interface parameter** (D9 TBD). Unlike the RS
  codec there is no `SYMBOLS_PER_BEAT`; a beat carries a slice of one
  codeword. The exact width and the partial-beat mask are open sub-questions
  of D9.
- **No Forney stage** (structural fact of binary BCH). Every error value is
  1, so the Chien search drives a direct bit flip. The error-value hardware
  that the RS decoder needs is absent here.
- **Evenness shortcut in the syndrome unit** (structural fact of binary BCH).
  Only the t odd syndromes S_1, S_3, ..., S_2t-1 are computed; the even
  syndromes are obtained by squaring in GF(2^m).
- **Generated field constants** (R3). The primitive polynomial, generator
  polynomial and log/antilog tables are emitted by a Python generator into
  `rtl/generated/` from the profile parameters; no field constant is a
  literal in the datapath.
- **Every block reports** (R2). The decoder never silently passes a failed
  block: per-block status carries ok / corrected count / uncorrectable,
  and running counters feed the register block.
- **Golden-model verification** (R4). Every profile is checked against
  `galois` on random data, error patterns up to t and beyond t (to prove
  the uncorrectable flag), and erasures where enabled.

## Configurable, not yet chosen (chapter 6.2)

- m, the field dimension, and t, the correctable bit count (D1, D2)
- shortening (D3) -- full length or a shortened block
- whether both cores are built, or encoder-only / decoder-only (D4)
- erasure decoding present or absent (D5)
- throughput architecture and bits per beat (D6, D9)
- per-profile generator conventions: first root b, primitive polynomial (D8)
- key-equation solver algorithm (D11)
- the first consumer, which fixes all of the above (D10)

## Explicitly not features

- Soft-decision or list decoding, interleaving beyond a boundary permutation,
  concatenation with other codes.
- A scrambler / randomizer inside the codec (D12: out unless a named standard
  consumer needs one).
