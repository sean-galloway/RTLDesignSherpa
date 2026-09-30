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

- **Valid/ready core at both ends** (D9). `rs_encoder_core` and
  `rs_decoder_core` present the house streaming contract: valid, ready,
  data, a `last` flag on the final symbol of a block; the decoder adds
  erasure flags in and a per-block status out. A consumer instantiates the
  core and nothing else.
- **Optional adapters, selectable per end** (D9). `INTAKE_IF` and
  `OUTLET_IF` each `NONE` (default), `AXIS` or `AXI4`, independently, so
  AXIS-in/AXI4-out and the other pairings are one core with different
  adapters generated. Only the adapters selected exist in the netlist.
- **Symbol width is a code property** (D1). `SYMBOL_WIDTH` = m is its own
  parameter (default 8). `DATA_WIDTH` must be an integer multiple of it,
  checked at elaboration; `SYMBOLS_PER_BEAT = DATA_WIDTH / SYMBOL_WIDTH` is
  the throughput factor (D6). A bus that does not divide fails to elaborate
  rather than straddling symbols across beats.
- **Two key-equation solvers** (D11). `KES_ALGO = "RIBM"` (default): the
  reformulated inversionless Berlekamp-Massey array, 3t + 1 cells, shortest
  critical path. `KES_ALGO = "EUCLID"`: the modified Euclidean array, 2t
  cells, the textbook algorithm in systolic form. Same ports, same result up
  to a common scale; one generate in the decoder core selects them.
- **Scrambler behind a parameter** (D12). `ENABLE_SCRAMBLER` generates the
  standard's PRBS stage with its polynomial, seed and placement as
  parameters; the OFF build carries no LFSR logic and is a tested
  configuration.
- **Generated field constants** (R3). The primitive polynomial, generator
  coefficients and log/antilog tables are emitted by a Python generator into
  `rtl/generated/` from the profile parameters; no field constant is a
  literal in the datapath.
- **Every block reports** (R2). The decoder never silently passes a failed
  block: per-block status carries ok / corrected count / uncorrectable, and
  running counters feed the register block.
- **Golden-model verification** (R4). Every profile is checked against
  `reedsolo` or `galois` on random data, error patterns up to t and beyond t
  (to prove the uncorrectable flag), and erasures where enabled.

## Configurable, not yet chosen (chapter 6.2)

- t, the correctable-symbol count, and with it n and k (D2)
- shortening (D3) -- full length or a standard's shortened block
- erasure decoding present or absent (D5)
- encoder-only builds for transmit-only or RAID-write consumers (D4)
- per-profile generator conventions: first root b, dual basis (D8)
- the first consumer, which fixes all of the above (D10)

## Explicitly not features

- BCH (its own component), soft-decision or list decoding, interleaving
  beyond a boundary permutation, concatenation with other codes.
