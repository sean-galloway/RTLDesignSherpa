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

# Verification Strategy

## Golden model

Every configuration is verified against a software Reed-Solomon
implementation on the same blocks: `reedsolo` (MIT) with the profile's
primitive polynomial, first root and shortening, cross-checked by `galois`
(MIT) for the field tables the generator emits. The TB encodes with the
model and checks the RTL encoder byte for byte; it injects errors into
model-encoded blocks and checks the RTL decoder's corrected output and
verdict against the model's decode.

## Test matrix

| Axis | Values | Why |
|---|---|---|
| profile | each row of table 6.4 the build admits | field constants and shortening differ per profile |
| errors per block | 0, 1, t-1, t, t+1, random | 0 exercises the bypass; t+1 must be flagged uncorrectable, never miscorrected |
| erasures (if built) | 0 .. 2t, mixed with errors up to 2e + f = 2t | the erasure budget |
| symbols per beat | 1, and the consumer's S | the S-fold datapaths |
| solver | riBM and Euclid | identical roots and values on every corrected block |
| scrambler | off and on | the OFF build must be tested as its own configuration |
| adapters | NONE/NONE first; then AXIS/AXIS and AXI4/AXI4; the mixed pairs follow | the core is proven before any wrapper |
| back-pressure | none, random on both ends, sustained on the output | the valid/ready contract and the block buffer's full behaviour |
| framing | short block, long block, missing `last` | the framing-error path |

: Table 6.5: Verification matrix

## Test structure

cocotb tests under `dv/tests/` with TB classes in `dv/tbclasses/`, Pattern B
(`cocotb_test_*` prefixes), the three run levels through both the REG_LEVEL
grid and TEST_LEVEL depth, per the `test-patterns` skill. Traffic at the
adapters uses the existing AXI-Stream and AXI4 BFMs; nothing drives a
valid/ready port by hand. Registers are read by name through the generated
regmap.

## Formal

No assertions in RTL. Candidate properties for `formal/` blocks: the
valid/ready contract at both ends of each core; the encoder's parity
equals the golden LFSR for one block (bounded); the solver's degree
invariant (deg Lambda <= number of iterations) and the equivalence of the
two solvers on symbolic syndromes for small t.

## Coverage

Functional coverage on the matrix above plus: every syndrome cell non-zero
at least once, every Chien position rooted at least once across the run,
Forney with a zero and a maximal error value, the uncorrectable path taken
by both the degree check and the root-count check.
