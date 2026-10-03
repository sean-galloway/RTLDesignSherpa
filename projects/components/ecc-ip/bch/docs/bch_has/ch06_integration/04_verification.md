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

Every configuration is verified against a software binary BCH implementation
on the same blocks: `galois` (MIT) is the first candidate because it exposes
`galois.BCH` with explicit primitive-polynomial, generator and shortening
control. `aff3ct` (MIT) is the cross-check. This is the model-first order
from the reed-solomon TASK-002 lesson: the golden model is validated before
any RTL is compared against it.

The testbench encodes with the model and checks the RTL encoder bit for bit;
it injects errors into model-encoded blocks and checks the RTL decoder's
corrected output and verdict against the model's decode.

## Test matrix

| Axis | Values | Why |
|---|---|---|
| profile | each row of table 6.4 the build admits | field constants and shortening differ per profile |
| errors per block | 0, 1, t-1, t, t+1, random | 0 exercises the bypass; t+1 and more must match the reference decoder's verdict -- uncorrectable, or the identical miscorrection where the code itself cannot tell -- and an uncorrectable block's data must be exactly as received |
| reference model | `galois.BCH` | the hardware algorithms in Python on the same field, validated against AFF3CT |
| erasures (if built) | 0 .. 2t, mixed with errors up to 2e + f = 2t | the erasure budget |
| bits per beat | 1, and the consumer's B | the B-fold datapaths |
| solver | BM, Euclid, small-t where applicable | identical roots on every corrected block |
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
valid/ready contract at both ends of each core; the encoder's parity equals
the golden LFSR for one block (bounded); the evenness shortcut
S_2j = S_j^2 on the syndrome unit; the equivalence of the solver candidates
on symbolic odd syndromes for small t; the no-Forney structural fact that
correction is a pure bit flip.

## Coverage

Functional coverage on the matrix above plus: every odd syndrome cell
non-zero at least once, every Chien position rooted at least once across the
run, the uncorrectable path taken by both the degree check and the root-count
check, and the re-check syndrome path when implemented.
