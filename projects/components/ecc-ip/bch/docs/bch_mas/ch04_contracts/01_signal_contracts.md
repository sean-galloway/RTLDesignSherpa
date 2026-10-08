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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Signal Contracts and K-maps

## What a contract is

A signal contract in this repo is a machine-checkable statement of what a
signal is allowed to do. Each contract has three parts, in order:

1. **Term list:** every signal or expression in play, with its defining
   expression and `file:line` citation.
2. **Invariants:** the strict relationships between terms, each cited, each
   stating which rows of the decision table it renders impossible.
3. **Decision table:** one row per combination of the terms. Rows the
   invariants forbid are marked `ILLEGAL`; legal rows carry the resulting
   output.

The canonical methodology is in `vault/handbook/design/signal-contracts-and-kmaps.md`;
the shared generator machinery is in `bin/kmaps/`.

## Which signals have contracts

The BCH workbook documents the control/qualifier signals whose correctness is
non-obvious: parity-phase select, block-boundary and frame-error qualifiers,
syndrome completion, no-error bypass, correctability verdict, Chien
root-position enables, and uncorrectable pass-through. The complete list is in
the generated workbook.

## Pre-RTL citation posture

At MAS v0.1 there is no RTL, so the contracts cite the MAS pages where the
intended expressions are written verbatim. When the first RTL lands, every
MAS citation is re-pointed at the corresponding `.sv` file and line. The
generator's citation gate then enforces that the workbook and the RTL agree;
a drift fails the run.

## Regenerating the workbook

```
python3 projects/components/ecc-ip/bch/docs/gen_bch_signal_contracts_kmaps.py
```

The generator writes:

```
projects/components/ecc-ip/bch/docs/bch_signal_contracts.xlsx
```

Do not hand-edit the `.xlsx`; it is a build artifact of the generator.

## Workbook contents

The generated workbook contains:

- a contract sheet for the core signals
- a kmap sheet per block with the key combinational decisions
- term lists, invariants, decision tables, `depends_only_on` sufficiency
  arguments, and `rtl_sop` expressions for review against the landed RTL

Since the 2026-10-08 citation migration (TASK-003 close) every citation
points at the landed RTL `file:line` and the generator's
`verify_citations` gate fails the build if an RTL edit moves a quoted line.
For every kmap the verdict is the derived minimal cover diffed against
`rtl_sop` (IDENTICAL or DIFFERS); all eight maps of the landed design
render IDENTICAL.
