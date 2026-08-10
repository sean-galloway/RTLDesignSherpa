# Signal contracts + K-maps methodology

How to build (and maintain) a `*_signal_contracts.xlsx` workbook for a
component: a machine-checked reference for what every interface signal is
allowed to do, plus Karnaugh maps for the key combinational decisions.

Existing instances:

    projects/components/memory-controllers/pumice-ddr2-lpddr2/docs/
        pumice_signal_contracts.xlsx + gen_signal_contracts_kmaps.py
    projects/components/dmas/stream/docs/
        stream_signal_contracts.xlsx + gen_signal_contracts_kmaps.py

TODO (TOOLING-KMAP step 5, vault/Tasks/tooling/open.md): the common generator machinery belongs in
bin/ so the per-project scripts hold only their signal tables and mirrored
expressions; two diverging copies is the known copy-paste failure mode.

## What the workbook is

Two kinds of sheets:

1. CONTRACT sheets — one table per interface group (an AXI master, the CSR
   bus, the monbus output...). Columns: Signal / Width / Dir / Driver /
   Legal-Correct behavior / invariant / bug history. The behavior column is
   the contract: when the signal may assert, what it must hold across, what a
   violation means downstream. Every row must be checkable against the RTL —
   no aspirational prose. Rows covering logic that once had a real bug carry
   the fix reference (commit or known_issues file); those rows are the ones a
   future reader needs most.

2. K-MAP sheets — for each important combinational decision signal, a
   Karnaugh map with the RTL expression quoted verbatim beside it and its
   file:line cited. Gray order 00 01 11 10; more than 4 variables becomes one
   4x4 grid per value of the extra (page) variables; 1-cells green, 0-cells
   grey. Each map carries an "inspection check" note describing what a
   healthy map looks like (e.g. "single contiguous block; a lone 1 in the
   bottom row means the stale-view guard was dropped") so a bad future edit
   is visible on sight.

## The rule that makes it trustworthy

Maps are COMPUTED, never drawn. The generator holds a Python mirror of the
exact RTL expression and evaluates it over all input combinations to fill
the grid — so grid and RTL agree by construction. Two enforcement
mechanisms, both mandatory:

- Citation registry: every quoted expression is registered with its
  file:line, and the generator greps each citation ON EVERY RUN, exiting
  nonzero if the RTL has drifted from the quote. A stale map cannot be
  silently regenerated. (The stream generator's `verify_citations()` is the
  reference implementation: 73 entries.)
- Idempotence: running the generator twice produces byte-stable sheet
  content. The xlsx is a build artifact of the script; never hand-edit the
  workbook.

When the RTL changes: the citation check fails, you update the mirror AND
the quote together, re-run, and diff the grid. A changed cell is a changed
behavior — which is exactly the review you wanted to have.

## Choosing signals

Not everything — the decisions that gate money paths:

- arbitration / grant terms, issue qualifications (valid gating)
- credit / outstanding-limit / space-accounting terms
- drain / pop / advance strobes coupling two blocks (the stream WLAST/drain
  term that fixed a deadlock is the canonical example)
- error latches and their clear terms
- anything that was ever the subject of a known_issues entry

Expressions with more than ~6 inputs: factor them the way the RTL does and
map the sub-terms separately, rather than exploding pages.

## Why bother (evidence)

The act of mirroring expressions IS a design review. The stream workbook's
first generation surfaced six findings the test suite had not: a
combinational arvalid that can retract under abort (AXI stability
violation), an un-latched AW address riding an implicit cross-module
contract, a transient descriptor-error gate whose real backstop is in
another module, a vestigial overflow gate, an unreachable input half worth a
cover property, and a sim-only over-drain guard. The pumice workbook's
K-map pass similarly predated and informed its scheduler rework.

## Running

    source env_python
    python3 projects/components/<comp>/docs/gen_signal_contracts_kmaps.py

Nonzero exit = citation drift: the RTL moved under a quote. Fix the mirror
and the quote together; never suppress the check.
