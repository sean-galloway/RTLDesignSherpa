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

2. DECISION sheets — for each important combinational decision signal, a
   CONTRACT TABLE (not a Gray grid). Canonical spec and rationale:
   vault/handbook/design/signal-contracts-and-kmaps.md. Three parts, in
   order:

     a. TERM LIST — every signal/expression the decision depends on, with
        its defining expression and file:line. The table's columns come from
        this. No anonymous axes: a bare name like `w_can_issue` with no
        equation is the exact failure this format replaced.
     b. INVARIANTS — the strict relationships BETWEEN terms ("if `a==0`
        then `b[1:0]` is always `2'b10`"), each cited, each stating which
        rows it renders impossible.
     c. TABLE — one row per combination of the terms. Rows the invariants
        forbid are marked ILLEGAL and name WHICH invariant excludes them;
        legal rows carry the resulting output. `x` means provably
        don't-care, not unknown, and every `x` collapse is licensed by an
        invariant.

   Why not a grid: grid area is 2^n whether 8 combinations are reachable or
   60, past 4 terms it pages (so Gray adjacency — the only reason to draw a
   grid — holds only within a page), and it has nowhere to record an
   inter-term relationship, so impossible states get rendered with real 0/1
   values. Keep a grid ONLY for a small, dense decision; the handbook note
   has the full argument.

   Each sheet still carries an "inspection check" note describing what a
   healthy result looks like (e.g. "rows 4-7 must all be ILLEGAL(I1); a
   legal row there means the stale-view guard was dropped") so a bad future
   edit is visible on sight.

## The rule that makes it trustworthy

Tables are COMPUTED, never written by hand. The generator holds a Python
mirror of the exact RTL expression and evaluates it over all input
combinations to fill the rows — so table and RTL agree by construction. The
invariants are evaluated too: a row an invariant calls impossible is checked
to be unreachable, so a WRONG invariant fails the run instead of silently
deleting a real case. Two enforcement
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
the quote together, re-run, and diff the table. A changed row is a changed
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
