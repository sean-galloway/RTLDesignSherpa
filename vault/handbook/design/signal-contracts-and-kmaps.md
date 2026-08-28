---
title: Signal contracts and K-maps
summary: Every important block gets a contracts workbook; maps are computed, never drawn.
---

# Signal contracts + K-maps (design practice)

For every substantial block (engines, schedulers, arbiters, controllers),
maintain a `*_signal_contracts.xlsx`: contract sheets per interface
(signal / width / dir / driver / legal behavior / invariant / bug history)
and Karnaugh maps for the key combinational decisions.

- Methodology (canonical): bin/SIGNAL_CONTRACTS_KMAPS.md.
- Placement (ONE per block, in the component's docs/): the generator lives at
  `projects/components/<component>/docs/gen_signal_contracts_kmaps.py` and emits
  `<component>_signal_contracts.xlsx` beside it. Before writing a new one, check
  whether the component already has one and UPDATE it in place - never add a
  parallel copy or a `signal_contracts/` subdir (a second copy rots; the copy
  nobody regenerates is the one the next session reads).
- Maps are COMPUTED from a Python mirror of the verbatim RTL expression,
  file:line cited; a citation registry greps every quote on every run and
  fails on drift. The xlsx is a build artifact - never hand-edit.
- What to map: arbitration/grant terms, issue qualifications, credit and
  space accounting, cross-block drain/pop strobes, error latch/clear,
  FSM exit decisions ([[minimal-fsm]]) - and anything that ever had a
  known_issues entry.
- Why: mirroring the expressions IS a design review. The stream workbook's
  first pass surfaced six findings the test suite had not (a retractable
  arvalid, an unlatched AW address contract, a transient error gate...).
- Reference implementations: pumice + stream
  docs/gen_signal_contracts_kmaps.py. New blocks copy the pattern; the
  common machinery is being promoted to bin/ (TOOLING-KMAP step 5 in
  vault/Tasks/tooling/open.md).

## The required artifact is a CONTRACT TABLE, not a grid

**Direction from Sean, 2026-08-28, after reviewing the emitted maps: "all of
the kmaps so far are unacceptable as there is no way to discern what signals
map to what."** That is the governing requirement. A Gray-coded grid labels
its axes with bare strings, so a reader cannot tell what any axis IS, and it
has nowhere to record the relationships BETWEEN terms. Both are fatal for the
decisions worth documenting, which is why the form changes.

The required shape has three parts, in this order:

1. **Term list.** Every signal/expression in play, with its defining
   expression and `file:line`. These names become the table's columns. No
   anonymous axes.
2. **Invariants — the strict relationships between terms.** e.g. "if `a==0`
   then `b[1:0]` is always `2'b10`", each with a citation and, crucially, the
   consequence for the table (which rows it renders impossible).
3. **The decision table.** One row per combination of the terms. Rows the
   invariants forbid are marked ILLEGAL and cite WHICH invariant excludes
   them. Legal rows carry the resulting output.

This is deliberately NOT a traditional K-map. As Sean put it, it "works in the
real world where more than 3-4 expressions are at play" — which is the regime
almost every interesting decision in this repo lives in.

### Why the table wins once terms or illegal states are numerous

* **Grid cost is 2^n regardless of legality.** A 6-term map is 64 cells, all
  rendered, whether 8 combinations are reachable or 60. A table's length
  tracks the REACHABLE set. In real RTL that set is usually a small fraction
  of 2^n — ops are near-one-hot, modes are mutually exclusive, qualifiers
  imply one another — so the table is short exactly where the grid is mostly
  noise.
* **Past 4 terms the grid loses the only property it was for.** The emitter
  pages: 4 bits on rows/cols, the rest become separate pages. Gray adjacency
  holds only WITHIN a page, so any group spanning pages is invisible. You pay
  the full 2^n rendering cost and lose the visual-minimization benefit that
  justified it.
* **A grid has nowhere to put an inter-term relationship.** Given "if `a==0`
  then `b[1:0]==2'b10`", the grid still renders cells for `b=01`/`b=11` —
  with a real 0 or 1 in them. That misleads in both directions: it invites
  reasoning about states that cannot occur, and a benign-looking value in an
  unreachable cell can mask what the RTL would actually drive.
* **Illegality becomes auditable.** "These cells are unreachable" as prose is
  an assumption. A row marked ILLEGAL(I2) is a claim you can check — and if
  I2 is wrong, the row it wrongly excluded is named.
* **Named terms restore traceability**, which is the original complaint.

The grid's one real advantage is visual adjacency for minimisation at <= 4
dense variables. The answer there is to DERIVE implicants mechanically
(Quine-McCluskey, step 4 below) rather than eyeball them — better anyway, and
it still works at 6 terms where the eye does not. Keep a grid only for a
genuinely small, dense decision; reach for the table otherwise.

### Worked shape

    Terms
    | Term            | Definition (verbatim RTL)             | Cite            |
    |-----------------|---------------------------------------|-----------------|
    | w_is_col        | cmd_op inside {RD,WR,RDA,WRA}         | arbiter.sv:141  |
    | w_col_ok        | bank_rdwr_ready_i[rank][bank]         | arbiter.sv:143  |
    | rd_op_ready_i   | port: "rd aligner has a free slot"    | cmd_path.sv:117 |

    Invariants (strict relationships)
    | #  | Invariant                          | Cite  | Consequence          |
    |----|------------------------------------|-------|----------------------|
    | I1 | w_is_rd implies w_is_col           | :141  | is_rd=1,is_col=0 ill.|
    | I2 | init_done=0 implies cmd_op==NOP    | :738  | col ops illegal then |

    Decision table: w_gate
    | # | is_col | col_ok | is_rd | rd_rdy | legal      | w_gate | note        |
    |---|--------|--------|-------|--------|------------|--------|-------------|
    | 0 |   0    |   x    |   0   |   x    | legal      |   1    | non-column  |
    | 1 |   1    |   0    |   0   |   x    | legal      |   0    | tCCD block  |
    | 5 |   0    |   x    |   1   |   x    | ILLEGAL I1 |   —    |             |

`x` in a legal row means genuinely don't-care (the output is provably
independent of that term there) — not "unknown". Collapsing rows with `x` is
how the table stays short; every collapse must be justified by the
sufficiency argument below.

## The six criteria still apply — they are about EVIDENCE, not layout

The audit below predates the format change and its numbering is still the
reference used by [[TOOLING-KMAP]]. Criteria 1, 2, 5 and 6 carry over to the
table unchanged in spirit: computed cells, a defined ordering, explicit
don't-cares, and derived-vs-RTL implicants. Criteria 3 and 4 are now
STRUCTURAL — the term list and the invariant list are parts of the artifact
rather than footnotes to a grid.

**Audited 2026-08-06: what we emit today is a Gray-ordered truth table, not a
K-map that proves anything.** The cell values are computed from a Python
mirror of the cited RTL. That is the hard half, and it is done. The half that
turns a picture into a proof is absent: `grep -ciE
"implicant|minimal|quine|espresso"` over both generators returns nothing but
prose inside `CHECK BY INSPECTION` strings.

### 1. Cells are COMPUTED, never drawn
From a Python mirror of the verbatim RTL expression, file:line cited, with a
citation registry that greps every quote on every run. Hand-drawn maps encode
what the author believed. (DONE.)

### 2. A defined, stated ordering
GRID FORM: axes Gray-ordered, so adjacent cells differ in exactly one variable
— that adjacency is what makes a rectangular group a valid simplification, and
a binary-ordered grid is a truth table wearing a grid's clothes. (DONE.)

TABLE FORM: adjacency is not the point, so order rows for READABILITY —
group by the dominant term, keep ILLEGAL rows next to the legal rows they
neighbour, and say at the top which ordering was chosen. An unordered table
is as unreadable as a binary-ordered grid.

### 3. Every term has its OWN equation and citation — now the TERM LIST
This is the criterion Sean's 2026-08-28 review failed us on, and it is why the
artifact changed shape. `varnames` was a list of STRINGS: nothing said what
`w_can_issue` IS, which expression produced it, or where it lived. A reader
could not tell whether an axis was a flop, a wire, or a composite the author
invented for the map. **A term that is itself a multi-term expression hides
exactly the logic the artifact claims to expose.**

In the table form this is no longer a footnote — the TERM LIST is part 1 of
the artifact and the table's columns come from it. Each term: name, defining
expression, file:line. If a term is composite, either use its inputs as the
terms instead, or record WHY collapsing them is sound as an invariant (part 2)
with its citation.

### 4. A SUFFICIENCY argument: why only these terms — now the INVARIANT LIST
The emitter puts 2 bits on rows, 2 on cols, and pages the rest. Nothing anywhere
justifies that the mapped function depends only on the variables shown. If a
decision truly depends on seven signals and four are mapped, the map is a SLICE,
and a slice is only meaningful with a statement of what is held constant and
why the rest cannot change the outcome.

In the table form this is part 2, the INVARIANT LIST, and it does double duty:
it states why the omitted signals cannot change the outcome, AND it is what
licenses every ILLEGAL row and every `x` collapse. That is the payoff of
making it structural — the same statements that justify the artifact's scope
also shrink it.

Write it explicitly: "`f` depends only on (a,b,c,d) because e,f,g are qualified
upstream at <cite> / are constant in this mode / are don't-cares under <cite>."
Without that sentence the map cannot be evidence of anything.

### 5. Unreachable cells marked as DON'T-CARE, not as 0 or 1
Today unreachable combinations get a real 0/1 and a prose aside
("(1,1,x) cells are unreachable cover"). That is wrong in both directions: it
can hide a bug (an unreachable cell showing a benign 0 that the RTL would
actually drive 1), and it blocks legal simplification (a don't-care is free to
join a group; a 0 is not).

Mark them `X`, and cite the invariant that makes them unreachable. An
unreachable cell with no citation is an assumption, not a fact.

### 6. Implicants derived, and compared against the RTL as written
The point of a K-map is to produce a minimal covering expression and then ASK
WHETHER THE RTL MATCHES IT. Three outcomes, all informative:

- **identical** -- the RTL is minimal; the map is a proof of that.
- **RTL is bigger** -- redundant terms. Sometimes deliberate (timing,
  readability); the map makes you say which.
- **RTL is smaller / differs** -- either a bug, or an unstated invariant doing
  work. This is the case that finds defects.

`CHECK BY INSPECTION: <prose>` is a human assertion, not this. It is worth
keeping as intent, but it is not the check.

## Why this matters more than it sounds

The stream workbook's first pass found six real defects, so the practice already
pays even half-built. But "we have K-maps" currently reads as stronger evidence
than it is, and that is the dangerous part -- the same shape as the monitor
timeout that was believed covered at STREAM because a DIFFERENT timeout was
tested ([[AMBA-MONTRACK]] and its sibling gap). A map with no sufficiency
argument and no implicants is a picture of the code, not a check on it, and a
picture agrees with the code by construction.

Open work: [[TOOLING-KMAP]] (the emitter), then per component:
[[STREAM-KMAP]] (partial workbook, finish it), [[RAPIDS-KMAP]] (no
workbook at all), [[PUMICE-KMAP]] (partial workbook, finish it).
