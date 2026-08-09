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

## What makes a K-map GOOD (and what ours are currently missing)

**Audited 2026-08-06: what we emit today is a Gray-ordered truth table, not a
K-map that proves anything.** The grid itself is honest -- `GRAY2 = [(0,0),
(0,1), (1,1), (1,0)]`, so adjacency really is a single-bit change -- and the
cell values are computed from a Python mirror of the cited RTL. That is the
hard half, and it is done. The half that turns a picture into a proof is
absent: `grep -ciE "implicant|minimal|quine|espresso"` over both generators
returns nothing but prose inside `CHECK BY INSPECTION` strings.

A map earns the name when all six hold. Ours currently satisfy 1 and 2.

### 1. Cells are COMPUTED, never drawn
From a Python mirror of the verbatim RTL expression, file:line cited, with a
citation registry that greps every quote on every run. Hand-drawn maps encode
what the author believed. (DONE.)

### 2. Axes are Gray-ordered
Adjacent cells differ in exactly one variable, which is what makes a rectangular
group a valid simplification. A binary-ordered grid is a truth table wearing a
grid's clothes. (DONE.)

### 3. Every axis variable has its OWN equation and citation
This is the one the workbooks skip. `varnames` is a list of STRINGS. Nothing
says what `w_can_issue` IS, which expression produces it, or where it lives. A
reader cannot tell whether an axis is a flop, a wire, or a composite the author
invented for the map. **An axis that is itself a multi-term expression hides
exactly the logic the map claims to expose.**

Each axis needs a line: name, defining expression, file:line. If an axis is
composite, either map its inputs instead, or state why collapsing them is sound
(e.g. "these three are mutually exclusive by construction, proven at <cite>").

### 4. A SUFFICIENCY argument: why only these variables
The emitter puts 2 bits on rows, 2 on cols, and pages the rest. Nothing anywhere
justifies that the mapped function depends only on the variables shown. If a
decision truly depends on seven signals and four are mapped, the map is a SLICE,
and a slice is only meaningful with a statement of what is held constant and
why the rest cannot change the outcome.

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
