# TASK-006: emit CONTRACT TABLES (proofs), not K-map pictures

> Migrated 2026-09-27 from `vault/Tasks/tooling/open.md` as **TOOLING-KMAP** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** open 2026-08-06; SCOPE CHANGED 2026-08-28 — the output FORM
changes, not just its rigour. Sean, after reviewing the emitted maps: "all
of the kmaps so far are unacceptable as there is no way to discern what
signals map to what... it should list out the signals that have strict
relationships (like if a=0 then b[1:0] is always 2'b10) then use these terms
in a table going through each possible value, then marking the ones that are
illegal, and marking the legal combinations with what the output should be.
This isn't necessarily the form a traditional kmap is, but it works in the
real world where more than 3-4 expressions are at play."

So the deliverable is a THREE-PART CONTRACT TABLE (term list -> invariants ->
decision table), spec and rationale in
[[signal-contracts-and-kmaps]]. Items 1-4 below survive but are re-aimed:
item 1 becomes the term list (structural, not a footnote), item 2's
don't-cares now also cover ILLEGAL rows with the invariant that excludes
them, item 3's sufficiency argument becomes the invariant list, and item 4
(implicants) matters MORE, because the table deliberately gives up the
grid's visual adjacency and mechanical derivation is what replaces it.

NEW item 0, ahead of the rest: teach the emitter the table form and add an
invariant checker -- evaluate each declared invariant over the full space and
FAIL the run if a row it calls impossible is actually reachable. A wrong
invariant must not silently delete a real case.

Audit of both `gen_signal_contracts_kmaps.py` (stream) and pumice's merged
`gen_pumice_signal_contracts.py`: the grids are
Gray-ordered and computed from cited RTL -- genuinely good -- but they stop
short of proving anything. `grep -ciE "implicant|minimal|quine|espresso"` finds
nothing in either generator; every "cover" hit is prose inside a
`CHECK BY INSPECTION` string. See [[signal-contracts-and-kmaps]] for the six
criteria; the emitter satisfies two.

Work, in the order that pays:

1. **Axis derivation table.** `kmap()` takes `varnames` as bare strings. Take
   `(name, expr, cite)` triples instead and emit them above the grid. An axis
   that is itself a composite expression hides the logic the map claims to show.
2. **Don't-care support.** Let `fn` return `None`/`X`; render as `X`, styled
   distinctly, and require a `reason=` citation per unreachable region. Today
   unreachable cells get a real 0/1 plus a prose aside -- which both hides bugs
   and blocks legal grouping.
3. **Sufficiency field.** A required `depends_only_on=` argument explaining why
   the mapped function ignores every other input. Fail the run if it is empty.
   Without it a paged map is a slice with no stated invariant.
4. **Implicant derivation.** Quine-McCluskey is fine at <= 6 variables (our cap).
   Emit the minimal sum-of-products, then DIFF it against the mirrored RTL
   expression and label the result identical / RTL-redundant / RTL-differs.
   The third case is the defect finder.
5. **Promote to bin/.** **DONE for stream, 2026-09-25 -- pumice remains.**
   The machinery now lives in `bin/kmaps/` (`minimize`, `writer`, `citations`,
   `styles`, 544 lines across 5 modules) and stream's generator imports it,
   dropping 2006 -> 1581 lines. Sequenced correctly: items 0-4 were discharged
   first by STREAM TASK-001, so the one implementation received the
   improvements rather than two.

   Verified BEHAVIOUR-NEUTRAL, which is the acceptance test for a refactor of
   a working generator: the regenerated workbook reproduces content-hash
   `3cc43a66d2fffb60` across 10 sheets with the citation gate green -- the
   promotion changed no output at all. The lifted bodies were confirmed
   line-for-line identical to their originals (86/86 and 283/283 lines) rather
   than retyped.

   `verify_citations(cites, repo)` is parameterised on promotion; the registry
   and repo root are per-component, as are the RTL path constants and the
   `build_*` builders.

   **Remaining: pumice.** `gen_pumice_signal_contracts.py` still carries its
   own copy and its API diverged -- `axis_eqs=` as a separate argument where
   the shared writer folds equations into `varnames` triples, and it has no
   citation gate at all. Converting it is a real refactor of a green workbook
   rather than a rename, and pumice's task lane belongs to another session, so
   it was documented rather than done. Until then two implementations exist and
   item 5 is not fully closed.

Acceptance: a workbook where every map states its axis equations, its
sufficiency argument, its don't-cares with citations, and a derived-vs-RTL
verdict.
