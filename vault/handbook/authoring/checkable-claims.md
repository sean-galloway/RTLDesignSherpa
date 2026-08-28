---
title: Checkable claims
summary: Every number and every duration in a doc or an RTL comment must be measurable, or it must not be written. Both failure modes cost real work.
---

# Checkable claims

A doc is read as evidence. Anything in it that *looks* measured will be quoted
as measured, so a figure nobody took is worse than no figure: it is confidently
wrong and it survives review, because a reviewer checking a doc against RTL
cannot see a synthesis run or a git log that never happened.

Two classes have bitten this repo, and they are the same defect wearing
different clothes.

## Invented resource numbers

**Case (2026-08-27, repo-wide).** Area and gate-count estimates were spread
across 32 files in six books -- `Resource Usage | ~500 LUTs`, per-component
breakdowns like `Command FSM: ~20 LUTs, ~40 FFs`, whole `Estimated Area`
sections, and architecture comparisons (`Ripple Carry ~32 / Brent-Kung ~240 /
Kogge-Stone ~450`). None came from a synthesis run. Sean: *"Please remove area
estimates and gate count claims. Those are made up."* They were removed, not
labelled -- a hedged fabrication is still on the page, and the hedge is the
first thing a skimmer drops.

Note the review rounds could never have caught these: the reviewer brief marks
unsourced timing/area as a known-weak class and tells it to skip them, so the
qc loop reported the book clean while every one of those numbers sat in it.
**A class the reviewer is told to ignore will never converge on its own.**

What survived the sweep, and why:

- **LUT *levels*** in `monitor_trans_cam` / `monbus_cam` -- timing-path depth
  tied to real xc7a100t runs and the documented WNS fixes.
- **The CDC memory-style comparison** -- derived from real Xilinx primitive
  geometry (SRL32 depth, BRAM 512x72).
- **Structural gate counts that are countable and true** -- a wire-only
  `reverse_vector` genuinely is 0 gates; a prefix cell genuinely is 2 AND +
  1 OR. These are facts about the RTL, not predictions about a mapper.

Watch for the **prose form**, which a numeric grep misses: one page's
humanized text opened *"Fifty LUTs."* -- the deleted figure spelled out.

## Invented durations

**Case (2026-08-27, same day).** Correcting the docs, I wrote "the
long-standing 0.67/cycle", "which this comment claimed for a long time", and
"nothing noticed for a month" into RTL comments, a doc page, a task record and
a tool comment. Sean: *"Monitor code is only a few months old. There is no
history."* Checked: `monbus_compressor.sv` was added 2026-06-07 (~2.5 months),
`axi_monitor_base.sv` traces only to the repo's squashed initial commit, and
the "month" of unnoticed residue was eight days (deleted 2026-08-19, found
2026-08-27).

Duration rhetoric feels like narrative rather than data, which is exactly why
it goes in unchecked -- but "long-standing" is a claim about the log, and the
log is one command away. `git log --diff-filter=A --follow -- <file>` settles
it. Prefer the date or the measurement to the adjective: *"measured 0.67/cycle
at depth 2"* needs no history at all.

## The rule

Before a number or a duration lands, ask what would settle it -- a synthesis
report, a simulation, a `git log` -- and either run that or delete the claim.
If it is genuinely an estimate that earns its place, say what it is derived
*from*, so the next reader can redo the derivation rather than trust it.

This is the doc-side twin of [[kimi-review-rounds]] rule 5 (verify a finding
before acting on it) and rule 6's *new arithmetic, unchecked* -- correcting a
wrong number means writing a new one, and the new one is unverified the moment
it lands.
