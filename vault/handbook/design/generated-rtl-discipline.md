---
title: Generated RTL discipline
summary: A fix applied to generated RTL without back-porting its generator resurrects the bug on the next regeneration; regen-and-diff is the audit.
---

# Generated RTL discipline

CLAUDE.md's Critical Rule #0 covers one direction: change a generator, delete
and regenerate everything it produces. This note records the INVERSE failure,
which Rule #0 does not catch and which accumulated silently for months.

**Fixing the generated .sv without back-porting the generator plants a
time bomb: the next regeneration silently resurrects the bug.** The header
says `AUTO-GENERATED - DO NOT EDIT MANUALLY`, but under deadline the .sv gets
the fix and the .py does not — and nothing runs the generator again for
months, so nothing notices.

*Case (2026-08-10, found during MATH-007):* regenerating the bf16 + ieee754
families into a temp dir and diffing against the tree found **13 generated
files carrying tree-only hand-fixes**, three of them whole bug classes:

- the MATH-001 RNE fix (guard export, true sticky, `G & (R|S|LSB)`) in
  bf16/fp32 mantissa_mult + multiplier — the generators still emitted the
  folded sticky that MATH-001 removed;
- the count_leading_zeros bit-reverse wrappers in five adder/FMA generators —
  dead wrong since d62b794d fixed CLZ to count from the MSB; a regen would
  have reintroduced reversed operands into working RTL;
- the e4m3 exp=15 round-carry overflow wrap guard in `fp8_e4m3_multiplier`
  and `fp16_to_fp8_e4m3` — and back-porting it into the shared conversion
  template propagated the fix to `bf16_to_fp8_e4m3` and `fp32_to_fp8_e4m3`,
  where the same bug was still LIVE (input ~510 silently returned +0.0 with
  no flags; before/after sim proved it).

The same sweep found the formal harnesses for both mantissa_mults still
asserting the pre-MATH-001 folded-sticky contract — a fix has to land in the
generator, the RTL, the docs, the TB model, AND the formal properties, or the
next audit relitigates it.

## The rules

- **Fix the generator first, then regenerate.** If the fire drill demanded a
  direct .sv edit, back-port to the .py in the same change — the generator diff
  is part of the fix, not a follow-up.
- **Regen-and-diff is the audit, and it is cheap.** Regenerate everything into
  a temp dir and diff against the tree (ignore the `// Created:` date line).
  Any hunk is either an un-backported hand-fix (back-port it) or an intended
  generator improvement (adopt it). Zero-diff is the healthy state.
- **A shared template fixed once fixes every instantiation** — that is the
  point of generating. The e4m3 wrap guard was hand-fixed in one conversion
  and latent in two siblings until the template got the fix.

Related: [[filelists]] (the same one-source rule for compile closures);
the kimi-review-rounds rule 6 case in `vault/handbook/authoring/` — "fix the
source comment or the doc error regrows" is this note's rule applied to prose.
