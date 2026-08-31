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

## Generated code has a SIZE contract with the tools, not just a content one

Adding registers to an RDL is not a neutral act. Measured 2026-08-31: nine new
registers grew a PeakRDL regblock from `'h88` to `'hb4`, which pushed the
generated module past **Verilator's inlining threshold**. Un-inlined, Verilator
stopped unifying the block's `__out_t` struct typedef across two instantiating
parents and emitted the struct PORT as `VL_OUT8(hwif_out,0,0)` — one bit —
which broke C++ codegen for a downstream harness build.

Two things to carry from that:

- **`verilator --lint-only` CANNOT catch this class.** Lint passed clean at
  both sizes, with every waiver removed. Only the C++ compile fails. If your
  gate for generated RTL is lint, it is blind to codegen — run an actual
  `--cc` plus `make -f V<top>.mk` on at least one consumer.
- **A struct-typed port crossing a module boundary is the fragile construct.**
  It was already fragile (the same closure fails at the old size too, in the
  inlined face); the size change only selected which face appeared. Treat "it
  worked before" for a struct port as luck that a regeneration can revoke.

## Regenerate into the directory the FILELIST consumes

Check where the build actually reads from before running the generator. A
second, orphaned copy of generated output is a live trap: it satisfies nothing,
drifts silently, and captures the next regen that uses a default `-o`.
*Case: `projects/components/misc/rtl/generated/` is referenced by no filelist,
Makefile or script, had already diverged from the real
`rtl/regs/generated/`, and swallowed the first regen attempt — the build kept
compiling the stale copy while the "regenerated" one sat unused.*

Related: [[filelists]] (the same one-source rule for compile closures);
the kimi-review-rounds rule 6 case in `vault/handbook/authoring/` — "fix the
source comment or the doc error regrows" is this note's rule applied to prose.
