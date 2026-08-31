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
registers grew a PeakRDL regblock from `'h88` to `'hb4`, and that was enough to
push the generated module across **Verilator's inlining threshold** — at `'h88`
`obs_regs_top` is inlined with no separate C++ class, at `'hb4` it gets its own
class and its struct output port is emitted as `VL_OUT8(hwif_out,0,0)`, one
bit. So a regeneration can change how a downstream tool STRUCTURES the design,
not just what the design contains.

State the evidence precisely, because the first version of this note did not:

- **Verified here:** the inline flip at `'h88` -> `'hb4`, by building the same
  consumer closure at both sizes.
- **Verified here:** at `'h88`, with a correctly resolved source list, that
  closure verilates AND compiles with zero errors.
- **Reported by the consuming session, not verified here:** that `'hb4` broke
  their real build. Plausible and consistent, but their diagnostic repro was
  later found faulty, and re-testing `'hb4` would mean re-breaking a shared
  tree, so it stays unverified.
- **RETRACTED:** an earlier version of this note claimed a *pre-existing
  structural* Verilator typedef bug underneath all this. There is none. See
  the next section for what actually produced that illusion.

The durable part regardless: **`verilator --lint-only` cannot see any of this.**
Lint passes clean at both sizes with every waiver removed; only the C++ codegen
and compile differ. If your gate for generated RTL is lint, it is blind to the
class — run an actual `--cc` plus `make -f V<top>.mk` on at least one consumer.

## Never pass a raw `-f` filelist straight to verilator

This is the trap that manufactured the "structural Verilator bug" above, and it
cost two sessions most of a day.

These filelists compose with `-f`, and the same sub-filelist is reached down
several paths, so **a filelist expands with duplicates**. It is not a
combining-two-tops artifact — a SINGLE filelist self-duplicates. Measured
2026-08-31 over `rtl/amba/filelists/` + the misc observers: **66 filelists
affected**, `amba_all.f` at 322 redundant entries of 700,
`axi4_intf_master_observer.f` at 69 of 119.

Verilator does not deduplicate. Compile a package twice and it mints two
distinct C++ types for one typedef, and struct assignments across module
boundaries then fail with `__struct__0` vs `__struct__1`. Add `-Wno-fatal` and
verilate marches past that and emits a degraded one-bit struct port. Both look
exactly like RTL defects. Neither is.

The real build is immune only because `get_sources_from_filelist()` dedupes.
So: resolve through the Python helper, the way the build does —

    python3 -c "
    import os
    from TBClasses.shared.filelist_utils import get_sources_from_filelist as G
    s, inc = G(repo_root=os.environ['REPO_ROOT'], filelist_path='<path>.f')
    print('\n'.join(s))"

— and never hand a bare `-f` to verilator for anything past `--lint-only`. A
standalone verilator invocation is exactly the shortcut a debugging session
reaches for, which is what makes this worth writing down. Fixing it at the
source (dedupe in the filelist graph, or a `--check-dup` in
`bin/filelist_registry.py`) is open work.

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
