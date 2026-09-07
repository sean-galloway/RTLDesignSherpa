<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# coverage — Dropped (ended without completing)

_None._

### COV-002: delta has five RTL files, no tests at all, and two copies of one module

**Status:** DROPPED 2026-09-07 -- Sean: "delta should be skipped." delta is
deliberately out of scope, not an oversight. Recorded rather than deleted so
the next person scoping repo-wide coverage finds the decision instead of
re-raising the same observation.

The findings below are accurate and still describe the tree; they are simply
not work anyone intends to do. If delta is ever brought back into scope, this
is the starting point.

**The gap.** `projects/components/delta` has no `dv/` directory. Not an empty
one -- none. Its five `.sv` files all use `` `ALWAYS_FF_RST ``, so all five
changed from SYNCHRONOUS to ASYNCHRONOUS reset when the macro became
unconditional (2026-09-07), and not one line of that was exercised. It is
excluded from `projects/components/Makefile`'s COMPONENTS list for exactly this
reason, with a comment saying so, which makes the omission tidy rather than
visible.

`bch`, `hive`, `memory-controllers/ddr3-lpddr3` and `ddr4-lpddr4` are in the
same comment but contain zero `.sv` files -- empty scaffolds, not a risk.
delta is the only real one.

**Second finding, same file.** `rtl/delta_axis_flat_4x16.sv` and
`rtl_test/delta_axis_flat_4x16.sv` both declare `module delta_axis_flat_4x16`
and differ only in header comments (`Subsystem: delta` vs
`Subsystem: delta_axis_flat_4x16.sv`) and trailing whitespace. Two files, one
module name, no filelist discipline between them -- they collide if anything
ever elaborates both. Nothing explains what `rtl_test/` is for; `rtl/Makefile`
does not mention it.

This is the shape that cost real time twice on 2026-09-07 (`rtl/asic_only/`,
`cdc_handshake_formal.sv`): a duplicate that nobody diffs, kept because the
reason for it was written once and never re-checked. See
[[silent-fallbacks]] rule 15.

**Raised:** 2026-09-07, while scoping which components the sync-to-async reset
change had actually been exercised against.
