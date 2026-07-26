---
title: Filelists
summary: Every module MUST have a filelist and MUST be registered in bin/filelists.toml; components own their closure, consumers -f include.
---

# Filelists

**Every module has a filelist, and every filelist area is registered in
`bin/filelists.toml`.** This is not a style preference - it is the compile
closure contract, and the two failure modes it prevents are both silent.

## The rule

1. **A component owns its compile closure.** Its `.f` lists its own sources and
   `-f` includes the filelists of anything it depends on.
2. **A consumer never hand-lists another area's sources.** It `-f` includes that
   area's filelist. Hand-listing means the consumer's copy silently rots the
   moment the owning area adds, splits or renames a file.
3. **Every area appears in `bin/filelists.toml`.** An unregistered area is
   invisible to `--check`, so its modules are exempt from coverage without
   anyone deciding they should be.

`bin/filelists.toml` is a REGISTRY/index of where the lists live -- it does not
store them. Every `.f` lives in the owning area's **`filelists/` dir** (the
canonical location); the toml just records the area so the checker can find it.
Placement is currently inconsistent in a few spots -- see
AMBA-FILELIST-CONSISTENCY.

New module -> new (or extended) `.f` in the owning area's `filelists/` dir, in
the same commit. Not "before the test lands" - in the same commit, because a
module with no filelist has no consumers and is indistinguishable from dead
code the next time someone audits.

## A shared block set gets its own `.f`

When several lists in an area need the same group of building blocks, factor
them into one `<area>_<thing>_bb.f` and `-f` include that, rather than repeating
the group. *Case (2026-07-25): the async-FIFO pointer/control set was copied
across `fifo_async.f`, `gaxi_fifo_async.f` and four `apb*_slave_cdc*.f` --
`glitch_free_n_dff_arn` in 8 lists, five more blocks in 7 each. The four apb
lists were the worst: each already `-f` included `gaxi_fifo_async.f` AND
separately repeated all ten blocks that list pulls in. One `cdc_fifo_bb.f`
removed 67 lines of `-f`.* Underscores in the name, like every other `.f`.

**Prove the refactor changed nothing.** Resolve every affected consumer BEFORE,
re-resolve AFTER, and diff the sorted sets -- `--check` passing does not tell
you a consumer kept its sources, only that modules are reachable from some list.
Order within the leaf blocks will shift, which is fine (module definitions have
no ordering requirement among themselves; headers must still come first), so
compare sets, then run the tests.

That diff is also how you find dead weight: the same pass showed `fifo_async.f`
had been dragging in `bin2gray`, which nothing instantiates -- `counter_bingray`
does the conversion inline specifically to avoid it. A module that is in a
closure but never instantiated still compiles, so nothing complains.

## Why: both failure modes are silent

- **`//` is a comment.** A doubled slash in a path silently drops that source.
  The build then fails somewhere unrelated, or - worse - succeeds because
  another list happened to pull the file in.
- **Generate-gated submodules hide.** A module only instantiated under a
  non-default generate (`addr_check`, `monbus_compressor`) is invisible to
  default-parameter elaboration. It compiles fine until someone flips the
  parameter, and then the missing source surfaces as an elaboration error in a
  configuration nobody was testing.

A stray extra `-I` masks both, which is why the audit exists rather than
relying on "the build passes".

## Tooling

    python3 bin/filelist_registry.py --check       every module reachable from some .f
    python3 bin/filelist_registry.py --audit       consumers hand-listing common/amba
    python3 bin/filelist_registry.py --find MOD    which filelist provides a module
    python3 bin/filelist_registry.py --resolve F   fully expanded source list
    python3 bin/filelist_registry.py --list        where the filelists live

`--check` resolves `-f` includes and `$*_ROOT` substitution exactly the way the
cocotb consumer does
(`bin/TBClasses/shared/filelist_utils.get_sources_from_filelist`), so a list
that passes `--check` is one the tests can actually compile.

## The exempt list is a debt ledger, not an escape hatch

`[exempt]` in `bin/filelists.toml` suppresses a module from `--check` with a
stated reason. It exists so a genuine pending case does not mask a real
regression - not as a way to land a module without a filelist.

Adding an entry needs a reason that names when it goes away. "No consumer yet"
is acceptable for a wrapper that is genuinely unreferenced; it is not
acceptable for something you simply have not wired up.

## `--check` passing is weaker than it looks

`--check` reports `PASS` when `declared - covered - exempt` is empty. The
printed "covered" count can therefore be lower than the module count with zero
uncovered - the difference is the exempt set. Read all three numbers, not the
`PASS`.

As of 2026-07-23: common 57 modules / 55 covered, amba 152 / 147 - the 7-module
gap is entirely the exempt list (multi-instance wrappers with no consumer yet).

**Nothing runs `--check` automatically.** It is not in the pre-commit hook and
not in CI, so today the rule is enforced by whoever remembers. Wiring it into a
gate is tracked in the common and amba task areas.

## `--check` and `--audit` cannot see a hand-listed test

Both tools follow filelists. A test that builds its own `verilog_sources = [...]`
array is outside that graph entirely, so it can reference a path that no longer
exists while both tools report PASS. *Case: the CDC move rewrote every test that
named a cdc FILELIST and missed three that named a PATH --
`test_fifo_async_wavedrom`, `test_counter_bingray_wavedrom` and
`test_counter_johnson_wavedrom` were broken for a day with a green `--check`,
and were only found by running the suite.* Formal `.sby` harnesses have the same
blind spot: they list sources by hand, which is why the `apb*_slave_cdc` ones
were missing `gaxi_fifo_async` and its whole tree. Generate a harness's
`[files]` from the area's filelist instead.

There is a check for this now - use it rather than the greps:

    python3 bin/filelist_registry.py --blindspots

It reports the three things the filelist graph cannot see: tracked `.f` files no
registered area covers, tests building their own `verilog_sources` array (or
appending to one), and `.sby` harnesses whose source paths do not resolve.
Mutation-checked: unregistering `rtl/cdc` in the toml makes it name all 14 of
that area's filelists.

As of 2026-07-26 it reports 516 findings, so it is NOT wired into a gate yet -
gating on a check that already fails just teaches people to skip it. Burn-down
and gating are TOOL-012. Run it by hand after any move, split or new area, which
is exactly when this class of breakage appears.

Related: [[naming-and-style]] (module/file naming), [[test-runner]] (tests
consume filelists via `get_sources_from_filelist`, never a hand-listed array).
