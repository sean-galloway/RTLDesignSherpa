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
    python3 bin/filelist_registry.py --blindspots  what --check/--audit cannot see
    python3 bin/filelist_registry.py --find MOD    which filelist provides a module
    python3 bin/filelist_registry.py --resolve F   fully expanded source list
    python3 bin/filelist_registry.py --list        where the filelists live

The first three run in CI on every PR (`--blindspots` ratcheted); the rest are
for humans.

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

**The checks are gated now** (2026-07-26). `.github/workflows/filelist-checks.yml`
runs on push to main and every PR: `--check` and `--audit` as hard gates,
`--blindspots --ratchet` against `bin/blindspots_baseline.json`.
`bin/hooks/pre-commit` is the local mirror, installed per clone with
`make setup-hooks`.

**There is exactly ONE tracked pre-commit hook, and that is deliberate.** Git
installs a single `.git/hooks/pre-commit`, so a second hook file does not add a
check -- it REPLACES every check in whatever it overwrites. On 2026-08-28 a
second hook appeared at `tools/hooks/pre-commit` carrying the task-ID and
declaration-order checks, and `make setup-hooks` COPIED it over the filelist
symlink. The filelist checks then did not run locally at all until 2026-09-02.
Nothing failed and nobody noticed, because CI still ran them: the local gate
was silently absent, not visibly broken.

Two things changed so it cannot recur. `bin/hooks/pre-commit` now carries every
check (task IDs, declaration order, test/DUT protocol family, filelist
contract) and `tools/hooks/` is gone. And `make setup-hooks` SYMLINKS rather
than copies, so the installed hook cannot drift from the tracked one.

Add a new check to that file. Do not add another hook.

**The ratchet is the reason a gate could land at all.** `--blindspots` had 516
findings; requiring zero would have meant no gate for months, and gating on a
failing check just teaches people to `--no-verify`. Instead the baseline records
each count and CI fails only when one GROWS. Burn-down lowers it
(`--blindspots --update-baseline`); nothing lets it silently regrow. Raising the
baseline to make a build pass defeats the entire mechanism -- the fix is to use
a filelist.

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

It reported 516 findings when it was written, which is why CI ratchets it rather
than demanding zero (see above). Burn-down is TOOL-012. Run it by hand after any
move, split or new area -- exactly when this class of breakage appears, and
sooner than the PR that would catch it.

## The gap the graph cannot see: a GENERATE-GATED submodule

A module instantiated under `if (PARAM > 0)` is invisible to a
default-parameter elaboration. So a filelist that omits it looks complete, and
lints clean, for exactly as long as nobody sets the parameter. The first
consumer that does gets `Cannot find file containing module`.

It is not a rare corner. Measured 2026-08-31 across the monitor family:
`axi_monitor_addr_check` (gated by `N_ADDR_RANGES > 0`) was listed by **2 of
24** `*_mon` / `*_mon_cg` filelists — `ae61c9f1` fixed one and stopped — and
NEITHER observer filelist listed `monbus_axil4_axil4_group`, which
`EGRESS_AXIL=1` selects and which the Genesys2 harness had been consuming.

So when auditing a filelist, do not read it against a default elaboration.
**Elaborate it at the parameter values that turn its generate blocks ON:**

    verilator --lint-only -GN_ADDR_RANGES=4 -f <filelist> --top-module <top>

and grep the module for `generate`/`if (` around instantiations to learn which
parameters those are. The same applies to a block whose egress or protocol
variant is parameter-selected: build BOTH arms.

Related: [[naming-and-style]] (module/file naming), [[test-runner]] (tests
consume filelists via `get_sources_from_filelist`, never a hand-listed array).
