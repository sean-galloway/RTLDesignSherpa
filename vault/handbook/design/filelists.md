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

Related: [[naming-and-style]] (module/file naming), [[test-runner]] (tests
consume filelists via `get_sources_from_filelist`, never a hand-listed array).
