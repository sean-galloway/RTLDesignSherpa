---
name: filelists
description: Filelist rules - EVERY module MUST have a .f and MUST be registered in bin/filelists.toml. Components own their compile closure, consumers -f include, never hand-list another area's sources. Use when adding ANY new RTL module, test, or .f file.
---

# filelists

READ FIRST: vault/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: vault/handbook/design/filelists.md.

**A new module lands with its filelist IN THE SAME COMMIT**, and its area must
appear in bin/filelists.toml. A module with no .f has no consumers and is
indistinguishable from dead code. Consumers `-f` include; never hand-list
another area's sources.

Check before you commit: `python3 bin/filelist_registry.py --check`
(also --audit / --find MODULE / --resolve F / --list). Note that `--check`
prints PASS when `declared - covered - exempt` is empty - read all three
numbers, not the PASS. `[exempt]` in the registry is a debt ledger with a
stated reason, not a way to land a module without a filelist.

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
