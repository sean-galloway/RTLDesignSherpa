---
name: filelists
description: Filelist rules - components own their compile closure, consumers -f include, never hand-list another area's sources. Registry tooling for coverage/audit. Use when adding RTL, tests, or any .f file.
---

# filelists

READ FIRST: docs/handbook/design/naming-and-style.md (the handbook is the repo's memory; this skill is the
signpost). Components own their closure; consumers -f include. Tool: bin/filelist_registry.py (--check/--audit/--unrolled). Registry: bin/filelists.toml.

The handbook root is docs/handbook/INDEX.md - design/, dv/, fpga/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
