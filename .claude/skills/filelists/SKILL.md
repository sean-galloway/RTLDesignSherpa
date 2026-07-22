---
name: filelists
description: Filelist rules - components own their compile closure, consumers -f include, never hand-list another area's sources. Registry tooling for coverage/audit. Use when adding RTL, tests, or any .f file.
---

# Filelists: -f closure rule

Registry: bin/filelists.toml. Tool: bin/filelist_registry.py
  --list / --check (module coverage) / --audit (cross-area hand-listing) /
  --unrolled (inlined bodies) / --find MODULE / --resolve FILE.f

Rules:
- A consumer -f includes a component's filelist; NEVER hand-lists its .sv.
- Generated areas (bridge, nexys char bridges): never hand-edit their .f;
  fix the generator/config and re-run the recorded regen command.
- Filelists must resolve STANDALONE (source env_python provides the 13
  $*_ROOT vars); resolving only under a flow Makefile is a defect.
- Parse with TBClasses.shared.filelist_utils.get_sources_from_filelist -
  never hand-roll a parser (every hand-rolled one has gotten the
  conventions wrong).
- `//` is a comment: a doubled slash silently drops a source.
- Verilator: tables/loops >64 deep need --unroll-count raised in sim builds.
