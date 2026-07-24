---
title: Naming and style
summary: Module/signal conventions, headers, and where files live.
---

# Naming and style

- Modules `{category}_{function}.sv`; params UPPER_CASE; ports snake_case
  (common blocks: i_/o_ prefixes); registers r_*, wires w_*.
- Every module: header block (purpose, params with ranges, ports, notes).
  No emojis anywhere in RTL or pipeline-consumed docs.
- Files end with a trailing newline - a missing one once failed 98 tests
  as warnings-promoted-to-errors, and --lint-only does not catch it.
- Generated code lives in named SUBDIRECTORIES, never beside hand-written
  files; hand-written files in a generator-owned dir get their own
  *_static/ dir (bridge_cam precedent).
- Filelists: see [[filelists]] - every module MUST have one and MUST be
  registered in bin/filelists.toml.
- Before TB work, run bin/audit_signal_naming_conflicts.py - factory
  prefix collisions (desc_valid vs desc_ar_valid) break BFM discovery.
