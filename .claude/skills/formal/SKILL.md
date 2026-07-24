---
name: formal
description: Formal verification flow - SymbiYosys via sv2v flatten, in-RTL ifdef FORMAL properties, mutation-checking every new assertion, harness vacuity traps. Use when writing properties, regenerating proofs, or after changing any module with a formal dir.
---

# formal

READ FIRST: vault/handbook/dv/formal.md (the handbook is the repo's memory; this skill is the
signpost). sv2v deletes assertions without --exclude=Assert; mutation-check every property; watch the vacuity traps; BMC-25 is not induction.

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
