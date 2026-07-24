---
name: regressions
description: How to run a regression correctly - always "make clean-all && make run-all-{gate,func,full}-parallel", never a bare pytest. Use whenever running or re-running any test suite in val/ or projects/components/, or before reporting a suite as passing.
---

# regressions

READ FIRST: vault/handbook/dv/running-regressions.md (the handbook is the repo's memory; this
skill is the signpost).

The one rule agents break: **`clean-all` is not optional.** Stale
`local_sim_build/`/`sim_build/`/`__pycache__` survive your edit and hand you a
green run against the OLD design. Skipping the clean does not error - it makes
the result more optimistic than the code deserves.

```bash
source env_python
cd val/amba && make clean-all && make run-all-full-parallel
```

Never substitute a bare `pytest <dir>` - that silently drops the level,
parallelism, and reruns the target supplies. Report pass COUNTS, not just rc=0.

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
