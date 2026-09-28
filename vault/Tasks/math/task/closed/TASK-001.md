# TASK-001: filelist coverage: 134 math modules have no .f; 106 of 119 math tests hand-list sources

> Migrated 2026-09-27 from `vault/Tasks/math/closed.md` as **MATH-003** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-08-06 -- 134 missing .f generated
(bin/gen_math_filelists.py), 24 hand-maintained lists had incomplete
closures (regenerated), all 119 tests converted
(bin/convert_math_tests_to_filelists.py). gate 119/119, func 134/134 on
clean builds.
**Priority:** P2 — mechanical but large; drives every future test review of the area
**Owner:** TBD

The [[filelists]] rule (every module has a `.f`, tests take the closure, never
hand-list) is broadly unimplemented in rtl/math:

- **134 of 171 modules have no filelist** (38 exist in rtl/math/filelists/).
  Generation is scriptable: each module's `.f` is its instantiation closure
  (the deps_of logic in bin/build_review_bundle.py already computes it), then
  `python3 bin/filelist_registry.py --check` must pass.
- **106 of 119 val/math tests hand-list `verilog_sources = [...]`** (13 use
  get_sources_from_filelist). Convert once the filelists exist, in batches
  with a regression run per batch. The cdc audit found the same class in
  miniature (3 tests) and it was fixed in-line there.
- Related smaller item from the same findings: wrappers that DO use the
  filelist helper then pass `includes=[]` (the cdc batch-5 pattern) — fold
  those into the conversion batches.




---
