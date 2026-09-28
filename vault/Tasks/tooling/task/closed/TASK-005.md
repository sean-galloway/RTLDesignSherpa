# TASK-005: Tests resolve filelists through the toml registry, not hardcoded paths

> Migrated 2026-09-27 from `vault/Tasks/tooling/open.md` as **TOOL-011** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** CLOSED 2026-09-27 -- helper, module= mode, 353 tests migrated, handbook note
**Owner:** tooling session (Claude)

Every test hardcodes its filelist location:

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path='rtl/common/filelists/fifo_async.f')

So moving a module's `.f` (e.g. the CDC reorg: common/amba -> rtl/cdc) forces an
edit to every test that names the old path. That is the repo's #1 silent-failure
trap -- a missed test path resolves to nothing and the test "passes" against no
DUT. It made the CDC reorg touch ~10 test files it should not have had to.

**Fix:** resolve the filelist by MODULE NAME through `bin/filelists.toml` /
`bin/filelist_registry.py`, which already answers "which filelist provides
module X" (`--find MODULE`). The test names the module, the registry returns the
`.f`; location is the registry's concern, not the test's.

- [x] Add a `filelist_for(module)` helper to `TBClasses/shared/filelist_utils`
      that calls the registry (or reads the toml) and returns the `.f` path.
- [x] `get_sources_from_filelist` gains a `module=` mode: given a module name,
      resolve via the registry instead of a literal `filelist_path`.
- [x] Migrate tests from `filelist_path='...'` to `module='...'`. A module move
      then updates only the toml, never the tests.
- [x] Keep `filelist_path=` working for the harness/consumer cases that assemble
      a specific `.f` rather than one module.

**Payoff, concretely:** had this existed, the CDC reorg would have moved 12 `.sv`
+ their `.f` + one toml area, and touched ZERO test files. It is the structural
fix for the fragility [[filelists]] describes.

## Closure (2026-09-27)

- `filelist_for(repo_root, module)` in `bin/TBClasses/shared/filelist_utils.py`
  resolves through `bin/filelists.toml`'s `filelist_dirs`: a named `<module>.f`
  is the fast path, otherwise a direct-source scan of the registered filelists;
  no hit raises FileNotFoundError, several raise ValueError (a test must never
  resolve to two DUTs). About 5 ms per call.
- `get_sources_from_filelist(repo_root, filelist_path=None, *, module=None)`
  takes exactly one of the two. `filelist_path=` stays for the harness and
  consumer cases that assemble a specific `.f`.
- 353 val tests migrated: 346 keyword calls to `module='<stem>'`, 7 val/amba
  files that assign the path first to `filelist_path = filelist_for(repo_root,
  '<stem>')`. The migration was re-derived from HEAD so every diff line is the
  substitution or the import and nothing else (regex over `git diff -U0`: zero
  stray lines), after a first pass had both broken the 7 assignment files
  (NameError in 247 val/amba cells) and dropped a blank line in 116 files.
- Unit tests: `bin/tests/test_filelist_utils.py` (6). Regression per area at
  GATE after `make clean-all`: common 77, math 120, cdc 36, monitor-lite 99,
  amba 810/811 -- the one failure is independent of the change and filed as
  amba BUG-037.
- Handbook: [[filelists]] "Tests name the module, not the filelist path".

Not migrated, by design: projects/components tests that build a `.f` path from a
component-relative constant (`_FILELIST = ...`) -- those are the harness cases
the fourth box keeps working, and each component lane owns its tests.
