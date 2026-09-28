# TASK-005: Tests resolve filelists through the toml registry, not hardcoded paths

> Migrated 2026-09-27 from `vault/Tasks/tooling/open.md` as **TOOL-011** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** Not Started
**Owner:** TBD

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

- [ ] Add a `filelist_for(module)` helper to `TBClasses/shared/filelist_utils`
      that calls the registry (or reads the toml) and returns the `.f` path.
- [ ] `get_sources_from_filelist` gains a `module=` mode: given a module name,
      resolve via the registry instead of a literal `filelist_path`.
- [ ] Migrate tests from `filelist_path='...'` to `module='...'`. A module move
      then updates only the toml, never the tests.
- [ ] Keep `filelist_path=` working for the harness/consumer cases that assemble
      a specific `.f` rather than one module.

**Payoff, concretely:** had this existed, the CDC reorg would have moved 12 `.sv`
+ their `.f` + one toml area, and touched ZERO test files. It is the structural
fix for the fragility [[filelists]] describes.
