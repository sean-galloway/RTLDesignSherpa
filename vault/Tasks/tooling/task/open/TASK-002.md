# TASK-002: Finish validating the cloud bootstrap on a genuinely clean box

> Migrated 2026-09-27 from `vault/Tasks/tooling/open.md` as **TOOL-004** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** Not Started
**Owner:** TBD

`bin/install_tools.sh` and `bin/cloud_bootstrap.sh` were written and partly
verified on 2026-07-23, but two paths have never executed:

- [ ] **The oss-cad-suite download.** Only `--no-formal` was exercised; the
      workstation already had the suite, so the ~2 GB fetch, the GitHub-API tag
      resolution, and the tarball layout assumption (`oss-cad-suite/bin/...`)
      are all unproven. If the release asset naming has changed, the resolver
      builds a 404 URL.
- [ ] **A clean-box run end to end.** Every step was verified individually
      (apt has Verilator 5.020 on Ubuntu 24.04; `CocoTBFramework` resolves from
      PyPI at 0.6.1; sv2v and Verible download and execute) but never in
      sequence on a machine that had none of it.
- [ ] The `val/common` smoke test at the end of `cloud_bootstrap.sh` has not
      been observed passing from a cold start.

Verified and not in doubt: the pinned-Verilator shim resolves to 5.020 even
with oss-cad-suite on PATH. That was the part most likely to be silently wrong.

---
