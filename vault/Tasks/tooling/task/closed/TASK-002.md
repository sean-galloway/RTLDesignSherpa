# TASK-002: Finish validating the cloud bootstrap on a genuinely clean box

> Migrated 2026-09-27 from `vault/Tasks/tooling/open.md` as **TOOL-004** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** closed 2026-09-27 (opened 2026-07-23) -- all three paths executed on a clean box
**Owner:** TBD

`bin/install_tools.sh` and `bin/cloud_bootstrap.sh` were written and partly
verified on 2026-07-23, but two paths have never executed:

- [x] **The oss-cad-suite download.** (2026-09-27: fetched, tag resolved, `oss-cad-suite/bin/*` layout as assumed; yosys, sby, iverilog, gtkwave all present after install) Only `--no-formal` was exercised; the
      workstation already had the suite, so the ~2 GB fetch, the GitHub-API tag
      resolution, and the tarball layout assumption (`oss-cad-suite/bin/...`)
      are all unproven. If the release asset naming has changed, the resolver
      builds a 404 URL.
- [x] **A clean-box run end to end.** (2026-09-27: ubuntu:24.04 container, nothing preinstalled but git/python3/curl/build-essential; `cloud_bootstrap.sh` rc=0 in 51 s wall on this network) Every step was verified individually
      (apt has Verilator 5.020 on Ubuntu 24.04; `CocoTBFramework` resolves from
      PyPI at 0.6.1; sv2v and Verible download and execute) but never in
      sequence on a machine that had none of it.
- [x] The `val/common` smoke test (2026-09-27: `test_counter_bin.py` 2 passed from cold, Verilator 5.020 from apt matching the pin) at the end of `cloud_bootstrap.sh` has not
      been observed passing from a cold start.

Verified and not in doubt: the pinned-Verilator shim resolves to 5.020 even
with oss-cad-suite on PATH. That was the part most likely to be silently wrong.

---

## Closed 2026-09-27: what the clean box found

Run three times in a fresh `ubuntu:24.04` container against a scratch clone
(tooling close-out, monitor-lite session). The first run died before Verilator:
`install_tools.sh` called `sudo` unconditionally and a container is root with
no sudo binary -- so the "clean box" path this script exists for had never
actually executed. Two more things surfaced once it ran:

1. `unzip` is not on a clean box, so the sv2v step warned and skipped. Added
   to the apt set.
2. `cloud_bootstrap.sh`'s closing "Not available in this sandbox" report
   checked PATH without the install prefixes on it (this shell never sources
   env_python), so it printed yosys and sby "missing" two screens after
   installing them. The report now adds `/mnt/data/tools` and
   `~/.rtlds-tools` bins before looking.

Third run, all three boxes above ticked: Verilator 5.020 (apt, matches pin),
oss-cad-suite installed with the bundled 5.045 neutralised, sv2v v0.0.13
installed, CocoTBFramework 0.6.1 from PyPI, smoke test 2 passed, rc=0.
Vivado and Verible remain "not available", as documented.
