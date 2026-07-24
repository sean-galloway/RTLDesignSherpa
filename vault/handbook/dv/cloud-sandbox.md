---
title: Cloud sandbox
summary: Running sims and review batches off the workstation - what to provision, what is impossible, what only exists on one disk.
---

# Running off the workstation

`bin/cloud_bootstrap.sh` provisions a fresh sandbox (Claude cloud, Codespace,
CI runner) far enough to run simulations and [[kimi-review-rounds]].

`env_python` needs no changes to work there. Its tool paths are either guarded
by `if [ -d ]` or are harmless PATH prepends of directories that do not exist,
so it falls through to whatever the sandbox has. Its one hard requirement is
that `$REPO_ROOT/venv` exists - which is the main thing bootstrap creates.

## Verilator stays pinned at 5.020

Newer releases have cocotb VCD/FST generation bugs that surface as corrupt or
empty waves rather than as an error, so an unnoticed upgrade costs a debugging
session before anyone suspects the simulator. Ubuntu 24.04 ships exactly
`5.020-1`, so `apt-get install verilator` is the right source in a sandbox -
no source build needed. Bootstrap warns if the version does not match.

## The framework comes from PyPI, not a sibling checkout

Locally `cocotb-framework` is an editable install of the RTLDesignSherpa-DV
checkout next door. A sandbox has no sibling checkout, so it resolves from
PyPI - which means **the `requirements.txt` pin must be a version that actually
exists there**. A pin that only exists as a local git tag installs an older
release and the sandbox silently runs different BFMs. Verify with
`CocoTBFramework.__version__` after install, which bootstrap does.

## What a sandbox cannot do

- **Vivado** - FPGA builds and board runs. Licensed, ~100 GB, and the boards
  are on a desk. Not a provisioning problem; these stay on the workstation.
- **yosys / sby / sv2v** - formal ([[formal]]) needs the oss-cad-suite tarball,
  ~2 GB. Installable if wanted; not fetched by default because simulation does
  not need it.
- **verible-verilog-lint** - style lint only. Optional.

Simulation, pytest, doc generation and review batches all work without these.

## Only what is pushed exists

A cloud agent clones from the remote. It does not need `main` - any pushed
branch works - but uncommitted files and unpushed commits are invisible, and so
is anything that was never in a repo at all.

That last case is the one that bites: the Kimi review collateral at
`/mnt/data/github/rtl-doc-review/` (dispatch scripts, reviewer brief, and every
round of critiques) is **untracked on a single disk**. The scripts were vendored
into `bin/review/` so a sandbox can run a round; the round history was not, and
is not reproducible without re-spending the tokens.
