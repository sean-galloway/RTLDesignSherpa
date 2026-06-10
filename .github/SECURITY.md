# Reporting Vulnerabilities

If you find a problem in this project that should not be discussed in a
public GitHub issue, please email **sean.galloway@outlook.com** with the
details. Please do not open a public issue for the report itself.

We aim to acknowledge new reports within a week.

## Scope

This project is an educational SystemVerilog design + verification
repository. It is not deployed as a network service and does not handle
production user data. The most relevant report categories are:

- **Silent RTL defects** — an RTL bug that lets a test pass when the
  design behavior is in fact incorrect (e.g., a monitor that suppresses
  legitimate errors, a checker that signs off invalid bursts, a
  scoreboard that compares the wrong fields).
- **Generator output integrity** — defects in code generators
  (`bridge_generator.py`, PeakRDL flows, etc.) that produce SystemVerilog
  or test code with stealthy mismatches between wrapper and core, where
  the wrapper compiles cleanly but exercises the wrong RTL behavior.
- **Formal flow tooling** — issues in the formal harnesses under
  `formal/` that report PASS on a proof that did not actually execute,
  or that mask counterexamples.
- **Build / install / CI scripts** — vulnerabilities in any script
  that could be invoked unintentionally during a `pytest` run, an
  `env_python` source, or a CI job.
- **Exposed credentials** — any tokens, SSH keys, vendor licenses, or
  private data inadvertently committed to the repo.

Out of scope:

- Simulation-only behavior that has no impact outside the test
  environment.
- Bugs in the open-source toolchain itself (Verilator, CocoTB, yosys,
  sby, etc.) — please file those upstream.
- Bugs in vendor IP or vendor tool flows that this repo only references.

## What to include

- The affected subsystem and module (e.g., `rtl/amba/shared/...`).
- The commit SHA you reproduced against (`git rev-parse HEAD`).
- Tool versions: simulator (`verilator --version`), Python, CocoTB.
- A minimal reproducer if one exists — ideally the exact `pytest …`
  invocation and the relevant log excerpt.
- Your contact email for follow-up.

## Supported versions

The project tracks the `main` branch. Older tags / branches are not
patched — please reproduce against the latest `main` before reporting.
