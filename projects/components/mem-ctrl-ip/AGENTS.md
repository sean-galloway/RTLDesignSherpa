# mem-ctrl-ip — working rules

Scope: everything under `projects/components/mem-ctrl-ip/` (common-ip,
research-ip, product-ip) plus the Nexys A7 characterization/build areas
(`projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/`).

## RTL rules

- **No assertions in RTL.** Checkers live in testbenches (cocotb/Python).
  Do not add `assert`/`$error`/`SVA` to synthesizable sources, even under
  `ifndef SYNTHESIS`. (Pre-existing assertion blocks are legacy; do not
  extend them.)

## Storage-backend verification rule

Any new or changed storage backend — anything that drives
`mc_cmd_arbiter`'s `wr_commit_*` / `rd_issue_*` handshake — must be
co-verified against the **real `mc_cmd_arbiter`** at **max-depth
`NUM_ENTRIES`** with **more than N chunks in flight per direction** before
the change is considered done. Unit/fub tests of the backend alone are
necessary but not sufficient.

Why: the commit/issue-ready contract with the arbiter is structural ("sink
has room"), and the arbiter's column mask gates its entire pick pool on
that one scalar. A slot-qualified ready deadlocked the whole scheduler in
the 2026-10-13/14 granite hang and was invisible at `NUM_ENTRIES=1` (the
next push self-heals it), in unit isolation (locally well-behaved), and
with `<= N` chunks (no recycling). Three independent escape hatches had to
fail simultaneously before anything went red.

Where the nets live:

- Contract surface (fast, directed): `common-ip/dv/tests/macro/
  test_mc_store_arbiter_contract.py` — store + real arbiter, N=8, 2xN
  chunks, checks commit/drain/B/issue completion.
- Real-system repro: `product-ip/granite-ddr2-lpddr2/dv/tests/top/
  test_granite_top_geared.py` always runs one `NUM_ENTRIES=8,
  GRANITE_MANY=12` cell (back-to-back outstanding bursts > N). This is the
  cell that caught the hang class.
- Board-level gate: `ddr2_char_framework/dv/tests/test_granite_char_uart.py`
  (whole-harness, engines, exactly how the A7 drives it).

## Sims

Every shell: `source env_python` from the repo root and
`export PYTHONPATH="$(pwd)/bin"` before running pytest. SIM is verilator;
Sims never run under icarus. Sim builds are disposable
(`dv/tests/*/local_sim_build/`); clean rebuild when the RTL changes in ways
verilator's cache may miss.
