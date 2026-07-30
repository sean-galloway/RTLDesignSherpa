<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# NexysA7 tasks — open (not started)

### NEXYS-001: Consistent Makefiles across the stream characterization flows

**Priority:** Medium
**Status:** [ ] Open (2026-07-29)

**Goal:** The NexysA7 stream-characterization flows each carry their own
Makefile with drifting targets and build settings. Make them consistent — but
first **define what "consistent" means** (open question, to settle with Sean),
then align the flows to it.

**Flows in scope:**
- `projects/NexysA7/stream_characterization/flows-stream-bridge/` — perf/char
  (the "stream-perf"/"stream-char" flow; `dv/tests/Makefile` + host runner).
- `projects/NexysA7/stream_characterization/flows-stream-monitor/` — monitor
  coverage.
- siblings: `flows-idma-bridge/`, `flows-vivado-mcdma/`, and the top-level
  `stream_characterization/Makefile` dispatcher.

**Why now:** drift is already biting. Concrete symptoms:
- The perf sim build was missing `--unroll-count 4096 --unroll-stmts 20000`
  (needed once monitors-on `RD_MON_MAX_TRANS = NUM_CHANNELS*AR_MAX+4 > 64`),
  while the sibling monitors-on sims (`test_stream_mon`, `test_stream_top_monbus`,
  macro `test_stream_core`) already had it. Fixed ad hoc in commit fe58c772 — but
  the per-flow copy is exactly the rot a consistent contract would prevent.
- `compile_args` are duplicated three times inside `test_stream_char.py` alone.
- Target names / levels / clean semantics are not guaranteed identical across
  flows.

**To DEFINE (the real first step):** what a consistent flow Makefile guarantees —
candidate contract:
- Same target names + meaning: `clean-all`, `run-all-{gate,func,full}`,
  `*-parallel`, `*-wave`, `help`, and the `REG_LEVEL`/`TEST_LEVEL` bridge.
- One shared source of Verilator build args (the unroll flags, the `-Wno-*`
  set) instead of per-test copies — likely a shared include or a helper in
  `make/` / `bin/`, mirroring the components `make/tests.mk` convergence.
- `make clean-all` ALWAYS wipes generated + `local_sim_build` before a run
  (the CRITICAL RULE #0 regen discipline).
- Consistent host-runner entry points (`run_characterization.py`, suites).

**Deliverable:** the agreed definition captured in
[[fpga/cmn-infra/build-flows]], then the flow Makefiles converged to it (shared
include, no duplicated build args), with a note in each flow pointing at the
common contract.

**Related:** the components-side convergence already done via `make/tests.mk`
([[reference_components_regression_makefile]] pattern) is the model to mirror.
