# TASK-001: Consistent Makefiles across the stream characterization flows

> Migrated 2026-09-27 from `vault/Tasks/nexysa7/open.md` as **NEXYS-001** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

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

**Unified board runner (the bigger half — stop writing a new runner per test):**
Every board test currently re-implements connect + config + kick + poll + verify
in its own `main()`, and `poc_coverage.py` bypasses the shared runner entirely
(rolls its own bridge + config). Layer it once:

1. **Common UART harness (host-stack, already exists — reuse, never reinvent):**
   the transport + by-name register access -- `UARTAxiBridge`, `autodetect_port`
   (ttyUSB numbering drifts), and CSR-by-name via `harness_addrs.H()` (harness
   CSRs) / regmap `A()` (STREAM regs). See [[fpga/cmn-infra/host-stack]]. The
   runner PLUGS INTO this; it must not own UART/AXIL or hardcode offsets.
2. **Shared runner** on top: `CharacterizationRunner`'s core
   (`configure_stream` / `clear_stats` / `setup_timer` / `kick_channels` /
   `poll_completion`) -- one engine for every flow.
3. **Plug-points**: a `workload` (legacy chain / mixed extended chain / error- or
   packet-type-triggering traffic) and a `verify`/`coverage` step (TIMER beat +
   CRC, perf-window read, or **monbus tally sweep for the packet tuples**), plus
   a `loop` mode (one-shot / N-iter soak / scenario sequence).

Then a new board test is a `{workload, verify, loop}` config, NOT a new program:
`stream_ext_soak` = {mixed ext chains, TIMER+CRC, soak}; monitor coverage =
{all-packet-type traffic, tally sweep, scenario sequence}; legacy char =
{legacy chains, perf windows}. Kill the roll-your-own path in `poc_coverage`;
fold `stream_ext_suite` / `stream_ext_soak` / `run_characterization` onto the
shared runner.

**Deliverable:** the agreed definition captured in
[[fpga/cmn-infra/build-flows]], then the flow Makefiles converged to it (shared
include, no duplicated build args), with a note in each flow pointing at the
common contract.

**Related:** the components-side convergence already done via `make/tests.mk`
([[reference_components_regression_makefile]] pattern) is the model to mirror.

---
