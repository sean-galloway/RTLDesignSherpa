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

### NEXYS-002: Rehome NexysA7 under projects/fpga-systems + split Genesys2-specific flows

**Priority:** Medium
**Status:** [ ] Open (2026-07-29)

**Goal:** Structural reorg of the FPGA board projects under the existing
`projects/fpga-systems/` parent.

**Moves:**
- Move `projects/NexysA7/` -> `projects/fpga-systems/NexysA7/`.
- The stream-perf / stream-mon collateral that is **Genesys2-specific** (today it
  lives under the NexysA7 tree, e.g. `flows-stream-bridge/rtl/stream_char_genesys2_top.sv`,
  `flows-stream-monitor/rtl/stream_mon_genesys2_top.sv`, and any Genesys2 XDC /
  build recipes) moves into a `projects/fpga-systems/Genesys2/` directory.
- Split shared vs board-specific: NexysA7-only tops/XDC stay under NexysA7,
  Genesys2-only under Genesys2, common harness/host under a shared area
  (mirrors the [[fpga/cmn-infra]] split already in the handbook).

**Then update ALL references:** filelists (`*.f`), `get_paths`/env roots in the
`dv/tests` wrappers, host `sys.path` inserts, Makefile paths, XDC includes, and
the handbook/vault links (`vault/handbook/fpga/NexysA7/...`,
`vault/handbook/fpga/Genesys2/...`, and this Tasks area's own path). Run
`bin/filelist_registry.py --check` and the char/mon sims after the move.

**Note:** likely rename/rehome this very Tasks area to
`vault/Tasks/projects/fpga-systems/...` (mirror-the-repo-path convention) as part
of the move; fold NEXYS-001 in with it.

---

### NEXYS-003: Migrate the remaining char flows onto the shared fpga/bin layer

**Priority:** Medium
**Status:** [ ] Open (2026-07-30)

**Goal:** `fpga/bin/` now holds the common UART/board/sequence layer
(`uart_link.py`, `board.py`, `boards/`, `sequence.py`, one `program_fpga.tcl`).
The pumice DDR2 flow was migrated as the proof. Bring the other flows across.

**Still duplicated (3 copies of the port scan):**
- `stream_characterization/flows-stream-bridge/host/harness_addrs.py`
  — `autodetect_port()` (SCRATCH round-trip probe)
- `rapids_characterization/flows-rapids-beats/host/rapids_char_io.py`
  — `autodetect_port()` (CSR_ID 'RAP1' probe)
- `cdc_counter_display/host/cdc_demo.py`
  — `autodetect_port()` (BUILD_ID 'CDC1' probe)

Each becomes a thin wrapper over `uart_link.find_port(probe=...)`, exactly as
`ddr2_char.autodetect_port` now is. New callers should prefer
`Board.find_uart_port(probe=...)`, which also filters by USB serial.

**Still duplicated (6 remaining copies of program_fpga.tcl):**
`flows-litedram-uart`, `flows-rapids-beats`, `flows-stream-bridge`,
`flows-stream-monitor`, `flows-vivado-mcdma`, `timing_characterization/fpga`.
Each flow Makefile drops its inline `program:` recipe and instead sets
`BITSTREAM` + `RDS_ROOT` and includes the global `make/fpga_flow.mk` (the
[[test-runner]] `make/tests.mk` pattern, applied to board handling); the
per-flow tcl is then deleted. Note `flows-stream-bridge` also switches bitstream
name on `BOARD=genesys2` — fold that into the Makefile, not the tcl.

**Then:** consider moving the Vivado build targets (`project`/`synth`/
`bitstream`/`utilization`/`timing`) into `make/fpga_flow.mk` too — they are
near-identical across all seven flows. Deliberately left out of the first pass
so adopting the file could not break a working build. Overlaps NEXYS-001.

**Sequences:** consider `projects/fpga-systems/<board>/<component>/bin/` sequence areas
for rapids/stream, mirroring `projects/fpga-systems/NexysA7/pumice/bin/`.

**Pumice area scaffold (created 2026-07-30, empty):** the component shape is
declared at `projects/fpga-systems/NexysA7/pumice/` — `rtl/` (flat, shared blocks),
`dv/{tb,tbclasses,tests}` (tests those blocks), `bin/` (sequences, populated),
and `build-perf/{rtl,dv,host,fpga}` for one harness build, with `fpga/`
holding `tcl,constraints,bitstream,reports`. Siblings are `build-<variant>/`.
See its README for the what-goes-where rules.

The migration is a near-mechanical mapping from the existing tree:
- `ddr2_char_framework/rtl/*`  -> `pumice/rtl/` (flat; keep `bridges/` as-is)
- `ddr2_char_framework/dv/{tb,tbclasses,tests}` -> `pumice/dv/`
- `flows-ours-uart/{rtl,rtl-vivado}` -> `pumice/build-perf/rtl/`
- `flows-ours-uart/host` -> `pumice/build-perf/host/`
- `flows-ours-uart/{tcl,constraints,bitstream,reports}` -> `pumice/build-perf/fpga/`
- `flows-ours-uart/{rtl-vivado,bin}` -> `pumice/build-perf/{rtl-vivado,bin}`
- `flows-ours-uart/{csv,plots,docs}` -> `pumice/build-perf/results/`
- `flows-litedram-uart/{rtl,constraints,tcl}` -> `pumice/build-litedram/`
  (`litedram_hp.yml`, `regen.sh`, `README.md`, `HARNESS_PLAN.md` at its root)

**While moving litedram, two things to fix rather than carry over:**
- `regen.sh` writes to `build_board/` + `build_sim/` at the flow root. Point it
  at `gen/board/` + `gen/sim/` (`--output-dir`) so generated cores sit in one
  named subdirectory per CRITICAL RULE #0.1, and update the `.gitignore`
  (already scaffolded as `gen/`).
- `rtl/char_engine_harness.sv` is described as DUT-agnostic and is what makes
  the pumice-vs-LiteDRAM comparison apples-to-apples, yet it lives in the
  litedram flow. It belongs in `pumice/rtl/` (shared by both builds); check
  whether `flows-ours-uart` has diverged its own copy of the same wiring before
  promoting it.

Then fix: `*.f` filelists + `bin/filelists.toml`, `DDR2_CHAR_FRAMEWORK_ROOT`
and `CHAR_ROOT`/`FLOW_ROOT` in `env_python` and the flow Makefile, tcl
`project_root` derivations, `get_paths` in the moved dv tests, `pumice_env.py`'s
`FLOW_HOST_REL`, and the handbook/vault links.

**Parent directory: SETTLED (Sean, 2026-07-30).** New FPGA board areas live
under `projects/fpga-systems/<board>/<component>/`, agreeing with NEXYS-002's
plan. The pumice area was created there. NEXYS-002's move of the existing
`projects/NexysA7/` tree lands alongside it.

**Unverified:** the migrated `make program` path and the pumice `run_smoke.py`
board path have NOT been run against hardware (no board attached, and pyserial
is not installed in the venv — `pip install pyserial` before board work).
