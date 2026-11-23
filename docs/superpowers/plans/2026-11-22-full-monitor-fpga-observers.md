# Full-Monitor FPGA Observers Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add passive full-feature AXI observer variants and measure full-monitor FPGA optimizations against a reproducible, functionally identical full-monitor baseline.

**Architecture:** Extract the two existing observer bodies into shared cores with a `USE_FULL_MONITOR` tap selector, then preserve the current names as lite wrappers and add separate full wrappers. Passive read/write full-monitor taps drive `axi_monitor_filtered` from real bus handshakes; a new `cmd_refused` event makes saturation loss visible without allowing `block_ready` to influence the observed bus.

**Tech Stack:** SystemVerilog, Vivado OOC synthesis/place/route, cocotb with RDS-DV AXI BFMs, pytest through repository Make targets, SymbiYosys/sv2v formal, Markdown characterization.

**Spec:** `docs/superpowers/specs/2026-11-22-full-monitor-fpga-observers-design.md`

## Global Constraints

- Work on shared `main`; never create a branch or worktree. Commit with `git commit -F <msgfile> -- <paths>`, verify the named staged set, and add no attribution trailers.
- Never switch an existing project consumer to a full observer. Existing lite names, defaults, packet behavior, and register map stay compatible.
- Do not hand-edit generated RTL or register outputs. Do not commit generated/report churn or unrelated active Onyx, mem-ctrl, or other agent changes.
- All new modules have a `.f` filelist covered by `bin/filelists.toml`; use reset macros for resettable state and `r_`/`w_` signal conventions. No assertions in synthesizable RTL.
- Full-before/full-after comparisons use identical parameters and cones. Kintex-7 is `xc7k325tffg900-2` at 6.667 ns; Artix-7 is `xc7a100tcsg324-1` at 10.0 ns.
- Every simulation command starts with `source env_python`, uses `clean-all` before a regression, and invokes the area Make target. Never run bare pytest.
- A rejected optimization is reverted and documented with its numbers. Lite observers are context, never the correctness reference for full-only behavior.
- Keep the existing `obs_regs` map. Full variants use existing parameter defaults; only the explicit full-feature synthesis/test profile enables every cone.

## Review Focus

- **Observed command at table saturation:** the external bus must continue handshaking while the refused count increases exactly once per untracked accepted command; Task 4's passivity test pins this.
- **Same-ID command at the command cap:** a merge into a pending entry is tracked, not refused; Task 2's directed and formal tests pin the zero-refusal case.
- **Same-cycle AW+W and banked writes:** write-order attribution must remain intact and external W handshakes must not be gated; Task 4 reuses the same-cycle/banked stimulus against the passive write tap.
- **Stale payload after reset/clear and slot reuse:** an invalid entry must produce no match or event, and a reused slot must return only its new ID/payload; Tasks 6 and 7 include mutation-sensitive tests.
- **Capability self-description:** full variants report only built full cones while lite `OBS_CAPS0[5:4]` remains zero; Tasks 1, 3, and 4 check both families so the shared core cannot advertise absent logic.

---

### Task 1: Extract shared observer cores without changing lite behavior

**Files:**
- Rename: `projects/components/utility-ip/misc/rtl/axi4_intf_master_observer.sv` -> `projects/components/utility-ip/misc/rtl/axi4_intf_master_observer_core.sv`
- Rename: `projects/components/utility-ip/misc/rtl/axi4_intf_slave_observer.sv` -> `projects/components/utility-ip/misc/rtl/axi4_intf_slave_observer_core.sv`
- Create: the two original observer paths as thin lite wrappers
- Modify: `projects/components/utility-ip/misc/rtl/filelists/axi4_intf_master_observer.f`
- Modify: `projects/components/utility-ip/misc/rtl/filelists/axi4_intf_slave_observer.f`
- Create: `vault/tracking/projects/components/utility-ip/misc/task/active/TASK-007.md`
- Modify: `vault/tracking/projects/components/utility-ip/misc/task/INDEX.md`

**Interfaces:**
- Produces: `axi4_intf_master_observer_core #(..., parameter bit USE_FULL_MONITOR = 1'b0)` and the slave equivalent; this task elaborates only `USE_FULL_MONITOR=0`.
- Preserves: public `axi4_intf_master_observer` and `axi4_intf_slave_observer` ports and parameter defaults exactly.
- Produces: misc TASK-007, linked to spec commit `c334d64a0`, as the owner tracker for all later tasks.

- [ ] **Step 1: Capture the lite register/traffic baseline**

```bash
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub clean-all
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub run-axi4_intf_observer-full-parallel
```

Expected: all existing observer cells pass. Record the count in TASK-007.

- [ ] **Step 2: Create the tracker and perform the mechanical core rename**

Set misc TASK INDEX `Next ID: TASK-008`, active count 1. Rename each body module to `*_core`, add `USE_FULL_MONITOR=0`, and leave its current monlite generate path as the only implemented branch. Create thin wrappers that declare the original public interface and instantiate the core with `USE_FULL_MONITOR(1'b0)` using `.*` signal connections.

- [ ] **Step 3: Make capability selection explicit without changing lite values**

Add localparams in each core for the family-dependent cone bits. For `USE_FULL_MONITOR=0`, `OBS_CAPS0[5:4]` must remain `2'b00`; error/timeout/completion/threshold bits retain their current lite expressions. Do not add the full branch in this task.

- [ ] **Step 4: Update standalone filelists and lint/elaborate both lite tops**

Each existing filelist includes the core before its thin public wrapper and retains the existing dependency closure. Run:

```bash
python3 bin/filelist_registry.py --check
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub clean-all
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub run-axi4_intf_observer-full-parallel
```

Expected: registry PASS and exactly the Step 1 observer result. Any packet, capability, or register difference is a failed extraction, not an accepted behavior change.

- [ ] **Step 5: Commit the compatible core extraction**

Commit only the two cores, two lite wrappers, two filelists, TASK-007, and its INDEX with message `refactor(misc): share observer bodies behind stable lite wrappers`.

### Task 2: Add exact command-refusal accounting to the full monitor

**Files:**
- Modify: `rtl/amba/ocelus/axi_monitor_trans_mgr.sv`
- Modify: `rtl/amba/ocelus/axi_monitor_base.sv`
- Modify: `rtl/amba/ocelus/axi_monitor_filtered.sv`
- Modify: `val/amba/test_axi_monitor_trans_mgr.py`
- Modify: `formal/amba/axi_monitor_trans_mgr/formal_axi_monitor_trans_mgr.sv`
- Modify: `formal/amba/axi_monitor_trans_mgr_banked/formal_axi_monitor_trans_mgr_banked.sv`

**Interfaces:**
- Produces: `output logic cmd_refused` on `axi_monitor_trans_mgr`, `axi_monitor_base`, and `axi_monitor_filtered`.
- Defines: `cmd_refused = cmd_valid && cmd_ready && !addr_hit_any && !(|addr_alloc_oh)` after the upstream ID filter. This covers command-cap refusal and no-free-slot refusal, but not a held command or same-ID merge.
- Consumes: existing `addr_hit_any`, `addr_alloc_oh`, and actual `cmd_valid && cmd_ready`; no admission policy changes.

- [ ] **Step 1: Add failing directed refusal scenarios**

Add `phase_command_refusal_accounting` to the transaction-manager TB with these checks:

```python
assert refused_for_full_new_id == 1       # actual handshake, no allocation
assert refused_while_not_ready == 0       # valid held without ready
assert refused_for_same_id_merge == 0     # existing pending entry absorbs it
assert refused_after_free_and_accept == 0 # allocation succeeds again
```

Exercise `MAX_TRANSACTIONS=4` (no command reserve) and a reserved-cap configuration so both full-table and command-cap refusal are covered.

- [ ] **Step 2: Run the directed test and prove the output is missing**

```bash
source env_python && make -C val/amba clean-all
source env_python && make -C val/amba run-axi_monitor_trans_mgr-gate-parallel
```

Expected: compile/elaboration failure for unconnected `cmd_refused`, or the new scenario failing because no refusal event exists.

- [ ] **Step 3: Implement and plumb `cmd_refused`**

Compute the single event in `axi_monitor_trans_mgr` without changing `addr_wants_alloc`, `w_cmd_headroom`, or CAM writes. Pass it through base and filtered status ports. Existing in-path wrappers may leave the new filtered output open; their admission behavior does not change.

- [ ] **Step 4: Add formal non-vacuity and exclusivity properties**

In both unbanked and banked formal harnesses, bind `cmd_refused` and prove it implies an actual command handshake, no same-ID hit, and no allocation. Prove no refusal for a held command or a successful allocation. Add covers for cap refusal, no-free-slot refusal at depth 4, same-ID merge at cap, and refusal followed by successful allocation after retirement.

- [ ] **Step 5: Run targeted simulation and formal**

```bash
source env_python && make -C val/amba run-axi_monitor_trans_mgr-full-parallel
make -C formal/amba/axi_monitor_trans_mgr clean prove cover
make -C formal/amba/axi_monitor_trans_mgr_banked clean prove cover
```

Expected: simulation PASS; prove PASS; every new cover reached. Mutate `cmd_refused` to ignore `cmd_ready` and confirm the held-command property fails.

- [ ] **Step 6: Commit refusal plumbing**

Commit only the three RTL files, directed TB, and two formal harnesses with message `feat(amba): report full-monitor command admission loss`.

### Task 3: Build passive full taps and separate public full observers

**Files:**
- Create: `rtl/amba/axi4/axi4_rd_monfull_snoop.sv`
- Create: `rtl/amba/axi4/axi4_wr_monfull_snoop.sv`
- Create: `rtl/amba/filelists/axi4_rd_monfull_snoop.f`
- Create: `rtl/amba/filelists/axi4_wr_monfull_snoop.f`
- Create: `projects/components/utility-ip/misc/rtl/axi4_intf_master_observer_full.sv`
- Create: `projects/components/utility-ip/misc/rtl/axi4_intf_slave_observer_full.sv`
- Create: `projects/components/utility-ip/misc/rtl/filelists/axi4_intf_master_observer_full.f`
- Create: `projects/components/utility-ip/misc/rtl/filelists/axi4_intf_slave_observer_full.f`
- Modify: `projects/components/utility-ip/misc/rtl/axi4_intf_master_observer_core.sv`
- Modify: `projects/components/utility-ip/misc/rtl/axi4_intf_slave_observer_core.sv`
- Test: `projects/components/utility-ip/misc/dv/tests/fub/test_axi4_intf_observer.py`

**Interfaces:**
- Produces: `axi4_rd_monfull_snoop` with AR-like `cmd_*`, R-like `data_*`, all full configuration inputs, MonBus output, `busy`, `active_transactions`, `error_count`, `transaction_count`, `dropped_count`, and `refused_count`.
- Produces: `axi4_wr_monfull_snoop` with AW-like `cmd_*`, W-like `data_*`, B-like `resp_*`, the same configuration/status groups, `USE_WDATA_ORDER_Q`, and `NUM_BANKS`.
- Produces: public `axi4_intf_{master,slave}_observer_full`, each instantiating its Task 1 core with `USE_FULL_MONITOR(1'b1)`.
- Consumes: Task 2 `axi_monitor_filtered.cmd_refused`.

- [ ] **Step 1: Add compile/elaboration runners for the absent full tops**

Add full-top parameter sets to `test_axi4_intf_observer.py` using `_PARAMS_ALL` for all cones and `_PARAMS` for the default profile. The first run must fail because the full modules/filelists do not exist.

- [ ] **Step 2: Implement the passive read tap**

Instantiate `axi_monitor_filtered` with `IS_READ=1`, `IS_AXI=1`, actual observed valid/ready pairs, and read response derived from accepted `data_valid && data_ready && data_last`. Gate monitor-valid inputs with `cfg_monitor_enable`, clear on `cam_clear | ~cfg_monitor_enable`, and leave `block_ready` unconnected to observation.

- [ ] **Step 3: Implement the passive write tap**

Use `IS_READ=0`, `IS_AXI=1`, separate actual W and B handshakes, and forward `USE_WDATA_ORDER_Q`/`NUM_BANKS`. Do not insert an AXI master/slave endpoint, skid buffer, or ready gate.

- [ ] **Step 4: Add per-tap refused counters**

In each tap use a saturating 16-bit `r_refused`, cleared by reset or the monitor clear epoch and incremented only on `cmd_refused`. Drive `dropped_count=16'd0`; full reporter backpressure is not a drop. Drive emitted status from the full monitor's existing counters.

- [ ] **Step 5: Select full taps and truthful capabilities in the shared cores**

Add the `USE_FULL_MONITOR=1` generate branch. Connect all existing full-only masks, window triggers, debug enables, performance enables, and range controls. Master full taps enable the existing ID slice per port with base `CH_BASE + gi*NUM_CHANNELS`; lite wiring remains byte-for-byte in its own branch. Full `OBS_CAPS0[5:4]` reflect `TAP_ENABLE_PERF_LOGIC` and `TAP_ENABLE_DEBUG_LOGIC`.

- [ ] **Step 6: Add thin full wrappers and standalone filelists**

Use the existing observer interface/defaults, not the in-path full wrapper defaults. Full observer filelists include the shared core, full wrapper, both passive tap closures, and the existing observer dependencies. Run registry checking and compile all four public observer tops.

- [ ] **Step 7: Run default full observer register/traffic tests and lite control**

```bash
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub clean-all
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub run-axi4_intf_observer-gate-parallel
```

Expected: new full register/traffic cells pass and all lite cells retain Task 1 results.

- [ ] **Step 8: Commit the unoptimized full observer source baseline**

Commit the taps, cores, full wrappers, filelists, and runner declarations with message `feat(misc,amba): add passive full-monitor observer variants`. Record this commit hash in TASK-007 as `baseline_rtl_commit`; no optimization has yet been made.

### Task 4: Prove full-only features, passivity, and loss accounting

**Files:**
- Modify: `projects/components/utility-ip/misc/dv/tests/fub/test_axi4_intf_observer.py`
- Modify: `projects/components/utility-ip/misc/dv/tbclasses/axi4_intf_observer_tb.py`
- Modify: `formal/amba/axi_monitor_base/formal_axi_monitor_base.sv`
- Modify: `formal/amba/axi_monitor_filtered/formal_axi_monitor_filtered.sv`

**Interfaces:**
- Consumes: all Task 3 public full observer tops and status outputs.
- Produces: reusable `cocotb_test_observer_full_passivity`, `cocotb_test_observer_full_perf_debug`, and `cocotb_test_observer_full_saturation_reuse` scenarios.

- [ ] **Step 1: Write the independent passivity/saturation test**

Drive more distinct IDs than the table can hold in a fixed cycle window while forcing MonBus not ready. Hold each offered command stable until its actual ready handshake, but count offered and accepted beats independently of DUT status; compare the acceptance timeline with the lite control under identical stimulus. Assert:

```python
assert external_accepted == external_offered
assert full_acceptance_timeline == lite_acceptance_timeline
assert external_replays == 0
assert refused_total == external_accepted_untracked
assert refused_for_id_outside_master_slice == 0
assert dropped_count == 0
assert tap_blocked == (refused_total != 0)
```

Run both master-full and slave-full with `MAX_TRANSACTIONS=4` and the reserved-cap configuration. Enable the master ID slice for the filtered-ID check; an excluded ID must produce no allocation and no refusal.

- [ ] **Step 2: Write full-only performance/debug coverage**

Using `_PARAMS_ALL`, trigger a software performance window and a transaction state change. Require `OBS_CAPS0[5:4]==2'b11`, observe the full performance-window and debug packets, and check their event order and payload against the TB model. The lite control must continue reporting `OBS_CAPS0[5:4]==0`.

- [ ] **Step 3: Add same-cycle/banked write and clear/reuse coverage**

Run same-cycle AW+W with `USE_WDATA_ORDER_Q=1`, `NUM_BANKS=4`, and more than one outstanding write. Check response attribution, no external backpressure, no false refusal for same-ID merges, exact post-clear accounting, and no stale event after reset/reissue.

- [ ] **Step 4: Run the full observer matrix to expose integration defects**

```bash
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub clean-all
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub run-axi4_intf_observer-full-parallel
```

Expected: all new full scenarios and existing lite scenarios PASS. Fix tap integration only; do not optimize the full monitor in this task.

- [ ] **Step 5: Verify base/filtered refusal pass-through formally**

Bind `cmd_refused` in the base and filtered formal harnesses. Prove combinational pass-through from the transaction manager to the filtered output and add a non-vacuous cover that reaches a refusal at each boundary. Run clean prove/cover for both harnesses.

- [ ] **Step 6: Commit verified baseline DV**

Commit only observer DV and any formal binding changes with message `test(misc,amba): prove full observers passive and loss-accounted`. Update TASK-007 with counts and confirm `baseline_rtl_commit` still names the Task 3 RTL checkpoint.

### Task 5: Add the full-observer synthesis matrix and capture the baseline

**Files:**
- Create: `rtl/amba/fpga/bin/full_observer_synth_sweep.sh`
- Modify: `rtl/amba/fpga/tcl/monitor_synth.tcl`
- Modify: `docs/markdown/rtl-amba/monitor/monitor_characterization.md`
- Modify: `vault/tracking/projects/components/utility-ip/misc/task/active/TASK-007.md`

**Interfaces:**
- Produces: `RUN_LABEL=<label> JOBS=<n> full_observer_synth_sweep.sh [feature_master feature_slave deploy_full deploy_lite]`.
- Produces: isolated reports under `rtl/amba/fpga/results/full_observer_<RUN_LABEL>/` and one CSV per run label.
- Adds: optional `SYNTH_GENERICS` to the Tcl recipe; existing callers see no change.

- [ ] **Step 1: Extend the Tcl recipe compatibly**

Pass nonempty `SYNTH_GENERICS` to `synth_design`. Add `LUT as Memory` to the per-row `summary.txt` without changing the existing `summary.csv` column layout. Preserve all existing utilization, hierarchy, route-status, power, and register-to-register timing reports.

- [ ] **Step 2: Implement the named synthesis rows**

`feature_master` and `feature_slave` use the corresponding full public filelist/top, `MAX_TRANSACTIONS=16`, `NUM_BANKS=1`, `N_ADDR_RANGES=4`, and all six reporter cones enabled. `deploy_full` uses master-full with `MAX_TRANSACTIONS=64`, `NUM_BANKS=4`, and existing defaults. `deploy_lite` uses the existing master-lite top at the same deployment capacity for context.

- [ ] **Step 3: Run static checks and the complete full-before matrix**

```bash
bash -n rtl/amba/fpga/bin/full_observer_synth_sweep.sh
RUN_LABEL=full_before JOBS=4 rtl/amba/fpga/bin/full_observer_synth_sweep.sh
```

Expected: 6 full rows plus 2 lite context rows, all present; zero unrouted nets in every accepted row. A failed row must be fixed or reported as failed, never skipped silently.

- [ ] **Step 4: Extract hierarchy and critical paths**

Record LUT, FF, LUTRAM, BRAM, register-to-register WNS, failing endpoints, logic levels, startpoint, and endpoint. Identify the highest-cost and worst-timing full-monitor subblocks from reports, not RTL impressions. Select `feature_master` on both parts as the common per-candidate A/B row.

- [ ] **Step 5: Publish baseline tables and commit the measurement infrastructure**

Append a full-observer section to the existing characterization document with the `baseline_rtl_commit`, flow commit, parameters, absolute values, and reproduction command. Do not commit raw Vivado logs or result directories. Commit the script, Tcl, Markdown, and tracker with message `measure(amba,misc): capture full observer FPGA baseline`.

### Task 6: Measure reset-free CAM ID/payload storage

**Files:**
- Modify: `rtl/amba/ocelus/monitor_trans_cam.sv`
- Modify: `val/amba/test_monitor_trans_cam.py`
- Modify: `docs/markdown/rtl-amba/monitor/monitor_characterization.md`
- Modify: `vault/tracking/projects/components/utility-ip/misc/task/active/TASK-007.md`

**Interfaces:**
- Preserves: every `monitor_trans_cam` port and lowest-free allocation/match behavior.
- Changes only: reset/clear handling of `r_id` and `r_payload`; `r_valid` retains async reset and synchronous clear.

- [ ] **Step 1: Add mutation-sensitive clear/reuse coverage**

Add `t19_sync_clear_reuse`: fill a slot with a nonzero ID/payload, assert synchronous `clear`, verify all match vectors are invalid, then reuse the slot with a different ID/payload. Require new-ID matches, old-ID misses, exact new payload, and no stale valid bits. Verify it passes the baseline; mutating the new readback to the old payload must fail it.

- [ ] **Step 2: Split validity/control from payload storage**

Keep `r_valid` in `ALWAYS_FF_RST`. Write `r_id` and `r_payload` only on `entry_we[gi]` in a reset-free clocked process. Do not add a RAM attribute: all entries are read in parallel, so distributed/block RAM is structurally inapplicable.

- [ ] **Step 3: Run CAM and transaction-manager verification**

```bash
source env_python && make -C val/amba clean-all
source env_python && make -C val/amba run-monitor_trans_cam-full-parallel
source env_python && make -C val/amba run-axi_monitor_trans_mgr-full-parallel
make -C formal/amba/axi_monitor_trans_mgr clean prove cover
make -C formal/amba/axi_monitor_trans_mgr_banked clean prove cover
```

Expected: PASS with all covers reached.

- [ ] **Step 4: Measure the identical feature-master row on both parts**

```bash
RUN_LABEL=cam_reset_after JOBS=2 rtl/amba/fpga/bin/full_observer_synth_sweep.sh feature_master
```

Compare against `full_before` on each part. Keep only if it improves area or gives a named timing benefit without an unacceptable area regression. Otherwise revert the RTL change and retain the new test.

- [ ] **Step 5: Record and commit the disposition**

Publish before/after absolute values and deltas, including a negative result. Commit the kept RTL or only the test/document evidence with message `perf(amba): measure reset-free full-monitor CAM payload storage`.

### Task 7: Measure reset-free reporter transaction snapshots

**Files:**
- Modify: `rtl/amba/ocelus/axi_monitor_reporter.sv`
- Modify: `projects/components/utility-ip/misc/dv/tests/fub/test_axi4_intf_observer.py`
- Modify: `docs/markdown/rtl-amba/monitor/monitor_characterization.md`
- Modify: `vault/tracking/projects/components/utility-ip/misc/task/active/TASK-007.md`

**Interfaces:**
- Preserves: reporter event timing after the first valid post-reset snapshot, FIFO priority, `event_reported`, and MonBus stability.
- Changes only: reset handling of `r_trans_table_local` plus a one-bit snapshot-valid guard.

- [ ] **Step 1: Strengthen reset/reissue against phantom stale events**

Before new post-reset traffic, assert that no completion/error/debug packet is emitted from the pre-reset transaction table. After new traffic, require exactly the model's new events. A mutation that exposes the stale snapshot on the first post-reset cycle must fail this scenario.

- [ ] **Step 2: Move the snapshot to a reset-free process**

Remove per-entry reset and the snapshot loop from the main resettable process. Capture every `trans_table` entry every cycle in a separate reset-free clocked process. Keep `monbus_valid`, event count, reported flags, and output payload resettable.

- [ ] **Step 3: Guard the first post-reset snapshot**

Add `r_snapshot_valid`, reset to 0 and set to 1 after the first capture. Gate error/timeout/completion/threshold/performance/debug event consumption until this bit is set, so stale local payload cannot emit. Do not suppress a real event after the first valid snapshot.

- [ ] **Step 4: Run reporter formal and full observer DV**

```bash
make -C formal/amba/axi_monitor_reporter clean prove cover
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub clean-all
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub run-axi4_intf_observer-full-parallel
```

Expected: all proofs/covers and all full/lite observer cells PASS.

- [ ] **Step 5: Measure and keep or revert**

Run `RUN_LABEL=reporter_reset_after JOBS=2 rtl/amba/fpga/bin/full_observer_synth_sweep.sh feature_master` on both parts and compare against the immediately preceding accepted source state, with `full_before` also shown for cumulative effect. Keep only a measured win; otherwise revert the reporter RTL and retain the strengthened test.

- [ ] **Step 6: Record and commit the disposition**

Commit the kept reporter RTL or only the test/document evidence with message `perf(amba): measure reset-free full-monitor reporter snapshots`.

### Task 8: Replace serial CAM allocation scans with bit-identical lowest-set selection

**Files:**
- Modify: `rtl/amba/ocelus/monitor_trans_cam.sv`
- Modify: `rtl/amba/ocelus/axi_monitor_trans_mgr.sv` only for its exact address-allocation mirror
- Modify: `val/amba/test_monitor_trans_cam.py`
- Create: `formal/amba/monitor_trans_cam/Makefile`
- Create: `formal/amba/monitor_trans_cam/monitor_trans_cam.sby`
- Create: `formal/amba/monitor_trans_cam/monitor_trans_cam_gold.sv`
- Create: `formal/amba/monitor_trans_cam/formal_monitor_trans_cam_equiv.sv`
- Modify: `docs/markdown/rtl-amba/monitor/monitor_characterization.md`
- Modify: `vault/tracking/projects/components/utility-ip/misc/task/active/TASK-007.md`

**Interfaces:**
- Preserves: `addr_alloc_oh`, `data_alloc_oh`, `resp_alloc_oh`, masks, phase priority `addr > data > resp`, and `w_addr_alloc_mirror_oh` exactly.
- Produces: formal combinational/sequential equivalence between the pre-rewrite CAM golden copy and the rewritten CAM.

- [ ] **Step 1: Add directed allocation boundaries and the golden equivalence harness**

Test empty masks, only the highest slot eligible, all three phases requesting, one eligible slot shared by all masks, disjoint masks, full table, and clear/reuse. Save the current CAM as `monitor_trans_cam_gold.sv`; the harness drives identical inputs and asserts all match, free, allocation, valid, ID, and payload outputs equal at every cycle.

- [ ] **Step 2: Prove the harness is sensitive before rewriting**

Run equivalence on the unchanged pair (PASS), then mutate one golden lowest-free choice or phase exclusion and require FAIL. Restore the golden copy before implementation.

- [ ] **Step 3: Implement lowest-set selection**

For each phase, form the remaining free vector and eligible mask, then select only the lowest set bit using `x & (~x + 1'b1)` (or the equivalent carry-chain idiom). Clear the selected bit before the next phase. Apply the identical lowest-set rule to the transaction manager's address mirror. Do not change admission conditions, age/rank updates, or payload writes.

- [ ] **Step 4: Run equivalence, directed stress, and transaction-manager formal**

```bash
make -C formal/amba/monitor_trans_cam clean prove
source env_python && make -C val/amba clean-all
source env_python && make -C val/amba run-monitor_trans_cam-full-parallel
source env_python && make -C val/amba run-axi_monitor_trans_mgr-full-parallel
make -C formal/amba/axi_monitor_trans_mgr clean prove cover
make -C formal/amba/axi_monitor_trans_mgr_banked clean prove cover
```

Expected: equivalence PASS, all simulation cells PASS, all proofs PASS, all covers reached.

- [ ] **Step 5: Measure and keep or revert**

Run `RUN_LABEL=cam_alloc_after JOBS=2 rtl/amba/fpga/bin/full_observer_synth_sweep.sh feature_master` on both parts. Compare area and the CAM startpoint/endpoint against the preceding accepted state. Retain only if timing improves without an unacceptable area regression or area improves at no timing cost; otherwise revert both RTL files and retain equivalence/directed tests.

- [ ] **Step 6: Record and commit the disposition**

Commit kept RTL and new equivalence collateral, or only tests/documents for a rejection, with message `perf(amba): measure carry-chain full-monitor CAM allocation`.

### Task 9: Run the final matrix, regressions, and close the record

**Files:**
- Modify: `docs/markdown/rtl-amba/monitor/monitor_characterization.md`
- Modify: `docs/markdown/rtl-amba/monitor/axi_monitor_base.md`
- Create: `projects/components/utility-ip/misc/docs/axi4_intf_observer.md`
- Modify: `vault/tracking/projects/components/utility-ip/misc/task/active/TASK-007.md`
- Move: TASK-007 to `vault/tracking/projects/components/utility-ip/misc/task/closed/TASK-007.md`
- Modify: `vault/tracking/projects/components/utility-ip/misc/task/INDEX.md`

**Interfaces:**
- Produces: one final source state with absolute full-before/full-after and cumulative retained-optimization tables.
- Produces: explicit retained/rejected dispositions, residual timing misses, final recommendation, verification counts, and reproduction commands.

- [ ] **Step 1: Run all final synthesis rows**

```bash
RUN_LABEL=full_after JOBS=4 rtl/amba/fpga/bin/full_observer_synth_sweep.sh
```

Expected: 6 full rows plus 2 lite context rows, no silently skipped rows, zero unrouted nets in accepted rows. Compare only identical profile/part pairs and include absolute values, deltas, critical paths, and any placement variation caveat.

- [ ] **Step 2: Run every affected formal harness**

Run clean prove/cover for `axi_monitor_trans_mgr`, `axi_monitor_trans_mgr_banked`, `axi_monitor_base`, `axi_monitor_filtered`, `axi_monitor_reporter`, and the four AXI4 full wrappers; run the new CAM equivalence proof. Expected: PASS with all intended covers reached and mutation-sensitive non-vacuity checks recorded.

- [ ] **Step 3: Run clean final regressions**

```bash
source env_python && make -C val/amba clean-all
source env_python && make -C val/amba run-all-full-parallel
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub clean-all
source env_python && make -C projects/components/utility-ip/misc/dv/tests/fub run-all-full-parallel
```

Expected: all cells pass. Do not claim completion with red tests. If an unrelated shared-tree integration fails, reproduce it against untouched paths, leave TASK-007 active, and report the blocker rather than hiding it.

- [ ] **Step 4: Update documentation and sweep stale comments**

Document the full public variants, passive taps, `cmd_refused`, capability behavior, synthesis commands, retained/rejected experiments, residual misses, and when full-only features justify the remaining cost. Update any comments that still describe the old reset or allocator implementation. Preserve the existing characterization document's References section and add verified prior-art citations for any newly used published technique.

- [ ] **Step 5: Close TASK-007 only after evidence is complete**

Use `git mv` to close TASK-007, set active count 0 and closed count 7 while retaining `Next ID: TASK-008`. Record final test counts, formal results, baseline/final source hashes, and the final recommendation.

- [ ] **Step 6: Commit the final record**

Commit only documentation and the old/new tracker paths with message `docs(amba,misc): report full observer FPGA optimization results`. Do not commit raw reports or generated formal flats.
