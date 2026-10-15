# mc_init_plane Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extract DRAM init from `mc_scheduler_plane` into a common `mc_init_plane` and close the LPDDR2 init gaps (CSR-backed MR1/2/3 OP values, telemetry, DV) so granite's init work translates directly to pumice.

**Architecture:** `mc_xddr2_init_sequencer` gains three LP-OP input ports + `init_state_o`; a new common macro `mc_init_plane` wraps the sequencer + `mc_xddr2_mode_register`; granite/pumice cores instantiate it and flip the scheduler plane to its already-existing external-init mode (`HAS_INIT_SEQUENCER=0, HAS_MODE_REGISTER=0`, the mode scoria already uses). Both RDLs gain `LP_MR1/2/3_OP` registers (JEDEC-default resets → bit-identical out-of-reset behavior).

**Tech Stack:** SystemVerilog (verilator via cocotb/cocotb-test), SystemRDL + PeakRDL (`bin/peakrdl_generate.py`), pytest.

**Spec:** `docs/superpowers/specs/2026-10-15-mc-init-plane-design.md`

## Global Constraints

- **No assertions in RTL.** Checkers live in testbenches (cocotb/Python) only.
- Every shell: `source env_python` from the repo root AND `export PYTHONPATH="$(pwd)/bin"`. SIM=verilator; sims never run under icarus.
- Out-of-reset behavior must be **bit-identical**: LP_OP CSR resets are 0x23/0x01/0x02 (the old localparam values); the DDR2 path is untouched.
- Commits: explicit pathspecs, `--no-verify` (broken foreign pre-commit hook), NEVER `git add -A` — other agents share this worktree (active foreign churn in dma-ip/fabric-gen; do not touch those paths).
- New registers append at the end of each addrmap — no existing register address changes.
- `init_state_o[4:0]` is the raw FSM enum encoding (S_RESET=0 … S_L_MR3=19); telemetry only, not a stable ABI.
- Existing FSM encodings (from `mc_xddr2_init_sequencer.sv`): S_RESET=0, S_DFI_INIT=1, S_PREA1=2, S_EMR3=3, S_EMR2=4, S_EMR1=5, S_MR0_DLL=6, S_PREA2=7, S_REF1=8, S_REF2=9, S_MR0=10, S_OCD_DEF=11, S_OCD_EXIT=12, S_WAIT=13, S_DONE=14, S_L_RESET=15, S_L_ZQ=16, S_L_MR1=17, S_L_MR2=18, S_L_MR3=19.

## Review Focus

- `init_restart_i` held high as a *level* — the restart is rising-edge detected; a held-high input must not re-trigger the chain every cycle. (Pinned in Task 1.)
- `memtype_i` flipped after DONE + restart — the DDR2/LPDDR2 branch is sampled at the S_DFI_INIT exit, so a restart after a memtype change must run the *other* chain cleanly. (Pinned in Task 1.)
- `dfi_init_complete_i` dropping mid-chain (PHY glitch) — the FSM must not stall or reset; it only gates the S_DFI_INIT exit. (Pinned in Task 1.)
- Training-plane ZQ/DQ requests arriving **before** `init_done` — must be silently gated (no `trn_cmd` activity). (Pinned in Task 5.)
- CSR-swept LP OP values must appear verbatim in the MRW row field as `{MA[5:0], OP[7:0]}` at the core's DFI command stream, end-to-end. (Pinned in Tasks 1 and 4.)

---

### Task 1: `mc_xddr2_init_sequencer` — LP OP ports + `init_state_o`

**Files:**
- Modify: `projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_xddr2_init_sequencer.sv`
- Create: `projects/components/mem-ctrl-ip/common-ip/dv/filelists/mc_xddr2_init_sequencer_fub.f`
- Create: `projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_xddr2_init_sequencer_tb_top.sv`
- Test: `projects/components/mem-ctrl-ip/common-ip/dv/tests/fub/test_mc_xddr2_init_sequencer.py`

**Interfaces:**
- Consumes: existing sequencer RTL (FSM at `mc_xddr2_init_sequencer.sv:170-262`, command decode at :268-386).
- Produces (Task 2 wires these): new ports `input logic [7:0] lp_mr1_op_i, lp_mr2_op_i, lp_mr3_op_i` and `output logic [4:0] init_state_o`. MRW packing stays `row = {MA[5:0], OP[7:0]}` (`mrw_row()` at :149-151).

- [ ] **Step 1: Write the failing fub test**

Model build/run idiom on `common-ip/dv/tests/macro/test_mc_store_arbiter_contract.py` (cocotb test + pytest wrapper via `cocotb_test.simulator.run`, sources via `TBClasses.shared.filelist_utils.get_sources_from_filelist`, per-test `sim_build_path`). New dir `tests/fub/`. Drive `mc_clk` only (no DFI clock at this level). Use short waits: `t_init_wait_i=4, t_dll_wait_i=4, t_mrd_wait_i=2, t_rp_wait_i=2, t_rfc_wait_i=2`; `with_timeout` on every phase (200 µs idiom). Assertions:

1. `test_ddr2_chain_order_shadows`: `memtype_i=DDR2`, `dfi_init_complete_i=1` after reset; record `(op, bank, row)` on every `init_cmd_valid_o` cycle and every `(mr_seq_we_o, index, data)`. Expected DDR2 sequence:
   `PREA, MRS(b=2,row=mr2_i), MRS(b=3,row=mr3_i), MRS(b=1,row=mr1_i), MRS(b=0,row=mr0_i|0x100), PREA, REF, REF, MRS(b=0,row=mr0_i), MRS(b=1,row=mr1_i|0x380), MRS(b=1,row=mr1_i)`; shadows exactly `(3,mr3),(2,mr2),(1,mr1),(0,mr0|0x100),(0,mr0),(1,mr1)` — the OCD-default MRS writes NO shadow. Ends with `init_done_o=1`, `init_state_o==14` (S_DONE).
2. `test_lpddr2_chain_op_sweep`: `memtype_i=LPDDR2`, `lp_mr*_op_i = 8'h5A/8'hC3/8'h3C` (deliberately ≠ defaults). Expected ops: 5×`MRS` with rows `{6'd63,8'h00}, {6'd10,8'hFF}, {6'd1,8'h5A}, {6'd2,8'hC3}, {6'd3,8'h3C}`; shadows only `(1,16'h005A),(2,16'h00C3),(3,16'h003C)`.
3. `test_restart_level_held`: after DONE, drive `init_restart_i=1` and hold it; chain re-runs exactly ONCE (count command pulses == 1 chain), then holding does not re-run again (count stable over 500 cycles).
4. `test_restart_other_memtype`: after DONE with DDR2, set `memtype_i=LPDDR2`, pulse `init_restart_i`; expect exactly the 5-command LPDDR2 chain and DONE again.
5. `test_init_complete_never`: hold `dfi_init_complete_i=0`; assert `init_cmd_valid_o` never rises, `init_state_o==1` (S_DFI_INIT), `init_done_o==0` (with_timeout-bounded).
6. `test_init_complete_glitch`: `dfi_init_complete_i=1` until the first PREA issues, then drop it to 0 for the rest of the chain; the DDR2 chain still completes in order and reaches DONE.

- [ ] **Step 2: Run test to verify it fails**

`cd /mnt/data/github/RTLDesignSherpa && source env_python && export PYTHONPATH="$(pwd)/bin" && python -m pytest projects/components/mem-ctrl-ip/common-ip/dv/tests/fub/test_mc_xddr2_init_sequencer.py -x -q`
Expected: FAIL — verilator compile error (ports `lp_mr*_op_i` / `init_state_o` don't exist yet).

- [ ] **Step 3: Implement the port change in `mc_xddr2_init_sequencer.sv`**

Add the three `lp_*_op_i` inputs; replace the three localparams in the `S_L_MR1/2/3` decode arms with the ports. Add `init_state_o` — registered assign of `r_state` in the status `ALWAYS_FF_RST` block (:391-403). No other logic moves.

- [ ] **Step 4: Run test to verify it passes**

Same pytest command. Expected: 6 passed.

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_xddr2_init_sequencer.sv \
        projects/components/mem-ctrl-ip/common-ip/dv/filelists/mc_xddr2_init_sequencer_fub.f \
        projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_xddr2_init_sequencer_tb_top.sv \
        projects/components/mem-ctrl-ip/common-ip/dv/tests/fub/test_mc_xddr2_init_sequencer.py
git commit --no-verify -m "mc init sequencer: CSR-backed LPDDR2 MR1/2/3 OP ports + init_state telemetry, directed fub test"
```

### Task 2: `mc_init_plane` macro

**Files:**
- Create: `projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_init_plane.sv`
- Create: `projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_init_plane.f`
- Create: `projects/components/mem-ctrl-ip/common-ip/dv/filelists/mc_init_plane_macro.f`
- Create: `projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_init_plane_tb_top.sv`
- Test: `projects/components/mem-ctrl-ip/common-ip/dv/tests/macro/test_mc_init_plane.py`

**Interfaces:**
- Consumes: Task 1 sequencer ports; `mc_xddr2_mode_register` (ports per its instantiation in `mc_scheduler_plane.sv:372-393`: `mr_we_i/mr_index_i/mr_data_i/mr_rank_i`, `cl_o/cwl_o/bl_o/al_o`, `mr_req_o/mr_grant_i` tied off).
- Produces (Task 3 relies on exactly these names): module `mc_init_plane` with params `NUM_RANKS=1, NUM_BANKS=8, ROW_WIDTH=14` (`BKW=$clog2(NUM_BANKS)`); ports `mc_clk, mc_rst_n, memtype_i, t_init_wait_i[15:0], t_dll_wait_i[15:0], t_mrd_wait_i[7:0], t_rp_wait_i[7:0], t_rfc_wait_i[7:0], mr0_i..mr3_i[15:0], lp_mr1_op_i..lp_mr3_op_i[7:0], init_restart_i, dfi_init_start_o, dfi_init_complete_i, init_cmd_valid_o, init_cmd_op_o (dram_op_e), init_cmd_bank_o[BKW-1:0], init_cmd_row_o[ROW_WIDTH-1:0], init_busy_o, init_done_o, init_state_o[4:0], cl_o[3:0], cwl_o[3:0], bl_o[3:0]`. Children named `u_init` / `u_mode_reg` (core-level debug paths stay greppable).

- [ ] **Step 1: Write the failing macro test**

Same idiom as Task 1. Assertions:
1. `test_ddr2_chain_at_plane_boundary`: default MRs (`mr0_i=16'h0433`, others 0); record the command stream and shadows; assert the Task-1 §1 sequence verbatim; `cl_o==4'd3`, `bl_o==4'd8` after DONE (decode of MR0=0x433: CL3, BL8).
2. `test_lpddr2_chain_at_plane_boundary`: `memtype_i=LPDDR2`; assert the 5-MRW sequence with default OP ports (0x23/0x01/0x02); after DONE `bl_o==4'd8` (MR1 BL8).
3. `test_state_telemetry`: `init_state_o` passes through 0→1 early, sits at 13 (S_WAIT) between commands, lands 14.

- [ ] **Step 2: Run test to verify it fails**

`python -m pytest projects/components/mem-ctrl-ip/common-ip/dv/tests/macro/test_mc_init_plane.py -x -q`
Expected: FAIL — cannot find `mc_init_plane` (filelist/toplevel missing).

- [ ] **Step 3: Implement `mc_init_plane`**

New macro: instantiate the sequencer (`u_init`) and mode register (`u_mode_reg`, `NUM_RANKS` param, `mr_rank_i='0`, request ports tied off as in `mc_scheduler_plane.sv:381-386`). Pass `mr_seq_*` straight through; expose `init_busy_o`, `init_done_o`, `init_state_o`, `cl/cwl/bl_o`. Filelist `macro/mc_init_plane.f` mirrors `mc_scheduler_plane.f`'s format (pkg + the two fub filelists); the DV filelist mirrors `mc_store_arbiter_macro.f` (closure: `mc_common_pkg.sv` → fubs → tb_top); `dv/rtl/mc_init_plane_tb_top.sv` is a thin port-for-port wrapper.

- [ ] **Step 4: Run test to verify it passes**

Same pytest command. Expected: 3 passed.

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_init_plane.sv \
        projects/components/mem-ctrl-ip/common-ip/rtl/filelists/macro/mc_init_plane.f \
        projects/components/mem-ctrl-ip/common-ip/dv/filelists/mc_init_plane_macro.f \
        projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_init_plane_tb_top.sv \
        projects/components/mem-ctrl-ip/common-ip/dv/tests/macro/test_mc_init_plane.py
git commit --no-verify -m "mc_init_plane: common init plane (sequencer + mode-register shadow) with macro test"
```

### Task 3: Rewire granite + pumice cores to the init plane

**Files:**
- Modify: `projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_core.sv`
- Modify: `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/top/pumice_core.sv`
- Modify: `projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/granite_all.f`
- Modify: `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/filelists/pumice_all.f`

**Interfaces:**
- Consumes: Task 2 `mc_init_plane` (exact port names above).
- Produces: cores with `u_init_plane`, new core input ports `lp_mr1_op_i/lp_mr2_op_i/lp_mr3_op_i[7:0]`, scheduler plane instance switched to `.HAS_INIT_SEQUENCER(1'b0), .HAS_MODE_REGISTER(1'b0)` with its external init port fed from `u_init_plane`.

- [ ] **Step 1: Confirm the pre-change regression baseline**

`source env_python && export PYTHONPATH="$(pwd)/bin"`
`python -m pytest projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/dv/tests/top/test_granite_core.py projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/dv/tests/top/test_granite_top_geared.py -q`
Expected: PASS (baseline). Record time; these are the nets that must stay green.

- [ ] **Step 2: Rewire `granite_core.sv`**

Add the three LP OP input ports next to `mr3_i` (:105). Instantiate `u_init_plane` (`.NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH)`); wire its `init_cmd_*` to the scheduler plane's external init port — replace the current ties at :612-616 (`.init_done_i(1'b1)` → `w_init_done`, etc.); route `w_init_start/w_init_complete` between `u_init_plane` and `u_dfi_plane` instead of the scheduler plane (:605, :790); connect `cl_o/cwl_o/bl_o` core outputs to the init plane; add `-f .../macro/mc_init_plane.f` to `granite_all.f` after the scheduler-plane line (:20). LP OP ports: for this task tie them to the JEDEC defaults at the core boundary via localparams (`8'h23/8'h01/8'h02`) — Task 4 replaces the ties with real wiring.

- [ ] **Step 3: Rewire `pumice_core.sv`**

Same changes (scheduler instantiation at :601; external-init ties and DFI init nets near :667/:866; `pumice_all.f` after :36).

- [ ] **Step 4: Run the regression nets**

Granite: `test_granite_core.py`, `test_granite_top_geared.py`, `test_granite_bankfifo_debug.py`. Pumice: `dv/tests/top/` suite (at minimum `test_pumice_core.py`, `test_pumice_top.py -k lpddr2 or smoke`, `test_pumice_top_csr.py`). Plus the two new common tests (guard against integration surprises). Expected: all PASS.

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_core.sv \
        projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/top/pumice_core.sv \
        projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/filelists/granite_all.f \
        projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/filelists/pumice_all.f
git commit --no-verify -m "granite/pumice: compose u_init_plane; scheduler plane on external-init mode"
```

### Task 4: `LP_MR1/2/3_OP` CSRs in both products

**Files:**
- Modify: `projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/regs/granite_csr.rdl`
- Modify: `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_csr.rdl`
- Regenerate: `product-ip/granite-ddr2-lpddr2/regs/generated/**`, `research-ip/pumice-ddr2-lpddr2/regs/generated/**`
- Modify: `projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_top_geared.sv`
- Modify: `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/top/pumice_top.sv`
- Test: `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/dv/tests/top/test_pumice_top.py` (add a test cell)

**Interfaces:**
- Consumes: Task 3 core ports `lp_mr1_op_i/lp_mr2_op_i/lp_mr3_op_i`.
- Produces: hwif paths `hwif_out.LP_MR1_OP.value[7:0]` (reset 0x23), `hwif_out.LP_MR2_OP.value` (0x01), `hwif_out.LP_MR3_OP.value` (0x02) in BOTH tops; regenerated regblock RTL, regmap.py, and markdown docs committed.

- [ ] **Step 1: Add the test cell (failing)**

In `test_pumice_top.py`, add `test_lp_mr_op_csr_to_mrw_stream`: program `LP_MR1_OP=0x5A, LP_MR2_OP=0xC3, LP_MR3_OP=0x3C` over the CSR bus, force init (memtype=LPDDR2), capture the MRW commands reaching the DFI command formatter (same hook the existing `smoke_lpddr2` cell uses to verify MR63/10/1/2/3 at :586-599), and assert rows `{6'd1,8'h5A},{6'd2,8'hC3},{6'd3,8'h3C}`. Run: `python -m pytest .../test_pumice_top.py -k lp_mr_op -q` → Expected: FAIL (registers don't exist).

- [ ] **Step 2: Add registers to both RDLs**

Append three registers at the end of each addrmap, each `reg { field { sw=rw; hw=r; reset=...; } value[7:0]; }` following the existing `MR0`-style entries (granite `granite_csr.rdl` ~:151; pumice `pumice_csr.rdl` analogous). Names exactly `LP_MR1_OP`, `LP_MR2_OP`, `LP_MR3_OP`.

- [ ] **Step 3: Regenerate both CSR blocks**

For each product, regenerate with the same invocation that produced the current artifacts: `python bin/peakrdl_generate.py <rdl> -o <product regs/generated dir> --cpuif apb3` (match the cpuif/flags the existing generated headers document; granite output dir `product-ip/granite-ddr2-lpddr2/regs/generated`, pumice `research-ip/pumice-ddr2-lpddr2/regs/generated`). Then `python bin/check_rdl_regen.py --staged` → clean. Verify by diff that only appended offsets/content changed (no existing-address churn).

- [ ] **Step 4: Wire the tops**

`granite_top_geared.sv` next to the `MR0.VAL` wiring (:428-431): `.lp_mr1_op_i(hwif_out.LP_MR1_OP.value)`, etc. — replacing the Task-3 core-boundary default ties is NOT needed if Task 3 wired core inputs to `hwif`… wait: Task 3 added core ports tied to localparam defaults at the core level; the tops must now drive those core ports from hwif. Do this by connecting the core port to the hwif value in the top (the core's internal default tie is only a fallback; simplest: in Task 3 leave the core input ports as ports and have each top drive them — pick ONE place. Decision: core keeps pure ports; tops drive them. In Task 3 the cores therefore connect `.lp_mr1_op_i(lp_mr1_op_i)` port-to-port; the JEDEC-default constants live in the TOPS' tie/CSR wiring. Adjust Task 3 Step 2 accordingly if not already done.) Same in `pumice_top.sv`.

- [ ] **Step 5: Run tests**

`python -m pytest .../test_pumice_top.py -k lp_mr_op -q` → PASS. Then granite CSR path: `test_granite_top_geared.py` (full) → PASS. Re-run `check_rdl_regen.py --staged` → clean.

- [ ] **Step 6: Commit**

```bash
git add projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/regs \
        projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/regs \
        projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_csr.rdl \
        projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_top_geared.sv \
        projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/top/pumice_top.sv \
        projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/dv/tests/top/test_pumice_top.py
git commit --no-verify -m "granite/pumice CSR: LP_MR1/2/3_OP registers (JEDEC defaults), wired to init plane"
```

### Task 5: Training-plane DV (runtime ZQ + DQ cal)

**Files:**
- Create: `projects/components/mem-ctrl-ip/common-ip/dv/filelists/mc_training_plane_macro.f`
- Create: `projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_training_plane_tb_top.sv`
- Test: `projects/components/mem-ctrl-ip/common-ip/dv/tests/macro/test_mc_training_plane.py`

**Interfaces:**
- Consumes: `mc_training_plane` as-is (`common-ip/rtl/macro/mc_training_plane.sv`; ports at :56-68 per the exploration report — `trn_cmd_*` maintenance channel, `cal_expect_o/cal_data_i/cal_valid_i` sideband, `dfi_clk/dfi_rstn`).
- Produces: nothing later tasks consume; closes the TASK-042/G-16 verification gap.

- [ ] **Step 1: Write the failing macro test**

Two clocks (`mc_clk`, `dfi_clk` — unrelated frequencies fine, e.g. 100/75 MHz). Assertions:
1. `test_zqcs_interval`: `memtype_i=LPDDR2, zq_en_i=1, zq_interval_i` tiny (≈20 cycles), `t_zqcs_i=2, t_zqcl_i` large; after `init_done_i=1`, observe `trn_cmd_req_o` with ZQCS op + grant response (`trn_cmd_grant_i` driven by TB after a few cycles); `zq_busy_o` rises around it; repeat ≥2 intervals.
2. `test_zqcl_after_long_interval`: `zq_interval_i` spanning multiple ZQCS periods → ZQCL op requested; `zqcs_total_o` counts.
3. `test_zq_overdue_and_defer`: `zq_defer_en_i=1` with continuous re-demand (drive grant only late) → `zq_overdue_o` rises and overdue behavior follows `zq_overdue_max_i` (mirror the block's documented policy in `mc_lpddr2_zq_ctrl.sv` header).
4. `test_dq_cal_mrr32_40`: `cal_start_i=1` pulse; expect MRR commands on `trn_cmd_*` (grant them); when `cal_expect_o` rises, drive `cal_data_i` with a known pattern + `cal_valid_i=1` for one `dfi_clk`; expect `cal_done_o=1`, `cal_err_o=0`, `mrr32_data_o`/`mrr40_data_o` holding the captured pattern.
5. `test_gated_before_init_done` + `test_gated_ddr2`: request ZQ/cal with `init_done_i=0` and (separately) `memtype_i=DDR2`; assert `trn_cmd_req_o` never rises and no cal activity.

- [ ] **Step 2: Run test to verify it fails**

Expected: FAIL — DV filelist/tb_top missing (compile/toplevel error). This task changes NO RTL; if any assertion fails against the existing RTL, stop and file the finding rather than patching RTL silently.

- [ ] **Step 3: Add the DV filelist + tb_top**

Mirror `mc_store_arbiter_macro.f` closure: `mc_common_pkg.sv` → `mc_lpddr2_zq_ctrl.sv`, `mc_lpddr2_dq_cal.sv`, `mc_training_shell.sv` (if separate; check `mc_training_plane.f`) → tb_top wrapper with both clock domains.

- [ ] **Step 4: Run test to verify it passes**

Expected: 5 passed.

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/common-ip/dv/filelists/mc_training_plane_macro.f \
        projects/components/mem-ctrl-ip/common-ip/dv/rtl/mc_training_plane_tb_top.sv \
        projects/components/mem-ctrl-ip/common-ip/dv/tests/macro/test_mc_training_plane.py
git commit --no-verify -m "mc_training_plane: runtime ZQ + DQ cal macro DV (TASK-042/G-16 verification)"
```

### Task 6: Docs + full regression + lint

**Files:**
- Modify: `projects/components/mem-ctrl-ip/common-ip/docs/common_has/ch02_architecture/01_plane_stack.md`
- Create: `projects/components/mem-ctrl-ip/common-ip/docs/common_mas/chXX_init_plane/01_mc_init_plane.md` (chapter number follows existing `common_mas` layout)
- Modify: `projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/config/product_config.md`
- Modify: `projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/docs/pumice_has/ch02_overview/06_what_moved_to_common.md` (+ init-sequences chapter for the LP MR CSRs)
- Modify: `vault/Tasks/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/task/open/TASK-042.md` (status note only; do not close)

**Interfaces:**
- Consumes: everything above.

- [ ] **Step 1: Docs**

Update the plane-stack doc (init plane between scheduler and DFI in the stack list + one-paragraph responsibility: JEDEC sequencing, MR shadow, PHY handshake, telemetry). New common-MAS chapter: ports table, child fubs, both JEDEC sequences, `LP_MR*` register surface, `init_state_o` encoding table. `product_config.md`: stack list gains `mc_init_plane`. Pumice HAS what-moved: init plane + LP MR CSRs; note the standing "init-timing CSR values are MC-frequency-dependent" caution in the init-sequences chapter. TASK-042: status note that runtime-ZQ RTL is common and now macro-verified; board exercise remains open.

- [ ] **Step 2: GTKW for the init plane**

Check `common-ip/dv/tools/gtkw_curated_fubs.py` and the granite `dv/tests/GTKW/` mechanism; add a `u_init_plane` gtkw following the existing pattern (skip with a note if the tooling is product-tree-only).

- [ ] **Step 3: Full regression sweep**

From repo root, env sourced:
`python -m pytest projects/components/mem-ctrl-ip/common-ip/dv/tests -q` (all new + contract)
`python -m pytest projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/dv/tests/top -q`
`python -m pytest projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/dv/tests/top -q`
`python -m pytest projects/components/mem-ctrl-ip/common-ip/dv/tests/macro/test_mc_store_arbiter_contract.py -q`
`python -m pytest projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/test_granite_char_uart.py -q` (uart smoke; board-independent RTL-sim gate)
Harness lint: `make -C projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/targets/granite lint` (use `set -o pipefail`; SIM=verilator)
Expected: all green.

- [ ] **Step 4: Commit**

```bash
git add projects/components/mem-ctrl-ip/common-ip/docs \
        projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/config/product_config.md \
        projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/docs/pumice_has \
        vault/Tasks/projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/task/open/TASK-042.md
git commit --no-verify -m "docs: mc_init_plane plane-stack/MAS/HAS updates + TASK-042 status note"
```

## Self-Review Notes

- Spec §1 (sequencer ports) → Task 1. §2 (plane) → Task 2. §3 (scheduler plane, no RTL removal; scoria/andesite untouched) → Task 3 only flips params in the two cores. §4 (cores) → Task 3. §5 (CSR) → Task 4. §6 (DV) → Tasks 1/2/5. §7 (regression) → Task 6 + per-task gates. §8 (docs) → Task 6.
- Type consistency: `lp_mr1_op_i/lp_mr2_op_i/lp_mr3_op_i` + `init_state_o[4:0]` used identically in Tasks 1-4; hwif paths `LP_MR{1,2,3}_OP.value` identical in Tasks 4 and 6 docs.
- Known tension resolved: Task 3 originally tied LP OP core inputs to defaults; corrected inline so cores keep pure ports and the tops own the default/CSR wiring (single source of truth).
- Board re-run: explicitly out of scope (spec non-goal; bit-identical defaults).
