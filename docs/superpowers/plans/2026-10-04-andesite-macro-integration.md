# Andesite Macro Integration + Layer Births Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Finish andesite DDR4/LPDDR4 items 1–3 from the P3 close-out: the macro integration pass (P1 init/mode-register rewiring, cmd_path landing, parked-suite re-derivation, training layer), the nine deferred review minors M-1…M-9, and the birth of `andesite_dfi_layer` + `andesite_axi4_layer` capped by `andesite_core` and a top-level suite.

**Architecture:** The scheduler macro (`andesite_scheduler_layer`) is rewired to the P1 `init_sequencer`/`mode_register` so it fully elaborates; the command word widens by `bg[1:0]`; a new `andesite_dfi_cmd_path` (P1 single-shot formatter in a scoria-style registered pipeline) carries the DFI 4.0 command surface; training FUBs move into a new `andesite_training_layer` owning the DFI training pins and a one-active mux; then the DFI layer, AXI4 layer (rename-carry of scoria with a logic-parity gate), and `andesite_core` assemble the full stack. Single-rank (`NUM_RANKS=1`) design point throughout.

**Tech Stack:** SystemVerilog (Verilator lint/cocotb sim via the repo make flow), Python DV (pytest + cocotb), PeakRDL-era CSR images (driven, not decoded), the family carry-gate scripts.

**Spec:** `.superpowers/sdd/2026-10-04-andesite-rtl-bootstrap-p3/progress.md` (the P3 ledger — its "Remaining before P3 truly closes" + "Owner ruling (training home)" + "Final: minor (deferred)" sections are the authoritative punch list this plan executes), plus `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/ch02_blocks/10_dfi_datapath.md`, `09_training.md`, `ch03_interfaces/01_dfi40_pins.md`, and the andesite HAS ch03/04.

## Global Constraints

- Test environment, verbatim: `export PATH="$(git rev-parse --show-toplevel)/venv/bin:$PATH"` and `export PYTHONPATH=<repo>/bin` (repo = `/mnt/data/github/RTLDesignSherpa`). Run python/heredocs from the repo root only (the cwd trap).
- Before trusting any pytest-vs-direct-run disagreement: `rm -rf <tests-dir>/__pycache__` (pytest's rewrite cache serves stale code to the cocotb sim).
- cocotb reads of comb-driven outputs need `Timer(1ns)`. Count hex digits programmatically (`'A5'*16`), never by hand. Reset-macro bodies cannot hold comma-separated case labels.
- Shared-trunk discipline (other agents commit on `main` constantly): immediately before every commit run `git status --porcelain | grep '^[AM]'`; stage path-scoped only (`git add <exact paths>`); never `git status --porcelain --staged` (old git); never rewrite landed commits; if a hook sweep or `fatal: cannot lock ref 'HEAD'` hits, wait-and-retry. Do not commit the T9-parked suite until Task 2 un-parks it.
- Naming: macro-tier modules are `*_layer` (MC-001, closed); FUB training interfaces stay `*_ifc`. New DV tbclasses keep the established class names (`AndesiteMemCmdSchedulerTB` does NOT rename).
- The doc-instantiation gate + task-ID checker + markdown-link checker + filelist-contract checker run in pre-commit hooks; MAS port tables must match landed RTL at each task's commit (floor 0). Kmap CITES anchor comment blocks in `addr_mapper`/`mode_register` must not be shifted (drift gate).
- Carry gates: `dv/bin/check_carry_diff.sh <andesite.sv> ../scoria-ddr3-lpddr3/rtl/<path> <exception_regex> additive` — scoria's macro source is `rtl/macro/scoria_scheduler_layer.sv`.
- Single-rank design point: `NUM_RANKS=1`, CS lanes qualified for one rank; multi-rank must be *documented* as out of scope, not silently wrong.
- P1 `andesite_init_sequencer` accepts **only** `MEMTYPE_DDR4` (`3'b010`); any other memtype latches `init_err`. The P1 init FSM has **no** DFI init handshake and no `tRFC`/`tXPR` inputs.
- `bin/filelist_registry.py --check` must PASS at every task boundary.

## Review Focus

The five input classes the spec implies but no single task's obvious tests exercise, most likely first:

1. **Init-command backpressure (cmd_ack pacing):** if the scheduler output path stalls (maintenance demand, FIFO full), P1 `cmd_req` must hold until `cmd_ack` without dropping or double-issuing an MRS/ZQCL; withheld ack must eventually latch `init_err` (watchdog), not hang. *Pinned in Task 1's verification and Task 2's suite.*
2. **Wrong memtype at the macro:** `memtype_i != DDR4` (e.g. an LPDDR4 bring-up bring-before-init case) must surface `init_err_o` and never `init_done`. *Pinned in Task 1 (port export) and Task 2 (TB drives DDR4; a wrong-memtype case asserts init_err).*
3. **Simultaneous training enables:** `wrlvl_en` (MR1) high while firmware pulses `rdlvl_en_i` or `ca_train_en_i` must not interleave the shared DFI training pins — one training owns the pins until done. *Pinned in Task 4's mux tests.*
4. **Bank-group loss between mapper and pins:** `addr_mapper.bg_o` must survive scheduler admission → packed word → CDC → formatter so a golden ACT vector shows `dfi_bg` — the L/S delta's whole point. *Pinned in Task 3's golden-vector test and Task 8's roundtrip.*
5. **Init ZQCL actually reaching the DRAM command stream:** P1 raises `zq_cal_start` (a pulse), not a grant-style request; if it is dropped, init completes with no ZQCL and only the macro suite can catch it. *Pinned in Task 2's init-order golden (ZQCL present between last MRS and init_done).*

---

## File structure

- Modify: `rtl/macro/andesite_scheduler_layer.sv` — P1 rewiring (T1), widened output word + `bg` (T3), training port surgery (T4).
- Modify: `rtl/fub/andesite_{rd,wr}_intake.sv`, `rtl/fub/andesite_wrlvl_ifc.sv`, `rtl/fub/andesite_rdlvl_ifc.sv`, `rtl/fub/andesite_ca_train_ifc.sv`, `rtl/fub/andesite_refresh_ctrl` suite, MAS/HAS pages — minors (T5), training doc reconcile (T4).
- Create: `rtl/fub/andesite_dfi_cmd_path.sv` + `rtl/filelists/fub/andesite_dfi_cmd_path.f` + `dv/tests/fub/test_andesite_dfi_cmd_path.py` (+ tbclass if needed) (T3).
- Create: `rtl/macro/andesite_training_layer.sv` + filelist + `dv/tests/macro/test_andesite_training_layer.py` (T4).
- Create: `rtl/macro/andesite_dfi_layer.sv` + filelist (T6).
- Create: `rtl/macro/andesite_axi4_layer.sv` + filelist + `dv/tests/macro/test_andesite_scoria_axi4_logic_parity.py` (rename-map parity gate) (T7).
- Create: `rtl/top/andesite_core.sv` + `rtl/filelists/top/andesite_core.f` + `dv/tests/top/test_andesite_core.py` + `dv/tbclasses/andesite_core_tb.py` (carried from scoria) (T8).
- Modify: `rtl/filelists/andesite_all.f` (+ macro/top tier lists as modules land); `rtl/lint_reports/verilator/*` regenerate via `make verilator-<glob>`.
- Un-park: `dv/tests/macro/test_andesite_scheduler_layer.py`, `dv/tbclasses/andesite_scheduler_layer_tb.py` — become tracked in T2.

---

### Task 0: Ledger, vault task, plan commit

**Files:**
- Create: `.superpowers/sdd/2026-10-04-andesite-macro-integration/progress.md` (gitignored scratch, the P3 pattern — inherits the P3 ledger's rulings; per-task entries land here as Tasks 1–9 execute)
- Create: `vault/Tasks/andesite-ddr4-lpddr4/task/open/TASK-016.md` (next ID per `bin/check_task_ids.py --next andesite-ddr4-lpddr4/task` — the checker burns any numeric appearing repo-wide, incl. pumice's TASK-013/014/015 tokens and an andesite RTL comment; TASK-016 is the first clean numeric. Move `open → active` when Task 1 starts, `→ closed` at Task 9)
- Commit: this plan file

- [ ] **Step 1:** Create the ledger with a header naming this plan + the P3 ledger as its spec, and the standing gotchas (env exports, pycache purge, trunk sweep checks, carry-gate paths).
- [ ] **Step 2:** File TASK-011 ("macro integration + training/dfi/axi4 layer births") per the lane's TASK-000 filing recipe (filename = H1, bump the INDEX Next ID + open count).
- [ ] **Step 3:** `git status --porcelain | grep '^[AM]'` sweep check; path-scoped `git add` of the plan + vault files; commit `docs: andesite macro-integration plan + TASK-011`.

---

### Task 1: Rewire `u_init`/`u_mode_reg` to the P1 blocks

**Files:**
- Modify: `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_scheduler_layer.sv` (u_init ~294–343, u_mode_reg ~348–374, output-word pack ~773–778 untouched here)
- Modify: `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/ch02_blocks/05_scheduler.md` (port table), `03_mode_register.md` if it names macro shadow outputs
- Test: `make -C projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl verilator-scheduler` (the failing-then-passing gate); regression `make -C .../dv/tests/fub run-andesite_init_sequencer-func` + `run-andesite_mode_register-func`

**Interfaces:**
- Consumes: P1 `andesite_init_sequencer` ports (exact names): `clk, reset_n, csr_init_trigger, csr_memtype[2:0], csr_geardown_en, csr_parity_en, tinit1_csr, tinit3_csr, tinit4_csr, tdllk_csr, tzqinit_csr, tmrd_csr, tmod_csr, csr_mr0_image..csr_mr6_image[15:0], cmd_ack, parity_alert_i, recovery_interval_i[15:0], csr_telem_clear_i, retract_ack_i` → outputs `mr_image_out[15:0], mr_load, reset_n_out, cke_out, cmd_req, cmd_op(dram_op_e), cmd_bank[2:0], cmd_addr[17:0], zq_cal_start, gear_down_entry, parity_enable_out, init_done, init_err, ca_train_start, retract_req_o, obs_recovery_state_o[1:0], obs_alerts_seen_o[15:0], obs_cmds_dropped_o[15:0], obs_cmds_resent_o[15:0]`.
- Consumes: P1 `andesite_mode_register` ports: `clk, rst_n, memtype_i, rank_i, wr_en_i, wr_addr_i[5:0], wr_data_i[15:0], rd_en_i, rd_addr_i[5:0]` → outputs `rd_data_o[15:0], mr_sel_o[5:0], mr_data_o[15:0], mpr_page_o[1:0], fgr_factor_o[1:0], rtt_nom_o[2:0], rtt_wr_o[2:0], rtt_park_o[2:0], rd_dbi_en_o, wr_dbi_en_o, ca_parity_lat_o[1:0], wrlvl_en_o, lpddr4_odt_o[2:0]`.
- Produces (macro boundary changes): **remove** `dfi_init_start_o`, `dfi_init_complete_i`, `cl_o`, `cwl_o`, `bl_o`; **add** `init_err_o`, `rtt_nom_o[2:0]`, `rtt_wr_o[2:0]`, `rtt_park_o[2:0]`, `rd_dbi_en_o`, `wr_dbi_en_o`, `mpr_page_o[1:0]`, `fgr_factor_o[1:0]`, `ca_parity_lat_o[1:0]`, `lpddr4_odt_o[2:0]`. Internal nets `init_cmd_valid/init_cmd_op/init_cmd_bank/init_cmd_row` keep their names and keep feeding `u_arbiter` (macro 684–687); `init_done`, `wrlvl_en_o` unchanged. Later tasks rely on: `zq_cal_start` net feeding u_zq (this task), `parity_enable_out`/`mpr_page_o`/`fgr_factor_o` exported, and the macro presenting zero PINNOTFOUND.

- [ ] **Step 1: Red gate — run the macro lint and confirm the 49 PINNOTFOUND are the only errors**

Run: `make -C projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl verilator-scheduler 2>&1 | tail -3`
Expected: FAIL, `%Error-PINNOTFOUND` at u_init/u_mode_reg only (49 errors; ignore MODDUP/PINMISSING warnings — pre-existing, ruled).

- [ ] **Step 2: Rewire `u_init` to P1 (exact map)**

In `andesite_scheduler_layer.sv`, replace the u_init port map per this table (carried pin → P1 pin):

| P1 pin | Connect to |
|---|---|
| `clk` / `reset_n` | `aclk` / `aresetn` |
| `csr_memtype` | `3'(memtype_i)` |
| `csr_init_trigger` | `init_restart_i` |
| `csr_geardown_en` | `1'b0` |
| `csr_parity_en` | `1'b0` |
| `parity_alert_i`, `recovery_interval_i`, `csr_telem_clear_i`, `retract_ack_i` | keep `1'b0` / `16'd0` ties (TASK-006 wiring stays parked per T7 ruling) |
| `tinit1_csr` | `t_init_wait_i` |
| `tinit3_csr` | `t_rp_wait_i` (RESET# release→CKE; comment the semantic rename) |
| `tinit4_csr` | `t_mrd_wait_i` (CKE→first-MRS; comment) |
| `tdllk_csr` | `t_dll_wait_i` |
| `tzqinit_csr` | `t_zqinit_wait_i` |
| `tmrd_csr` | `t_mrd_wait_i` is already used for tinit4 — **conflict** → add a new macro input `t_mrd_wait_i` exists today; P1 needs both `tinit4_csr` and `tmrd_csr`. Wire `tinit4_csr` to a **new macro input `t_cke_wait_i[15:0]`** and `tmrd_csr` to existing `t_mrd_wait_i`. Add `t_cke_wait_i` to the macro port list + MAS 05 table. |
| `tmod_csr` | **new macro input `t_mod_wait_i[15:0]`** (MAS 05 table) |
| `csr_mr0_image..csr_mr3_image` | existing `mr0_i..mr3_i` |
| `csr_mr4_image..csr_mr6_image` | **new macro inputs `mr4_i, mr5_i, mr6_i[15:0]`** (DDR4 needs MR4/MR5/MR6 in the init order) |
| `cmd_ack` | `w_init_cmd_ack` — new net, driven in Step 4 |
| `reset_n_out` | `dram_reset_n_o` |
| `mr_load` / `mr_image_out` | `mr_seq_we` / `mr_seq_data` (existing nets into u_mode_reg) |
| `cmd_req` / `cmd_op` / `cmd_bank` / `cmd_addr[ROW_WIDTH-1:0]` | `init_cmd_valid` / `init_cmd_op` / `init_cmd_bank` / `init_cmd_row` (existing nets; low bits of `cmd_addr`, width-slice explicitly) |
| `zq_cal_start` | `w_init_zq_start` new net (Step 5) |
| `gear_down_entry`, `ca_train_start`, `parity_enable_out`, `init_err` | `gear_down_entry_o`, `ca_train_start_o` new macro outputs; `parity_enable_out` → new macro output `parity_enable_o`; `init_err` → `init_err_o` |
| `retract_req_o`, `obs_*` | open |

Delete the carried connections `t_rfc_wait_i`, `t_xpr_wait_i`, `dfi_init_start_o`, `dfi_init_complete_i`, `mr_seq_index` and their now-dead macro ports (`dfi_init_start_o`, `dfi_init_complete_i`, `t_rfc_wait_i`, `t_xpr_wait_i` **stay as macro inputs** if other consumers… — they have none: remove `dfi_init_start_o`/`dfi_init_complete_i` ports entirely; keep `t_rfc_wait_i` (refresh uses tRFC at runtime — verify: it is a scheduler runtime input consumed by refresh_ctrl, NOT only init; check before deleting; expected: **keep**).

- [ ] **Step 3: Rewire `u_mode_reg` to P1 (exact map)**

| P1 pin | Connect to |
|---|---|
| `clk`/`rst_n` | `aclk`/`aresetn` |
| `memtype_i` | `memtype_i` |
| `rank_i` | `'0` |
| `wr_en_i`/`wr_data_i` | `mr_seq_we`/`mr_seq_data` |
| `wr_addr_i` | `{3'b000, init_cmd_bank}` (MR index arrives on cmd_bank; the init FSM writes MRs in MR_ORDER) |
| `rd_en_i`/`rd_addr_i` | `'0` |
| `wrlvl_en_o` | existing `wrlvl_en_o` net (unchanged) |
| `rtt_nom_o/rtt_wr_o/rtt_park_o/rd_dbi_en_o/wr_dbi_en_o/mpr_page_o/fgr_factor_o/ca_parity_lat_o/lpddr4_odt_o` | new macro outputs of the same names |
| Delete | `cl_o`, `cwl_o`, `bl_o` macro outputs + `mr_seq_index` net; drop `al_o/drv_strength_o/odt_o/wr_o` (already unconnected). |

- [ ] **Step 4: Drive `cmd_ack` honestly**

`cmd_ack` must pulse exactly when an init-sourced command is accepted at the output boundary. Find the net where `init_cmd_valid`-sourced commands win arbitration and are pushed to the output command FIFO (the carried arbiter already multiplexes `init_cmd_*` — locate its grant/fire pulse for the init source; if the carried design merges init into the arbiter candidate list, use that source's fire). `assign w_init_cmd_ack = <init-source fire pulse>`; add a 1-line comment naming the net. If (and only if) no such per-source pulse exists, combine the output-FIFO push with an init-source qualifier — do NOT tie `cmd_ack = cmd_req` at the macro (that would lie about acceptance; the TB-pattern tie exists only for standalone init tests).

- [ ] **Step 5: ZQCL pulse into u_zq**

`zq_cal_start` is a one-cycle pulse at the end of init (after tMOD). Wire `w_init_zq_start` into the existing zq_ctrl demand path so the init ZQCL is issued on the command stream like any ZQCL (check how scoria's macro wired `zqcl_req_o`/`zqcl_grant_i` to `u_zq` in `../scoria-ddr3-lpddr3/rtl/macro/scoria_scheduler_layer.sv` and mirror the shape with the P1 pulse; grant feedback is not needed — pulse starts a demand the zq_ctrl FSM owns).

- [ ] **Step 6: Green gate — macro lint-as-top clean**

Run: `make -C projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl verilator-scheduler 2>&1 | tail -3`
Expected: PASS, zero errors (the flattened `lint_reports/verilator/andesite_scheduler_layer.f` regenerates; warnings may remain).

- [ ] **Step 7: Regression — P1 suites + consumers of the changed pin names**

Run: `rm -rf .../dv/tests/fub/__pycache__` then `make -C .../dv/tests/fub run-andesite_init_sequencer-func` and `run-andesite_mode_register-func` and `run-andesite_cmd_arbiter-func` and `run-andesite_refresh_ctrl-func` and `run-andesite_zq_ctrl-func`
Expected: all green (init/mode suites unchanged-green; arbiter/refresh/zq prove the consumer paths the port-consumers gate watches).

- [ ] **Step 8: Reconcile MAS tables to the new macro ports**

`05_scheduler.md`: port table gains `t_cke_wait_i`, `t_mod_wait_i`, `mr4_i..mr6_i`, `init_err_o`, `parity_enable_o`, `gear_down_entry_o`, `ca_train_start_o`, `rtt_*_o`, `*_dbi_en_o`, `mpr_page_o`, `fgr_factor_o`, `ca_parity_lat_o`, `lpddr4_odt_o`; loses `dfi_init_start_o`, `dfi_init_complete_i`, `cl_o`, `cwl_o`, `bl_o` (kmap-pinned fences untouched). `03_mode_register.md`: add a one-line note that the macro shadow outputs now follow the P1 policy-output set.

- [ ] **Step 9: Commit**

```bash
git status --porcelain | grep '^[AM]'   # sweep check
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_scheduler_layer.sv projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/ch02_blocks/
git commit -m "feat(andesite): macro init/mode_register rewired to the P1 blocks"
```

---

### Task 2: Re-derive the parked macro suite against the P1 sequence; un-park

**Files:**
- Modify: `dv/tbclasses/andesite_scheduler_layer_tb.py` (untracked today)
- Modify: `dv/tests/macro/test_andesite_scheduler_layer.py` (untracked today)
- Modify: `dv/tests/macro/conftest.py` / `Makefile` only if they gate tracked-vs-untracked (check first; likely no change)

**Interfaces:**
- Consumes: Task 1's macro (DDR4-only init, no `dfi_init_*` handshake, `cl/cwl/bl` gone, policy outputs present, init order per P1: RESET#(tinit1) → RESET# release → tinit3 → CKE → tinit4 → MRS in order **MR3, MR6, MR5, MR4, MR2, MR1, MR0** (one per tMRD) → tMOD → ZQCL → max(tdllk,tzqinit) → `init_done`; P1 convention `cmd_addr == 16'h0010 + cmd_bank` per MRS is a TB golden convention from the init TB — reuse the init TB's (`dv/tb/andesite_init_tb.sv:149,175`) addressing/ack idioms).
- Produces: the first TRACKED composed-suite for the renamed macro; later tasks must keep it green.

- [ ] **Step 1: Red — run the parked suite against the Task-1 macro and watch it fail**

Run: `TEST_TYPE=init_sequence_in_jedec_order make -C .../dv/tests/macro <equivalent direct pytest of test_andesite_scheduler_layer.py>` (use the macro Makefile's invocation; export PATH/PYTHONPATH first)
Expected: FAIL — old golden drives `memtype_i=DDR3`, expects `dfi_init_start_o`, old MR order, `cl_o/cwl_o/bl_o`.

- [ ] **Step 2: TB updates**

`andesite_scheduler_layer_tb.py`: `memtype_i = MEMTYPE_DDR4`; delete the DFI-init handshake play (`drive dfi_init_complete_i / watch dfi_init_start_o` per docstring line ~21) and the `dfi_init_*` drives; drive the new timing CSRs `t_cke_wait_i`, `t_mod_wait_i` and MR images `mr4_i..mr6_i` (small values, e.g. 5/6/7 cycles); drop any `cl_o/cwl_o/bl_o` reads. Keep `AndesiteMemCmdSchedulerTB` class name. Keep the four wrlvl idle-drive lines (training ports still on the macro until Task 4).

- [ ] **Step 3: Golden re-derivation**

In the test: replace the scoria DDR3 init-order golden with the P1 order (list in Interfaces). Assert on the drained command stream: RESET# low ≥ tinit1 before any command; CKE precedes first MRS; MRS sequence is exactly MR3,6,5,4,2,1,0 with ≥tMRD spacing; ZQCL present after tMOD and before `init_done`; `init_done` only after max(tdllk,tzqinit). Add the Review-Focus case: `memtype_i = MEMTYPE_LPDDR4` → `init_err_o` rises, `init_done` never does.

- [ ] **Step 4: Green**

Run the suite (all `TEST_TYPE`s the file parametrizes).
Expected: PASS (target: the file's full param set; at minimum the init-order, stall-survival, and wrong-memtype cases).

- [ ] **Step 5: Un-park — the suite becomes tracked**

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/dv/tests/macro/test_andesite_scheduler_layer.py projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/dv/tbclasses/andesite_scheduler_layer_tb.py
git status --porcelain | grep '^[AM]'
git commit -m "feat(andesite): macro suite re-derived to the P1 init sequence; un-parked"
```

---

### Task 3: Widened command word + `andesite_dfi_cmd_path` (new FUB)

**Files:**
- Modify: `rtl/macro/andesite_scheduler_layer.sv` (output-word pack ~773–778: add `bg`; internal `a_cmd_bg` net from the arbiter's group select — find where `bg_o` from the addr_mapper path enters scheduling today (T1/T3 delta sites) and carry it to the pack)
- Create: `rtl/fub/andesite_dfi_cmd_path.sv`, `rtl/filelists/fub/andesite_dfi_cmd_path.f`, `dv/tests/fub/test_andesite_dfi_cmd_path.py`
- Modify: `rtl/filelists/andesite_all.f` (add the fub list), `docs/andesite_mas/ch02_blocks/10_dfi_datapath.md` (cmd_path section becomes real: name the module, the container, the CS lanes)

**Interfaces:**
- Consumes: P1 `andesite_dfi_cmd_formatter` (`op_i, bank_i, bg_i, row_i, col_i, rank_i, memtype_i, parity_en_i` → `dfi_cs[RANKS-1:0], dfi_act_n, dfi_ras_n, dfi_cas_n, dfi_we_n, dfi_bank, dfi_bg, dfi_address, dfi_cke, dfi_parity_in`); scoria's cmd_path test list (`test_scoria_dfi_cmd_path.py`, 9 tests) as the port-shape reference.
- Produces: `andesite_dfi_cmd_path` with parameters `NUM_RANKS=1, RANK_W, NUM_BANKS, ROW_WIDTH, COL_WIDTH, ADDR_WIDTH=18, BANK_WIDTH=2, BG_WIDTH=2, CMD_HISTORY_EN=0`; ports: `dfi_clk, dfi_rstn, memtype_i, parity_en_i`, command input `cmd_valid_i, cmd_ready_o, cmd_data_i[CMD_DW-1:0]` where `CMD_DW = 4 + RKW + BKW + BGW + ROW_WIDTH + COL_WIDTH + 1` packed **`{ap, col, row, bg, bank, rank, op}`** (bg inserted between row and bank — the widening), structural backpressure `rd_op_ready_i, wr_op_ready_i`, data-path strobes `wr_fire_o, rd_fire_o, fire_rank_o[RKW-1:0], wr_accept_o`, DFI outputs `dfi_address_o[ADDR_WIDTH-1:0], dfi_bank_o, dfi_bg_o[BG_WIDTH-1:0], dfi_act_n_o, dfi_ras_n_o, dfi_cas_n_o, dfi_we_n_o, dfi_cs_o[RANKS-1:0], dfi_cke_o, dfi_parity_in_o`. **One** `andesite_dfi_cmd_formatter` instance, outputs registered one cycle (scoria's registered-pipeline inheritance); a read is held when `!rd_op_ready_i`, a write when `!wr_op_ready_i` (clears `wr_accept_o`); no self-inserted idle cycles; fire strobes registered to align. No per-sub fan-out: `N_SUBCMD` and the sub strides are **not** carried (DDR4 single-channel; andesite has no sub-word framing inputs).

- [ ] **Step 1: Red — write the ported suite and watch it fail to build**

Port from `test_scoria_dfi_cmd_path.py`: `never_inserts_an_idle_cycle`, `read_holds_only_for_the_aligner`, `write_holds_only_for_staged_data`, `fire_strobes_follow_the_op`, `random_soak` (5). Drop sub-packing/phase-placement tests (no per-sub fabric) — note the drop in the commit message. Add two andesite-specific tests reusing the P1 formatter golden table (`test_andesite_dfi_cmd_formatter.py`): `registered_output_matches_formatter_golden` (per-op `{cs,act_n,ras_n,cas_n,we_n,bank,bg,address}` one cycle after accept, with `bg` from the word) and `parity_is_qualifed_by_parity_en` (toggle `parity_en_i`, flip one address bit). New tbclass `andesite_dfi_cmd_path_tb.py` only if the scoria tbclass can't be adapted cleanly.
Run: `make -C .../dv/tests/fub run-andesite_dfi_cmd_path-func`
Expected: FAIL (module doesn't exist).

- [ ] **Step 2: Implement `rtl/fub/andesite_dfi_cmd_path.sv`**

Skeleton: unpack `cmd_data_i` (`{w_ap, w_col, w_row, w_bg, w_bank, w_rank, w_op}`), instantiate the P1 formatter with `op_i=w_op, bank_i=w_bank, bg_i=w_bg, row_i=w_row, col_i=w_col, rank_i=w_rank, memtype_i, parity_en_i`, register every DFI output + strobes one cycle, implement the read/write structural holds (`cmd_ready_o` gating by op class), optional `andesite_cmd_history_checker` generate copied from the macro's existing pattern. 120–180 lines, no timing logic (JEDEC spacing stays in the scheduler).

- [ ] **Step 3: Scheduler word widening**

Carry `a_cmd_bg` from the arbiter/group-select point to the pack; change `CMD_W`/pack to include `bg[1:0]`; update the macro .f only if a new file is needed (none). Update the MAS 05/10 prose: the packed word is now `{ap,col,row,bg,bank,rank,op}`.

- [ ] **Step 4: Green**

Run: `make -C .../dv/tests/fub run-andesite_dfi_cmd_path-func` (expect PASS, 7 tests) and re-run `verilator-scheduler` + the macro suite (Task 2) — the widened word must not regress the composed suite.

- [ ] **Step 5: Gates + commit**

Run: `bin/filelist_registry.py --check` (PASS) and `make -C .../rtl verilator-andesite` if such glob exists, else the scheduler+new-FUB lints.
```bash
git status --porcelain | grep '^[AM]'
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/andesite_dfi_cmd_path.sv projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/filelists/ projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/dv/tests/fub/test_andesite_dfi_cmd_path.py projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/macro/andesite_scheduler_layer.sv projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/ch02_blocks/
git commit -m "feat(andesite): dfi_cmd_path around the P1 formatter; scheduler word widened with bg"
```

---

### Task 4: `andesite_training_layer` — training moves out of the scheduler

**Files:**
- Create: `rtl/macro/andesite_training_layer.sv`, `rtl/filelists/macro/andesite_training_layer.f`, `dv/tests/macro/test_andesite_training_layer.py` (+ tbclass)
- Modify: `rtl/macro/andesite_scheduler_layer.sv` (remove `u_wrlvl` ~491–517 and the training ports ~182–200; add the maintenance command channel), `rtl/filelists/andesite_scheduler_layer.f` (drop wrlvl line? — no: the FUB file stays in the tree and moves to the training layer's filelist), `andesite_all.f`
- Modify: `docs/andesite_mas/ch02_blocks/09_training.md` (Parent line + neighbors), `ch03_interfaces/01_dfi40_pins.md` (source block column), `docs/andesite_has/ch03_architecture/03_training.md` (what-it-costs section), `docs/andesite_has/ch02_overview/03_module_hierarchy.md` (macro tier row)

**Interfaces:**
- Consumes: the three FUB port lists (wrlvl: strobe/cs_sel/tWLDQSEN/tWLMRD/tWLMRD_max/tWLO/tWLOE + dfi_phylvl pair + prime_dq + telemetry; rdlvl: `rdlvl_en_i, cs_sel_i, csr_mr3_mpr_enter/exit_i, t_mpr_enter/exit/readout_i, tmod_i, t_rdlvl_timeout_i, mpr_pattern_i, cmd_req_o/ack_i/op_o/bank_o/addr_o, dfi_phylvl_req_cs_n_i/ack_cs_n_o, dfi_phy_rdlvl_cs_n_o, telemetry`; ca_train: `ca_train_en_i, wdq_cal_en_i, chan_sel_i, 4× csr_mpc_*_i[15:0], t_ca_train_i, t_wdq_cal_i, t_ca_timeout_i, ca_sample_i, wdq_sample_i, cmd_req_o/ack_i/op_o/mpc_op_o[5:0], telemetry`); scheduler's new maintenance channel (this task defines it): `trn_cmd_req_i, trn_cmd_ack_o, trn_cmd_op_i (dram_op_e), trn_cmd_bank_i[2:0], trn_cmd_addr_i[17:0], trn_cmd_mpc_i[5:0]` admitted at maintenance priority beside refresh/ZQ.
- Produces: `andesite_training_layer` ports (controller domain, `mc_clk/mc_rst_n` for the FUBs and CSR side): CSR-side `wrlvl_strobe_i, wrlvl_cs_sel_i[3:0], t_wldqsen_i, t_wlmrd_i, t_wlmrd_max_i, t_wlo_i, t_wl... (all existing scheduler training CSR ports move here verbatim), rdlvl CSR images/timings, ca_train CSR images/timings, `wrlvl_en_i` (sourced from the macro's `wrlvl_en_o` at assembly), PHY-side `dfi_phylvl_req_cs_n_o[NUM_CS], dfi_phylvl_ack_cs_n_i[NUM_CS], dfi_phy_wrlvl_cs_n_o[NUM_CS], dfi_wrlvl_strobe_o, dfi_phy_rdlvl_cs_n_o[NUM_CS], wrlvl_prime_dq_i, mpr_pattern_i, ca_sample_i, wdq_sample_i`, telemetry outputs (wrlvl result/attempts/flips/timeout/ever_done/state; rdlvl result/status/obs_*; ca_train result/status/obs_*), and the mux winner's command channel `trn_cmd_req_o, trn_cmd_ack_i, trn_cmd_op_o, trn_cmd_bank_o, trn_cmd_addr_o, trn_cmd_mpc_o`. One-active policy: `wrlvl_en_i` (DRAM-side mode) wins over `rdlvl_en_i` over `ca_train_en_i/wdq_cal_en_i`; an active flow locks the mux until `result_valid_o`. **Clocking:** the PHY-facing training handshake pins are in the DFI clock domain at the boundary — the `cdc_synchronizer`+`sync_pulse` crossing pattern from `scoria_dfi_layer.sv:400-455` is carried INTO this layer (Task 6 deliberately does not carry it), so the FUBs stay on `mc_clk` and the pins present cleanly to the PHY.

- [ ] **Step 1: Red — training-layer suite**

New `test_andesite_training_layer.py` (≥6 tests): `smoke_wrlvl_path_still_works` (strobe→result via the layer, reusing the wrlvl FUB golden), `rdlvl_issues_mrs_pair` (enter/exit MR3 images on the cmd channel via req/ack), `ca_train_uses_mpc_opcodes` (enter/exit opcodes appear, undecoded), `one_active_lockout` (pulse rdlvl during wrlvl → rdlvl waits; pins stay wrlvl's; after wrlvl result, rdlvl proceeds), `timeout_paths_report` (rdlvl timeout status distinct), `random_soak` (legal one-active throughout). tbclass instantiates the layer, mock-acks the cmd channel.
Run: suite fails (module missing).

- [ ] **Step 2: Implement `andesite_training_layer.sv`**

Instantiate `u_wrlvl/u_rdlvl/u_ca_train` (all on `mc_clk`); one-active arbiter (priority + busy lock; `wrlvl` holds the pins while `wrlvl_en_i` is high — that is a mode, not a pulse; document the interaction: firmware must clear MR1[7] before pulsing rdlvl/ca, and the lockout test proves the layer serializes even if they don't); mux the DFI training pins and the cmd channel from the winner. Carry the PHY-handshake crossing from `../scoria-ddr3-lpddr3/rtl/macro/scoria_dfi_layer.sv:400-455` (`cdc_synchronizer` for levels, `sync_pulse` for the one-cycle strobe) so the DFI-domain training pins cross cleanly; FUB-side logic stays in `mc_clk`.

- [ ] **Step 3: Scheduler surgery**

Remove `u_wrlvl` + the 16 training ports; add the `trn_cmd_*` channel into the arbiter at maintenance priority (mirror how refresh/ZQ demands enter; the ack is the same accept pulse used for init in Task 1's Step 4 pattern). Update `andesite_scheduler_layer.f` (wrlvl FUB moves to the training filelist), `andesite_all.f`, and the Task-2 suite/TB (drop the four training idle-drive lines — the macro no longer has those ports; the training suite now covers them).

- [ ] **Step 4: Green + regression**

Run: training suite (PASS), macro suite (PASS), wrlvl/rdlvl/ca_train FUB suites (PASS, untouched), `verilator-scheduler` + `verilator-training` lint (PASS).

- [ ] **Step 5: Doc reconcile + commit**

Edit the four doc pages listed in Files (exact sentences located by the M- fact-find: 09_training.md:27–28,257–259; 01_dfi40_pins.md:82–100; 03_training.md:113–120; 03_module_hierarchy.md macro-tier table).
```bash
git status --porcelain | grep '^[AM]'
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/macro/ projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/filelists/ projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/dv/ projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/
git commit -m "feat(andesite): andesite_training_layer born; wrlvl moves out of the scheduler"
```

---

### Task 5: Deferred review minors M-1…M-9

**Files (all under `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/`):**
- M-1: `docs/andesite_mas/ch02_blocks/04_addr_mapper.md:29,39-68` — status line to the landed posture; Table 2.9 params → `AXI_ADDR_WIDTH`, `NUM_RANKS`, `NUM_BANKS`; drop `HASH_EN` (hash is `hash_en_i` input); Table 2.10 widths → `$clog2(NUM_RANKS)` / `$clog2(NUM_BANKS)`; drop the `byte offset` port row (move to params as `BYTE_OFFSET_WIDTH`).
- M-2: `rtl/fub/andesite_rd_intake.sv:13,208`, `andesite_wr_intake.sv:13,53,66,293,419,422`, `andesite_wrlvl_ifc.sv:13,33` — `scoria_*` → `andesite_*` in comments and the two `$error` strings.
- M-3: `rtl/fub/andesite_rdlvl_ifc.sv:89-94`, `andesite_ca_train_ifc.sv:81-86` — delete the never-live `TELEM_NORESULT` enumerator; add a one-line comment that the 2-bit telemetry space is 3-live/1-reserved.
- M-4: `rtl/fub/andesite_ca_train_ifc.sv` — reset `r_timeout_cnt` on the `ST_SAMPLE → ST_MPC_ENTER` (exit-pass) transition so the exit pass gets its own budget; `rtl/fub/andesite_rdlvl_ifc.sv:175-179` — HANDSHAKE comment to "transition to CAPTURE on active-low req assertion".
- M-5: `docs/andesite_mas/ch02_blocks/08_odt_ctrl.md:84-93` — policy table to the four landed states (`PARK/RD_NOM/RD_SELF/WR`) with the RD_SELF-vs-RD_NOM distinction.
- M-6: `docs/andesite_mas/ch00_front_matter/00_document_info.md:41` — 0.4 row: move `wrlvl_ifc` from carried-modified to rename-only (counts 9→8 modified, 14→15 rename-only).
- M-7: `docs/andesite_mas/ch02_blocks/02_init_sequencer.md:184-187` — RESENDING: "holds the recovery interval, then returns to IDLE so the scheduler re-issues the dropped command from its request queue".
- M-8: `dv/tests/fub/test_andesite_refresh_ctrl.py:590-597` — compare `req_fgr1x` cadence against the plain-smoke baseline captured in the same test (assert equal request cycle indices, not `len > 0`).
- M-9: no action (record-only).

**Interfaces:** none cross-task.

- [ ] **Step 1: Apply M-1, M-5, M-6, M-7 (doc-only) and M-2, M-3, M-4 (RTL-comment/enum + one counter reset)**
- [ ] **Step 2: M-8 test strengthening — run the refresh suite red-then-green** (old assertion passes vacuously; new cadence compare must PASS against current RTL — if it fails, the FGR 1x path has a real bug: stop and report, don't weaken).
- [ ] **Step 3: Regression — rdlvl/ca_train/wrlvl/intake/odt suites + `verilator-*` for the touched FUBs**
- [ ] **Step 4: Commit**

```bash
git status --porcelain | grep '^[AM]'
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/
git commit -m "fix(andesite): deferred review minors M-1..M-8 (M-9 record-only)"
```

---

### Task 6: `andesite_dfi_layer` birth

**Files:**
- Create: `rtl/macro/andesite_dfi_layer.sv` (~200–260 lines), `rtl/filelists/macro/andesite_dfi_layer.f`, `dv/tests/macro/test_andesite_dfi_layer_smoke.py` (elaboration + loopback smoke)
- Modify: `rtl/filelists/andesite_all.f`, `docs/andesite_mas/ch02_blocks/10_dfi_datapath.md` (layer section: name the module, DBI routing, init-pair generation), `docs/andesite_has/` module-hierarchy row if it lists the layer

**Interfaces:**
- Consumes: `andesite_dfi_cdc` (ctl↔dfi FIFOs, `CMD_DW` param — widen its command word to the Task-3 `CMD_DW` including `bg` and update its packed-word comment), Task-3 `andesite_dfi_cmd_path`, `andesite_dfi_wr_serializer` (`db_wr_dbi_en_i`, `wd_dbi_i`, mask-DBI reuse), `andesite_dfi_rd_aligner` (`rd_dbi_en_i`, `dfi_rddata_dbi_i`, `rd_dbi_o`); scoria's `scoria_dfi_layer.sv` (457 lines) as the wiring reference (cdc→cmd_path→serializer/aligner, fire-strobe chaining, gear phase masking, write-token pacing).
- Produces: `andesite_dfi_layer` ports — controller side: `ctl_clk, ctl_rstn, cmd_valid_i/cmd_ready_o/cmd_data_i[CMD_DW-1:0]` (widened), `wd_valid_i/wd_ready_o/wd_data_i/wd_dbi_i/wd_strb_i`, `rd_valid_o/rd_ready_i/rd_data_o/rd_dbi_o`, init `init_busy_i/init_done_i` (from the macro), policy inputs `rd_dbi_en_i, wr_dbi_en_i` (sourced from the macro's Task-1 outputs at assembly); PHY side: `dfi_clk, dfi_rstn, memtype_i, rd_phase_i, wr_phase_i, t_phy_wrlat_i, t_rddata_en_i, gear_i`, DFI 4.0 command surface `dfi_address_o, dfi_bank_o, dfi_bg_o, dfi_act_n_o, dfi_ras_n_o, dfi_cas_n_o, dfi_we_n_o, dfi_cs_o, dfi_cke_o, dfi_parity_in_o`, the three CS-qualified lanes `dfi_cs_o` (command, from cmd_path) + `dfi_wrdata_cs_o`/`dfi_rddata_cs_o` driven `'0` at this design point (documented per scoria v3.1 precedent), write data `dfi_wrdata_o/dfi_wrdata_en_o/dfi_wrdata_mask_o`, read data `dfi_rddata_en_o/dfi_rddata_i/dfi_rddata_valid_i`, init `dfi_init_start_o` (asserted from `init_busy_i`), and DBI `dfi_rddata_dbi_i` in / `dfi_wrdata_dbi_o` semantics exactly as the serializer/aligner define. **Training pins are NOT here** (owner ruling: the training layer owns them — do not carry scoria's inline wrlvl CDC).

- [ ] **Step 1: Red — smoke suite + lint**

`test_andesite_dfi_layer_smoke.py`: elaborate the layer as top (verilator lint-as-top is the primary gate; the cocotb smoke pushes one ACT+RD+WR through with a trivial DFI sink model, checks `dfi_cs_o` one-hot-low and `dfi_wrdata_mask_o`/`rd_dbi_o` behavior with DBI enabled vs disabled).
Run: fails (module missing).

- [ ] **Step 2: Implement the layer**

Carry scoria's wiring shape: CDC (with widened `CMD_DW`) → cmd_path (`pcmd_*`), `pwr_staged_valid`→cmd_path `wr_op_ready_i`, `wr_accept_o` pops the token; `w_wr_fire`→serializer, `w_rd_fire`→aligner; gear-down `w_phase_active` masking of `dfi_wrdata_en_o/rddata_en_o`; DBI enables from policy inputs; `dfi_init_start_o = init_busy_i` registered. No training CDC, no `dfi_signal_pack` instantiation (stays dormant — scoria doesn't instantiate it either).

- [ ] **Step 3: Green**

Run: smoke suite PASS; `make -C .../rtl verilator-dfi` PASS (cmd_path/cdc/serializer/aligner/layer lint clean); registry `--check` PASS.

- [ ] **Step 4: Doc reconcile + commit**

10_dfi_datapath.md: state the layer composition + CS-lane design point + "training pins live on `andesite_training_layer`, not here". Commit message notes the doc claim about `dfi_error` was reconciled (scoria never had it; not added).

---

### Task 7: `andesite_axi4_layer` birth (rename-carry + parity gate)

**Files:**
- Create: `rtl/macro/andesite_axi4_layer.sv` (rename-carry of `../scoria-ddr3-lpddr3/rtl/macro/scoria_axi4_layer.sv`, 622 lines), `rtl/filelists/macro/andesite_axi4_layer.f`, `dv/tests/macro/test_andesite_scoria_axi4_logic_parity.py` (source-parity gate, ported from `test_scoria_pumice_logic_parity.py`)
- Modify: `rtl/filelists/andesite_all.f`, `docs/andesite_has/ch02_overview/03_module_hierarchy.md` (if the row needs the "now landed" nuance — it already names `andesite_axi4_layer`)

**Interfaces:**
- Consumes: the 7 already-carried andesite sub-FUBs (`andesite_wr_splitter, andesite_axi_burst_chopper, andesite_wr_intake, andesite_wr_data_cam, andesite_rd_intake, andesite_rd_cmd_cam, andesite_rd_return_ring`); scoria's layer interface (AXI4 slave bundles, `bank_lsb_i/hash_en_i/hash_seed_i`, the `wr_sch_*`/`rd_sch_*` CAM vectors + commit/issue/return channels, `busy_o`).
- Produces: `andesite_axi4_layer` driving the scheduler macro's existing CAM ports (`wr_sch_valid_o` … `rd_issue_slot_o` — names match scoria's, which the macro's inputs were carried to receive); the rename map `scoria_→andesite_` applied to module + instance names only; parameters unchanged.

- [ ] **Step 1: Red — the parity gate**

Port `test_scoria_pumice_logic_parity.py`'s PORTED-table pattern: assert `andesite_axi4_layer.sv` is byte-identical to `scoria_axi4_layer.sv` under the rename map (`sed 's/scoria/andesite/g'` equivalence), plus the sub-FUB rename-map rows the scoria gate uses.
Run: fails (file missing).

- [ ] **Step 2: The carry**

`git log --oneline --follow` scoria's file briefly for recent fix history, then rename-carry with `sed 's/scoria/andesite/g'` (verify no scoria-only submodule sneaks in — all 7 sub-FUBs exist in andesite), create the filelist mirroring scoria's macro .f composition with andesite paths, add to `andesite_all.f`.

- [ ] **Step 3: Green**

Run: parity gate PASS; `make -C .../rtl verilator-axi4` PASS; registry `--check` PASS.

- [ ] **Step 4: Commit**

`feat(andesite): andesite_axi4_layer born as the scoria rename-carry with a logic-parity gate`

---

### Task 8: `andesite_core` + top suite — the capstone

**Files:**
- Create: `rtl/top/andesite_core.sv`, `rtl/filelists/top/andesite_core.f`, `dv/tbclasses/andesite_core_tb.py` (carried from `../scoria-ddr3-lpddr3/dv/tbclasses/scoria_core_tb.py`), `dv/tests/top/test_andesite_core.py` (4 tests, ported from `test_scoria_core.py`)
- Modify: `rtl/filelists/andesite_all.f` (top tier), `docs/andesite_has/ch02_overview/03_module_hierarchy.md` (top tier "now landed" note if needed)

**Interfaces:**
- Consumes: everything — Task-1 macro (init/policy outputs), Task-4 training layer, Task-6 dfi layer, Task-7 axi4 layer; `scoria_core.sv` as the assembly reference (instantiation order, tie-offs, CSR plumbing stubs).
- Produces: `andesite_core` = AXI4 slave + APB-ish CSR stub (drive the macro/task CSRs with the scoria_core pattern; if scoria_core has a real CSR block, carry its stub posture) + the four layers wired: axi4 CAM ↔ scheduler, scheduler widened cmd word → dfi layer, policy outputs (rtt/dbi/parity/wrlvl_en) → training/dfi layers, training pins to the PHY boundary, DFI pins out. The exact wiring table is assembled in this task from the produced interfaces of Tasks 1–7.

- [ ] **Step 1: Red — port the 4 top tests** (`init_then_write_read_roundtrip`, `write_lands_where_the_dram_thinks_it_lives`, `read_returns_preloaded_data`, `several_banks_round_trip`) with `AndesiteCoreTB` (AXI4 master BFM + `DFISlavePHY` + `MemoryModel` + `DramStateModel` carried from scoria's tbclasses, renamed).
- [ ] **Step 2: Implement `andesite_core.sv` (assembly only — no new logic; tie-offs per scoria_core).**
- [ ] **Step 3: Green** — 4/4 tests; `make -C .../rtl verilator-` core lint; registry PASS.
- [ ] **Step 4: Commit** `feat(andesite): andesite_core assembles the four layers; top suite green`.

---

### Task 9: Final gate, doc rows, ledger close, whole-branch review

- [ ] **Step 1: Full gate** — every andesite suite (fub + macro + top), `bin/filelist_registry.py --check`, `make -C projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl verilator` (master lint), grep gate `grep -rni "scoria_" projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/ | grep -v "Carried from\|carried"` (post-M-2 sanity).
- [ ] **Step 2: Doc version rows** — HAS ch00 + MAS ch00 new 0.5 rows: the integration pass landed (macro elaborates, training layer, cmd_path, dfi/axi4 layers, core; file counts reconciled to the marking tables).
- [ ] **Step 3: Ledger** — final entries in `.superpowers/sdd/2026-10-04-andesite-macro-integration/progress.md` (per-task rulings + carry-gate regexes + gotchas, the P3 pattern).
- [ ] **Step 4: Whole-branch review on a fresh agent** (the P3 pattern: full range review, verdict, fix pass for Critical/Important).

---

## Plan-level risks (recorded, not blocking)

- **cmd_ack pulse shape** (Task 1 Step 4) is the one place the plan cannot name the exact net in advance; the constraint (honest accept pulse; watchdog must still latch `init_err`) pins the semantics, and the Task-2 suite proves it.
- **wrlvl is a mode, not a pulse** — the one-active mux interacts with `wrlvl_en_i` staying high for entire sweeps; Task 4's lockout test is the pin.
- **Task 8 CSR plumbing** may surface scoria_core dependencies on scoria CSR blocks that have no andesite counterpart; if so, carry the scoria stub posture and record the gap in the ledger rather than inventing a CSR block (PeakRDL generation is out of scope).
- LPDDR4 command path (formatter CA submodule) remains the recorded TASK-008 follow-on — this plan does not build it and no test here may claim LPDDR4 command formatting.
