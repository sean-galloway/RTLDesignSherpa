# andesite RTL bootstrap P2 (unchanged-block carry) — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Carry the ten behaviorally-unchanged scoria FUBs (plus the dormant pair, uninstantiated) into the andesite tree as `andesite_*` with scoria's model-first suites ported and green, per HAS ch02's inheritance table.

**Architecture:** Pure carry: `scoria_*` → `andesite_*` rename, `scoria_pkg::*` → `andesite_pkg::*` import swap, header comment updates. Dependency-driven re-sequence: `rd_intake`/`wr_intake` instantiate `addr_mapper` (P3-modified), so they land at the front of P3, not in P2 — the spec's idealized list yields to the real dependency graph. Design authority for each carried block is scoria's RTL + books (the carry is the point; nothing is re-derived).

**Tech Stack:** SystemVerilog (Verilator/Verible), cocotb + pytest, the Task-1/2 scaffolding.

**Spec:** `docs/superpowers/specs/2026-10-04-andesite-rtl-bootstrap-design.md` §3 P2/P3. Prior phase: `docs/superpowers/plans/2026-10-04-andesite-rtl-bootstrap-p0p1.md` (landed).

## Global Constraints

- Carry rules: diff each carried file against its scoria source — the ONLY permitted differences are (1) the module name, (2) the package import, (3) header comments, (4) the dependency-driven exceptions recorded in Task 1 Step 1. Anything else is a defect; the diff is the review instrument. A `git diff -w` check script enforces this per file.
- The package enum width change (4→5 bit `dram_op_e`) needs no edit: op-typed ports use `dram_op_e`. The `[3:0]` AXI QOS/cache/region fields stay `[3:0]` (AXI widths, not op encodings).
- Naming/filelists/lint/venv/commit-prefix rules unchanged from the P0+P1 plan (Global Constraints carry over).
- Suites: port scoria's dedicated suite where one exists (rename, green). Where scoria has no dedicated FUB suite (rd_cmd_cam, wr_data_cam, bank_timers, rd_return_ring, dfi_cdc, dormant pair), the carry test is lint + verilator elaboration + a cocotb reset/idles smoke, and the plan records "model-first suite lands with the P3 integration tier" — scoria covered several of these at macro/top level, and the carry keeps that posture honestly.
- Commit prefix `feat(andesite):`; one commit per task; `python3 bin/check_task_ids.py` PASS before every commit.

## Review Focus

1. **Silent behavior drift in the carry** — a rename that accidentally touches logic (a `scoria_` inside a string, a generate label, an include guard) compiles and runs but isn't the inherited block anymore. The per-file `diff -w` gate against the scoria source is the pin.
2. **Package swap side effects** — `andesite_pkg`'s extra enum member (OP_MPC) and 3-bit memtype change elaboration semantics only where modules case on memtype or size op storage; the carry tasks grep each file for `memtype`/`dram_op` uses and the diff gate proves no edit was needed.
3. **Suite port fidelity** — a ported test that mocks the renamed DUT or re-derives expectations from the andesite tree instead of scoria's suite is a new test, not a transfer. Ported suites must come from `scoria-ddr3-lpddr3/dv/tests/fub/` + `dv/tbclasses/` with renames only, and a ported suite that passes unchanged-in-spirit is the evidence.
4. **cmd_history_checker parameter growth** — the DDR4 long/short additions must be named-parameter/CSR-input shape per the MAS ("parameter change, not mechanism change"); inventing internal constants or restructuring the checker is scope creep.
5. **Dormant honesty** — powerdown_ctrl/dfi_signal_pack carry uninstantiated: no P2 wrapper may instantiate them, and a tree grep proves it at the gate.

---

## File Structure

Carried RTL (all under `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/rtl/fub/`, filelists `rtl/filelists/fub/andesite_<name>.f`):
- `andesite_bank_timer.sv`, `andesite_bank_timers.sv` (instantiates bank_timer — in-set), `andesite_page_policy.sv`
- `andesite_rd_cmd_cam.sv`, `andesite_wr_data_cam.sv`
- `andesite_wr_splitter.sv` (instantiates axi_burst_chopper — in-set), `andesite_axi_burst_chopper.sv`, `andesite_rd_return_ring.sv`, `andesite_dfi_cdc.sv`
- `andesite_cmd_history_checker.sv` (+ DDR4 L/S spacing parameters)
- `andesite_powerdown_ctrl.sv`, `andesite_dfi_signal_pack.sv` (dormant pair)
- Re-sequenced to P3: `andesite_rd_intake.sv`, `andesite_wr_intake.sv` (instantiate addr_mapper).

Ported DV: `dv/tbclasses/andesite_<block>_tb.py`, `dv/tests/fub/test_andesite_<block>.py` (where scoria suites exist).

### Task 1: Carry wave 1 — timers and page policy

**Files:**
- Create: `rtl/fub/andesite_bank_timer.sv`, `rtl/fub/andesite_bank_timers.sv`, `rtl/fub/andesite_page_policy.sv` + filelists
- Create: `dv/tbclasses/andesite_bank_timer_tb.py`, `dv/tbclasses/andesite_page_policy_tb.py` (ported), `dv/tests/fub/test_andesite_bank_timer.py`, `dv/tests/fub/test_andesite_page_policy.py`
- Test: scoria's suites ported, green; `diff -w` gates pass

**Interfaces:**
- Produces: `andesite_bank_timer`, `andesite_bank_timers`, `andesite_page_policy` with scoria's exact port lists (renamed module only). Task 2's CAMs and the P3 scheduler consume them by these names.

- [ ] **Step 1: Pin the carry-diff gate + the dependency facts**

Write `bin/tmp` no — write the check as a repo script `projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/dv/bin/check_carry_diff.sh` (new): given a carried file and its scoria source, `diff -w` must show ONLY lines matching the permitted-difference pattern (module name, package import, header comment block). Record the Task-1 Step-1 exceptions the scan already established: `bank_timers` instantiates `bank_timer` (in-set; the instantiation name updates with the rename — permitted as part of the rename rule). Grep the three sources for `memtype`/`dram_op` uses; record that the package swap needs no logic edit (both use typed ports only). This step's output is the gate script + a short findings paragraph in the task's commit message.

- [ ] **Step 2: Write the failing tests (ported suites)**

Copy `test_scoria_bank_timer.py` → `test_andesite_bank_timer.py`, `test_scoria_page_policy.py` → `test_andesite_page_policy.py`, and their tbclasses, with `scoria` → `andesite` renames (module names, filelist paths, DUT strings). Run: `make run-andesite_bank_timer-func` and `make run-andesite_page_policy-func`. Expected: FAIL (modules don't exist).

- [ ] **Step 3: Carry the three modules**

Copy the sources with rename + import swap + header updates (documentation path → andesite MAS; "Carried unchanged from scoria_<name> per HAS ch02"). Create filelists (mirror the scoria filelist structure: pkg + in-set deps + the module).

- [ ] **Step 4: Run green + diff gate + lint**

Run both suites (Expected: PASS). Run the carry-diff gate on all three files (Expected: only permitted differences). `make verilator-andesite_bank_timer verilator-andesite_bank_timers verilator-andesite_page_policy && make verible`.

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4
git commit -m "feat(andesite): carry bank_timer/bank_timers/page_policy from scoria (P2 wave 1)"
```

### Task 2: Carry wave 2 — CAMs and datapath helpers

**Files:**
- Create: `rtl/fub/andesite_rd_cmd_cam.sv`, `andesite_wr_data_cam.sv`, `andesite_wr_splitter.sv`, `andesite_axi_burst_chopper.sv`, `andesite_rd_return_ring.sv`, `andesite_dfi_cdc.sv` + filelists
- Create: ported suites for `axi_burst_chopper` and `wr_splitter` (scoria has them); elaboration+smoke tests for rd_cmd_cam, wr_data_cam, rd_return_ring, dfi_cdc
- Consumes: Task 1 modules where scoria's sources reference them (none instantiated here; CAMs reference intakes/ring only in comments — verified at Step 1).

**Interfaces:**
- Produces: the six modules with scoria port lists; `andesite_wr_splitter` instantiates `andesite_axi_burst_chopper` (rename of scoria's internal instantiation, permitted).

- [ ] **Step 1: Dependency + memtype/dram_op scan; pin exceptions**

Same scan as Task 1 Step 1 for the six sources. Expected findings (pre-established): wr_splitter instantiates axi_burst_chopper (in-set rename, permitted); dfi_cdc references dfi_cmd_path in comments only; the four pkg-free modules need no import swap; CAMs have no dedicated scoria suites (smoke-test posture per Global Constraints).

- [ ] **Step 2: Write the failing tests**

Port the chopper and splitter suites (renames). Write minimal elaboration-smoke cocotb tests for rd_cmd_cam, wr_data_cam, rd_return_ring, dfi_cdc (reset + idle inputs + a few clocks, assert no X on key outputs — the point is elaboration and lint through the sim pipeline). Run all six targets: Expected FAIL (modules missing).

- [ ] **Step 3: Carry the six modules + filelists** (rename/import/header rules as Task 1).

- [ ] **Step 4: Run green + diff gate + lint** (six suites, six diff gates, verilator ×6, verible).

- [ ] **Step 5: Commit** `feat(andesite): carry CAMs, splitter/chopper, return ring, dfi_cdc (P2 wave 2)`

### Task 3: `andesite_cmd_history_checker` — the checker with DDR4's spacing set

**Files:**
- Create: `rtl/fub/andesite_cmd_history_checker.sv` + filelist; ported `dv/tbclasses/andesite_cmd_history_checker_tb.py`, `dv/tests/fub/test_andesite_cmd_history_checker.py`
- Modify: none outside the andesite tree (MAS 01_block_inventory.md row already names the parameter growth — verify wording during execution and update in place if the landed param names differ).

**Interfaces:**
- Consumes: scoria's cmd_history_checker source + suite.
- Produces: `andesite_cmd_history_checker` with scoria's port list PLUS the DDR4 long/short spacing inputs the MAS names (tCCD_L/S, tRRD_L/S as runtime CSR-shaped inputs — exact names per the MAS `cmd_history_checker` paragraph and scoria's existing timing-input naming convention). The diff gate for THIS file carries one extra permitted difference: the added parameter ports, listed in the commit message.

- [ ] **Step 1: Read scoria's cmd_history_checker parameter surface + the MAS paragraph; pin the added port names.** Write the failing test first: extend the ported suite with cases that drive a same-bank-group pair and a cross-bank-group pair and assert the checker flags the L violation only inside a group and the S violation across groups (small CSR values). Expected: FAIL (module missing).

- [ ] **Step 2: Carry + add the four spacing inputs** (mechanism untouched — the additions are inputs and comparators in the same shape as scoria's existing timing checks).

- [ ] **Step 3: Run green + diff gate (with the recorded exception) + lint.**

- [ ] **Step 4: Commit** `feat(andesite): cmd_history_checker carried with DDR4 L/S spacing set (P2)`

### Task 4: Dormant pair + P2 gate

**Files:**
- Create: `rtl/fub/andesite_powerdown_ctrl.sv`, `andesite_dfi_signal_pack.sv` + filelists + elaboration smokes (no suites in scoria; uninstantiated carry).
- Modify: HAS/MAS `ch00_front_matter/00_document_info.md` (0.3 rows), MAS `ch01_overview/01_block_inventory.md` (status wording for the carried set, in place).

**Interfaces:**
- Produces: the P2-complete inheritance inventory (10 active carried + 2 dormant); P3 starts from addr_mapper + the intakes.

- [ ] **Step 1: Carry the dormant pair** with a header note "carried dormant per HAS Ch 3.1 — uninstantiated until the named waking condition". Elaboration smokes. Diff gate.

- [ ] **Step 2: Dormant-honesty grep** — assert no andesite file outside the pair's own filelists references `andesite_powerdown_ctrl`/`andesite_dfi_signal_pack` (Review Focus 5). Add the grep as a step the gate commit records.

- [ ] **Step 3: Book rows.** HAS ch00 0.3 row: "P2 carried: bank_timer(s), page_policy, rd/wr CAMs, splitter+chopper, return ring, dfi_cdc, cmd_history_checker (with the DDR4 L/S spacing set) land as andesite_* with scoria's suites ported; the dormant pair rides uninstantiated; rd/wr_intake re-sequenced to P3 (they instantiate addr_mapper, a P3 block — dependency order over the idealized list)." MAS ch00 matching row + status. MAS block-inventory wording updates in place if param names diverged.

- [ ] **Step 4: Full gate + commit.** All P2 suites green; `make lint-all`; generator rerun (exit 0 — CITES untouched); `python3 bin/check_task_ids.py`. Commit `feat(andesite): P2 gate -- unchanged twelve carried (ten active + dormant pair), intakes re-sequenced to P3`.

---

## Self-Review notes

- Spec coverage: spec §3 P2 items map to Tasks 1-4; the intake re-sequence is the one deviation, forced by the real instantiation graph (rd_intake/wr_intake → addr_mapper) and recorded as a ruling in the gate commit. P3 absorbs them at its front.
- Review Focus 1 → per-task Step-1 gates + the diff script. Focus 2 → the memtype/dram_op scans. Focus 3 → ported-suite provenance (scoria paths in the ported files' headers). Focus 4 → Task 3's exception-listed additions. Focus 5 → Task 4 Step 2.
- Interface consistency: consumed names (bank_timer etc.) match scoria's port lists exactly; P3 plans consume them by the andesite_ names fixed here.
- Proportion: no RTL bodies in this plan — the RTL is scoria's; the plan pins the carry rules, the gates, and the one bounded change (checker spacing set).
