# Merlin (5-Stage Pipelined RV32I) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build merlin, the falcon-ladder rung 2 core: kestrel's RV32I ISA and halt contract on a 5-stage IF/ID/EX/MEM/WB pipeline with forwarding, load-use interlock, and EX branch resolution — green on the rv32ui battery, a directed hazard suite, spike lockstep, and riscv-formal retire checks.

**Architecture:** Single-issue in-order 5-stage pipeline over the shared `common-rv32i` fubs (`rv32i_decode`, `rv32i_imm_gen`, `rv32i_alu`, `rv32i_pkg`) with four explicit pipeline-register modules and a separate hazard/forwarding unit. Branches and JALR resolve in EX (predict-not-taken, 2-bubble flush). Halts retire at WB (halting instruction is the last to retire; side effects of doomed instructions suppressed at MEM). RVFI retires at WB for spike lockstep and riscv-formal.

**Tech Stack:** SystemVerilog (house style: `ALWAYS_FF_RST` macros, `reset_defs.svh`, `[DEPTH]` arrays, no bespoke SRAM), cocotb 2.x pytest benches (kestrel patterns), SymbiYosys riscv-formal, spike 1.1.0 lockstep, GTKW save files.

**Spec:** `projects/components/riscv-ip/merlin-rv32i/PRD.md` (v0.2 — M1–M7 all DECIDED) + rung 2 of `docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md`.

## Global Constraints

- Module prefix `merlin_`; shared ISA fubs come from `common-rv32i` unchanged (no edits to `rv32i_*` modules).
- Resets via the `ALWAYS_FF_RST` macros and the `reset_sync` boundary pattern copied from `kestrel_core.sv` (N=3, active-low).
- x0 kept zero by writes (write-side zeroing, kestrel ruling 2026-10-20), never a read-side mux.
- Halt-cause encoding from `rv32i_pkg`: `HALT_ECALL=1, HALT_EBREAK=2, HALT_IALIGN=3, HALT_LALIGN=4, HALT_SALIGN=5, HALT_ILL=F`.
- Memory: Harvard core ports, registered-read behavioral BRAM in the TB (kestrel `tb_top` pattern), `mem_wait` input carried but tied `1'b0` in `merlin_tb_top` (M5 seam for peregrine's cache).
- No branch prediction, no CSRs beyond kestrel's stub, no Zicntr, no MonBus (merlin v1).
- Every new RTL/DV file gets a filelist entry; `bin/filelist_registry.py --check` must pass before each commit.
- Commit gates: `bin/check_broken_links.py --ratchet`, `bin/check_task_ids.py`, pre-commit hooks.
- Tests run from the area's `dv/tests/` with `source env_python` first; `SEED`/`REG_LEVEL`/`TEST_LEVEL` env per house pytest convention.

## Review Focus

The five spec-silent failure modes most likely to bite, each pinned by a test in the owning task:

1. **Branch compares stale operands** — a branch in EX whose comparator reads `id_ex.rs*_data` instead of the *forwarded* operands silently mis-resolves after an ALU→branch dependency. Test: Task 4 directed program `branch_after_alu`.
2. **Store-data (rs2) not forwarded** — rs2 feeds both the ALU-B mux and the MEM write-data register; forwarding only the ALU operand corrupts `sw` after a producer. Test: Task 4 `store_data_forward`.
3. **Flush/stall same-cycle priority** — a taken branch in EX coincident with a load-use stall in ID: flush must win or the stalled load executes. Test: Task 4 `flush_during_loaduse`.
4. **x0 forwarded** — a write to x0 must never become a forwarding source (rd_addr==0 excluded) and x0 reads stay 0. Test: Task 2 hazard unit `x0 never forwards` case + Task 3 rv32ui battery (the battery hammers x0).
5. **mem_wait mid-transaction** — a load/store held by `mem_wait` must not double-issue `dmem_req` or double-retire (`rvfi_valid` gated by the hold). Test: Task 3 mem_wait-pulse case in the core golden-trace bench.

---

### Task 1: `merlin_pkg` + pipeline register modules

**Files:**
- Create: `projects/components/riscv-ip/merlin-rv32i/rtl/includes/merlin_pkg.sv`
- Create: `projects/components/riscv-ip/merlin-rv32i/rtl/fub/merlin_if_id.sv`, `merlin_id_ex.sv`, `merlin_ex_mem.sv`, `merlin_mem_wb.sv`
- Create: filelists `.../rtl/filelists/merlin_pkg.f`, `.../rtl/filelists/fub/merlin_pipe_regs.f`, `.../rtl/filelists/merlin_all.f` (aggregates; mirror `common-rv32i/rtl/filelists/` layout)
- Test: `projects/components/riscv-ip/merlin-rv32i/dv/tests/test_merlin_pipe_regs.py` (+ `dv/tbclasses/merlin/__init__.py`, `dv/filelists/merlin_tb.f` entry added in Task 3)

**Interfaces:**
- Produces: packed structs in `merlin_pkg`, one per stage boundary — `if_id_t {pc[31:0], insn[31:0], valid}`, `id_ex_t {pc, rs1_data, rs2_data, imm, rs1_addr[4:0], rs2_addr[4:0], rd_addr[4:0], funct3[2:0], alu_op(alu_op_e), alu_src_a_pc, alu_src_b_imm, rd_wen, wb_sel[1:0], dmem_req, dmem_we, branch, jump, jalr, halt_cause[3:0], csr_stub, valid}`, `ex_mem_t {pc, next_pc, alu_y, store_data, rd_addr, rd_wen, wb_sel, funct3, dmem_req, dmem_we, ls_misalign, halt_cause, csr_stub, valid}`, `mem_wb_t {pc, next_pc, alu_y, load_data, rd_addr, rd_wen, wb_sel, csr_stub, halt_cause, valid}`. `wb_sel`: `WB_ALU=0, WB_LOAD=1, WB_LINK=2, WB_LUI=3` (localparams in the pkg).
- Produces: four register modules, all with `(clk, rst_n, stall, flush, <in>_i, <out>_o)`; semantics: `flush` → write the bubble record (`valid=0`, `halt_cause=HALT_NONE`, `rd_wen=0`, `dmem_req=0`); `stall` → hold; else capture input.

- [ ] **Step 1: Write the failing unit test** (`test_merlin_pipe_regs.py`): drive each register through capture / stall-hold / flush-bubble and assert the bubble record fields are exactly the safe values above (especially `rd_wen=0`, `dmem_req=0`).
- [ ] **Step 2: Run it, confirm FAIL** (`pytest test_merlin_pipe_regs.py -x -q` from `dv/tests/` after `source env_python`): modules don't exist.
- [ ] **Step 3: Implement** `merlin_pkg.sv` and the four register modules (struct ports, `ALWAYS_FF_RST`; flush wins when both flush and stall assert).
- [ ] **Step 4: Re-run, PASS.** Then `bin/filelist_registry.py --check`.
- [ ] **Step 5: Commit** (`rtl(merlin): pipeline register modules + merlin_pkg`).

### Task 2: `merlin_hazard` — forwarding + interlock unit

**Files:**
- Create: `projects/components/riscv-ip/merlin-rv32i/rtl/fub/merlin_hazard.sv` (+ add to `fub/merlin_pipe_regs.f` → rename aggregate `fub/merlin_fubs.f` if cleaner — pick one name and keep it)
- Test: `projects/components/riscv-ip/merlin-rv32i/dv/tests/test_merlin_hazard.py`

**Interfaces:**
- Consumes: the Task 1 structs' fields (plain ports, not structs — the unit is combinational glue).
- Produces: `merlin_hazard(id_rs1_addr, id_rs2_addr, idex_rd_addr, idex_rd_wen, idex_is_load, exmem_rd_addr, exmem_rd_wen, memwb_rd_addr, memwb_rd_wen, ex_flush)` → `fwd_a[1:0], fwd_b[1:0]` (`FWD_IDEX=0, FWD_EXMEM=1, FWD_MEMWB=2` — EX/MEM priority over MEM/WB), `stall_ifid` (load-use: `idex_is_load && idex_rd_addr!=0 && (idex_rd_addr==id_rs1_addr || idex_rd_addr==id_rs2_addr)`), `flush_ifid`, `flush_idex` (from `ex_flush`). rd_addr==0 never matches (Review Focus 4).

- [ ] **Step 1: Failing test** covering the full matrix: {no hazard, EX/MEM hit, MEM/WB hit, both (EX/MEM wins), x0 producer (never forwards), load-use (stalls), load-use vs x0 (no stall), flush wins over stall}.
- [ ] **Step 2–4:** run-FAIL / implement / run-PASS loop.
- [ ] **Step 5: Commit.**

### Task 3: `merlin_core` + `merlin_tb_top` — the vertical slice

**Files:**
- Create: `projects/components/riscv-ip/merlin-rv32i/rtl/top/merlin_core.sv`
- Create: `projects/components/riscv-ip/merlin-rv32i/dv/tb/merlin_tb_top.sv` (kestrel_tb_top pattern: unified 64 KiB behavioral memory, `+imem=` plusarg, `tb_mem_*` backdoor loader port, tohost mailbox via the store port, `mem_wait` tied 0)
- Create: `projects/components/riscv-ip/merlin-rv32i/dv/tbclasses/merlin/merlin_tb.py` (adapt `kestrel_tb.py`; import `RV32IInterpreter` from kestrel's tbclasses via `sys.path` insert — same idiom kestrel's own tests use)
- Create: `projects/components/riscv-ip/merlin-rv32i/rtl/filelists/top/merlin_core.f`, `dv/filelists/merlin_tb.f`; extend `merlin_all.f`
- Test: `projects/components/riscv-ip/merlin-rv32i/dv/tests/test_merlin_core.py`

**Interfaces:**
- Consumes: Tasks 1–2; `rv32i_decode`/`rv32i_imm_gen`/`rv32i_alu` port lists (see `kestrel_core.sv` instantiations, lines ~170–250); `kestrel_regfile(clk, rs1_addr, rs1_data, rs2_addr, rs2_data, rd_addr, rd_data, rd_wen)` — instantiate it as-is from kestrel's filelist in v1 (a family `rv32i_regfile` in common-rv32i is a follow-up note, not this task).
- Produces: `merlin_core` ports identical to `kestrel_core`'s (`clk, rst_n, mem_wait, imem_addr, imem_addr_next, imem_rdata, dmem_req, dmem_addr, dmem_rdata, dmem_wstrb, dmem_wdata, halt, halt_cause, rvfi_*`) so the TB and riscv-formal harness shapes carry over. `rvfi_valid` pulses at WB retire; `rvfi_order` counts retirements.
- Datapath decisions the implementer cannot re-derive: EX branch comparator uses **forwarded** operands (Review Focus 1); store data forwarded into `ex_mem.store_data` (Review Focus 2); load data assembled (byte rotate + sign-extend, kestrel's `ls_load_data` logic verbatim) in MEM; WB mux = `wb_sel` {ALU, LOAD, LINK(pc+4), LUI(imm)}, csr_stub forces 0; `HALT_IALIGN` raised in EX on misaligned taken target, `HALT_LALIGN/SALIGN` computed in EX from the offset adder and carried to suppress the MEM request; halt freezes fetch when the halting instruction reaches WB, and all younger in-flight instructions are squashed (valid=0, never retire).

- [ ] **Step 1: Failing golden-trace test** reusing kestrel's focus programs (`dv/tests/programs/focus.hex`, `rv32ui_ops.hex` — copy the hex files into merlin's `programs/`, note provenance): run to halt, diff the RVFI trace against `RV32IInterpreter` (all fields), plus a mem_wait-pulse case (Review Focus 5).
- [ ] **Step 2: Run, FAIL** (no RTL).
- [ ] **Step 3: Implement `merlin_core`** top-down: fetch/PC mux (redirect from EX), four register instances, hazard unit, EX (ALU + branch comparator — kestrel's shared signed/unsigned comparator logic carries), MEM (LS datapath), WB (regfile write + RVFI).
- [ ] **Step 4: PASS;** filelist registry check.
- [ ] **Step 5: Commit.**

### Task 4: Directed hazard suite

**Files:**
- Create: `projects/components/riscv-ip/merlin-rv32i/dv/tests/programs/hazard_*.hex` (hand-assembled, one per case) + `dv/tests/test_merlin_hazards.py`

**Interfaces:** consumes Task 3's bench + golden interpreter.

Cases (each is a program whose RVFI trace is golden-diffed): `forward_matrix` (every producer stage × both operands), `loaduse_matrix` (dependent at distance 0/1/2 — distance 0 must cost exactly one bubble: also assert cycle count from the trace), `branch_after_alu` (Review Focus 1), `store_data_forward` (Focus 2), `flush_during_loaduse` (Focus 3), `jalr_forward`, `branch_flush_backtoback`.

- [ ] **Step 1: write the programs + failing test** (test enumerates cases like kestrel's `CASES` dict).
- [ ] **Step 2: FAIL → Step 3: fix what the suite catches → Step 4: PASS.**
- [ ] **Step 5: Commit.**

### Task 5: rv32ui battery + spike lockstep

**Files:**
- Create: `dv/tbclasses/merlin/rv32ui_battery.py` (adapt kestrel's: normalize/re-key vendor `rv32ui-p-*` images, run to halt/tohost/timeout, gp==1 verdict, func-level RVFI+spike diff)
- Create: `dv/tests/test_merlin_rv32ui.py`, `dv/tests/test_merlin_fuzz.py` (port kestrel's fuzz seeds pattern)

- [ ] **Step 1: battery runner + test wired (fails until green).**
- [ ] **Step 2: run battery — 42/42** at gate level; func level adds the spike commit-log lockstep (`spike --isa=RV32I -l --log=...`).
- [ ] **Step 3: Commit.**

### Task 6: riscv-formal retire checks

**Files:**
- Create: `formal/merlin/riscv-formal/` mirroring `formal/kestrel/riscv-formal/`: `formal_merlin.sv` (NRET=1 wrapper binding merlin's RVFI), `checks.cfg`, per-check `.sby` set (same check list as kestrel's), `Makefile`, `.gitignore`

- [ ] **Step 1: copy and adapt the harness;** `make -C formal/merlin/riscv-formal` runs the insn/pc/reg checks against WB-stage retirement.
- [ ] **Step 2: all checks PASS** (or reach kestrel's documented depth/status where a check is bounded).
- [ ] **Step 3: Commit.**

### Task 7: GTKW + doc skeletons + vault closeout

**Files:**
- Create: `projects/components/riscv-ip/merlin-rv32i/dv/tests/GTKW/merlin_tb_top/merlin_tb_top.gtkw` (groups: halt, fetch, pipeline regs `u_core.q_if_id` etc., hazard (fwd/stall/flush), data-memory, regfile write, RVFI — kestrel/gatling precedent)
- Create: `docs/merlin_has/` + `docs/merlin_mas/` skeleton chapters under `merlin-rv32i/docs/` (hazard/forwarding chapter stubs naming the two waveforms)
- Modify: `vault/tracking/projects/components/riscv-ip/merlin-rv32i/` — `git mv` TASK-001 to `closed/`, INDEX counts, area README status note if one exists

- [ ] **Step 1: author the .gtkw; verify every signal against a real `WAVES=1` FST dump** (fst2vcd header cross-check, the kestrel/gatling method from 2026-10-30).
- [ ] **Step 2: doc skeletons; link ratchet + task-id gates.**
- [ ] **Step 3: Commit + close TASK-001.**

---

## Self-review notes

- Spec coverage: PRD §4.1 (T1/T3), §4.2 (T2/T4), §4.3 (T3), §4.4 (T3/T6), §5 (T4/T5/T6/T7), §7 sequencing items 2–4 (T1–T6), books (T7 skeletons; full book prose is a follow-on task, say so when closing).
- Deliberately out of scope (PRD §2): prediction, CSRs beyond the stub, M/A/F, caches, MonBus.
- `rv32i_regfile` family consolidation in `common-rv32i`: noted as follow-up in Task 3, not silently forked.
