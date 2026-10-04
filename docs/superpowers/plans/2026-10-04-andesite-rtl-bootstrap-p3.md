# andesite RTL bootstrap P3 (modified + new FUBs) — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the modified and new FUB tier: `addr_mapper` (with the P2-re-sequenced intakes behind it), `global_timers`, the scheduler pair, `refresh_ctrl` (FGR), `zq_ctrl` + MPC submodule, `odt_ctrl`, the training trio + parity-recovery FSM, and the DFI datapath — completing the 26-FUB inventory before P4's macros/top.

**Architecture:** Carried-MODIFIED blocks follow the P2 discipline: scoria's module carried rename/import-only, then the andesite delta applied on top as a *recorded exception* the toothed carry-diff gate (`dv/bin/check_carry_diff.sh`, fixed in P2) verifies — every scoria line present modulo renames, additions exactly the named set. NEW blocks build to the MAS pages with model-first tests. Suites: scoria's ported where they exist; MAS-driven new tests elsewhere.

**Tech Stack:** SystemVerilog (Verilator/Verible), cocotb + pytest, the P0-P2 scaffolding.

**Spec:** `docs/superpowers/specs/2026-10-04-andesite-rtl-bootstrap-design.md` §3 P3/P4. Plans: P0+P1 and P2 (landed). Books: the andesite MAS ch02 pages are per-block design authority; scoria's RTL + books for the carried halves.

## Global Constraints

- Carry rules: P2's Global Constraints carry over verbatim, with the toothed gate. Each carried-MODIFIED task records its exception set (the andesite delta) in its commit and passes it to the gate as the regex (+ `additive` where the growth is purely additive); the gate's deletion-side policing is what protects scoria's logic.
- New-block rules: MAS ch02 page is the contract (ports, FSM fences, anchors); TDD red first; no invented JEDEC numbers (named CSRs / Q1 placeholders per the books); no assertions in RTL except the checker's carried `$fatal` discipline (verification-side block).
- Suites: port scoria's where present; MAS-driven tests for andesite-only surfaces. The fires_* / fatal-text pattern from the checker suite is the model for any check that must be proven armed.
- Naming/filelists/lint/venv/commit prefixes unchanged. One commit per task; `python3 bin/check_task_ids.py` PASS before every commit.
- CITES migration: when a block whose MAS page carries kmap citations lands, the generator's CITES re-point at the RTL lines (P1 did the formatter; P3 does mode_register + addr_mapper at the gate task). The generator must exit 0 after every re-point, and reruns stay byte-identical.

## Review Focus

1. **Carry-then-delta ordering** — the delta must be legible as additions/modifications ON the carried base (the gate enforces deletions-side); a rewrite wearing a carry's clothes is the failure mode.
2. **L/S semantics at the scheduler** — same-group vs cross-group selection must come from the mapped bank group of both the candidate and the last-issued command; a scheduler that special-cases LPDDR4 with an if-memtype instead of degenerating through the parameterization repeats the reviewed bug class.
3. **FGR on the inherited base** — refresh_ctrl keeps scoria's landed TASK-001 modes byte-behaviorally and adds FGR as interval arithmetic (reload-only rule); a mode that disturbs the elastic/TCR/credit machinery is a regression.
4. **Recovery FSM isolation (TASK-006)** — the parity/alert recovery sub-FSM must sit beside the init FSM and never touch the bank machine; the scheduler sees a retract, not a new maintenance class.
5. **MPC opcode honesty** — zq_ctrl's LPDDR4 MPC path and the CA-training interface must not invent MPC opcode encodings; the LPDDR4 CA encodings are TBC(JESD209-4) until the cold-storage read, so the submodule carries the issue ports and a documented stub posture.

---

## File Structure

Carried-MODIFIED (`rtl/fub/`): `andesite_addr_mapper.sv`, `andesite_global_timers.sv`, `andesite_cmd_arbiter.sv`, `andesite_mem_cmd_scheduler.sv` (macro-tier module, carried to rtl/macro/), `andesite_refresh_ctrl.sv`, `andesite_zq_ctrl.sv`, `andesite_wrlvl_ifc.sv`, `andesite_dfi_cmd_path.sv`, `andesite_dfi_rd_aligner.sv`, `andesite_dfi_wr_serializer.sv`.
Carried (behind addr_mapper, per the P2 ruling): `andesite_rd_intake.sv`, `andesite_wr_intake.sv`.
NEW: `andesite_odt_ctrl.sv`, `andesite_rdlvl_ifc.sv`, `andesite_ca_train_ifc.sv`, + the MPC submodule (inside zq_ctrl per its MAS page) + the alert-recovery sub-FSM (inside init_sequencer per its MAS page).
Filelists per module; suites ported/created per task.

### Task 1: `andesite_addr_mapper` — the decode grows bank groups (+ the intakes behind it)

**Files:** Create `rtl/fub/andesite_addr_mapper.sv`, `andesite_rd_intake.sv`, `andesite_wr_intake.sv` + filelists + ported suites (scoria has suites for the intakes and the mapper — verify at Step 1; the arbiter suite's mocks referenced the mapper too).

**Interfaces:**
- Produces: `andesite_addr_mapper` with scoria's port list PLUS `bg_o` (the MODIFIED delta, MAS 04); `andesite_rd_intake`/`andesite_wr_intake` carried rename-only (they instantiate the mapper — in-set rename).
- Design authority: MAS `ch02_blocks/04_addr_mapper.md` (decode fence anchor; BG between CS and bank); scoria's mapper for the carried base.

- [ ] **Step 1:** Scan scoria's addr_mapper/rd_intake/wr_intake sources + suite inventory; pin the carry exceptions (mapper: +`bg_o` and its decode; intakes: in-set instantiation rename only). Port suites, renamed: RED.
- [ ] **Step 2:** Carry all three (rename/import/header); apply the mapper delta: `bg_o` from the bank-group field per the MAS fence (symbolic decode structure preserved; the group select is a function of the address per the ADDR_MAP-style CSR config scoria carries). GREEN (suites + gate with the recorded exception).
- [ ] **Step 3:** Lint + commit `feat(andesite): addr_mapper with bank-group decode; intakes carried behind it (P3 t1)`.

### Task 2: `andesite_global_timers` — the long/short pairs

**Files:** Create `rtl/fub/andesite_global_timer(s).sv` + filelist + ported suite (scoria's global_timers suite exists — verify).

**Interfaces:**
- Produces: `andesite_global_timers` with scoria's ports PLUS the tCCD_L/S, tRRD_L/S counter set (MODIFIED delta; MAS 05 names them; cmd_history_checker's new parameters consume the same names).
- The inherited next-state fix carries with the block (the MAS/HAS "inherit the FIXED form" note).

- [ ] **Step 1:** Scan + pin exceptions (the L/S counter additions + their readiness outputs); port suite: RED.
- [ ] **Step 2:** Carry + delta; the L/S readiness flags follow the same next-state-function discipline (both counter and status from one next-state — the pumice ISSUE-018 fix shape). GREEN + gate + lint.
- [ ] **Step 3:** Commit `feat(andesite): global_timers with the L/S pairs on the fixed next-state base (P3 t2)`.

### Task 3: Scheduler pair — `andesite_cmd_arbiter` + `andesite_mem_cmd_scheduler`

**Files:** Create `rtl/fub/andesite_cmd_arbiter.sv`, `rtl/macro/andesite_mem_cmd_scheduler.sv` + filelists + ported suites (scoria's cmd_arbiter + scheduler suites exist).

**Interfaces:**
- Produces: the scheduler pair with L/S-aware admission (MAS 05's fence anchor: `issue_ok = timers.ok AND group(last) checks`); maintenance request/grant channel with the source tag; LPDDR4 degenerates L=S through the parameterization (Review Focus 2).

- [ ] **Step 1:** Scan scoria's arbiter/scheduler + suites; pin exceptions (L/S admission inputs from the timers/addr_mapper; the maintenance tag). RED.
- [ ] **Step 2:** Carry + delta per MAS 05. Suite extension: same-group vs cross-group issue cases proving tCCD_L gates same-group and tCCD_S permits cross-group at the arbiter's pick. GREEN + gate + lint.
- [ ] **Step 3:** Commit `feat(andesite): scheduler pair with bank-group-aware L/S admission (P3 t3)`.

### Task 4: `andesite_refresh_ctrl` — FGR on the inherited base

**Files:** Create `rtl/fub/andesite_refresh_ctrl.sv` + filelist + ported suite (scoria's refresh_ctrl suite + formal evidence carried in the comment).

**Interfaces:**
- Produces: refresh_ctrl with scoria's landed modes (elastic/TCR/credit window) byte-behavioral PLUS the FGR interval arithmetic (MAS 06's fence: factor select, tREFI reload, tRFC-per-density; clamp rule carried from the mode_register posture).

- [ ] **Step 1:** Scan + pin exceptions (FGR factor input, per-density tRFC, the reload-only scaling). Port scoria's suite: RED.
- [ ] **Step 2:** Carry + FGR delta. New tests: per-factor interval scaling (1x/2x/4x reload values), the retention credit window scaled per factor, modes-still-clean when FGR changes mid-run (reload-only). GREEN + gate + lint.
- [ ] **Step 3:** Commit `feat(andesite): refresh_ctrl -- FGR 1x/2x/4x on the inherited TASK-001 base (P3 t4)`.

### Task 5: `andesite_zq_ctrl` + the MPC submodule

**Files:** Create `rtl/fub/andesite_zq_ctrl.sv` + filelist + ported suite (scoria's zq_ctrl suite exists).

**Interfaces:**
- Produces: scoria's zq_ctrl carried (DDR4 core byte-behavioral: interval CSR, request-and-wait, placement policy) PLUS the NEW LPDDR4 MPC submodule per MAS 07 — issue ports and FSM states named there; **no MPC opcode encodings invented** (Review Focus 5): the submodule drives the formatter's CA path at the protocol level with the opcode as an input image (TBC(JESD209-4)).

- [ ] **Step 1:** Scan + pin exceptions (MPC submodule = additive; a `memtype_i`-gated branch selects the issue path). Port suite: RED.
- [ ] **Step 2:** Carry + submodule. New tests: MPC submodule FSM states per the MAS fence (IDLE→ISSUE→WAIT→DONE), request/grant discipline, interval reload; DDR4 suite still green (the inherited core untouched). GREEN + gate + lint.
- [ ] **Step 3:** Commit `feat(andesite): zq_ctrl carried; LPDDR4 MPC submodule added, encodings TBC (P3 t5)`.

### Task 6: `andesite_odt_ctrl` — NEW

**Files:** Create `rtl/fub/andesite_odt_ctrl.sv` + filelist + new suite.

**Interfaces:**
- Produces: the policy block per MAS 08 (policy-state fence; command-stream tap; ODTL CSR latencies; rank coupling; init-seam ownership note). LPDDR4 paragraph: MR-programmed termination is init-side; the block is DDR4-scoped.

- [ ] **Step 1:** New-suite RED per MAS 08: policy transitions on the grant tap (IDLE→PARK, WR-self→RTT_WR, RD-other→NOM, RD-self→ODT off), latency enforcement on the pin, the init seam.
- [ ] **Step 2:** Implement; GREEN + lint (no carry gate — new block).
- [ ] **Step 3:** Commit `feat(andesite): odt_ctrl -- dynamic ODT policy block (P3 t6, NEW)`.

### Task 7: Training trio + the parity-recovery FSM

**Files:** Create `rtl/fub/andesite_wrlvl_ifc.sv` (carried), `andesite_rdlvl_ifc.sv`, `andesite_ca_train_ifc.sv` (NEW) + filelists + suites; MODIFY `rtl/fub/andesite_init_sequencer.sv` (append the TASK-006 recovery section per its MAS page — the 3-state sub-FSM, drop/retract/re-issue, telemetry).

**Interfaces:**
- Produces: the training interfaces per MAS 09 (wrlvl contract carried byte-behavioral; rdlvl MPR flow; ca_train MPC flow with no invented opcodes); the recovery FSM beside the init FSM.
- The kmap CITES for the formatter (P1) and the MAS 09 anchors stay MAS-pinned (the CA encodings remain TBC).

- [ ] **Step 1:** Port wrlvl suite (RED); write new-suite REDs for rdlvl/ca_train (handshake sequences per the MAS fences, four-state telemetry); extend the sequencer suite with the recovery FSM cases (alert pulse → ALERT_SEEN → retract → RESENDING → telemetry counters).
- [ ] **Step 2:** Carry wrlvl + build the new interfaces + the recovery FSM. GREEN + gates + lint.
- [ ] **Step 3:** Commit `feat(andesite): training trio + CA-parity recovery FSM (P3 t7)`.

### Task 8: DFI datapath — cmd_path, rd_aligner, wr_serializer

**Files:** Create `rtl/fub/andesite_dfi_cmd_path.sv`, `andesite_dfi_rd_aligner.sv`, `andesite_dfi_wr_serializer.sv` + filelists + suites (scoria's suites for these — verify; likely none → MAS 10-driven tests).

**Interfaces:**
- Produces: cmd_path widened for ACT_n/BG/parity (carried MODIFIED per HAS ch04's inventory); aligner/serializer with DBI pass-through on `dfi_wrdata_mask` per the TASK-005 study (write DBI reuses the mask pins; read DBI reports alongside rddata); write CRC noted inert.

- [ ] **Step 1:** Scan + pin exceptions (widened command pins; DBI mux on the mask path). Suite REDs.
- [ ] **Step 2:** Carry + deltas. GREEN + gates + lint.
- [ ] **Step 3:** Commit `feat(andesite): DFI datapath blocks -- widened cmd path, DBI on wrdata_mask (P3 t8)`.

### Task 9: P3 gate — CITES migration + books + full inventory gate

**Files:** Modify `docs/kmaps/gen_andesite_kmaps.py` (CITES re-points), HAS/MAS ch00 (0.4 rows), `rtl/filelists/andesite_all.f` (completeness).

- [ ] **Step 1:** Re-point the mode_register + addr_mapper CITES at the RTL lines (read the files, pin the lines, update the generator); rerun — exit 0, byte-identical across a 2-second boundary.
- [ ] **Step 2:** HAS/MAS ch00 0.4 rows: the modified/new tier landed; the inventory count line (26 files: 12 carried-inherited + 10 carried-modified + new blocks — count at execution and state it exactly); the MAS 02_what_changes table unchanged (markings copied, not re-derived — re-run the pair extraction as the gate).
- [ ] **Step 3:** Full gate: every suite in dv/tests/{fub,macro} green; `make lint-all`; generator green; `check_task_ids.py`; marking-pair consistency GREEN. Commit `feat(andesite): P3 gate -- modified/new tier complete; 26-FUB inventory closed`.

---

## Self-Review notes

- Spec coverage: P3 per spec §3; P4 (macros/top/full sims) remains the follow-on plan. The parity-recovery FSM (TASK-006) rides Task 7 as the spec's P3 text says.
- Review Focus 1 → per-task gates with recorded exceptions (now toothed). Focus 2 → Task 3's degeneration tests. Focus 3 → Task 4's modes-still-clean test. Focus 4 → Task 7's recovery isolation cases. Focus 5 → Tasks 5/7 opcode posture.
- Interface consistency: the L/S timing names (tCCD_L/S, tRRD_L/S) are fixed here and consumed consistently by global_timers (Task 2), the scheduler (Task 3), and the checker (landed); the `bg` field naming follows addr_mapper (Task 1).
- Proportion: bodies only where scoria leaves the choice open (FGR factor map, MPC FSM states, ODT policy table); carried internals stay in scoria's files, cited.
