# scoria advanced modes (TASK-001) implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land TASK-001's bounded commodity tranche — demand-aware elastic refresh (Mode A), temperature-compensated refresh (Mode B), ZQCS placement policy (Mode C) — behind CSRs in scoria, with the survey written into design-requirements §6.

**Architecture:** Three new CSR-selected behaviors in the two existing maintenance FUBs (`scoria_refresh_ctrl`, `scoria_zq_ctrl`), all gated so reset = baseline bit-identical. New CSR fields fit in reserved bits of `REF_CTRL`/`ZQ_CFG`; two telemetry registers append after `STALL_ZQ`. CSR fields ride the existing `scoria_csr` → `scoria_top` → `scoria_core` → `scoria_mem_cmd_scheduler` → FUB wiring. DV extends the existing FUB/macro test files with new `TEST_TYPE` cases; formal extends the existing `formal/scoria/refresh_ctrl` proof.

**Tech Stack:** SystemVerilog RTL, PeakRDL (`bin/peakrdl_generate.py`), cocotb + Verilator (`dv/tests` Makefiles), SymbiYosys (formal/scoria), Vivado batch (BUG-003 OOC flow).

**Spec:** `docs/superpowers/specs/2026-10-03-scoria-advanced-modes-design.md`

## Global Constraints

- **Reset = baseline, bit-identical.** Every new field resets so today's behavior is unchanged; new branches are gated by their enable (Mode A: `elastic_en`, Mode B: `tcr_en`, Mode C: `placement=0`). No new "shipped exception" to the pumice rule.
- **RDL regeneration:** `python3 bin/peakrdl_generate.py projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_csr.rdl -o projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/regs/generated --no-html` — never raw peakrdl. Generated RTL + Python regmap + markdown docs land in the same commit as the RDL change.
- **JEDEC law unchanged:** the ±8 postpone/pull-in ceiling stands; no timing-parameter semantics change. Modes are scheduling policy only.
- **No offsets move.** New fields consume reserved bits only: `REF_CTRL[31:13]` (19 bits), `ZQ_CFG[15:1]` (15 bits); new registers append at `0x184`/`0x188` (free tail before `ID @ 0xFF0`).
- **No assertions in RTL** (standing rule); new checkable properties go in `formal/scoria/refresh_ctrl`.
- **House RTL style:** match the file being edited (`r_`/`w_` prefixes, `mc_clk`/`mc_rst_n`, existing reset/flop pattern, module header updated with the new contract text).
- **Gates before any commit of RTL:** `make run-all-func` green in `dv/tests`, `make lint-all` green in `rtl/`, `bin/check_task_ids.py` green after any vault touch.

## Review Focus

Input classes the spec implies but a naive test would miss — each is pinned to a task below:

1. **`elastic_en=0` with garbage threshold CSRs** — thresholds must be unread when disabled; bit-identical means any value, not just zero. → Task 3 test `elastic_disabled_ignores_thresholds`.
2. **`trefi_derate_i = 3` (illegal encoding)** — must clamp to 4x (shift 2), never shift by 8. → Task 4 test `tcr_derate_illegal_clamps`.
3. **Flickering demand during ZQ deferral** (1-cycle pulses) — must neither deadlock ZQCS nor fire early; `overdue_max=0` under perpetual demand is documented starvation (observable, not a hang). → Task 5 test `placement_flicker_demand`.
4. **`tcr_en` flipped mid-stream** — the derated value takes effect from the next counter reload; a derated interval of 0..3 cycles must still be bounded by the pending ceiling (no wedge). → Task 4 test `tcr_derate_small_interval_bounded`.
5. **`placement` switched mid-deferral** — exiting deferral on policy change must not double-issue or lose the interval tick. → Task 5 test `placement_switch_mid_defer`.

---

### Task 1: Docs — design-requirements §6 + PRD/HAS pointers

**Files:**
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/design-requirements.md` (append after §5)
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/PRD.md` (roadmap "Later" bullet)
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/scoria_has/ch06_integration/01_verification_open.md` (dated note in the Status section)

**Interfaces:**
- Produces: the section text the RTL tasks and the vault close-out cite — §6 with the three modes named `elastic refresh` / `TCR` / `ZQCS placement`, and the deferred table (RAIDR, ChargeCache, PARA, SALP, power-down) with unblock conditions verbatim from spec §6.

- [ ] **Step 1: Write `## 6. Advanced modes — selectable scheduling / refresh (characterization)`** in `design-requirements.md`

Mirror pumice's advanced-modes chapter shape (one-bitstream characterization, config-not-param, red→green serial, STATS telemetry), then: (a) per-mode implementation-depth subsections for Modes A/B/C with the exact CSR names/defaults from Task 2 (`REF_CTRL.elastic_en`, `.pullin_idle_streak`, `.postpone_demand_streak`, `.tcr_en`, `.trefi_derate`; `ZQ_CFG.placement`, `.overdue_max`); (b) the deferred-candidates table with the spec's named unblock conditions; (c) the classification of all eight TASK-001 seeds (commodity-legal vs model-only vs already-inherited).

- [ ] **Step 2: Update PRD roadmap** — replace the "Later: … TASK-001 …" bullet with: bounded tranche (elastic refresh / TCR / ZQ placement) landed behind CSRs; survey and deferred conditions in `design-requirements.md` §6; deferred tranche filed as TASK-009.

- [ ] **Step 3: HAS Ch 6 note** — in the "Status, 2026-10-03" section of `01_verification_open.md`, append one dated line: 2026-10-03, TASK-001's bounded tranche exists behind CSRs; per-mode design in `design-requirements.md` §6; block-by-block confirmation is TASK-008's pass.

- [ ] **Step 4: Commit**

```bash
git add projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/design-requirements.md \
        projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/PRD.md \
        projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/docs/scoria_has/ch06_integration/01_verification_open.md
git commit -m "docs(scoria): TASK-001 advanced modes -- design-requirements §6, PRD/HAS pointers"
```

### Task 2: RDL — new CSR fields + regeneration

**Files:**
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_csr.rdl`
- Regenerate: `regs/generated/rtl/scoria_csr.sv`, `regs/generated/rtl/scoria_csr_pkg.sv`, `regs/generated/scoria_csr_regmap.py`, `regs/generated/docs/scoria_csr.md`

**Interfaces:**
- Consumes: nothing (first code task).
- Produces: `hwif_out.REF_CTRL.elastic_en/tcr_en/trefi_derate/pullin_idle_streak/postpone_demand_streak.value`, `hwif_out.ZQ_CFG.placement/overdue_max.value`, `hwif_out.REF_STATS_POSTPONE/REF_STATS_PULLIN.VAL.value` — the exact paths Task 6 wires in `scoria_top.sv`.

- [ ] **Step 1: Write the failing check** — run `python3 -c "import scoria_csr_regmap"`-style name check:

Run: `grep -c 'elastic_en\|tcr_en\|trefi_derate\|pullin_idle_streak\|postpone_demand_streak\|overdue_max\|REF_STATS_POSTPONE\|REF_STATS_PULLIN' projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/regs/generated/scoria_csr_regmap.py`
Expected: FAIL — 0 (fields absent).

- [ ] **Step 2: Edit the RDL** (`scoria_csr.rdl`):

In `REF_CTRL @ 0x140`: rename `RSVD_31_13[31:13]` → `RSVD_12_2[12:2]` and add:
```systemverilog
field { sw = rw; hw = r; desc = "1 = demand-aware elastic refresh (TASK-001 A)"; } elastic_en[13:13] = 1'b0;
field { sw = rw; hw = r; desc = "1 = temperature-compensated refresh (TASK-001 B)"; } tcr_en[14:14] = 1'b0;
field { sw = rw; hw = r; desc = "refresh-rate derate: 0=1x, 1=2x, 2=4x (3 clamps to 4x)"; } trefi_derate[16:15] = 2'h0;
field { sw = rw; hw = r; desc = "idle streak (MC cycles) before pull-in; reset 16 = baseline"; } pullin_idle_streak[24:17] = 8'd16;
field { sw = rw; hw = r; desc = "demand streak before postpone engages; reset 1 = baseline"; } postpone_demand_streak[31:25] = 7'd1;
```
In `ZQ_CFG @ 0xC4` (bits 15:1 currently unused): add `placement[2:1] = 2'h0` (desc "0 = request on expiry (baseline); 1 = defer under demand") and `overdue_max[15:3] = 13'd0` (desc "deferral cap in MC cycles; 0 = uncapped"). Append after `STALL_ZQ @ 0x180`: `REF_STATS_POSTPONE @ 0x184` and `REF_STATS_PULLIN @ 0x188`, each a single `sw = r; hw = w;` 32-bit `VAL` field with the spec's postpone/pull-in counting semantics in the desc.

- [ ] **Step 3: Regenerate**

Run: `python3 bin/peakrdl_generate.py projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_csr.rdl -o projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/regs/generated --no-html`
Expected: four generated files updated, no errors.

- [ ] **Step 4: Re-run the Step-1 check** — Expected: ≥ 8 matches. Then `cd projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl && make lint-all` — Expected: PASS (generated RTL elaborates under verilator/verible).

- [ ] **Step 5: Commit** (RDL + all four generated files together)

```bash
git add projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_csr.rdl projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/regs/generated
git commit -m "feat(scoria): TASK-001 mode CSRs (elastic/TCR/ZQ placement) + regen"
```

### Task 3: Mode A — demand-aware elastic refresh in `scoria_refresh_ctrl`

**Files:**
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_refresh_ctrl.sv`
- Test: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests/fub/test_scoria_refresh_ctrl.py`

**Interfaces:**
- Consumes: Task 2's CSR names (this task only touches the FUB; CSR wiring lands in Task 6).
- Produces: new FUB ports `elastic_en_i`, `pullin_idle_streak_i[7:0]`, `postpone_demand_streak_i[6:0]`, `obs_postpone_events_o[15:0]`, `obs_pullin_events_o[15:0]` (consumed by Task 6 wiring and the macro TB); behavior contract quoted in the module header.

- [ ] **Step 1: Write the failing tests** — add `TEST_TYPE` cases to `test_scoria_refresh_ctrl.py` (house `RefTB` pattern; add the five new DUT inputs to `setup()` with baseline defaults):

  - `elastic_pullin_idle_streak`: `elastic_en=1, pullin_limit=4, pullin_idle_streak=8, demand` drops at t0; assert NO pull-in grant path fires before 8 idle cycles (pull-in headroom unused), and a REF is requested within 1 cycle after the 8th idle cycle with `pending>0`.
  - `elastic_postpone_sustained_demand`: `elastic_en=1, postpone_limit=3, postpone_demand_streak=16`; demand pulses 4 cycles on/4 off (sporadic): assert requests fire on every expiry (strict behavior, `pending` never exceeds 1); then demand held 16+ cycles: assert `pending` grows to `postpone_limit+1` before request.
  - `elastic_disabled_ignores_thresholds` (Review Focus 1): `elastic_en=0`, `pullin_idle_streak=200, postpone_demand_streak=100`: assert trace equals the `smoke` case's request timing exactly (compare `obs_refi_cnt_o` reload values and request cycle numbers).
  - Add all three to `_FUNC`.

- [ ] **Step 2: Run to verify red**

Run: `cd projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests && make run-scoria_refresh_ctrl-func AREAS=fub`
Expected: FAIL — new ports don't exist (`elastic_en_i` undefined on DUT).

- [ ] **Step 3: Implement in `scoria_refresh_ctrl.sv`**

Add the five ports. Replace the hardcoded 16-cycle idle confirmation (`w_idle`, lines ~266-269) with `w_idle = (r_idle_streak >= (elastic_en_i ? pullin_idle_streak_i : 8'd16))`; add a demand-streak counter `r_demand_streak`; replace the request equation (lines ~285-288) with:
```systemverilog
assign w_req = enable_i
    && (w_idle ? ((r_pending > 0) || (r_pullin < w_pull_eff))
               : (elastic_en_i && (r_demand_streak < postpone_demand_streak_i)
                    ? (r_pending > 0)          // sporadic demand: strict
                    : (r_pending > w_post_eff)));// sustained demand: postpone
```
Increment `obs_postpone_events_o` on each refi expiry where the request is withheld solely by the sustained-demand branch; increment `obs_pullin_events_o` on each `w_grant_early`. Update the module header contract. When `elastic_en_i=0` the equation reduces to today's text bit-for-bit.

- [ ] **Step 4: Run to verify green** — same command as Step 2. Expected: PASS (including the pre-existing cases).

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_refresh_ctrl.sv projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests/fub/test_scoria_refresh_ctrl.py
git commit -m "feat(scoria): TASK-001 Mode A -- demand-aware elastic refresh"
```

### Task 4: Mode B — temperature-compensated refresh (tREFI derate)

**Files:**
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_refresh_ctrl.sv`
- Test: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests/fub/test_scoria_refresh_ctrl.py`

**Interfaces:**
- Consumes: Task 3's file (same module).
- Produces: new FUB ports `tcr_en_i`, `trefi_derate_i[1:0]`; consumed by Task 6.

- [ ] **Step 1: Write the failing tests** — new `TEST_TYPE` cases:
  - `tcr_derate_intervals`: `tcr_en=1` with `trefi_derate` 0/1/2: assert request spacing equals `t_refi_i`, `t_refi_i/2`, `t_refi_i/4` (measure via `obs_refi_cnt_o` reloads, tolerance ±1 cycle).
  - `tcr_derate_illegal_clamps` (Review Focus 2): `trefi_derate=3` behaves exactly as `=2`.
  - `tcr_derate_small_interval_bounded` (Review Focus 4): `t_refi_i=8, trefi_derate=2` (interval 2): assert requests bounded by the pending ceiling — no wedge, `pending_refreshes_o ≤ 8`, grants drain it.
  - `tcr_disabled_bitidentical`: `tcr_en=0` with `trefi_derate=2` → identical timing to `smoke`.

- [ ] **Step 2: Run red** — same make target. Expected: FAIL (`tcr_en_i` undefined).

- [ ] **Step 3: Implement** — add the two ports; in the interval logic (lines ~116-119, 169-175) apply the derate to the effective interval after the REFab/REFpb mux:
```systemverilog
assign w_derate_shift = (!tcr_en_i) ? 2'd0 : (trefi_derate_i > 2'd2) ? 2'd2 : trefi_derate_i;
// r_refi_cnt reloads from (w_refi_eff >> w_derate_shift)
```
Header contract updated.

- [ ] **Step 4: Run green** — Expected: all refresh cases PASS.

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_refresh_ctrl.sv projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests/fub/test_scoria_refresh_ctrl.py
git commit -m "feat(scoria): TASK-001 Mode B -- TCR tREFI derate"
```

### Task 5: Mode C — ZQCS placement policy in `scoria_zq_ctrl`

**Files:**
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_zq_ctrl.sv`
- Test: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests/fub/test_scoria_zq_ctrl.py`

**Interfaces:**
- Consumes: Task 2's CSR names.
- Produces: new FUB ports `placement_i[1:0]`, `overdue_max_i[12:0]`; consumed by Task 6.

- [ ] **Step 1: Write the failing tests** — new `TEST_TYPE` cases (house `ZqTB` pattern):
  - `placement_defers_under_demand`: `placement=1, overdue_max=0`; keep `demand_i=1` from interval expiry: assert `zq_req_o` stays low ≥ 40 cycles, then drop demand: assert request within 2 cycles.
  - `placement_overdue_max_forces_request`: `placement=1, overdue_max=10`, demand held: assert request fires 10±1 cycles after expiry despite demand, and exactly one ZQCS issues.
  - `placement_flicker_demand` (Review Focus 3): 1-cycle demand pulses every 3 cycles, `overdue_max=0`: assert deferral continues (no early fire) and, after pulses stop, the request fires; assert traffic was never blocked (no grant dependency change).
  - `placement_switch_mid_defer` (Review Focus 5): start `placement=1` with demand, then write `placement=0` mid-deferral: assert the request asserts at the next cycle after the write (no double interval consumption; `obs_zqcs_total_o` increments by exactly 1).
  - `placement_zero_bitidentical`: `placement=0` equals the existing `smoke`/`repeats` traces.

- [ ] **Step 2: Run red** — `cd projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests && make run-scoria_zq_ctrl-func AREAS=fub`. Expected: FAIL (`placement_i` undefined).

- [ ] **Step 3: Implement in `scoria_zq_ctrl.sv`** — add the two ports; in `ZQ_IDLE`, when `r_interval == 0` and `placement_i == 2'd1` and `demand_i` is high: hold in a deferral sub-state (add `ZQ_DEFER` to the enum, value `2'd3`), counting `r_defer_cnt`; exit to `ZQ_REQ` when `!demand_i` or (`overdue_max_i != 0 && r_defer_cnt >= overdue_max_i`). `zq_req_o` asserts only in `ZQ_REQ` (unchanged). `obs_overdue_o` additionally set during `ZQ_DEFER`. When `placement_i == 0` the FSM never enters `ZQ_DEFER` — bit-identical. Header contract updated.

- [ ] **Step 4: Run green** — Expected: all zq cases PASS.

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/fub/scoria_zq_ctrl.sv projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests/fub/test_scoria_zq_ctrl.py
git commit -m "feat(scoria): TASK-001 Mode C -- ZQCS defer-under-demand placement"
```

### Task 6: Hierarchy wiring + macro composition tests

**Files:**
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_mem_cmd_scheduler.sv` (ports at lines ~118-140; FUB instantiations at ~340-400)
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/top/scoria_core.sv` (ports + pass-through at the scheduler instantiation ~525-675)
- Modify: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/top/scoria_top.sv` (hwif wiring at ~362-380; core instantiation at ~287)
- Test: `projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests/macro/test_scoria_mem_cmd_scheduler.py` (+ `dv/tbclasses/scoria_mem_cmd_scheduler_tb.py` `_drive_idle` defaults)

**Interfaces:**
- Consumes: Task 2 hwif paths; Task 3/4/5 FUB ports.
- Produces: working end-to-end CSR→FUB paths named `ref_elastic_en_i`, `ref_pullin_idle_streak_i[7:0]`, `ref_postpone_demand_streak_i[6:0]`, `ref_tcr_en_i`, `ref_trefi_derate_i[1:0]`, `zq_placement_i[1:0]`, `zq_overdue_max_i[12:0]` on the scheduler/core/top; `REF_STATS_POSTPONE/PULLIN` inputs fed from the new obs outputs.

- [ ] **Step 1: Write the failing macro tests** — add to `test_scoria_mem_cmd_scheduler.py`:
  - `elastic_refresh_in_traffic`: sustained CAM demand + `ref_elastic_en_i=1, ref_postpone_demand_streak_i=16`: assert refresh request appears only after 16 sustained demand cycles and commands stay history-clean.
  - `tcr_doubles_rate`: `ref_tcr_en_i=1, ref_trefi_derate_i=1` vs 0: assert ≥ 1.8x REF count in a fixed 2000-cycle window with `CMD_HISTORY_EN=1`.
  - `zqcs_defer_under_demand`: `zq_enable=1, zq_interval=20, zq_placement_i=1, zq_overdue_max_i=0` with continuous read traffic: assert no ZQCS within 100 cycles while traffic persists; drain CAMs: assert ZQCS within 20; then `zq_overdue_max_i=8` rerun: assert ZQCS within ~28 cycles despite demand.

- [ ] **Step 2: Run red** — `cd projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests && make run-scoria_mem_cmd_scheduler-func AREAS=macro`. Expected: FAIL (scheduler ports undefined / TB driving absent ports).

- [ ] **Step 3: Wire the hierarchy** — add the seven new scheduler input ports and two new observable outputs, and connect the inputs through to the FUB instances (`elastic_en_i`, `pullin_idle_streak_i`, `postpone_demand_streak_i`, `tcr_en_i`, `trefi_derate_i` on `scoria_refresh_ctrl`; `placement_i`, `overdue_max_i` on `scoria_zq_ctrl`); mirror the ports on `scoria_core` and connect at its scheduler instantiation; in `scoria_top.sv` wire each from the corresponding `hwif_out...value` and connect the two `REF_STATS` inputs from the new `obs_postpone_events_o`/`obs_pullin_events_o` scheduler outputs. In the macro TB `_drive_idle`, default the new scheduler inputs to baseline (enables 0, streaks 16/1, derate 0, placement 0, overdue 0).

- [ ] **Step 4: Run green** — macro target plus `make run-all-func AREAS=fub` (FUB suites still green after port additions). Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/macro/scoria_mem_cmd_scheduler.sv \
        projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/top/scoria_core.sv \
        projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/rtl/top/scoria_top.sv \
        projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests/macro/test_scoria_mem_cmd_scheduler.py \
        projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tbclasses/scoria_mem_cmd_scheduler_tb.py
git commit -m "feat(scoria): TASK-001 wire mode CSRs through scheduler/core/top + macro tests"
```

### Task 7: Formal — re-prove `refresh_ctrl` with the new modes

**Files:**
- Modify: `formal/scoria/refresh_ctrl/formal_scoria_refresh_ctrl.sv`
- Modify: `formal/scoria/refresh_ctrl/scoria_refresh_ctrl.sby` (only if depth must rise)

**Interfaces:**
- Consumes: Task 3/4 RTL.
- Produces: green `make prove` for the refresh_ctrl block with modes present.

- [ ] **Step 1: Run the existing proof unchanged against the new RTL** — `cd formal/scoria/refresh_ctrl && make prove`. Expected: PASS. This is the regression gate: the RTL tasks changed `w_req`, the interval reload, and the FSM, so the pre-existing retention/accounting/rotor properties must still hold with the new ports at their resets. If any fails, stop and debug the RTL (the property is telling you the modes broke the baseline) — do not weaken the property.

- [ ] **Step 2: Extend the wrapper with the mode properties** — add the seven new DUT inputs as wrapper inputs and add:
  - `a_defaults_baseline`: `!elastic_en_i |-> (w_req == (enable_i && (w_idle_baseline ? ((r_pending > 0) || (r_pullin < w_pull_eff)) : (r_pending > w_post_eff))))` — with `w_idle_baseline` the 16-cycle form.
  - `a_ceiling_with_modes`: existing `a_pending_ceiling` / credit properties re-asserted with all new CSR inputs free (unconstrained).
  - `a_derate_bound`: `tcr_en_i |-> (r_refi_cnt <= (w_refi_eff >> ((trefi_derate_i > 2) ? 2 : trefi_derate_i)))` after each reload.
  - cover points: pull-in at the streak boundary; postpone branch entered and exited.

- [ ] **Step 3: Prove green** — `make prove` again. If BMC depth 34 is insufficient for the streak counters (a cex at exactly the boundary), raise `depth` to 48 in `scoria_refresh_ctrl.sby` and re-run. Expected: PASS (smtbmc bitwuzla, no cex). Note in the commit if the depth changed and why.

- [ ] **Step 4: Commit**

```bash
git add formal/scoria/refresh_ctrl
git commit -m "formal(scoria): TASK-001 refresh_ctrl modes re-proved (elastic/TCR)"
```

### Task 8: Full gates, BUG-003 re-measure, vault close-out

**Files:**
- Modify: `vault/Tasks/scoria-ddr3-lpddr3/task/open/TASK-001.md` (→ closed)
- Create: `vault/Tasks/scoria-ddr3-lpddr3/task/deferred/TASK-009.md`
- Modify: `vault/Tasks/scoria-ddr3-lpddr3/task/INDEX.md`, `vault/Tasks/scoria-ddr3-lpddr3/INDEX.md`
- Modify: `vault/Tasks/scoria-ddr3-lpddr3/bug/open/BUG-003.md` (measurement row only — stays open)

**Interfaces:**
- Consumes: all prior tasks.
- Produces: closed TASK-001, deferred TASK-009, updated INDEXes, fresh BUG-003 timing row.

- [ ] **Step 1: Full regression + lint**

Run: `cd projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests && make clean-all && make run-all-func` then `cd ../../rtl && make lint-all`
Expected: PASS both. Record the new test count for the vault note.

- [ ] **Step 2: BUG-003 OOC re-measure** — `command -v vivado` first; if present, run the bug's own repro flow (`BRIDGE_TOP=scoria_top BRIDGE_PART=xc7k325tffg900-2 BRIDGE_CLK_NS=10.0`, `monitor_synth.tcl`, ~3 min) and append a dated row (WNS reg2reg, fmax, LUTs, FFs, levels) to BUG-003 with a one-line note that refresh/zq changed but the arbiter cone did not. If vivado is absent, record "flow not runnable in this environment" in the commit message instead — do not skip silently.

- [ ] **Step 3: Vault close-out** — TASK-001: tick the per-bank-refresh carry-forward and survey items, mark the deferred seeds as deferred-to-TASK-009 with §6 conditions, Status CLOSED 2026-10-03, `git mv` to `closed/`. Create `TASK-009` in `deferred/` (RAIDR / ChargeCache / PARA / SALP-andesite / power-down, each with its spec §6 unblock condition; power-down notes it reverses the 2026-09-30 HAS decision and needs the owner). Update `task/INDEX.md` (open 4→3, closed 4→5, deferred 0→1, Next ID TASK-010) and area `INDEX.md` (task Next ID `TASK-010`).

- [ ] **Step 4: Final gates** — `bin/check_task_ids.py` PASS; `git status` clean.

- [ ] **Step 5: Commit + push**

```bash
git add vault/Tasks/scoria-ddr3-lpddr3
git commit -m "docs(scoria): close TASK-001, file deferred TASK-009, BUG-003 re-measured"
git push origin main
```
