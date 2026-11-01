# cache-ip Plane Restructure (amber/jet TASK-002) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Restructure amber and jet into CPU plane / coherence-core plane / fabric plane modules, with the ACE plane swappable for a future CHI plane — zero functional change, every existing suite green.

**Architecture:** `l1_core` (common-ip) becomes an aggregate of `l1_cpu_plane` + `l1_coh_core`; the snoop responder `l1_snoop_resp` moves into the fabric planes (`l1_axi4_plane` pair-rig flavor, `l1_ace_plane` onyx flavor with the merged `l1_ace_issue`); the four tops become thin plane compositions. jet gains `jet_cpu_plane` (frontend + `jet_rsp_seq` + request skid) and `jet_coh_core` extracted from `jet_top`/`jet_ace_top` by move-don't-edit.

**Tech Stack:** SystemVerilog (house style), cocotb Pattern-B suites, SymbiYosys formal, filelist registry.

**Spec:** `docs/superpowers/specs/2026-10-30-cache-ip-plane-restructure-design.md` (owner-approved, incl. the J8–J10 forward-reservation section).

## Global Constraints

- **Zero functional change.** The regression proof is: full amber + jet + common-ip DV suites and the formal harnesses green before and after, plus the `l1_ace_issue` byte-equivalence check (Task 2).
- Plane modules live in `rtl/plane/` (new directory) in common-ip and jet-mesi-l1; every new module gets a filelist + registry entry; removed files (`jet_ace_issue.sv`) get their filelists removed in the same commit.
- House style: `ALWAYS_FF_RST` macros, header comment block per existing modules, no assertions in synthesizable RTL (the sim-only assertion block at `jet_top.sv:1618–1657` moves with its logic or stays at top — decide per task 4, keep it sim-only).
- Instance names are pinned (they minimize DV tap churn): in `l1_core`: `u_cpu`, `u_coh`. In every top: `u_cpu`, `u_coh`, `u_fab`. Inside each fabric plane: `u_snoop` (the responder), `u_rd_monlite`, `u_wr_monlite`, `u_ace_issue` (ACE plane only). Inside `l1_coh_core`/`jet_coh_core`, the existing instance names are preserved verbatim (`u_control`, `u_tag`, `u_data`, `u_repl`, `u_fill`, `u_drain`, `u_monlite`; jet adds `u_mshr`, `u_wb`, `u_jet_monlite`). Inside `l1_cpu_plane`: `u_frontend`; jet's CPU plane adds `u_rsp`, `u_req_skid`.
- Commit gates per task: `bin/filelist_registry.py --check`, `bin/check_broken_links.py --ratchet`, `bin/check_task_ids.py`. Work on main; stage only own files (owner works in parallel on main).
- The J8/J9 forward reservations: the contract doc (Task 5) records them; no RTL for them.

## The tap-retarget table (from the 2026-11-01 inventory — the authoritative checklist)

After the restructure, every path below shifts; the left column is today, the right is the pinned target. The owning task updates the file and re-runs its suite.

| File | Today | After |
|---|---|---|
| `common-ip/dv/tb/l1_monlite_th.sv:256–289` | `u_core.u_control.*` | `u_core.u_coh.u_control.*` |
| `amber-mesi-l1/dv/tb/amber_miss_fill_macro_test.sv:451` | `u_control.victim_way_q` | `u_coh.u_control.victim_way_q` |
| `common-ip/dv/tbclasses/l1_core_tb.py` | `_tap.u_snoop.*`, `_tap.u_control.*`, `_tap.u_repl.*`, `_tap.u_tag.mem` | `_tap.u_snoop.*` stays (Task 1's TB wrapper keeps instance `u_snoop`); control/repl/tag become `_tap.u_core.u_coh.*` |
| `amber-mesi-l1/dv/tbclasses/amber_ace_top_tb.py` | `_tap = dut.u_core`, then `u_snoop`/`u_control` | `_tap = dut`; snoop via `u_fab.u_snoop`, control via `u_coh.u_control` |
| `amber-mesi-l1/dv/tbclasses/amber_pair_rig_tb.py` | `a.u_core.u_snoop/u_control/u_repl/u_tag/u_fill` | `a.u_fab.u_snoop`, `a.u_coh.u_control/u_repl/u_tag/u_fill` |
| `jet-mesi-l1/dv/tbclasses/jet_core_tb.py` | `u.u_snoop`, `u.u_fill`, `u.u_wb`, `u.u_control`, `u.u_mshr`, force on `r_cmt_state` | `u_fab.u_snoop`; rest under `u_coh.*` |
| `jet-mesi-l1/dv/tbclasses/jet_pair_rig_tb.py` | `a.u_snoop`, `a.u_fill`, `a.u_control` | `a.u_fab.u_snoop`, `a.u_coh.*` |
| `jet_top.sv:376`, `jet_ace_top.sv:390` | `u_frontend.stage_wr_ready` | `u_cpu.u_frontend.stage_wr_ready` |
| `l1_core.sv:484, 710–745` (monlite encoder taps) | `u_control.*` | `u_coh.u_control.*` |
| jet tops' monlite encoders (1222–1310 / 1341–1427) | `u_control.*` | `u_coh.u_control.*` |

Memory backdoors into the harness's own memory (`u_mem.u_core.r_mem`) are unaffected.

## Review Focus

1. **Vacuous tap retarget** — a retargeted path that names a real but wrong instance passes silently. Pin: after each task, `grep -rn "u_core\.u_snoop\|u_core\.u_control\|u_top\.u_snoop\|u_top\.u_control\|u_frontend\.stage" projects/components/cache-ip/*/dv/ projects/components/cache-ip/common-ip/rtl/top/ projects/components/cache-ip/*/rtl/top/` must return zero hits (old paths fully gone), and each suite must pass.
2. **`sn_want` sampling shift** — the AC-pending counter moves into the fabric planes; it must sample the AC pin handshake exactly as `jet_top.sv:1144–1159` does today (move verbatim). Pin: jet pair-rig + ace_top snoop-stress suites green.
3. **coh_req collision mux** (fill launch wins, WRITE_BACK replays; `jet_top.sv:1173–1197`) — moves verbatim into `l1_axi4_plane`/`l1_ace_plane`. Pin: jet suites green + code read in review.
4. **`l1_ace_issue` merge** — the two sources are already identical modulo names/comments; the merge is a rename of `amber_ace_issue.sv` to `common-ip/rtl/fub/l1_ace_issue.sv`. Pin: `git diff --no-index <(sed 's/amber_ace_issue/l1_ace_issue/g; ...' old) new` shows only name/comment drift; both ace_top suites green.
5. **`l1_core` loses its responder** — its ACE snoop pins become the seam bundle; a test that still drives ACE pins on `l1_core` fails to compile rather than silently passing, which is the desired failure mode. Pin: `test_l1_core` harness composes the responder (Task 1).

---

### Task 1: common-ip planes — `l1_cpu_plane`, `l1_coh_core`, `l1_core` as aggregate

**Files:**
- Create: `projects/components/cache-ip/common-ip/rtl/plane/l1_cpu_plane.sv` (wraps `l1_cpu_frontend` alone)
- Create: `projects/components/cache-ip/common-ip/rtl/plane/l1_coh_core.sv` (`l1_control` + `l1_tag_array` + `l1_data_array` + `l1_repl` + `l1_fill` + `l1_drain` + `l1_monlite`, plus the integration logic from `l1_core.sv:479–506` (fill-way one-hot, data-write mux) and `678–719` (coh_req sideband, monlite tap encoder — taps become `u_control.*` inside this module))
- Modify: `projects/components/cache-ip/common-ip/rtl/top/l1_core.sv` — becomes `u_cpu` + `u_coh`; **the `u_snoop` instance and the ACE snoop pins leave `l1_core`**: its ports gain the fabric seam bundle (snoop in: `snoop_req/addr/type` → `ready/safe`; snoop out: `crresp`, `cd*` per the existing `ctrl_snoop_*`/`ctrl_cr*` signal shapes; engine seam `fub_axi_*` and `coh_req_*` pass through unchanged)
- Create: `projects/components/cache-ip/common-ip/dv/tb/l1_core_fab_tb.sv` — TB wrapper composing `l1_core` (`u_core`) + `l1_snoop_resp` (`u_snoop`) wired to the seam, exposing the ACE snoop pins the old `l1_core` had, so `test_l1_core`'s stimulus survives
- Modify: `common-ip/dv/tbclasses/l1_core_tb.py` (tap retarget per the table: `_tap = self.dut`; `u_snoop` unchanged via the wrapper; control/repl/tag under `u_core.u_coh.*`), `common-ip/dv/tb/l1_monlite_th.sv`, `amber-mesi-l1/dv/tb/amber_miss_fill_macro_test.sv`
- Filelists: `common-ip/rtl/filelists/plane/l1_cpu_plane.f`, `plane/l1_coh_core.f`, updated `l1_core.f`; DV filelist for the new TB wrapper
- Test: existing `test_l1_core.py`, `test_l1_cpu_frontend.py`, `test_l1_control.py`, the monlite TH suite

**Interfaces:**
- Produces: `l1_cpu_plane(clk, rst_n, cpu_req_wr_*, cpu_rsp_rd_*, fe_req_valid/addr/we/be/wdata, ctrl_req_ready, ctrl_rsp_valid/data)`; `l1_coh_core` ports = today's `l1_core` ports minus the GAXI CPU pins minus the ACE snoop pins, plus the CPU-seam and fabric-seam bundles. `l1_core`'s external port list = today's list with ACE snoop pins replaced by the seam bundle.

- [ ] **Step 1: Baseline** — run the common-ip + amber DV suites green first (`pytest` from each area's `dv/tests/`, `TEST_LEVEL=gate` minimum) and record the counts in the task report.
- [ ] **Step 2: Move-don't-edit** — create the two plane modules by moving the instantiation blocks; `l1_core` recomposes; harness wrapper created. The rule: no logic edits inside moved blocks beyond instance-name renames of taps (`u_control.` → stays `u_control.` inside `l1_coh_core`; the monlite encoder moves with it).
- [ ] **Step 3: Retarget taps** per the table; compile the TBs (failure to compile = a missed pin, the desired failure mode).
- [ ] **Step 4: Suites green** — common-ip full suite + `test_l1_core` at all three geometries; grep check from Review Focus 1.
- [ ] **Step 5: Gates + commit.**

### Task 2: fabric planes — `l1_axi4_plane`, `l1_ace_plane`, `l1_ace_issue`

**Files:**
- Create: `common-ip/rtl/plane/l1_axi4_plane.sv` — `u_snoop` (`l1_snoop_resp`) + `u_rd_monlite`/`u_wr_monlite` (plain `axi4_master_*_monlite`), ACE snoop pins in, seam bundle to the core, `fub_axi_*` to the transports, `coh_req_*` exported; ports mirror what `amber_top` wires today between `l1_core` and the fabric
- Create: `common-ip/rtl/plane/l1_ace_plane.sv` — same plus `u_ace_issue` and the `axi4ace_*_monlite` pair, `coh_req_*` consumed internally; the ACE domain/barrel constants (`amber_ace_top.sv:546–547`) move here
- Create: `common-ip/rtl/fub/l1_ace_issue.sv` — rename of `amber_ace_issue.sv` (they are already identical modulo names/comments; keep jet's AW-only path documented as unexercised)
- Delete: `jet-mesi-l1/rtl/fub/jet_ace_issue.sv` + its filelist (replaced by the shared FUB)
- Filelists: `plane/l1_axi4_plane.f`, `plane/l1_ace_plane.f`, `fub/l1_ace_issue.f`; registry updates

- [ ] **Step 1: Equivalence evidence** — script-check the merge: normalized diff (module-name/comment-stripped) of old `amber_ace_issue.sv` vs new `l1_ace_issue.sv` is empty; record output in the report.
- [ ] **Step 2: Create the planes** (ports derived from the tops' existing wiring; the sn_want counter does NOT move yet — Task 3/4 wire it; planes take `sn_want`-related AC pins and export the count signal as a plane output `sn_want_o` computing exactly `jet_top.sv:1144–1159`).
- [ ] **Step 3: Elaboration check** — compile both planes standalone (verilator lint via the house flow); no functional test yet (spec doctrine: the tops' suites are the proof).
- [ ] **Step 4: Gates + commit.**

### Task 3: amber tops recompose onto planes

**Files:**
- Modify: `amber-mesi-l1/rtl/top/amber_top.sv` → `u_cpu` + `u_coh` + `u_fab` (`l1_axi4_plane`) + `u_monbus_arbiter`; `amber_ace_top.sv` → same with `l1_ace_plane` (per the pinned instance names)
- Modify: `amber-mesi-l1/dv/tbclasses/amber_ace_top_tb.py`, `amber_pair_rig_tb.py` (tap retarget per the table)
- Filelists: `amber_top.f`, `amber_ace_top.f`, `amber_all.f` updated
- Test: full amber DV suite (core, top, ace_top, pair rig)

- [ ] **Step 1: Recompose** both tops (move-don't-edit; the rresp coercion and reset_sync stay at top).
- [ ] **Step 2: Retarget** the two tbclasses per the table.
- [ ] **Step 3: Full amber suite green** + Review-Focus-1 grep.
- [ ] **Step 4: Gates + commit.**

### Task 4: jet planes — `jet_cpu_plane`, `jet_coh_core`, jet tops recompose

**Files:**
- Create: `jet-mesi-l1/rtl/plane/jet_cpu_plane.sv` (`u_req_skid` + `u_frontend` + `u_rsp`, from `jet_top.sv:336–376` + 892; the `stage_wr_ready` tap stays internal to this plane)
- Create: `jet-mesi-l1/rtl/plane/jet_coh_core.sv` (`u_control`, `u_mshr`, `u_wb`, arrays, `u_repl`, `u_fill`, `u_drain`, `u_monlite`, `u_jet_monlite` + the integration logic: fill-launch adapter 549–613, data-write mux 619–642, mon_state encoder 1218–1251; `sn_want` enters as a port)
- Modify: `jet-mesi-l1/rtl/top/jet_top.sv`, `jet_ace_top.sv` → `u_cpu` + `u_coh` + `u_fab` + `u_monbus_arbiter`; the sn_want counter (1144–1159) and coh_req replay mux (1173–1197) move into the planes (they were created in Task 2 — wire them); the sim-only assertion block (1618–1657) stays at top level
- Modify: `jet-mesi-l1/dv/tbclasses/jet_core_tb.py`, `jet_pair_rig_tb.py` (tap retarget per the table, including the `r_cmt_state` force path)
- Filelists: `plane/jet_cpu_plane.f`, `plane/jet_coh_core.f`, updated `jet_top.f`, `jet_ace_top.f`, `jet_all.f`
- Test: full jet DV suite

- [ ] **Step 1: Extract** `jet_coh_core` from `jet_top.sv` by move-don't-edit; `jet_cpu_plane` likewise.
- [ ] **Step 2: Recompose** both jet tops onto planes + the shared fabric planes from Task 2.
- [ ] **Step 3: Retarget taps**; full jet suite green + Review-Focus-1 grep.
- [ ] **Step 4: Gates + commit.**

### Task 5: contract doc + CHI stub

**Files:**
- Create: `projects/components/cache-ip/common-ip/docs/l1_fabric_contract.md` — per spec §"The seam contract document", including the J8 op-field and J9 sideband forward reservations (marked reserved, not built)
- Create: `common-ip/rtl/plane/l1_chi_plane_stub.sv` — seam-faithful core-facing ports, CHI pin skeleton (RXREQ/RXSNP/TXREQ/TXRSP/TXDAT/RXDAT groups) tied off
- Filelist + registry entry; elaboration proof step
- Modify: the two TASK-002 task files (amber + jet vault lanes) — move to closed with outcomes

- [ ] **Step 1: Write the contract doc** from the spec section (it is the source of truth — copy the contract, not the prose around it).
- [ ] **Step 2: Write the stub; prove elaboration** (verilator lint/elab via house flow; record the command in the doc).
- [ ] **Step 3: Gates + commit; close the vault tasks.**

### Task 6: full-regression + formal re-run

- [ ] **Step 1: Full re-run** — common-ip, amber, jet DV suites at `REG_LEVEL` full; `formal/amber` harnesses re-run (they bind leaves — expected unaffected; the run is the proof).
- [ ] **Step 2: Gates** — filelist registry, link ratchet, task IDs.
- [ ] **Step 3: Commit** any straggler cleanup; report the before/after suite counts.

---

## Self-review notes

- Spec coverage: planes (T1–T4), ace_issue merge (T2), contract doc + CHI stub (T5), zero-functional-change proof (per-task suites + T6), tap inventory (the table — the spec's deferred "plan phase inventories every tap" is discharged by the 2026-11-01 explore-agent audit embedded above).
- `test_l1_core` snoop retarget decision (spec left it to the plan): harness wrapper `l1_core_fab_tb.sv` composes the responder — chosen over moving the snoop portion to a plane-level test, because it preserves the existing stimulus and oracle coverage with one new thin file.
- `amber_pair_fabric`/`jet_pair_fabric` untouched (rig-level, per spec).
- The T1 baseline-count step is the zero-drift anchor every later task compares against.
