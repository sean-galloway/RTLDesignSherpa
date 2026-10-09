# amber MESI L1 — RTL Completion + Robust DV Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Finish the amber blocking MESI L1 cache RTL — `amber_control`, pending-fill bypass, victim buffer, fill/drain engines, frontend + monlite, `amber_core`, `amber_top`/`amber_ace_top` — and make its DV the strongest in the repo: gem5-SLICC-derived FSM oracles, cache_sim trace-replay parity (PRD success criterion 1), the two-ambers pair rig (the gated deliverable), and SymbiYosys control-layer proofs at tiny geometry.

**Architecture:** `amber_core` holds everything shared between the two rig tops: `amber_cpu_frontend` (GAXI slave latch), `amber_control` (the one FSM), `amber_pending_fill_bypass`, `amber_tag_array`/`amber_data_array` (landed), `amber_repl` (landed), `amber_victim` (depth-1), `amber_fill`/`amber_drain` (drive the `fub_axi_*` side of house `axi4_master_rd`/`axi4_master_wr` wrappers), `amber_snoop_resp` (landed, wraps house `axi4ace_snoop_slave`), and `amber_monlite` (drop-and-count MonBus observer). `amber` (pair-rig top) wraps the core with plain AXI4 masters observed through `axi4_master_*_monlite`; `amber_ace` (onyx-rig top) swaps in `axi4ace_master_*` + `amber_ace_issue`. There is no `RIG` parameter — the rig is the top module you instantiate.

**Tech Stack:** SystemVerilog (house style: `ALWAYS_FF_RST`/`RST_ASSERTED` macros from `rtl/amba/includes/reset_defs.svh`, declaration-order gate, logic-only, one-hot FSM per MAS ch02), cocotb 1.9.2 + cocotb-test via `source env_python`, rds-dv framework (`cocotb-framework` 1.2.0, incl. `AXI4ACESnoopMaster`), Verilator/Icarus, Yosys/sby/smtbmc (oss-cad-suite at `/mnt/data/tools/oss-cad-suite/bin`), node (for the JS cache_sim golden model), SymbiYosys.

**Spec:** `projects/components/cache-ip/amber-mesi-l1/PRD.md` (v0.6, all 11 decisions closed — this plan argues from it), `docs/amber_mas/` ch02 (block contracts) + ch06 (DV matrix), `../onyx-ace-ccu/PRD.md` D7 (ACE AC/CD/CR port contract), `../References/AMBA_ACE_Interface_Definition.md`, `bin/apps/cache_sim/js/model.js` (golden model), `../References/gem5-ruby-protocols/MESI_Two_Level-L1cache.sm` (oracle source).

## Global Constraints

- Write policy: **write-back + write-allocate** (PRD D5). `wt_na` exists as a bring-up mode only (DV matrix bring-up config).
- Coherence: **plain MESI on a 3-bit state field** (PRD D6); `AMBER_STATE_O` reserved; MOESI is a later upgrade. No snoop-filter/directory (deferred as onyx D3).
- Geometry: center **SETS=128, WAYS=4, LINE_BYTES=64, BUS_WIDTH=64**; formal tiny **16/2/64/64**; bring-up 4/2/32/32 (PRD D1, MAS ch06). Elaboration-parameterised 4–32 KiB / 32–64 B / 2–8 ways.
- Replacement: **{LRU, tree-PLRU, FIFO, RANDOM}, LRU default** (PRD D7); LRU/FIFO/RANDOM must match cache_sim exactly; tree-PLRU has no sim golden (TB-model cross-check only, recorded).
- CPU side: **GAXI slave** (PRD D2), `CPU_REQ_W = ADDR_WIDTH+1+BUS_WIDTH/8+BUS_WIDTH` packed `{addr,we,be,wdata}`, response `CPU_RSP_W = BUS_WIDTH`.
- Memory side: **AXI4 rd/wr masters on house `axi4_master_rd`/`axi4_master_wr` wrappers, `*_monlite` observation** (PRD D3/D8); `ARLEN=AWLEN=FILL_BEATS-1`, `*SIZE=log2(BUS_WIDTH/8)`, `*BURST=INCR`, single outstanding.
- Snoop port: **ACE-shaped AC/CD/CR exactly per onyx D7 / the in-repo ACE definition** (PRD D4); six IHI0022 snoop types; **CR only after CDLAST** (amber strengthens IHI0022; cocotb-framework `check_cr_order` compliance checked per transaction).
- Observation: `*_monlite` only, never `_mon` on measured paths; drop-and-count under backpressure (PRD D8). Event set = MAS ch04 Table 4.1.1.
- Arrays/queues: PRD D11 — house shared storage primitives + GLOBAL_REQUIREMENTS FPGA attributes; memories carry no reset; post-reset hardware init walk writes `STATE_I` to all ways (MAS ch03 option 1; formal assumes all-Invalid after reset). See Task 9 for the D11 compliance ruling (DECISION D-6).
- amber has **no register block**; MonBus is the only runtime visibility.
- Style: resets on `ALWAYS_FF_RST` macros, declaration-order gate, logic-only, `[DEPTH]` array syntax, valid/ready streaming, `unique case` FSMs with explicit illegal-state default → `CTRL_ERROR`, module prefix `amber_`.
- Filelists: every RTL file reachable from a `.f` under `rtl/filelists/`; area registered in `bin/filelists.toml`; own-area paths use `$AMBER_ROOT` registered in `env_python`, `bin/TBClasses/shared/filelist_utils.py`, `bin/filelist_registry.py` (mirror kestrel, DECISION D-1).
- TDD: every RTL task writes the cocotb test first, watches it fail, implements, watches it pass, commits. Partner stubs model *handshake timing only, never protocol* (DECISION D-12).
- Every commit passes `python3 bin/filelist_registry.py --check --audit --blindspots --ratchet --placement` and `python3 bin/check_broken_links.py --ratchet`; formal-bearing commits also pass `python3 bin/formal_status.py --check-flats --staged`.
- Run all Python/pytest/cocotb through the venv (`source env_python`); oss-cad-suite + sv2v on PATH for formal tasks.

## Review Focus

Spec-implied failure modes, each pinned to an owning task:

1. **Snoop-during-fill race** — the pending-fill bypass must answer with post-fill state, never pre-fill Invalid; beats not yet received stall CD (MAS ch02/02). Pinned in Task 4 (unit), re-pinned in Task 13 (formal: no stale data after external write).
2. **Victim-buffer overflow** — depth-1 is safe only under the single-outstanding property; a snoop-triggered path must never load a busy victim (MAS ch02/05 "never loaded while valid"). Pinned in Task 5, formal Task 13.
3. **PassDirty / WriteBack ordering** — a dirty victim draining while a snoop for the same line arrives must be served from `amber_victim`, and the drain must complete before the peer's fill data is considered authoritative. Pinned in Tasks 5–6, scenario-checked in Task 11.
4. **Policy parity drift** — LRU/FIFO/RANDOM must track cache_sim per access, per geometry; RANDOM's LFSR vs cache_sim's mulberry32 cannot match bit-for-bit (DECISION D-9). Pinned in Task 10.
5. **Monlite perturbation** — the observer must never stall the measured path; present-vs-absent runs must produce identical functional results (DV matrix: gate-cost delta is evidence). Pinned in Task 8 and re-checked in Task 11.
6. **Tiny-vs-center geometry divergence** — proofs run at 16/2, regression at 128/4; FULL grid re-runs tiny on both rigs as the formal companion (MAS ch06). Pinned in Tasks 1, 13.
7. **Post-reset X-leakage** — arrays have no reset; the init walk must complete before the first lookup, and the DV TBs must mirror the walk so unwritten locations cannot leak X (MAS ch03). Pinned in Tasks 3, 9, 13.
8. **Snoop re-pipelining** — zero-gap AC arrivals while control is mid-miss; AC skid absorbs, control serializes at safe boundaries, never mid-burst (MAS ch02/03). Pinned in Tasks 3, 7.
9. **Snoop vs victim-gather interleave** — the multi-cycle victim readout on port A must honor the snoop-priority stall rule. Pinned in Task 5.
10. **Recorded gaps stay recorded** — illegal-ACSOOP stimulus and mid-transaction reset from `amber_snoop_resp_testplan.yaml` carry forward explicitly (DECISION D-14).

## File Structure

```
projects/components/cache-ip/amber-mesi-l1/
├── rtl/
│   ├── includes/amber_pkg.sv            # EXISTS; Task 2 extends (FSM enum, event codes, ace types)
│   ├── fub/                             # EXISTS: snoop_kmap, tag_array, data_array, repl, snoop_resp
│   │   ├── amber_control.sv             # Task 3 (+4, +5 snoop-side paths)
│   │   ├── amber_pending_fill_bypass.sv # Task 4  (DECISION D-2)
│   │   ├── amber_victim.sv              # Task 5
│   │   ├── amber_fill.sv                # Task 6
│   │   ├── amber_drain.sv               # Task 6
│   │   ├── amber_cpu_frontend.sv        # Task 8
│   │   └── amber_monlite.sv             # Task 8
│   ├── top/                             # EMPTY except .gitkeep today
│   │   ├── amber_core.sv                # Task 9
│   │   ├── amber_top.sv                 # Task 11 (pair-rig top)
│   │   ├── amber_ace_top.sv             # Task 12
│   │   └── amber_pair_fabric.sv         # Task 11 (DECISION D-8)
│   └── filelists/                       # per-block closures + amber_all.f (Task 1)
├── dv/
│   ├── golden/amber_fsm_oracle.py       # Task 2 (gem5-derived, executable)
│   ├── tbclasses/                       # EXISTS (5); + control/pfb/victim/fill_drain/frontend/
│   │                                    #   core/pair_rig TB classes
│   ├── testplans/                       # EXISTS (5); + one per new block (in-task)
│   ├── traces/                          # Task 10 regression traces (cache_sim text format)
│   └── tests/                           # flat, existing convention (DECISION D-13)
├── docs/amber_mas/, docs/amber_has/     # Task 14 version bumps + errata
formal/amber/                            # Task 13 (control-layer sby areas)
```

## Tasks

### Task 1: `$AMBER_ROOT` registration + filelist scaffolding

**Files:**
- Modify: `env_python`, `bin/TBClasses/shared/filelist_utils.py`, `bin/filelist_registry.py`, `bin/filelists.toml` (comment only — area `amber` already registered)
- Create: `rtl/filelists/{amber_control,amber_pending_fill_bypass,amber_victim,amber_fill,amber_drain,amber_frontend,amber_core,amber_top,amber_ace_top}.f` (stubs, filled per task)
- Modify: `rtl/filelists/amber_all.f`; convert own-area `$REPO_ROOT/...` paths to `$AMBER_ROOT/...` in all existing amber `.f` files

**Interfaces:**
- Produces: `AMBER_ROOT` resolvable by simulators, the registry, and `get_sources_from_filelist`; registry gates green; baseline suite green.

- [ ] **Step 1: Register the variable in the 3 places.** `env_python`: `export AMBER_ROOT=$REPO_ROOT/projects/components/cache-ip/amber-mesi-l1`. `bin/filelist_registry.py` ROOTS: `"AMBER_ROOT": "projects/components/cache-ip/amber-mesi-l1"`. `bin/TBClasses/shared/filelist_utils.py`: `'AMBER_ROOT': os.path.join(components_root, 'cache-ip', 'amber-mesi-l1')`.
- [ ] **Step 2: Convert own-area paths** in the 7 existing `.f` files to `$AMBER_ROOT/...`; cross-area sources stay `-f $REPO_ROOT/rtl/amba/filelists/...` (never hand-listed).
- [ ] **Step 3: Create the 9 new per-block filelists** with their cross-area `-f` closures only (own files added by their tasks): control/bypass/victim/frontend/core pull `-f amber_pkg.f`; fill pulls `axi4_master_rd.f`; drain pulls `axi4_master_wr.f`; `amber_top.f` pulls the amba filelists for `axi4_master_rd_monlite`/`axi4_master_wr_monlite`, `axi4ace_snoop_slave.f`, `sdpram_slave_axi4_axi4.f` (pair-rig bench), `monbus_arbiter` closure; `amber_ace_top.f` pulls `axi4ace_master_rd/wr` closures. Verify each path with `ls`.
- [ ] **Step 4: Run gates + baseline.**

```bash
python3 bin/filelist_registry.py --check --audit --blindspots --ratchet --placement
python3 bin/check_broken_links.py --ratchet
make -C projects/components/cache-ip/amber-mesi-l1/dv/tests run-all-func
```

Expected: five registry/link PASS lines; the five existing unit suites (kmap, tag, data, repl, snoop_resp) pass. This is the green baseline every later task preserves.
- [ ] **Step 5: Commit** (`amber: register AMBER_ROOT + filelist scaffolding for control plane`).

---

### Task 2: `amber_pkg` extensions + gem5-derived FSM oracle

**Files:**
- Modify: `rtl/includes/amber_pkg.sv`
- Create: `dv/golden/amber_fsm_oracle.py`, `dv/golden/gem5_mapping_notes.md`
- Test: `dv/tests/test_amber_oracle.py`

**Interfaces:**
- Produces: `typedef enum logic [3:0]` `ctrl_state_t` (DECISION D-3: adds `CTRL_INIT` to the MAS ch02 table: `IDLE, INIT, LOOKUP, HIT_RD, HIT_WR, MISS_VICTIM, MISS_DRAIN, MISS_FILL, FILL_WRITE, REPLAY, SNOOP, ERROR`); MonBus event codes `AMBER_EV_*` per MAS ch04; `amber_ace_req_t` enum for Task 12; `amber_miss_class_t`. Oracle: `step(state, event) -> (next_state, outputs)` for every {M,E,S,I} × {CPU rd/wr, 6 snoops, fill done, drain done} cell, derived from `MESI_Two_Level-L1cache.sm` with the mapping/collapse recorded in `gem5_mapping_notes.md` (DECISION D-11: gem5 TBE transients IS/IM/IS_I/M_I/SINK_WB_ACK collapse onto amber's blocking CTRL transients; PF_* prefetch states out of scope; Table 3.0 pkg functions are the snoop decode authority already).
- Consumes: landed `amber_pkg` decode functions; existing `amber_snoop_kmap` TB as the style template.

- [ ] **Step 1: Write the failing test** — table-driven: every reachable cell of the oracle's transition table asserted against hand-cited gem5 transitions (cite file + action-block line in the test docstring); reserved/illegal encodings must land in ERROR; CRRESP/next-state columns must equal `amber_pkg.amber_snoop_crresp`/`amber_snoop_next_state` exactly (pins pkg↔oracle consistency from day one).
- [ ] **Step 2: Run, verify FAIL** (oracle file absent).
- [ ] **Step 3: Implement** the oracle + pkg extensions. Oracle is pure Python, no I/O, deterministic.
- [ ] **Step 4: Run, verify PASS**; kmap TB still green (pkg is additive).
- [ ] **Step 5: Commit** (`amber: pkg control-plane enums + gem5-derived FSM oracle`).

---

### Task 3: `amber_control` — blocking pipeline FSM (CPU path)

**Files:**
- Create: `rtl/fub/amber_control.sv`
- Create: `dv/tbclasses/amber_control_tb.py`
- Test: `dv/tests/test_amber_control.py` (names: `test_amber_control_s016w2_{gate,func,full}`, `test_amber_control_s128w4_*`)
- Modify: `rtl/filelists/amber_control.f`, `amber_all.f`

**Interfaces:**
- Produces: `amber_control` with the MAS ch02 port groups: tag/data port A (`ctrl_tag_a_*`, `ctrl_data_a_*`), `ctrl_repl_req/ctrl_repl_way/ctrl_repl_hit/ctrl_repl_update`, victim (`ctrl_victim_*`), fill (`ctrl_fill_start/ctrl_fill_done/ctrl_fill_addr`), drain (`ctrl_drain_start/ctrl_drain_done`), snoop (binding names per landed RTL: `ctrl_snoop_req/ready`, `ctrl_crresp`, `ctrl_cddata/ctrl_cdlast/ctrl_cdvalid/ctrl_cdready`), frontend (`ctrl_req_ready`, `ctrl_rsp_valid/ctrl_rsp_data`), init-walk outputs. FSM one-hot, `unique case`, illegal → `CTRL_ERROR` sticky.
- Consumes: Task 2 oracle (scoreboard), Task 1 filelists; **partner stubs**: fill/drain/victim/frontend/snoop_resp handshake models only (D-12).
- DECISION D-4: write-allocate merge happens on the replayed write hit via `be` (fill installs the raw line; `CTRL_REPLAY` write then merges) — the GAXI slave sees one request, one response.

- [ ] **Step 1: Write the failing test** — TB classes: (a) `HitSequence` directed rd/wr hits per state with policy-update checks vs oracle; (b) `MissSequence` miss→victim→(drain)→fill→install→replay vs oracle, dirty and clean victims; (c) `InitWalk` — after reset, first `ctrl_req_ready` only after all sets written `STATE_I` (Review Focus 7); (d) FULL: randomized request streams vs oracle lockstep, 10k transactions, seeds pinned by root conftest.
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Implement** `amber_control.sv`: `CTRL_INIT` walk; LOOKUP → hit service (port A data access same cycle as state check, MAS ch02 stage 2); miss path per MAS ch02 stage 3; replay. Snoop inputs stub-tied this task.
- [ ] **Step 4: Run gate/func/full at both geometries; verify PASS.** Verify the miss-path decision cover matches the `K-maps amber control` sheet axes `{hit, victim_dirty, pending_bypass_match}` → outputs `{start_drain, start_fill, replay_now}` (record verdict for ch05).
- [ ] **Step 5: Commit** (`amber: amber_control blocking pipeline FSM vs oracle`).

---

### Task 4: `amber_pending_fill_bypass` + snoop-during-fill

**Files:**
- Create: `rtl/fub/amber_pending_fill_bypass.sv`
- Modify: `rtl/fub/amber_control.sv` (snoop service + fill-beat interface)
- Test: extend `dv/tests/test_amber_control.py` (snoop classes); new plan `dv/testplans/amber_control_testplan.yaml`

**Interfaces:**
- Produces: leaf `amber_pending_fill_bypass` (DECISION D-2: MAS ch02 calls it a control sub-block; built as a leaf so Task 13 proves it standalone) with fields `pf_addr/pf_state/pf_data_valid[FILL_BEATS]/pf_active` per MAS ch02/02; `pf_load`, `pf_beat_set(i)`, `pf_match`, `pf_beat(i)` ports. Control gains snoop priority logic: `CTRL_SNOOP` entry stalls the CPU pipeline one cycle at safe boundaries only (never mid-burst), port B exclusive, port-A downgrade applied on the next free cycle.
- Consumes: Task 3; Task 7 will re-verify against the real adapter.

- [ ] **Step 1: Write the failing tests** — (a) snoop for the pending line pre-`RLAST` answered with post-fill state and received beats, `cd_ready` stall until a late beat arrives (Review Focus 1); (b) snoop applied after fill commit changes state normally; (c) snoop for *other* lines interleaved mid-fill at legal boundaries (Review Focus 8); (d) bypass never answers with pre-fill `STATE_I` — asserted as a TB invariant every cycle.
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Implement** the leaf + control integration (`CTRL_MISS_FILL` loads pf; `CTRL_FILL_WRITE` commits and clears).
- [ ] **Step 4: Run, verify PASS** at tiny + default.
- [ ] **Step 5: Commit** (`amber: pending-fill bypass + snoop-during-fill service`).

---

### Task 5: `amber_victim` + handoff + victim bypass

**Files:**
- Create: `rtl/fub/amber_victim.sv`
- Modify: `rtl/fub/amber_control.sv`
- Test: extend `test_amber_control.py`; new plan `dv/testplans/amber_victim_testplan.yaml`

**Interfaces:**
- Produces: `amber_victim` per MAS ch02/05: `victim_load/victim_addr_in/victim_data_in/victim_busy/victim_empty/victim_addr/victim_data/victim_valid`; control-side snoop match `victim_valid && snoop_line_addr == victim_addr` sources CD from the buffer.
- DECISION D-5: the victim line is gathered over `FILL_BEATS` port-A read cycles (data array port is `BUS_WIDTH` wide per MAS ch03, so MAS ch02's single-cycle `victim_load` of a full line is unreachable); `victim_load` is the final-beat strobe. MAS ch02 erratum recorded in Task 14.

- [ ] **Step 1: Write the failing tests** — dirty-victim drain sequence; snoop-hits-victim bypass (data served from buffer while drain outstanding, Review Focus 3); load-while-busy asserted impossible (single-outstanding invariant, Review Focus 2); snoop-priority stall during the gather beats (Review Focus 9).
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Implement** the buffer + gather counter + bypass mux in control.
- [ ] **Step 4: Run, verify PASS.**
- [ ] **Step 5: Commit** (`amber: depth-1 victim buffer + gather/bypass handoff`).

---

### Task 6: `amber_fill` + `amber_drain` (AXI4 master-side sequencing)

**Files:**
- Create: `rtl/fub/amber_fill.sv`, `rtl/fub/amber_drain.sv`
- Create: `dv/tbclasses/amber_fill_drain_tb.py`
- Test: `dv/tests/test_amber_fill_drain.py`; plans `dv/testplans/amber_{fill,drain}_testplan.yaml`

**Interfaces:**
- Produces: `amber_fill` — MAS ch02/06 control side (`fill_start/fill_addr/fill_done/fill_beat_valid/fill_beat_data/fill_beat_idx/fill_last`) + `fub_axi_ar*` toward `axi4_master_rd`; `amber_drain` — `drain_start/drain_done` + `fub_axi_aw*/w*/b*` toward `axi4_master_wr`; burst params per MAS ch03/02.
- DECISION D-6 (D11 queue inventory): `amber_fill` stages R beats in a `gaxi_fifo_sync` (DEPTH=4) so snoop-imposed port-A updates can pause data-array writes without dropping `fub_axi_rready`; `amber_drain` forwards victim beats directly (AW already accepted, W skid inside the wrapper absorbs). Remaining paths use existing skids/registers — recorded in the module header.

- [ ] **Step 1: Write the failing tests** — house `AXI4Master` BFM as responder: AR→R burst timing per MAS ch03/02 waveform, per-beat data check incl. `fill_beat_idx` order; drain AW/W/B waveform with `WSTRB=all-1s`; randomized R/B backpressure; single-outstanding assertion (no second AR before RLAST consumed).
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Implement** both engines.
- [ ] **Step 4: Run, verify PASS** (gate/func/full, both geometries).
- [ ] **Step 5: Commit** (`amber: fill/drain engines on axi4_master wrappers`).

---

### Task 7: `amber_snoop_resp` integration — stub out, real control in

**Files:**
- Modify: `dv/tbclasses/amber_snoop_resp_tb.py` (replace control-stub coroutine), `dv/tests/test_amber_snoop_resp.py` (integration parametrization)
- Modify: `rtl/fub/amber_control.sv` if the binding handshake diverges

**Interfaces:**
- Produces: closed loop real `amber_control` + real `amber_tag_array`/`amber_data_array`/`amber_repl` + real `amber_snoop_resp` (arrays/repl already landed); the existing evolving line-state model becomes the scoreboard. Binding contract per the landed RTL header: `ctrl_snoop_req` held until `ctrl_snoop_ready`; `ctrl_crresp` valid at the handshake and latched by the adapter; CD beats flow on `ctrl_cdvalid && ctrl_cdready`; CR-after-CDLAST preserved.

- [ ] **Step 1: Write the failing test** — keep every existing scenario green with the stub, then add `real_control_loop`: randomized snoops against an amber that is *simultaneously* serving random CPU traffic (both ports live), CR/CD compliance checked per transaction by the framework checker.
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Integrate** (replace stub; align names — MAS ch02's `ctrl_snoop_crresp/cddata/cdlast` vs landed `ctrl_crresp/ctrl_cddata/ctrl_cdlast/ctrl_cdvalid/ctrl_cdready`; the RTL wins, MAS erratum in Task 14).
- [ ] **Step 4: Run, verify PASS** — all six existing snoop_resp scenarios + the new loop, gate/func/full both geometries.
- [ ] **Step 5: Commit** (`amber: snoop responder closed loop with real control`).

---

### Task 8: `amber_cpu_frontend` + `amber_monlite`

**Files:**
- Create: `rtl/fub/amber_cpu_frontend.sv`, `rtl/fub/amber_monlite.sv`
- Create: `dv/tbclasses/amber_frontend_tb.py`, `dv/tbclasses/amber_monlite_tb.py`
- Test: `dv/tests/test_amber_frontend.py`; plans `dv/testplans/amber_{cpu_frontend,monlite}_testplan.yaml`

**Interfaces:**
- Produces: `amber_cpu_frontend` — GAXI slave per MAS ch02/09 (`cpu_req_wr_*`, `cpu_rsp_rd_*`, `CPU_REQ_W` packing), `req_ready` only in `CTRL_IDLE` with no snoop stall, response held under `cpu_rsp_rd_ready` low; response staging in a `gaxi_fifo_sync` (DEPTH=2, D-6). `amber_monlite` — taps per MAS ch04 emit points, 128-bit MonBus packets with house UNIT/AGENT ids per `monitor_common_pkg` rules, drop-and-count with saturating counter re-emitted as `AMBER_EV_DROPPED`.
- Consumes: house GAXI BFM family; `monbus_tally_axil` host tally agent.

- [ ] **Step 1: Write the failing tests** — request latch/replay visibility; backpressured response held stable; monlite: every event class in Table 4.1.1 observed at least once per scenario run; sustained backpressure forces drops and the dropped-count packet appears later; **present-vs-absent**: same stimulus with `USE_MONITOR=0`/`mon_ready` tied 1 produces identical frontend behavior (Review Focus 5).
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Implement** both modules.
- [ ] **Step 4: Run, verify PASS.**
- [ ] **Step 5: Commit** (`amber: GAXI frontend + drop-and-count monlite`).

---

### Task 9: `amber_core` integration + D11 ruling

**Files:**
- Create: `rtl/top/amber_core.sv`
- Create: `dv/tbclasses/amber_core_tb.py`
- Test: `dv/tests/test_amber_core.py`; plans `dv/testplans/amber_core_testplan.yaml`

**Interfaces:**
- Produces: `amber_core` per MAS ch01 hierarchy (all blocks above; `amber_top`/`amber_ace_top` wrap it later). External shape = MAS ch01/02 minus top-level masters: GAXI CPU, `fub_axi_*` rd/wr master sides, ACE snoop port, MonBus, plus the pair-rig coherence sideband `coh_req_{valid,addr,type}` (DECISION D-8).
- **D11 ruling (controller sign-off recorded in the commit message)**: PRD D11 says "`sdpram_core`-based tag/data stores"; the landed arrays (green DV, MAS ch03) are per-way inferred RAMs using exactly the `sdpram_core` internal idiom, because `sdpram_core` the module is a FUB/AXI burst *slave* — the wrong shape for a same-cycle multi-way tag compare. Task resolution: keep the landed arrays; satisfy D11's queue half with the two `gaxi_fifo_sync` instances from D-6; the genuine `sdpram_core` consumer is the pair-rig shared memory (Task 11). MAS ch01 ("arrays are built from `sdpram_core`") vs ch03 (explicitly not) contradiction is errata'd in Task 14. If the controller rules literal-sdpram-core, stop and replan Task 9 — do not improvise.

- [ ] **Step 1: Write the failing test** — bring-up config smoke (4/2/32/32, FIFO): single amber behind TB GAXI masters + AXI4 memory responder, random traffic vs the Task 2 oracle lockstep; init-walk then first-hit latency check; monlite tally cross-check vs oracle counters.
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Implement** `amber_core.sv` (pure structural; the D11 queues land here if not already in Tasks 6/8).
- [ ] **Step 4: Run, verify PASS** (gate/func, tiny + default + bring-up).
- [ ] **Step 5: Commit** (`amber: amber_core integration + D11 queue ruling`).

---

### Macro composition suites (T9.5 — inserted task, runs between Tasks 9 and 10)

Inserted per controller ruling (2026-10-08) + user directive. The eight landed FUBs cluster into four interaction groups around `amber_control`; each group becomes a **new SystemVerilog wrapper module** so cocotb drives a real DUT top (user directive: harness-side Python composition is not acceptable for these). Test-only wrappers take a `_test` suffix (user-approved; the repo `_th` idiom stays for plain harnesses). Suites are committed under `dv/tb/`, `dv/tbclasses/`, `dv/tests/`, `dv/testplans/` and run as regression cells — they are the bring-up ladder between unit suites and `amber_core`, and T11's pair rig inherits their pinned scenarios.

**Groups:**
1. **Lookup dataplane** — control + tag_array + data_array + repl (hit/miss, promotion, victim selection, multi-way compare, init-walk interaction).
2. **Miss/fill path** — control + pending_fill_bypass + fill (fill orchestration, mid-fill snoop service, killed-fill re-fetch, beat gathering).
3. **Eviction/writeback** — control + victim + drain (dirty-victim gather, victim-buffer pressure, drain ordering).
4. **Coherence/snoop loop** — control + snoop_resp + pending_fill_bypass + victim (PassDirty forwarding, snoop-vs-gather interleave, CR-after-CDLAST, zero-gap AC). Promote the Task 7 ad-hoc composition (`amber_snoop_resp_th.sv` + `real_control_loop`) into this named macro suite rather than building a fourth from scratch.

**Files:**
- Create: `dv/tb/amber_{lookup,miss_fill,eviction,coh}_macro_test.sv` (wrapper modules, `_test` suffix)
- Create: `dv/tbclasses/amber_{lookup,miss_fill,eviction,coh}_macro_tb.py`, `dv/tests/test_amber_{...}_macro.py`, `dv/testplans/amber_{...}_macro_testplan.yaml`

**Interfaces:** each wrapper instantiates only its group's landed FUBs plus harness BFMs (hierarchical taps per the sanctioned pattern); external ports = the union of member FUB ports the scenarios need. No production RTL is created or modified.

**Sign-off:** gate/func green per macro (tiny + default geometries); FULL for the coherence macro (it carries the T7-found bug pins). Randomized scenarios per group must cover the cross-block interactions the unit suites cannot reach (snoop-during-fill, victim-while-draining, killed-fill re-fetch, zero-gap AC mid-miss).

---

### Task 10: cache_sim trace-replay parity suite

**Files:**
- Create: `dv/traces/*.txt` (regression traces in cache_sim address-text format), `dv/golden/cache_sim_harness.py`, `dv/tbclasses/amber_parity_tb.py`
- Test: `dv/tests/test_amber_parity.py`; plan `dv/testplans/amber_parity_testplan.yaml`

**Interfaces:**
- Produces: pytest grid `{traces} × {LRU, FIFO, RANDOM} × {128/4/64/64, 16/2/64/64}`; per run, amber (via `amber_core` TB) replays the trace and hit/miss/miss-class counts are compared **exactly** against cache_sim totals (`hits/misses/compulsory/capacity/conflict`).
- DECISION D-9: cache_sim is word-addressed (byte-addr `>> 2`; `blockSize = LINE_BYTES/4` words), models a read-only footprint (writes replay as same-footprint write-allocate accesses), and its RANDOM uses mulberry32 — bit-identical LFSR parity is impossible. Resolution: exact native parity for LRU/FIFO; RANDOM parity runs with a **recorded cache_sim extension** (js policy branch replaying the RTL LFSR polynomial/seed, symmetric to the documented tree-PLRU caveat); traces generated deterministically in Python (sequential/strided/RandomLRU-walks/TH-shaped mixes, 1k–100k accesses), seeds pinned by root conftest.

- [ ] **Step 1: Write the failing harness** — node one-shot runner (`node -e` requiring `bin/apps/cache_sim/js/model.js`) + the LFSR-extension patch living in `dv/golden/` (applied to a copied module object, never editing the app in place).
- [ ] **Step 2: Run harness vs cache_sim's own `test/run_tests.js` expectations to validate the runner; then watch amber parity FAIL (no RTL path yet is fine — the TB comes from Task 9).
- [ ] **Step 3: Implement** the parity TB (trace → GAXI stimuli; per-access hit/miss recorded; miss-class from the TB's shadow fully-associative model, identical algorithm to model.js).
- [ ] **Step 4: Run the grid; verify PASS** — exact count equality per cell; any drift is a bug in RTL or harness, never "toleranced".
- [ ] **Step 5: Commit** (`amber: cache_sim trace-replay parity grid (PRD criterion 1)`).

---

### Task 11: Pair rig — two ambers + shared memory (gated deliverable)

**Files:**
- Create: `rtl/top/amber_top.sv`, `rtl/top/amber_pair_fabric.sv`, `dv/tb/amber_pair_rig_tb.sv`
- Create: `dv/tbclasses/amber_pair_rig_tb.py`
- Test: `dv/tests/test_amber_pair_rig.py`; plan `dv/testplans/amber_pair_rig_testplan.yaml`

**Interfaces:**
- Produces: `amber_top` — MAS ch01/02 port list verbatim (GAXI slave, AXI4 `m_axi_*` rd/wr via `axi4_master_rd_monlite`/`axi4_master_wr_monlite`, ACE snoop responder, single MonBus) + the coherence sideband from D-8. DECISION D-7: a house `monbus_arbiter` merges {amber_monlite, rd_monlite, wr_monlite} onto the one MonBus port pair. `amber_pair_fabric` — the minimal 2-master snoopy manager the plain-AXI4 rig needs (onyx proper waits per amber D10 / onyx v0.2): per direction, take `coh_req` → drive AC to the peer → gather CR/CD → if `PassDirty|DataTransfer`, buffer the CD line and source the requester's R beats from it (suppress the memory AR); else pass through to `sdpram_slave_axi4_axi4` shared memory. Depth-1 per direction, fair round-robin between the two caches, blocking caches make single-outstanding sufficient.
- Consumes: `axi4ace_snoop_slave` (in amber), `AXI4ACESnoopMaster` BFM for negative scenarios, `sdpram_slave_axi4_axi4` + leaf filelist, Task 9.

- [ ] **Step 1: Write the failing tests** — coherence scenarios: (a) M→remote-fill **PassDirty forwarding** (data from peer, not memory); (b) S→M upgrade invalidates peer (subsequent peer read misses → fabric forwards); (c) dirty eviction **WriteBack** visible to memory and peers; (d) E→S downgrade on ReadShared; (e) simultaneous same-line misses serialize fairly, both correct (no deadlock, Review Focus pair with Task 13); (f) randomized dual-CPU traffic vs a 2-cache Python lockstep model (extends the Task 2 oracle with a second cache + fabric rules); (g) MonBus present-vs-absent equivalence (Review Focus 5).
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Implement** `amber_pair_fabric.sv`, then `amber_top.sv`.
- [ ] **Step 4: Run gate/func at tiny + default; full nightly seed; verify PASS.**
- [ ] **Step 5: Commit** (`amber: pair rig — two ambers + fabric + shared memory coherent`).

---

### Task 12: `amber_ace_issue` + `amber_ace_top` (onyx-rig)

**Files:**
- Create: `rtl/fub/amber_ace_issue.sv`, `rtl/top/amber_ace_top.sv`
- Test: `dv/tests/test_amber_ace_top.py`; plan `dv/testplans/amber_ace_top_testplan.yaml`

**Interfaces:**
- Produces: `amber_ace_issue` — combinational event→transaction map per MAS ch02/08 Table 2.8.1 (ReadShared/ReadUnique on `arsnoop[3:0]`; CleanUnique/MakeUnique/WriteBack/Evict on `awsnoop[2:0]`), between control/fill/drain and `axi4ace_master_rd`/`axi4ace_master_wr`; `amber_ace_top` — same CPU/snoop/MonBus surface as `amber_top`, ACE masters with auto-pulsed RACK/WACK per the wrappers. DECISION D-10: pair rig sequences first (gated deliverable); this rig is the DV-matrix `FUNC default/LRU/amber_ace` sanity plus nightly.
- [ ] **Step 1: Write the failing test** — per Table 2.8.1 row: drive the cache event, capture `arsnoop/awsnoop` + address + burst; CleanUnique/MakeUnique are AW-only (no W beats); WriteBack carries the victim line; framework ACE compliance checker on the master pins.
- [ ] **Step 2: Run, verify FAIL.**
- [ ] **Step 3: Implement.**
- [ ] **Step 4: Run FUNC default + FULL tiny; verify PASS.**
- [ ] **Step 5: Commit** (`amber: amber_ace_issue + amber_ace_top on axi4ace masters`).

---

### Task 13: SymbiYosys control-layer proofs (tiny geometry)

**Files:**
- Create: `formal/amber/{amber_control,amber_pending_fill_bypass,amber_victim,amber_snoop_resp}/` — each `<block>.sby`, `formal_<block>.sv`, `<block>_flat.v`, `includes/reset_defs.svh` mapping

**Interfaces:**
- Produces: the four MAS ch06 proof targets at **SETS=16/WAYS=2/64B/64b**: (1) **no stale data after an external write** (snoop invalidation + pf state-accuracy); (2) **no deadlock/livelock under fair arbitration** (CPU vs snoop, liveness via fair constraint); (3) **victim handoff** (never loaded while busy; drain-done ordering); (4) **AC/CR/CD ordering** (CR only after CDLAST; one closed response). House sby pattern: `[tasks] prove/cover`, `smtbmc z3`, `read_verilog -formal -sv <block>_flat.v` + wrapper, `prep -top`, `delete t:$print` (copy `formal/common/gaxi_fifo_sync/gaxi_fifo_sync.sby` structure exactly).
- [ ] **Step 1: Write wrappers + sby files**; assumptions: all lines Invalid post-reset (mirror the init walk or assume the walk completed), fair arbitration constraint for liveness, memories abstracted (tag/data arrays replaced by abstract state or cut at port boundaries — smallest sound choice recorded per proof).
- [ ] **Step 2: Generate flats with the house flow** (same tooling the existing `formal/*/_flat.v` files use) and run `sby -f` on all four; iterate RTL on FAIL (fix RTL, not checks).
- [ ] **Step 3: Run the gate** — `python3 bin/formal_status.py --check-flats --staged` PASS.
- [ ] **Step 4: Re-run Task 4–7 unit suites** to confirm harness assumptions didn't mask sim behavior (Review Focus 6 divergence check).
- [ ] **Step 5: Commit** (`amber: control-layer SymbiYosys proofs green at tiny geometry`).

---

### Task 14: Coverage wiring + docs version bumps

**Files:**
- Modify: `docs/` — PRD v0.6→**v1.0** (status: RTL landed), MAS v0.5→**v1.0** (ch02 chapters flip to "RTL landed" status; errata: ch01↔ch03 sdpram_core wording, ch02 `ctrl_snoop_*`→`ctrl_*` names, ch02 single-cycle `victim_load`→gather+final-strobe, ch02 FSM table += `CTRL_INIT`, ch01/02 port list += coherence sideband, dv/tests/fub/→flat `dv/tests/` paths), HAS v0.5→**v1.0**; regenerate `AMBER_MAS_v1.0.{pdf,docx}`, `AMBER_HAS_v1.0.{pdf,docx}` via `docs/generate_{mas,has}_pdf.sh`
- Modify: `docs/amber_mas/ch05_verification/{01_kmap_verdicts,02_rtl_diff}.md` (control/miss-path/MonBus sheets verdicts: IDENTICAL / RTL-REDUNDANT with rationale / RTL-DIFFERS)
- Test: the gates themselves

- [ ] **Step 1: Testplan sweep** — one yaml per new block (created in Tasks 3–12); run `python3 bin/cov_utils/verify_testplan_coverage.py` for area amber; every `status: covered` claim backed by a named scenario; recorded gaps (illegal ACSNOOP, mid-transaction reset — D-14) restated, not dropped.
- [ ] **Step 2: Coverage merge** — `make -C projects/components/cache-ip/amber-mesi-l1/dv/tests coverage-report` (tests.mk → `bin/cov_utils/merge_testlevel_coverage.py`); confirm per-testlevel coverage report renders and monlite present-vs-absent delta is recorded.
- [ ] **Step 3: FULL grid nightlies** — run the MAS ch06 matrix: FULL default × all four policies × both rigs + FULL tiny both rigs + parity grid; archive logs under `dv/tests/logs/`.
- [ ] **Step 4: Docs bumps + errata** per Files; `python3 bin/check_broken_links.py --ratchet` PASS; filelist gates PASS.
- [ ] **Step 5: Commit** (`amber: v1.0 docs, kmap verdicts, coverage + FULL grid evidence`).

---

## Self-Review

1. **Spec coverage:** every MAS ch02 block lands (control 3, bypass 4, victim 5, fill/drain 6, snoop_resp integration 7, frontend/monlite 8, core 9, tops 11/12); ch06 formal targets → 13; parity criterion 1 → 10; gated pair rig → 11; D11 ruling → 9; observation present-vs-absent → 8/11. No gaps.
2. **Green-tree ordering:** each task is independently testable; Task 1 establishes and every later commit re-verifies the baseline; Tasks 4/5 extend control without orphaning 3's suite.
3. **Type/name consistency:** FSM states, pf fields, victim handshake, CRRESP bit order, and filelist names are fixed in Tasks 2/3 and referenced — not restated — later. The landed `amber_snoop_resp` port names are binding over MAS table spelling.
4. **Review Focus:** all ten items pinned (see section); DECISIONs D-1..D-14 marked in place.
