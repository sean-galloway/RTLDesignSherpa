# jet-mesi-l1 — Lockup-Free MESI L1 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement jet — the lockup-free upgrade of amber — per the J1–J7 rulings: `jet_pkg`, the `jet_mshr` MAB file, `jet_wb_buffer`, `jet_rsp_seq`, the `jet_control` lookup/commit pipeline, `jet_top`/`jet_ace_top`/`jet_pair_fabric` rig tops, J7 MonBus observation, oracle-lockstep DV, tiny-geometry formal liveness, FULL soak grids, and the Genesys2 J7 measurement sweep.

**Architecture:** Amber's coherence protocol, arrays, engines, interfaces, and observation carry over unchanged from `cache-ip/common-ip` (`l1_*` FUBs, reused as-is; **no amber RTL edits**). Jet adds three new FUBs — `jet_mshr` (full-assoc CAM MAB, Chinnakonda §9.8/§9.10.2), `jet_wb_buffer` (decoupled victim writeback, §10.10.1), `jet_rsp_seq` (in-issue-order response release over out-of-order internal completion, the Pause Q of §9.8) — and replaces the blocking `l1_control` FSM with `jet_control`'s lookup/commit split. The gem5-derived `amber_fsm_oracle` (timing-free) pins coherence semantics per line; jet's timing freedom is checked by windowed properties, not the oracle.

**Tech Stack:** SystemVerilog (house style: `ALWAYS_FF_RST`/`RST_ASSERTED` macros from `rtl/amba/includes/reset_defs.svh`, declaration-order gate, logic-only, `[DEPTH]` array syntax, valid/ready streaming, sticky CTRL_ERROR on illegal states), cocotb 1.9.2 + cocotb-test via `source env_python`, rds-dv framework (cocotb-framework 1.2.0), Verilator/Icarus, Yosys/sby/smtbmc (oss-cad-suite at `/mnt/data/tools/oss-cad-suite/bin`), node (JS cache_sim golden model).

**Spec:** `docs/superpowers/specs/2026-10-28-jet-mshr-design.md` (the module decomposition and phasing this plan implements), `projects/components/cache-ip/jet-mesi-l1/PRD.md` v0.2 (J1–J7 rulings, binding), jet HAS v0.3 (`docs/jet_has/`) and MAS v0.1 (`docs/jet_mas/`, the block contracts — entry formats, hazard rules, interface sketches live there and are NOT repeated here), `projects/components/cache-ip/References/AMBA_ACE_Interface_Definition.md` (the inherited ACE contract), `projects/components/cache-ip/amber-mesi-l1/dv/golden/amber_fsm_oracle.py` (the coherence oracle).

## Global Constraints

- **No amber RTL changes.** Common-ip `l1_*` primitives are reused as-is; anything jet needs that amber lacks is new jet RTL under `jet-mesi-l1/rtl/` (spec non-goal).
- **J1:** `jet_mshr` is a MAB (addresses + miss context, NO line data), full-assoc CAM by line address; `MSHR_COUNT` elaboration 2–16, **default 8**.
- **J2:** hit-under-miss for reads AND writes to any resident line; W-port priority **fill beats > write hits** (bounded by `FILL_BEATS=8` at 64 B line / 64-bit bus).
- **J3:** exact-line merge only; same class joins; cross-class waits for commit then proceeds (no escalation). A read miss matching an RU entry merges; a write miss matching an RNSD entry stalls until commit.
- **J4:** out-of-order internal completion; responses release in issue order (GAXI has no IDs). Snoop on a pending line answered at the entry's post-fill state, PF_GUARD-gated.
- **J5:** dirty victim captured to `jet_wb_buffer` at miss alloc; fill proceeds immediately; drains retire oldest-first; `VICTIM_DEPTH` elaboration 1–4, **default 2**; WB entry address held to BRESP.
- **J6:** strict stall — MSHR-full stalls new misses, WB-full stalls ONLY dirty-victim misses, set-oversubscription stalls the (WAYS+1)-th miss to a set, cross-class wait stalls per J3; snoops arbitrate ahead of new CPU accepts; snoops NEVER wait on the WB buffer (they snarf).
- **Set-oversubscription rule (§9.10.2):** each in-flight miss claims its victim way at alloc; per-set claim counters cap outstanding misses per set at WAYS.
- **Anti-livelock (§10.9):** after a CLEAN_UNIQUE upgrade grant for line L, snoops to L are held off only until the granted write's commit lands — a fixed, small cycle bound, never event-dependent.
- Geometry inherited from `l1_pkg`: center **SETS=128, WAYS=4, LINE_BYTES=64, BUS_WIDTH=64**; formal tiny **16/2/64/64** (amber D9 scope).
- CPU side: GAXI slave, `CPU_REQ_W = ADDR_WIDTH+1+BUS_WIDTH/8+BUS_WIDTH` packed `{addr,we,be,wdata}`, response `CPU_RSP_W = BUS_WIDTH` (amber D2, unchanged).
- Memory side: AXI4 rd/wr via house `axi4_master_rd`/`axi4_master_wr` wrappers with `*_monlite` observation; single AXI4 read ID — **fills serialize on the memory port in AR issue order** (spec §2; multi-ID is a future step, NOT this plan).
- Snoop port: ACE-shaped AC/CD/CR per onyx D7 (amber D4, unchanged); CR only after CDLAST.
- Observation: `*_monlite` only, never `_mon` on measured paths; drop-and-count under backpressure; MonBus 128-bit packets; jet adds the J7 event classes (MSHR alloc/merge/retire, occupancy gauge, WB occupancy, rsp-seq stalls).
- Module prefix `jet_` for new RTL; package `jet_pkg` extends `l1_pkg` (import + additions; note the shared package is `l1_pkg` at `$CACHE_COMMON_ROOT/rtl/includes/l1_pkg.sv` — the HAS's "amber_pkg" phrasing means this file).
- Filelists: every RTL file reachable from a `.f` under `jet-mesi-l1/rtl/filelists/`; area registered in `bin/filelists.toml`; `JET_ROOT` exported from `env_python`; jet filelists reference common-ip via `-f $CACHE_COMMON_ROOT/...` includes.
- TDD: every RTL task writes the cocotb test first, watches it fail, implements, watches it pass, commits. Partner stubs model handshake timing only, never protocol.
- Tests run from `projects/components/cache-ip/jet-mesi-l1/dv/tests/` with `SEED=<n> REG_LEVEL=GATE|FUNC|FULL python3 -m pytest test_jet_<unit>.py -v` through the venv (`source env_python`).
- Every commit passes `python3 bin/filelist_registry.py --check --audit --blindspots --ratchet --placement` and `python3 bin/check_broken_links.py --ratchet`; formal-bearing commits also pass `python3 bin/formal_status.py --check-flats --staged`; vault edits also pass `python3 bin/check_task_ids.py`.
- Stage only this workstream's files; other dirty files in the tree (pumice/mem-ctrl, rtl/amba, val/, docs/markdown/rtl-amba, bin/TBClasses) belong to other workstreams — never stage them.

## Review Focus

Spec-implied failure modes the happy-path tests could miss, each pinned to its owning task:

1. **Set-claim counter same-cycle alloc/retire** — an alloc and a retire to the same set in one cycle must net the claim count correctly, or the (WAYS+1)-th miss either deadlocks the set or double-claims a way. Pinned in Task 2 (`test_jet_mshr_set_claim_same_cycle`).
2. **Merge-list response completeness** — every seq tag appended to an entry's merge list gets exactly one response at commit, including the cross-class waiter that proceeds after commit (J3); a dropped or doubled tag hangs or corrupts the GAXI response stream. Pinned in Task 6 (`test_jet_control_merge_response_completeness`).
3. **WB snarf in the BRESP cycle** — a snoop matching a WB entry in the exact cycle its BRESP retires must still be answered from the buffer (ships-in-the-night, §10.12.2), never "not present". Pinned in Task 3 (`test_jet_wb_buffer_snarf_at_bresp`) and re-pinned in Task 7 (`test_jet_control_snoop_snarf_bresp_race`).
4. **PF_GUARD beat gating** — a snoop hitting a pending entry must not present CD data for beats not yet landed (`beats_rcvd` gate), and must never answer at the Invalid row. Pinned in Task 7 (`test_jet_control_snoop_pf_guard`).
5. **Response-sequencer head-of-line vs. deposit freedom** — `rsp_ready` low holds only the release pointer; deposits (fill commits, hit completions) never block on it, or the memory port ends up waiting on the CPU port (deadlock). Pinned in Task 4 (`test_jet_rsp_seq_backpressure_freedom`) and re-checked in Task 8's lockstep soak.

---

### Task 1: Area scaffolding + `jet_pkg`

**Files:**
- Create: `projects/components/cache-ip/jet-mesi-l1/rtl/includes/jet_pkg.sv`
- Create: `projects/components/cache-ip/jet-mesi-l1/rtl/filelists/{jet_pkg.f,jet_all.f}`
- Create: `projects/components/cache-ip/jet-mesi-l1/dv/tests/conftest.py` (copy amber's, `AREA = 'jet'`, also inserts amber's `dv/tbclasses` and `dv/golden` on `sys.path` so jet TBs subclass amber machinery and import `amber_fsm_oracle`)
- Create: `projects/components/cache-ip/jet-mesi-l1/dv/{tb,tbclasses,testplans,traces}/.gitkeep`
- Modify: `env_python` (add `export JET_ROOT=$REPO_ROOT/projects/components/cache-ip/jet-mesi-l1` next to `AMBER_ROOT`)
- Modify: `bin/filelists.toml` (new `[[area]] name = "jet"`, kind = "component", rtl_roots/filelist_dirs pointing at the jet dirs)

**Interfaces:**
- Produces (everything later imports): package `jet_pkg` containing `parameter int MSHR_COUNT = 8` (range checked 2–16), `parameter int VICTIM_DEPTH = 2` (1–4), `parameter int RSP_DEPTH = MSHR_COUNT + 2`, `parameter int SEQ_W = $clog2(RSP_DEPTH)`, `parameter int MW = $clog2(MSHR_COUNT)`, `typedef enum logic [1:0] {JET_CLS_RNSD, JET_CLS_RU} jet_fill_class_t`, `typedef enum logic [1:0] {JET_PEND_NONE, JET_PEND_DOWNGRADE_S, JET_PEND_INVALIDATE_I} jet_pend_eff_t`, and `FILL_BEATS`/geometry imported from `l1_pkg`.
- Produces: `jet_all.f` (starts as just `jet_pkg.f`; each later task appends its filelist).

- [ ] **Step 1: Write the failing test**

`dv/tests/test_jet_pkg.py`: a compile-only cocotb-test run (minimal `jet_pkg_th.sv` harness importing `jet_pkg` and exposing the parameters as localparams) asserting `MSHR_COUNT == 8`, `VICTIM_DEPTH == 2`, `RSP_DEPTH == MSHR_COUNT + 2`, and the two enum encodings' widths.

- [ ] **Step 2: Run test to verify it fails**

Run: `cd projects/components/cache-ip/jet-mesi-l1/dv/tests && SEED=1 REG_LEVEL=GATE python3 -m pytest test_jet_pkg.py -v`
Expected: FAIL — `jet_pkg.sv` not found by the filelist.

- [ ] **Step 3: Implement `jet_pkg`**

`rtl/includes/jet_pkg.sv`: header comment (ownership, J1/J5 rulings, date), `import l1_pkg::*;` plus the constants/types above. `jet_pkg.f` lists `$REPO_ROOT/rtl/amba/filelists/reset_defs.f` is NOT needed (pure package); list `-f $CACHE_COMMON_ROOT/rtl/filelists/l1_pkg.f` then `$JET_ROOT/rtl/includes/jet_pkg.sv`. Register the area and `JET_ROOT` per Files.

- [ ] **Step 4: Run test to verify it passes**

Run: same pytest command. Expected: PASS.

- [ ] **Step 5: Registry checks + commit**

Run: `python3 bin/filelist_registry.py --check --audit --blindspots --ratchet --placement && python3 bin/check_broken_links.py --ratchet`
Expected: clean. Commit `env_python`, `bin/filelists.toml`, the jet rtl/dv scaffold with `feat(jet): area scaffolding + jet_pkg (J1/J5 defaults)`.

---

### Task 2: `jet_mshr` — the MAB file

**Files:**
- Create: `rtl/fub/jet_mshr.sv`, `rtl/filelists/jet_mshr.f`
- Create: `dv/tb/jet_mshr_th.sv`, `dv/tbclasses/jet_mshr_tb.py`, `dv/tests/test_jet_mshr.py`, `dv/testplans/jet_mshr_testplan.yaml`

**Interfaces:**
- Consumes: `jet_pkg` (Task 1).
- Produces (used by `jet_control`, Tasks 5–7) — module `jet_mshr #(parameter int MSHR_COUNT = jet_pkg::MSHR_COUNT, SETS, WAYS, LINE_W, SEQ_W)`. House-idiom elaboration range check (cf. `l1_tag_array.sv:125`): an `initial` block `$error`s when `MSHR_COUNT` is outside 2–16 (the J1 range; the package carries only the default — SV package parameters can't be overridden, so the check belongs at the module, which is also what makes the J7 2/4/8/16 sweep possible).
  - Alloc: `alloc_i`, `alloc_line_i[LINE_W-1:0]`, `alloc_set_i[SET_W-1:0]`, `alloc_cls_i[1:0]`, `alloc_install_i`, `alloc_victim_way_i[WAY_W-1:0]`, `alloc_wb_slot_i`, `alloc_wb_valid_i`, `alloc_seq_i[SEQ_W-1:0]` → `alloc_gnt_o`, `alloc_idx_o[MW-1:0]`; stall reasons `full_o`, `set_full_o`.
  - Two combinational CAM probes: lookup side (`lkup_line_i` → `lkup_match_o`, `lkup_match_idx_o`, `lkup_match_cls_o`) and snoop side (`sn_line_i` → `sn_match_o`, `sn_match_idx_o`, `sn_beats_rcvd_o`, `sn_install_o`). Same-cycle alloc/match resolve alloc-first (entry visible to the match from the alloc cycle).
  - `merge_i`, `merge_idx_i`, `merge_seq_i`; `beat_i`, `beat_idx_i`, `beat_num_i`; `sn_eff_i`, `sn_eff_idx_i`, `sn_eff_value_i[1:0]`; `retire_i`, `retire_idx_i`.
  - Commit read port: `cpl_idx_i` → `cpl_line_o`, `cpl_install_o`, `cpl_pend_eff_o[1:0]`, `cpl_merge_seqs_o` (the entry's tag list + count), `cpl_wb_slot_o`, `cpl_wb_valid_o`.
  - `occupancy_o[MW:0]` (MonBus gauge, J7).
- Entry format and per-set claim counters: exactly the MAS ch02/02 table (fields `valid/line/cls/install_state/victim_way/wb_slot/merge/beats_rcvd/pend_eff/seq`); per-entry merge lists depth `MSHR_COUNT`, aggregate live tags bounded by `RSP_DEPTH` via the front-end tag allocator (Task 5).

- [ ] **Step 1: Write the failing tests**

`test_jet_mshr.py` scenarios: `alloc_and_match` (alloc → both probes see the entry from the alloc cycle), `full_stall` (`alloc_gnt_o` falls at `MSHR_COUNT` valids, `full_o` rises), `set_claim_cap` (at WAYS=4: four allocs to one set grant, the fifth to the same set sees `set_full_o` while an alloc to a different set still grants), **`set_claim_same_cycle`** (alloc+retire to the same set same cycle nets the counter — Review Focus 1), `merge_appends` (tags accumulate in order), `beat_marks` (`sn_beats_rcvd_o` tracks `beat_i`), `pend_eff_records`, `retire_frees` (entry, way claim, and occupancy all drop), `occupancy_gauge`.

- [ ] **Step 2: Run to verify fail** — `SEED=1 REG_LEVEL=GATE python3 -m pytest test_jet_mshr.py -v`; FAIL, module missing.

- [ ] **Step 3: Implement `jet_mshr`**

Entry array `[MSHR_COUNT]`; CAM compare per MAS ch02/02's alloc/match same-cycle rule; per-set claim counters (`SETS` counters, 2 bits at 4 ways) with same-cycle alloc/retire net update; oldest-entry tracking via the `seq` age bit for retire ordering.

- [ ] **Step 4: Run to verify pass** — same command, all scenarios PASS at GATE, then `REG_LEVEL=FUNC`.

- [ ] **Step 5: Register + commit** — append `jet_mshr.f` to `jet_all.f`; registry checks clean; commit `feat(jet): jet_mshr MAB file + unit TB`.

---

### Task 3: `jet_wb_buffer` — decoupled writeback buffer

**Files:**
- Create: `rtl/fub/jet_wb_buffer.sv`, `rtl/filelists/jet_wb_buffer.f`
- Create: `dv/tb/jet_wb_buffer_th.sv`, `dv/tbclasses/jet_wb_buffer_tb.py`, `dv/tests/test_jet_wb_buffer.py`, `dv/testplans/jet_wb_buffer_testplan.yaml`

**Interfaces:**
- Consumes: `jet_pkg` (Task 1); `l1_drain`'s existing victim-side interface from `common-ip/rtl/fub/l1_victim.sv` (the buffer presents the SAME drain-side interface shape so `l1_drain` works unchanged — the buffer is a `VICTIM_DEPTH`-deep FIFO behind an `l1_victim`-compatible head).
- Produces — module `jet_wb_buffer #(parameter int VICTIM_DEPTH = jet_pkg::VICTIM_DEPTH, LINE_W, LINE_BYTES, BUS_WIDTH)`. House-idiom elaboration range check: an `initial` block `$error`s when `VICTIM_DEPTH` is outside 1–4 (the J5 range).
  - Capture (from `jet_control`, beats read off data-array port B): `cap_i`, `cap_line_i[LINE_W-1:0]`, `cap_beat_i`, `cap_beat_data_i[BUS_WIDTH-1:0]` → `cap_gnt_o`, `cap_slot_o`; `wb_full_o`.
  - Drain side (to `l1_drain`): **exactly `l1_victim`-shaped at the head** (ruling 2026-10-28, superseding the per-beat sketch — `l1_drain` consumes `drain_start`/`victim_addr[ADDR_WIDTH]`/`victim_data[LINE_WIDTH]`/`drain_done` and may NOT be modified): `drain_valid_o` (head entry valid), `drain_addr_o[ADDR_WIDTH-1:0]` (head line address with zero offset bits), `drain_data_o[LINE_WIDTH-1:0]` (head full line); `drain_done_i` (BRESP) retires the head. No per-beat drain streaming. Capture stays beat-serial on the capture side, and a partially captured entry holds its slot open until all FILL_BEATS beats land (capture may pause, never abort).
  - Snarf (to the snoop path): `sn_line_i` → `sn_hit_o`, `sn_data_o` (full line), `sn_bresp_cycle_o` (entry retires this cycle — answer still valid, Review Focus 3); `sn_eff_i` records the post-snoop state effect on the entry.
  - `wb_occupancy_o` (MonBus gauge, J7).

- [ ] **Step 1: Write the failing tests**

`test_jet_wb_buffer.py` scenarios: `capture_then_drain` (beats in, oldest-first AW/W out, BRESP retires), `full_stall` (`VICTIM_DEPTH` entries → `wb_full_o`), `oldest_first_order` (capture A,B,C → drain order A,B,C regardless of BRESP interleave), `snarf_hit` (snoop match returns entry data), **`snarf_at_bresp`** (snoop landing in the entry's BRESP cycle is still answered — Review Focus 3), `snarf_invalidated_still_drains` (post-snoop effect recorded; drain completes the memory update per MAS ch02/03).

- [ ] **Step 2: Run to verify fail** — `SEED=1 REG_LEVEL=GATE python3 -m pytest test_jet_wb_buffer.py -v`; FAIL, module missing.

- [ ] **Step 3: Implement `jet_wb_buffer`** — entry format and lifecycle per MAS ch02/03 (address held to BRESP; data beats may leave as accepted; invalidated snarfed victim still drains).

- [ ] **Step 4: Run to verify pass** — GATE then FUNC.

- [ ] **Step 5: Register + commit** — `feat(jet): jet_wb_buffer + unit TB (J5)`.

---

### Task 4: `jet_rsp_seq` — response sequencer

**Files:**
- Create: `rtl/fub/jet_rsp_seq.sv`, `rtl/filelists/jet_rsp_seq.f`
- Create: `dv/tb/jet_rsp_seq_th.sv`, `dv/tbclasses/jet_rsp_seq_tb.py`, `dv/tests/test_jet_rsp_seq.py`, `dv/testplans/jet_rsp_seq_testplan.yaml`

**Interfaces:**
- Consumes: `jet_pkg` (`RSP_DEPTH`, `SEQ_W`).
- Produces — module `jet_rsp_seq #(parameter RSP_DEPTH, BUS_WIDTH, SEQ_W)`:
  - Tag alloc (front end): `tag_req_i` → `tag_gnt_o`, `tag_o[SEQ_W-1:0]` (tag-full is the front-end accept stall; bounded by any release).
  - Deposit (from lookup hits and the commit pipeline): `cpl_i`, `cpl_tag_i[SEQ_W-1:0]`, `cpl_data_i[BUS_WIDTH-1:0]`.
  - Release (GAXI response channel): `rsp_valid_o`, `rsp_data_o`, `rsp_ready_i`.
  - Mechanism per MAS ch02/04: CAM-free ring — completion records write at the tag's slot, release pointer walks in tag order; `rsp_ready_i` low holds ONLY the release pointer.

- [ ] **Step 1: Write the failing tests**

`test_jet_rsp_seq.py` scenarios: `in_order_release` (deposits out of order → releases in tag order), `head_of_line` (incomplete head blocks the port only), **`backpressure_freedom`** (`rsp_ready_i` held low for 50 cycles while deposits continue — every deposit accepted, none dropped, release resumes in order — Review Focus 5), `tag_reuse` (a tag is reusable only after its release), `wraparound` (tag space wraps at `RSP_DEPTH` under sustained traffic).

- [ ] **Step 2: Run to verify fail** — module missing.

- [ ] **Step 3: Implement `jet_rsp_seq`** — ring buffer of per-tag completion records; release pointer; no internal path gated on `rsp_ready_i`.

- [ ] **Step 4: Run to verify pass** — GATE then FUNC.

- [ ] **Step 5: Register + commit** — `feat(jet): jet_rsp_seq + unit TB (J4)`.

---

### Task 5: `jet_control` lookup stage — classify + hit-under-miss

**Files:**
- Create: `rtl/fub/jet_control.sv`, `rtl/filelists/jet_control.f`
- Create: `dv/tb/jet_control_th.sv`, `dv/tbclasses/jet_control_tb.py`, `dv/tests/test_jet_control.py`, `dv/testplans/jet_control_testplan.yaml`

**Interfaces:**
- Consumes: `jet_mshr` (Task 2), `jet_wb_buffer` (Task 3), `jet_rsp_seq` (Task 4), `l1_pkg` state decode, `l1_repl` victim interface, `l1_tag_array`/`l1_data_array` port shapes.
- Produces: the lookup half of `jet_control` per MAS ch02/01's interface sketch — `lkup_*` in (addr, we, be, wdata, seq tag), `lkup_rsp_*` out (hit data / stall), array port A drive (`tag_*`/`dat_*`), `repl_*`, `mshr_*` alloc/match/merge, `wb_*` capture, `fill_*` launch, and the four-class classify: `HIT` / `MERGE` / `MISS_ALLOC` / `STALL` with stall sub-reasons `{mshr_full, wb_full_dirty_victim, set_oversubscribed, cross_class_wait, tag_full}`.
- The TB harness drives real `l1_tag_array`/`l1_data_array`/`l1_repl` instances (they exist and are proven) with the fill/drain engines as handshake-timing-only stubs.

- [ ] **Step 1: Write the failing tests**

`test_jet_control.py` (lookup stage): `hit_read` / `hit_write` (resident line serves while a miss is outstanding — J2), `miss_alloc` (entry allocated, victim way claimed, fill launched, request not held), `merge_read_onto_ru` (J3 join), `stall_cross_class` (write miss behind RNSD entry waits, proceeds after commit), `stall_mshr_full`, `stall_wb_full_only_dirty` (clean-victim miss allocs freely with WB full — J6), `stall_set_oversubscribed`, `fill_beats_win_wport` (write hit yields the W port for a bounded 8-beat stream, then proceeds).

- [ ] **Step 2: Run to verify fail** — module missing.

- [ ] **Step 3: Implement the lookup stage** — classify table per MAS ch02/01 (one request, one window: tag read + MSHR CAM + WB match + set claim count in the same cycle); W-port arbitration fill beats > write hits; alloc-first same-cycle rule honored through `jet_mshr`.

- [ ] **Step 4: Run to verify pass** — GATE then FUNC.

- [ ] **Step 5: Register + commit** — `feat(jet): jet_control lookup stage + hit-under-miss (J2/J3/J6)`.

---

### Task 6: `jet_control` commit pipeline

**Files:**
- Modify: `rtl/fub/jet_control.sv` (commit pipeline)
- Modify: `dv/tbclasses/jet_control_tb.py`, `dv/tests/test_jet_control.py` (commit scenarios)

**Interfaces:**
- Consumes: Task 5's lookup stage; `l1_fill`'s `fill_done`/beat-stream interface; `jet_rsp_seq` deposit.
- Produces: `cpl_*` deposit stream to `jet_rsp_seq`; tag-install and merged-store writes on the array W port; `mshr_*` retire. Commit order = fill-engine completion order (single AXI4 read ID, AR issue order).

- [ ] **Step 1: Write the failing tests**

Add to `test_jet_control.py`: `commit_installs_tag` (install state S; M when PassDirty received — amber #106 rule; M for a write fill), `commit_merges_store_data` (amber D-4 byte-enable merge on just-filled beats, identical semantics to amber), **`merge_response_completeness`** (allocator + 3 merged requesters + 1 cross-class waiter → exactly one response per seq tag, in tag order at the rsp port — Review Focus 2), `commit_retires_entry` (MSHR entry, way claim, and occupancy freed), `pend_eff_applied_after_install` (a snoop that recorded downgrade-S during the fill sees its effect land AFTER the tag install — order pinned, amber `pending` semantics).

- [ ] **Step 2: Run to verify fail** — commit logic missing (fill_done ignored).

- [ ] **Step 3: Implement the commit pipeline** — the four MAS ch02/01 commit steps in order: merge store data → install tag → apply deferred snoop effects → retire + hand responses to `jet_rsp_seq`.

- [ ] **Step 4: Run to verify pass** — lookup + commit suites, GATE then FUNC.

- [ ] **Step 5: Commit** — `feat(jet): jet_control commit pipeline + merge responses (J3/J4)`.

---

### Task 7: Snoop path under concurrency

**Files:**
- Modify: `rtl/fub/jet_control.sv` (snoop service integration, anti-livelock hold-off)
- Modify: `dv/tbclasses/jet_control_tb.py`, `dv/tests/test_jet_control.py`

**Interfaces:**
- Consumes: `l1_snoop_resp` (unchanged, common-ip), `jet_mshr` snoop probe + `sn_eff_*`, `jet_wb_buffer` snarf.
- Produces: `sn_*` service decisions — array answer (port B) / pending-fill bypass at post-fill state (PF_GUARD: answer only for beats landed) / WB snarf — plus the bounded anti-livelock hold-off; snoop priority over new CPU accepts at the lookup stage.

- [ ] **Step 1: Write the failing tests**

Add: `snoop_hit_pending_entry` (answered at `install_state`, effect recorded in `pend_eff`), **`snoop_pf_guard`** (CD never presents beats not yet in `beats_rcvd`; never an Invalid-row answer — Review Focus 4), **`snoop_snarf_bresp_race`** (WB entry in its BRESP cycle still serves the snoop — Review Focus 3), `snoop_priority` (snoop presented with a CPU request pending → snoop served first), `anti_livelock_window` (after a CLEAN_UNIQUE grant, a snoop to that line is held off exactly until the granted write's commit, then served — bound measured in cycles), `snoop_never_waits_on_wb_full`.

- [ ] **Step 2: Run to verify fail** — snoop path not yet wired to MSHR/WB.

- [ ] **Step 3: Implement the snoop path** — three-source answer mux per MAS ch02/05; per-entry bypass generalizing amber's `l1_pending_fill_bypass` semantics (PF_GUARD from `beats_rcvd`); the bounded hold-off counter (bound = granted write's commit: W port one beat + tag one write).

- [ ] **Step 4: Run to verify pass** — full `test_jet_control.py`, GATE then FUNC.

- [ ] **Step 5: Commit** — `feat(jet): snoop-during-miss service + anti-livelock hold-off (J4/J5)`.

---

### Task 8: `jet_top` composition + oracle lockstep at FUNC

**Files:**
- Create: `rtl/top/jet_top.sv`, `rtl/filelists/jet_top.f`
- Create: `dv/tb/jet_core_th.sv` (full-core harness), `dv/tbclasses/jet_core_tb.py`, `dv/tests/test_jet_core.py`, `dv/testplans/jet_core_testplan.yaml`

**Interfaces:**
- Consumes: all prior tasks; `l1_fill`, `l1_drain`, `l1_cpu_frontend`, `l1_snoop_resp`, `l1_monlite` (common-ip, unchanged); `AmberControlTB` machinery (`amber-mesi-l1/dv/tbclasses/amber_control_tb.py` — monitor, LRU model, `oracle_step`, snoop driver, **including the BUG-001/002 pre-install-valid eviction guard**) and `amber_fsm_oracle.py` (amber dv/golden, timing-free, unchanged).
- Produces: `jet_top` (pair-rig top: `jet_control` + jet FUBs + common-ip arrays/engines/frontend/monlite, plain AXI4 masters through `axi4_master_*_monlite` — mirrors `amber_top`'s structure with `l1_control`→`jet_control` swapped); `JetCoreTB(AmberControlTB)` with the per-transaction slice checks replaced by an event-stream scoreboard: per-line coherence lockstep against the oracle (unchanged semantics), timing as windowed properties (fill starts within W cycles of alloc; responses release in tag order).

- [ ] **Step 1: Write the failing tests**

`test_jet_core.py`: amber's control-suite scenarios re-run on jet (the inheritance claim — spec DV plan) plus `windowed_fill_start` (every alloc's fill launches within the bound), `response_tag_order` (global in-issue-order release across interleaved hits/misses/merges), `oracle_lockstep_soak` (random traffic + snoop soak at FUNC, per-line oracle parity throughout).

- [ ] **Step 2: Run to verify fail** — `jet_top` missing.

- [ ] **Step 3: Implement `jet_top`** — structural composition per MAS ch01 hierarchy; no new logic.

- [ ] **Step 4: Run to verify pass** — `SEED=1 REG_LEVEL=FUNC python3 -m pytest test_jet_core.py -v`, then a 10-seed sweep; every seed 0 mismatches.

- [ ] **Step 5: Register + commit** — `feat(jet): jet_top composition + oracle-lockstep core TB`.

---

### Task 9: `jet_ace_top` + `jet_pair_fabric` + pair-rig DV

**Files:**
- Create: `rtl/fub/jet_ace_issue.sv`, `rtl/top/jet_ace_top.sv`, `rtl/top/jet_pair_fabric.sv`, `rtl/filelists/{jet_ace_issue.f,jet_ace_top.f,jet_pair_fabric.f}`
- Create: `dv/tb/jet_pair_rig_tb.sv`, `dv/tbclasses/jet_pair_rig_tb.py`, `dv/tests/test_jet_pair_rig.py`, `dv/testplans/jet_pair_rig_testplan.yaml`

**Interfaces:**
- Consumes: Task 8's `jet_top`; `amber_ace_issue.sv` / `amber_ace_top.sv` / `amber_pair_fabric.sv` as the structural templates (same roles, `jet_` names); house `axi4ace_master_*_monlite` wrappers; `AXI4ACESnoopMaster` from cocotb-framework.
- Produces: the two-jet pair rig (the spec §0 "amber_pair_fabric hosts two jets" deliverable) with the ACE AC/CD/CR contract per onyx D7 — CR only after CDLAST, `check_cr_order` per transaction.

- [ ] **Step 1: Write the failing tests**

`test_jet_pair_rig.py`: amber's pair-rig scenarios re-run with two jets (coherent traffic between the pair, snoop storms, concurrent misses to the same line from both sides — the merge/snoop stress), plus `pair_ships_in_the_night` (jet A's pre-BRESP WriteBack + jet B's clean-invalidating snoop to the same line — §10.12.2, answered from the WB buffer).

- [ ] **Step 2: Run to verify fail** — modules missing.

- [ ] **Step 3: Implement the three RTL files** — structural mirrors of amber's; `jet_ace_issue` maps jet's cache events to ACE transactions exactly as amber's does.

- [ ] **Step 4: Run to verify pass** — FUNC, 10-seed sweep, oracle parity per cache.

- [ ] **Step 5: Register + commit** — `feat(jet): jet_ace_top + jet_pair_fabric + pair-rig DV`.

---

### Task 10: J7 MonBus observation

**Files:**
- Modify: `rtl/fub/jet_control.sv`, `rtl/fub/jet_mshr.sv`, `rtl/fub/jet_wb_buffer.sv` (event taps — the occupancy gauges already exist from Tasks 2–3)
- Create: `dv/tbclasses/jet_monlite_tb.py`, `dv/tests/test_jet_monlite.py`, `dv/testplans/jet_monlite_testplan.yaml`

**Interfaces:**
- Consumes: `l1_monlite` (unchanged base taps: hits, misses, snoops, evictions, transitions); MAS ch04 event map.
- Produces: jet event classes on the same 128-bit MonBus packets: MSHR alloc/merge/retire, MSHR occupancy gauge, WB occupancy, rsp-seq stalls (tag-full events).

- [ ] **Step 1: Write the failing tests**

`test_jet_monlite.py`: `event_counts` (directed traffic → expected alloc/merge/retire counts), `occupancy_gauge_tracks` (gauge equals TB-model MSHR occupancy every cycle), `drop_and_count` (backpressure → overflow counter, never a stall on the measured path), `observer_transparency` (monlite present vs. absent → bit-identical functional results — amber's perturbation pin).

- [ ] **Step 2: Run to verify fail** — jet event classes not yet emitted.

- [ ] **Step 3: Implement the taps** — wire events into `l1_monlite` channels per MAS ch04 Table; drop-and-count discipline unchanged.

- [ ] **Step 4: Run to verify pass** — GATE then FUNC.

- [ ] **Step 5: Commit** — `feat(jet): J7 MonBus event classes + monlite TB`.

---

### Task 11: Formal harness at tiny geometry

**Files:**
- Create: `formal/jet/jet_control/jet_control_prove/...` and `..._cover/...` (mirror `formal/amber/` layout: `src/formal_jet_control.sv` wrapper + flat `.v` via `make/formal_flat.mk`)

**Interfaces:**
- Consumes: Tasks 5–7 RTL at the tiny 16-set/2-way geometry; amber D9 scoping (control-layer only); `bin/formal_status.py` flat registry.

- [ ] **Step 1: Write the properties** — `formal_jet_control.sv` binds the MAS ch05/01 set: **liveness** (oldest-entry progress; drain progress; snoop progress outside the hold-off window; bounded hold-off; the composed corner MSHR-full ∧ WB-full ∧ snoop pending ⇒ progress within a fixed bound) and **safety** (CRRESP decode pins with the three answer sources; per-entry BypassNeverAnswersInvalid + PF_GUARD beat gating; no two valid entries share a line; no two in-flight misses in a set claim the same way).

- [ ] **Step 2: Run cover first** — `sby` cover traces show each stall class and the composed corner are reachable at the tiny geometry (a liveness proof over unreachable states is vacuous — the cover run is the reachability evidence).

- [ ] **Step 3: Run prove** — all properties PASS or are iterated to PASS (a genuine counterexample is a design bug: root-cause per systematic-debugging, fix RTL, re-run).

- [ ] **Step 4: Register + commit** — `python3 bin/formal_status.py --check-flats --staged` clean; commit `formal(jet): tiny-geometry liveness + safety harness`.

---

### Task 12: FULL soak grids

**Files:**
- Modify: `dv/tests/test_jet_core.py`, `dv/tests/test_jet_pair_rig.py` (FULL-level scenarios)
- Modify: `projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch06_configuration/02_dv_matrix.md` (mark executed cells)

**Interfaces:**
- Consumes: Tasks 8–10; cache_sim golden corpus (`bin/apps/cache_sim/js/model.js`, node) for LRU/FIFO/RANDOM policy parity.

- [ ] **Step 1: Add the FULL scenarios per MAS ch06/02** — MSHR-saturating miss streams with concurrent hits+snoops; merge storms; set-oversubscription bursts into one set; the composed corner dynamically (MSHR-full + WB-full + snoop soak); **amber's FULL suite re-run on jet unchanged**.
- [ ] **Step 2: Run the grid** — geometry {tiny 16/2, default 128/4} × `MSHR_COUNT` {2,4,8,16} × `VICTIM_DEPTH` {1,2,4} × policy {LRU,FIFO,RANDOM} at REG_LEVEL=FULL, repo-root-pinned seeds per node; tree-PLRU by RTL self-check. Run as a background task; expect hours.
- [ ] **Step 3: Zero-mismatch gate** — every node 0 mismatches; any failure root-caused and fixed before proceeding (a failing corner is a design bug until proven a TB bug, per the BUG-001/002 lesson).
- [ ] **Step 4: Commit** — `test(jet): FULL soak grid, all corners green`.

---

### Task 13: Genesys2 bring-up + J7 measurement sweep

**Blocked until:** `vault/tracking/formal/amber/task/open/TASK-001.md` (amber rig measurement upgrade) lands. Do not start before; this task is the spec's phase 7 and the PRD's measurement success criterion.

**Files:**
- Create: `projects/components/cache-ip/jet-mesi-l1/docs/j7_measurement_report.md` (the J7 deliverable — the four metrics, amber vs jet side by side)

- [ ] **Step 1: Bring up the two-jet Genesys2 pair rig** (mirror of the amber rig, post-upgrade) with MonBus tally.
- [ ] **Step 2: Run the frozen J7 sweep** — amber's cache_sim trace corpus, identical traces on amber and jet, `MSHR_COUNT` ∈ {2,4,8,16}.
- [ ] **Step 3: Write the report** — the four metrics (hit-latency distribution under a miss stream, MSHR occupancy histogram, sustained fill bandwidth, drain/fill overlap), latencies quoted **load-to-use** (request accept → data usable, §9.10.3 rule); cache_sim concurrency-model cross-check or documented gap.
- [ ] **Step 4: Close the vault lane** — `vault/tracking/projects/components/cache-ip/jet-mesi-l1/task/open/TASK-001.md` → closed with the evidence pointers; `python3 bin/check_task_ids.py` clean; commit `docs(jet): J7 measurement report; close TASK-001`.

---

## Self-review notes (run 2026-10-28)

- Spec coverage: phases 1–7 → Tasks 1–13 (phase 1 = Tasks 1–2, 2 = 3, 3 = 4–5, 4 = 6+8, 5 = 7+11, 6 = 12, 7 = 13; Tasks 9–10 are the spec §0/§8 pair-rig and observation content the phase list folds into 4/6). Non-goals checked: no multi-ID fills, no amber RTL edits, no MOESI anywhere in the plan.
- Type consistency: `MSHR_COUNT`/`VICTIM_DEPTH`/`RSP_DEPTH`/`SEQ_W`/`MW`, the `jet_mshr` port names, and the `cpl_*` deposit stream are spelled identically in every task that uses them.
- Review Focus lines 1–5 each have a named test in the owning task (2, 6, 3+7, 7, 4+8).
