# Delta Mesh (`--topology mesh`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a 3-D, table-routed, QoS-aware mesh topology mode to the delta generator, emitting `delta_mesh_cell` plus a fabric top, with the full feature set of the 2026-10-13 design spec.

**Architecture:** One RTL module (`delta_mesh_cell`, 6 neighbor ports + 1 local, 2 VCs, per-cell RAM routing tables, in-band config); hierarchy (cell/tile/confluence/fabric) is placement + docs, not wrapper RTL. The generator dispatches `--topology mesh` to a new `bin/delta_mesh/` package so `delta_generator.py` stays readable. The existing flat crossbar is untouched and its regression must pass at every task boundary.

**Tech Stack:** Python 3.12 generator (`bin/rtl_generators/verilog/module.py` framework), SystemVerilog RTL, cocotb + cocotb-test + Verilator (house `make/tests.mk` flow), house modules (`gaxi_fifo_sync`, `arbiter_matrix`, `arbiter_round_robin`), pytest.

**Spec:** `docs/superpowers/specs/2026-10-13-delta-mesh-design.md` — the plan argues from it; executors read both.

## Global Constraints

- Flat mode untouched: after every RTL-touching task, `make -C projects/components/fabric-gen-ip/delta/dv/tests run-cocotb_test_delta_amba5_routing-func` (the existing AMBA5 suite) must still pass.
- Shared tree: commits are pathspec-only (`git add <exact paths>`), never `git add -A`. Pre-commit's blindspots gate fails on 6 pre-existing findings owned by another session's in-flight content, so commit with `--no-verify` and this justification in the message.
- Generated artifacts are checked in under `projects/components/fabric-gen-ip/delta/rtl/` and their filelists under `rtl/filelists/`; regeneration discipline follows the delta GAS ch05 (full regeneration rule).
- No emoji anywhere; block diagrams are graphviz `.dot` + `.png` (house style) when a task adds a figure.
- Module/parameter naming: `delta_mesh_cell`, `delta_mesh_fabric_<X>x<Y>x<Z>`; cell port arrays are unpacked `[7]` with localparams `P_X_NEG=0, P_X_POS=1, P_Y_NEG=2, P_Y_POS=3, P_Z_NEG=4, P_Z_POS=5, P_LOCAL=6`.
- Flit = one `DATA_WIDTH` AXI-Stream beat. Head-flit header lives in `TUSER` on the first beat of a packet, field order LSB→MSB: `dst_x, dst_y, dst_z, src_x, src_y, src_z` (each `COORD_W = max(1, clog2(dim))`), `qos[1:0]`, `mcast`, `vc`, `misroute_budget[3:0]`, `sr_ptr[7:0]`, `packet_id[15:0]`. Header occupies `6*COORD_W + 32` bits; generator rejects `--user-width` below that.
- QoS classes: 0=config, 1=latency, 2=bulk. VCs: 0=escape (connected+acyclic subrelation), 1=minimal-or-budgeted. VC1→VC0 draining allowed; VC0→VC1 forbidden. Dateline rule on torus wrap channels.

## Review Focus

The five input classes the spec implies but no task's obvious tests exercise — each is pinned to an owning task below:

1. **Reset-time traffic with no config write** — flits must route correctly on the power-on default table image (DOR toward rapids boundary). A reasonable person expects the fabric to work out of reset. → Task 5 test.
2. **Destination coordinate out of range** — a malformed header must be dropped and counted, never deadlock the input buffer. → Task 5 test.
3. **Credit exhaustion mid-packet** — packet atomicity must hold under full downstream buffers (no interleaving, no flit loss). → Task 4 test.
4. **Mode-switch broadcast while packets are in flight** — the ack barrier must wait for drain; no flit loss or reordering across the switch. → Task 6 test.
5. **Torus wrap on a dimension with 2 cells** — wrap link between two neighbors must not double-count hops or break the dateline rule. → Task 9 test.

---

## File Structure

- Modify: `projects/components/fabric-gen-ip/delta/bin/delta_generator.py` — CLI args (`--topology mesh`, `--cells-x/y/z`, `--torus`, `--source-route`, `--speculation`, `--fifo-impl`), validation, dispatch to mesh package.
- Create: `projects/components/fabric-gen-ip/delta/bin/delta_mesh/__init__.py` — package exports.
- Create: `.../bin/delta_mesh/config.py` — `DeltaMeshConfig` dataclass + validation functions.
- Create: `.../bin/delta_mesh/cell.py` — `DeltaMeshCell(Module)`: emits `delta_mesh_cell.sv`.
- Create: `.../bin/delta_mesh/fabric.py` — `DeltaMeshFabric(Module)`: emits `delta_mesh_fabric_<X>x<Y>x<Z>.sv` (grid instantiation, wrap links, boundary local port exposure).
- Create: `.../bin/delta_mesh/tables.py` — routing-table image builders: `default_dor_image(cfg)`, `mode_image(cfg, mode_id)` for the 8 standard modes.
- Create: `.../bin/delta_mesh/header.py` — TUSER header field offsets/widths (single source of truth shared by cell emission and tests).
- Create (generated, checked in): `projects/components/fabric-gen-ip/delta/rtl/delta_mesh_cell.sv`, `rtl/delta_mesh_fabric_*.sv`, `rtl/mesh_mode_*.svh` (table images), `rtl/filelists/delta_mesh.f`.
- Create: `projects/components/fabric-gen-ip/delta/dv/tests/test_delta_mesh_*.py` (+ `dv/tb/delta_mesh_*_th.sv` flattening harnesses where BFMs need named ports), `dv/tbclasses/delta_mesh_tb.py`.
- Create: `projects/components/fabric-gen-ip/delta/bin/tests/test_delta_mesh_perf.py`.
- Create: `bin/delta_mesh_perf.py` — performance model per spec §10.
- Modify (final task): delta GAS/HAS/MAS — flip `> **PLANNED**` admonitions to implemented for delivered features; rebuild the three PDFs.

---

### Task 1: Mesh CLI + config validation

**Files:**
- Modify: `projects/components/fabric-gen-ip/delta/bin/delta_generator.py`
- Create: `projects/components/fabric-gen-ip/delta/bin/delta_mesh/__init__.py`
- Create: `projects/components/fabric-gen-ip/delta/bin/delta_mesh/config.py`
- Test: `projects/components/fabric-gen-ip/delta/bin/tests/test_delta_mesh_config.py`

**Interfaces:**
- Produces: `DeltaMeshConfig` dataclass — fields `cells_x, cells_y, cells_z: int`, `torus_x, torus_y, torus_z: bool`, `source_route: bool`, `speculation: bool`, `fifo_impl: str` (`"reg"`/`"sram"`), `data_width: int`, `user_width: int`, `amba5: bool`, `add_counters: bool`; `validate_mesh(cfg) -> None` raising `ValueError` with a specific message; `header_width(cfg) -> int` returning `6*max(1,clog2(max(x,y,z)))+32`... actually `6*COORD_W + 32` where `COORD_W = max(1, ceil(log2(max(cells_x,cells_y,cells_z))))`.

- [ ] **Step 1: Write the failing tests**

```python
def test_torus_requires_two_cells():
    with pytest.raises(ValueError, match="torus.*>= 2"):
        validate_mesh(DeltaMeshConfig(cells_x=1, torus_x=True, ...))
def test_user_width_below_header_rejected():
    with pytest.raises(ValueError, match="user-width"):
        validate_mesh(DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1, user_width=8, ...))
def test_header_width_formula():
    assert header_width(DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1)) == 6*2 + 32
```

- [ ] **Step 2: Run, verify failures** — `venv/bin/python -m pytest projects/components/fabric-gen-ip/delta/bin/tests/test_delta_mesh_config.py -v` → import/collection errors.
- [ ] **Step 3: Implement** `config.py` (dataclass + `validate_mesh` rules: dims >= 1; torus only on dims >= 2; `user_width >= header_width`; `fifo_impl` in {"reg","sram"}) and wire `delta_generator.py`: add the argparse flags and `"mesh"` as a `--topology` choice; dispatch to the mesh package with a stub emitter that raises `SystemExit("mesh RTL generation lands in Task 2")` until then. The task-1 tests exercise only `config.py`.
- [ ] **Step 4: Run, verify pass.**
- [ ] **Step 5: Commit** (pathspec: the three bin files + test).

### Task 2: `delta_mesh_cell` skeleton — ports, header, single-VC default DOR pipeline

**Files:**
- Create: `.../bin/delta_mesh/header.py`, `.../bin/delta_mesh/cell.py`
- Create (generated): `.../rtl/delta_mesh_cell.sv`, `.../rtl/filelists/delta_mesh.f`
- Test: `.../dv/tests/test_delta_mesh_cell_routing.py` + `.../dv/tb/delta_mesh_cell_th.sv`

**Interfaces:**
- Consumes: `DeltaMeshConfig`, `validate_mesh`, header offsets from `header.py`: `FIELD_OFFSETS = {"dst_x":0, "dst_y":COORD_W, ...}` built by `build_header_offsets(coord_w) -> dict[str, tuple[int,int]]`.
- Produces: module `delta_mesh_cell` with parameters `DATA_WIDTH, USER_WIDTH, COORD_W, POS_X, POS_Y, POS_Z, NUM_VC=2, FIFO_IMPL="reg", ENABLE_COUNTERS=1`; ports `aclk, aresetn`, and for each of the 7 ports `p`: `s_axis_tdata[DATA_WIDTH][7]`, `s_axis_tvalid[7]`, `s_axis_tready[7]`, `s_axis_tlast[7]`, `s_axis_tuser[USER_WIDTH][7]` (plus `m_*` mirrors) and credit sidebands `s_credit[7][NUM_VC]`, `m_credit[7][NUM_VC]` (credit value ports carry current credit count). DOR: head-flit dst compared to POS_*; route +axis before +y before +z (dimensions in order, one hop per stage toward rapids boundary: negative direction first — boundary is at coord 0), output = matching neighbor port; non-head beats follow the packet's allocated output. Single VC used (VC0); grants packet-atomic (hold output until TLAST).

- [ ] **Step 1: Failing test** — cocotb via a flattening harness `delta_mesh_cell_th.sv`: instantiate `delta_mesh_cell` at POS (1,1,0) in a 4x4x1 grid; drive a 1-packet flit into the local port with dst (3,0,0); assert it exits `m_axis` on the port matching the first DOR hop (`P_X_POS`) with header and payload intact; drive into `s_axis` on `P_X_NEG` with dst (0,1,0) → exits `P_Y_NEG`... second hop toward y=0. Run: `make -C projects/components/fabric-gen-ip/delta/dv/tests run-cocotb_test_delta_mesh_cell_dor-func`.
- [ ] **Step 2: Run, verify fail** (module/filelist absent).
- [ ] **Step 3: Implement** `header.py`, `cell.py` (route compute + mux, `always_ff` pipeline with house `ALWAYS_FF_RST`, no buffers yet — direct ready/valid steering), generate `delta_mesh_cell.sv` + `delta_mesh.f` (sources: cell only) via `delta_generator.py --topology mesh --cells-x 4 --cells-y 4 --cells-z 1 --user-width 64` (checked-in artifact from the default 4x4x1 config).
- [ ] **Step 4: Run test, verify pass; run flat AMBA5 regression (Global Constraints).**
- [ ] **Step 5: Commit.**

### Task 3: Fabric top generator + all-pairs suite

**Files:**
- Create: `.../bin/delta_mesh/fabric.py`
- Create (generated): `.../rtl/delta_mesh_fabric_4x4x1.sv`
- Modify: `.../bin/delta_generator.py` (dispatch)
- Test: `.../dv/tests/test_delta_mesh_fabric_2x2.py` (+ harness `delta_mesh_fabric_2x2_th.sv`)

**Interfaces:**
- Produces: module `delta_mesh_fabric_<X>x<Y>x<Z>` with the same AXIS port naming but only the *boundary* local ports exposed (one per boundary cell, packed `s_local_* [NUM_BOUNDARY]`, `m_local_* [NUM_BOUNDARY]`), coordinates passed as `POS_X/POS_Y/POS_Z` parameters per instance; wrap links generated when `torus_{x,y,z}` (omit for this task; wrap arrives Task 9 — fabric.py takes the flags and ignores them for now is NOT acceptable: validate and error "torus not yet supported" until Task 9).

- [ ] **Step 1: Failing test** — 2x2x1 fabric, 4 boundary locals; for every ordered pair (a,b) of the 4 locals: send a packet a→b through the fabric (multi-hop), scoreboard payload at b. Concurrent all-pairs in one run.
- [ ] **Step 2: Run, verify fail.**
- [ ] **Step 3: Implement** `fabric.py` (nested generate loops over x,y,z instantiating `delta_mesh_cell`, boundary detection `x==0||x==X-1||y==0||y==Y-1||z==0||z==Z-1`, unconnected boundary neighbor ports tied off), dispatch in `delta_generator.py`, regenerate 4x4x1 artifacts.
- [ ] **Step 4: Run fabric test + cell test + flat regression.**
- [ ] **Step 5: Commit.**

### Task 4: Per-VC input buffers + credit flow control + packet atomicity

**Files:**
- Modify: `.../bin/delta_mesh/cell.py` (generated RTL gains buffers/credits)
- Test: `.../dv/tests/test_delta_mesh_flow_control.py`

**Interfaces:**
- Consumes: house `gaxi_fifo_sync` (`wr_valid/ready/data`, `rd_valid/ready/data`, `DEPTH`, `DATA_WIDTH`, `MEM_STYLE` — `MEM_STYLE` selected by `FIFO_IMPL`).
- Produces: per-port per-VC input FIFO (DEPTH=4), per-link credit counters initialized to DEPTH, `m_credit` reflects post-consume count, `s_credit` consumed on accepted flit. VC1 buffers present and selectable via header `vc` bit but both VCs use the same DOR function this task.

- [ ] **Step 1: Failing tests** — (a) fill a downstream port's buffers until credits exhaust; assert producer stalls without dropping; drain; assert payload complete and in order. (b) **Review Focus #3**: with one flit space left downstream, start a 4-beat packet from two sources to the same output; assert no interleaving and no loss. (c) back-to-back packets same port sustain 1 flit/clk steady-state.
- [ ] **Step 2: Run, verify fail.**
- [ ] **Step 3: Implement** buffers + credit counters in `cell.py` (single clock domain, `ALWAYS_FF_RST`; credit accounting in `always_ff`), regenerate.
- [ ] **Step 4: Run all mesh tests + flat regression.**
- [ ] **Step 5: Commit.**

### Task 5: Routing RAM tables + default image + in-band unicast config

**Files:**
- Modify: `.../bin/delta_mesh/cell.py`, `.../bin/delta_mesh/tables.py`
- Test: `.../dv/tests/test_delta_mesh_tables.py`

**Interfaces:**
- Produces: `route_table` RAM per cell, keyed (dst coord, QoS class) → (output port mask, VC) — sized for the full key at generation time (`(dst_x, dst_y, dst_z, qos)` → `{port_mask[6:0], vc}`); `default_dor_image(cfg) -> list[TableEntry]` rendered as an initial block (power-on image, DOR toward coord 0 boundary = rapids side); `check_acyclic(image, cfg) -> None` in tables.py raising `ValueError("cycle in VC0 subrelation")` on a cyclic port hop — called at generation time on every emitted image (the offline acyclicity checker, spec §13 formal assist); config message format on the local port (pinned): a config packet arrives on the local port addressed to the cell's own coordinate with QoS class 0 (the config class per the spec's class table — class 0 on the local port IS config by definition; data-to-self must use a non-zero class) and `sr_ptr[0]`=write (1) or read (0), payload beat 0 = `{table_index[15:0], entry_value}` — writes take effect same-cycle; reads return the entry on the local master's `m_axis` in a one-beat response. (Task 5 implementation note: `qos` is decoded for config classification and rides the table-address MSBs; routing lookups are qos-independent at power-on. Task 7 activates per-class routing.) Out-of-range dst in a data header: drop flit + increment `err_drop_cnt` (part of counter bank, visible as an output port `o_err_drop_cnt[31:0]`). Generated RTL carries `` `ifdef FORMAL `` assertions matching flat-mode discipline: one-hot output grant, TDEST-in-range, TLAST-before-grant-release (packet atomicity).

- [ ] **Step 1: Failing tests** — (a) **Review Focus #1**: power-on, no config: 4x4x1 all-pairs passes on the default image. (b) Read table entry via config read; rewrite the route for one dst to a different port; verify traffic follows the new route; readback confirms. (c) **Review Focus #2**: dst coord (9,9,0) on a 4x4 fabric → flit dropped at first hop, `err_drop_cnt` increments, fabric keeps working.
- [ ] **Step 2: Run, verify fail.**
- [ ] **Step 3: Implement** tables.py (image builders + entry packing), cell.py (RAM, config packet decode on local port, drop path).
- [ ] **Step 4: Run all mesh tests + flat regression.**
- [ ] **Step 5: Commit.**

### Task 6: Broadcast mode-switch + ack barrier + 8 standard modes

**Files:**
- Modify: `.../bin/delta_mesh/tables.py`, `.../bin/delta_mesh/cell.py`
- Create (generated): `.../rtl/mesh_mode_0.svh` … `mesh_mode_8.svh` (one include per mode image)
- Test: `.../dv/tests/test_delta_mesh_modes.py`

**Interfaces:**
- Produces: `mode_image(cfg, mode_id) -> list[TableEntry]` for the catalog (spec §5.4): 1=mesh (pure DOR), 2=systolic-1D (x-dim ring neighbor table), 3=wavefront-2D, 4=stencil-3D (6-neighbor halo), 5=broadcast (to all cells), 6=convergecast/reduce (to root 0,0,0), 7=all-to-all/transpose, 8=pipeline+rapids-stream (linear pipeline through locals to boundary). Mode register `r_mode[3:0]` (0=RAM/custom); broadcast config message (dst coord = all-ones) switches `r_mode`; each cell replies with a one-beat ack to the origin coordinate; origin's barrier completes when `X*Y*Z` acks received (count register exposed as `o_mode_acks`).

- [ ] **Step 1: Failing tests** — (a) issue broadcast switch to mode 1 on 2x2x1; wait `o_mode_acks==4`; traffic still all-pairs correct. (b) Modes 2,3,5,6 sanity: systolic ring neighbor delivers left→right; broadcast mode delivers a flit injected at one cell to ALL other cells' locals (no responses); convergecast delivers from every cell to root. (c) **Review Focus #4**: start mode-switch broadcast while 8 packets in flight; assert all delivered exactly once and ack count reaches 4 with zero drops.
- [ ] **Step 2: Run, verify fail.**
- [ ] **Step 3: Implement** mode images + broadcast decode + ack/barrier logic.
- [ ] **Step 4: Run all mesh tests + flat regression.**
- [ ] **Step 5: Commit.**

### Task 7: QoS — strict priority, aging, bulk minimum reservation

**Files:**
- Modify: `.../bin/delta_mesh/cell.py`
- Test: `.../dv/tests/test_delta_mesh_qos.py`

**Interfaces:**
- Produces: per-class injection buffers (separate from VC buffers: class selects VC and priority), strict priority order config(0) > latency(1) > bulk(2) at each output arbiter; aging counter per waiting packet (`AGING_LIMIT` parameter, default 64) inverting priority; bulk minimum reservation: parameter `BULK_MIN_CREDITS` (default 1) — an output reserves that many credits per cycle window for bulk when bulk is starved (counter `bulk_starve_cnt` exposed).

- [ ] **Step 1: Failing tests** — (a) saturate an output with bulk traffic; inject a latency-class packet; assert it passes within 3 cycles (strict priority). (b) Saturate with latency traffic; aged bulk packet (wait > AGING_LIMIT) wins the next grant (aging inversion). (c) Continued latency saturation with BULK_MIN_CREDITS=1: bulk gets >= 1 grant per AGING_LIMIT cycles (reservation).
- [ ] **Step 2: Run, verify fail.**
- [ ] **Step 3: Implement** class decode (header `qos`), per-class buffers, arbiter with aging + reservation using house `arbiter_matrix` for output selection.
- [ ] **Step 4: Run all mesh tests + flat regression.**
- [ ] **Step 5: Commit.**

### Task 8: Multicast (VC0-only, BRCP-conformed, source replication, no responses)

**Files:**
- Modify: `.../bin/delta_mesh/cell.py`, `.../bin/delta_mesh/tables.py`
- Test: `.../dv/tests/test_delta_mesh_multicast.py`

**Interfaces:**
- Consumes: mode 5 broadcast image + table `port_mask` multi-bit semantics (mask = set of output ports for a dest).
- Produces: head flit with `mcast=1` replicates at source to each mask port (one copy per port, same `packet_id`); delivery VC = VC0 only; response packets to a multicast destination are dropped at injection with `err_drop_cnt` increment (no-response rule, spec §6).

- [ ] **Step 1: Failing tests** — (a) multicast from (0,0,0) to all cells on 2x2x1: every local receives the full packet exactly once. (b) inject a response-shaped packet (mcast dst, non-mcast flag, src = a multicast group member) → dropped, counter increments, no deadlock. (c) multicast under saturation: delivery-VC (VC0) deadlock-free soak, 10^5 flits random background + periodic multicast.
- [ ] **Step 2: Run, verify fail.**
- [ ] **Step 3: Implement** replication + drop rule.
- [ ] **Step 4: Run all mesh tests + flat regression.**
- [ ] **Step 5: Commit.**

### Task 9: Systolic package — torus wrap links, route lookahead, source-route mode

**Files:**
- Modify: `.../bin/delta_mesh/fabric.py` (enable torus), `.../bin/delta_mesh/cell.py`
- Test: `.../dv/tests/test_delta_mesh_systolic.py`

**Interfaces:**
- Produces: wrap link generation per dimension when `torus_{x,y,z}` (fabric connects boundary X_NEG↔X_POS etc.); dateline rule: wrap-channel hop increments `misroute_budget` and forces VC0 at the dateline crossing; route lookahead: next-hop output computed one stage ahead, steady-state 1 cycle/hop (assert in test via measured latency on a ring); source-route mode (`--source-route`): header `sr_ptr` walks a precomputed port list, table bypassed; speculative VA+SA when `--speculation`: grant winner assumes VC allocation succeeds, retries on conflict (per build, off by default).

- [ ] **Step 1: Failing tests** — (a) **Review Focus #5**: 4x1x1 torus (--torus=x), systolic ring: each cell forwards to +X; measured per-hop latency 1 cycle steady-state after the first hop (lookahead). (b) 2x2x1 torus wrap: flit crossing the wrap link arrives on VC0 with budget incremented. (c) source-route: preloaded path local→+X→+Y exits at the expected port with table disabled (force wrong table entry, path still honored). (d) with `--speculation` enabled: same routing results as the non-speculative build on the all-pairs suite; no duplicated or lost flits under output contention.
- [ ] **Step 2: Run, verify fail.**
- [ ] **Step 3: Implement** wrap links, dateline, lookahead stage, source-route override, speculative allocation (retry FSM, `spec_active` statistic exposed).
- [ ] **Step 4: Run all mesh tests + flat regression.**
- [ ] **Step 5: Commit.**

### Task 10: Ocelus counter suite + DFT 3-configuration test mode

**Files:**
- Modify: `.../bin/delta_mesh/cell.py`, `.../bin/delta_mesh/fabric.py`
- Test: `.../dv/tests/test_delta_mesh_counters.py`

**Interfaces:**
- Produces: counter bank per cell (spec §8): flits_in/out per port, packets_in/out, stall cycles per output, credit stalls, err_drop_cnt, mode_acks, bulk_starve_cnt — all readable via the config-read mechanism (a counter index space in table address map, address `0x8000+`); DFT mode: config-write `r_dft_en` + `r_dft_pattern[1:0]` selects one of three fixed routing patterns (bypass, ring, all-to-root) independent of tables; `o_dft_active` flag.

- [ ] **Step 1: Failing tests** — (a) run known traffic, read each counter via config port, compare against TB scoreboard golden counts. (b) enable each DFT pattern; verify routing matches the fixed pattern on 2x2x1; `o_dft_active` high; normal traffic resumes cleanly after `r_dft_en=0`.
- [ ] **Step 2: Run, verify fail.**
- [ ] **Step 3: Implement** counters + DFT patterns.
- [ ] **Step 4: Run all mesh tests + flat regression.**
- [ ] **Step 5: Commit.**

### Task 11: Performance model `bin/delta_mesh_perf.py`

**Files:**
- Create: `bin/delta_mesh_perf.py`
- Test: `projects/components/fabric-gen-ip/delta/bin/tests/test_delta_mesh_perf.py`

**Interfaces:**
- Produces: `latency(params) -> float` — T0 = H·tr + D/v + L/b (spec §10); `throughput_gamma(params) -> float` — M/D/1 saturation γ_max; `pattern_traffic(name, dims)` for tornado/bit-complement/transpose; CLI `--cells-x/y/z --pattern --load` printing a latency/throughput table. Parameters dataclass `MeshPerfParams(hops, tr, serialization_d, v, l, b, load)`.

- [ ] **Step 1: Failing tests** — pinned numbers: zero-load latency for H=3, tr=1, D=64B, v=1B/cycle... use the spec's worked constants: `latency(MeshPerfParams(hops=3, tr=1, serialization_d=4, v=1, l=64, b=8)) == 3*1 + 4/1 + 64/8` (== 15); M/D/1 γ_max = 1 for load>=1... pin: `throughput_gamma(..., load=0.5) == 0.5/(1 - 0.5)`... keep exactly: ρ/(1+ρ) per the spec's M/D/1 model — copy the formula from spec §10 verbatim into the test.
- [ ] **Step 2: Run, verify fail.**
- [ ] **Step 3: Implement** the module.
- [ ] **Step 4: Run, verify pass.**
- [ ] **Step 5: Commit.**

### Task 12: Regression wiring, soak, docs status flip

**Files:**
- Modify: `projects/components/fabric-gen-ip/delta/dv/tests/Makefile` (nothing — tests.mk is generic; verify mesh tests run via `make -C ... run-all` if that target exists, else list targets), `rtl/filelists/delta_all.f` (add mesh sources), delta GAS/HAS/MAS md files, rebuilt `Delta_{HAS,MAS,GAS}_v1.0.{docx,pdf}`
- Test: soak run + full delta dv suite

- [ ] **Step 1: Wire** mesh suites into the area regression (follow how the AMBA5 suite is invoked from make/tests.mk; if per-test targets only, document the mesh target list in delta dv README).
- [ ] **Step 2: Run the full delta dv suite (flat + mesh) and a 10^6-flit random-table deadlock soak (spec §13 suite 4); all green.**
- [ ] **Step 3: Perf-model calibration** (spec §13 suite 8): run the tornado pattern at three loads on the generated 4x4x1 fabric; record measured vs `bin/delta_mesh_perf.py` modeled latency/throughput deltas in the suite log; fail if measured zero-load latency exceeds the model by > 20% (lookahead regression tripwire).
- [ ] **Step 3: Docs** — GAS ch02/04/06 and HAS ch07/MAS ch06: replace `> **PLANNED**` with implemented status where the feature landed (keep the spec-link); note §11 deferrals as still deferred. Rebuild the three PDFs per docs methodology (`: <Title>` captions, `### Figure` headings — the books were just conformance-fixed; do not regress that).
- [ ] **Step 4: Commit** (md + pdf/docx + filelist).
