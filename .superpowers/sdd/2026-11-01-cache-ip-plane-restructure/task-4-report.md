# Task 4 Report: jet planes — `jet_cpu_plane`, `jet_coh_core`, jet tops recompose

## What I implemented

Extracted the jet planes from the monolithic jet tops by move-don't-edit and
recomposed both tops onto the plane structure, mirroring the Task 3 amber
shape (`u_cpu` + `u_coh` + `u_fab` + `u_monbus_arbiter` + `u_reset_sync` +
the sim-only assertion block). External port lists of `jet_top` and
`jet_ace_top` are unchanged.

### New RTL

- `projects/components/cache-ip/jet-mesi-l1/rtl/plane/jet_cpu_plane.sv`
  - CPU plane: `u_req_skid` (the D-6 `gaxi_fifo_sync` request skid),
    `u_frontend` (`l1_cpu_frontend`), `u_rsp` (`jet_rsp_seq`). The
    `stage_wr_ready` response-staging-room tap stays internal to the plane.
    Core-facing seam: the skid's held lookup request (`lkup_valid/addr/we/be/
    wdata` + `lkup_ready`), the `ctrl_error` dead-stop input (gates the
    frontend ready, as the old top-level `ctrl_req_ready` assign did), and
    the J4 response-sequencer partner pins (`ctrl_tag_req`, `rsp_tag_gnt`,
    `rsp_tag`, `ctrl_cpl_valid/tag/data`).
- `projects/components/cache-ip/jet-mesi-l1/rtl/plane/jet_coh_core.sv`
  - Coherence-core plane: `u_control` (jet_control), `u_mshr`, `u_wb`,
    `u_tag`, `u_data`, `u_repl`, `u_fill`, `u_drain`, `u_monlite`,
    `u_jet_monlite`, plus the integration logic moved verbatim from the tops
    (verified block-by-block against the pre-restructure `jet_top.sv`):
    the fill-launch adapter (r_eng_busy/r_pend/r_flight + the JET_CLS ->
    amber_ace_req_t class map), the data-array W-port mux, the coh_req
    drain-collision replay register, the status roll-ups, and the mon_state
    pseudo-state encoder with its l1_monlite tap wiring.
  - `sn_want` enters as the `sn_want_i` port (the fabric plane's
    `sn_want_o`, computed in Task 2, is now wired).
  - `fill_ar_done` enters as a port; the tops drive it with
    `m_axi_arvalid & m_axi_arready` (the fabric plane owns the m_axi pins).
  - Exports the l1_monlite stream (`mon_*` + `mon_dropped`) and the J7
    `jet_monlite` stream (`j7_mon_*`) separately; the tops merge them with
    the fabric-plane stream on the D-7 arbiter.
  - The fabric snoop seam uses the fabric planes' port names
    (`ctrl_snoop_*`, `ctrl_crresp`, `ctrl_cd*`) so the tops wire it direct.

### Ruling: where the jet coh_req replay logic landed

Task 2 created the fabric planes from amber's wiring: `l1_axi4_plane` carries
a generic `core_coh_req_*` -> `coh_req_*` pass-through and `l1_ace_plane`
consumes `coh_req_*` on-chip in `l1_ace_issue` — neither contains the jet
drain-collision replay register. The replay logic (`r_wb_coh_pend` /
`r_wb_coh_addr`, old `jet_top.sv:1173-1197`) depends on jet-control internals
(`w_fill_accept`, `ctrl_drain_start`, `wb_drain_addr`, `ctrl_fill_addr`,
`eng_fill_class`), so it cannot live in the shared common-ip fabric planes
(common-ip must not depend on jet). It moved verbatim into `jet_coh_core`,
which exports the merged `coh_req_*` stream; `l1_axi4_plane` re-exports it to
`jet_top`'s pins and `l1_ace_plane` consumes it in `jet_ace_top`. The ACE
plane's type filter (`ace_rd_req` only for RNSD/RU/CU/MU, `ace_wr_req` only
for EVICT) reproduces the old `jet_ace_top` issue-stream behavior exactly
(fill launches present read classes; WRITE_BACK pulses are swallowed where
the old top had `ace_wr_req` tied off).

### Recomposed tops

- `projects/components/cache-ip/jet-mesi-l1/rtl/top/jet_top.sv`
- `projects/components/cache-ip/jet-mesi-l1/rtl/top/jet_ace_top.sv`
  - Both are now `u_cpu` (jet_cpu_plane) + `u_coh` (jet_coh_core) + `u_fab`
    (l1_axi4_plane / l1_ace_plane) + `u_monbus_arbiter` + `u_reset_sync` +
    the sim-only assertion block. The sn_want AC-pending counter was deleted
    from the tops (it lives in the fabric planes since Task 2) and
    `u_fab.sn_want_o` now feeds `u_coh.sn_want_i`.
  - The MonBus arbiter goes from 4 clients `{l1_monlite, rd, wr, j7}` to 3
    `{core(l1_monlite), fab(rd+wr, merged inside the fabric plane), j7}` —
    the same rd/wr pre-merge Task 3 accepted for amber. `jet_ace_top`
    likewise: 3 clients `{core, fab, j7}` (it gains the J7 stream with the
    shared core; the ace top is elaboration-pinned only, no DV consumer).
  - The sim-only assertions stay at top level, retargeted onto read-only
    hierarchical taps into `u_coh` (the sanctioned l1_core pattern);
    `jet_top`'s sideband assertions read the top-level `coh_req_*` ports,
    `jet_ace_top`'s read the on-chip `coh_req_*` nets.
  - Now-unused localparams pruned from the tops' parameter blocks (the T3
    amber pattern), keeping `STRB_W/RSP_DEPTH/SEQ_W/IW/UW/CPU_REQ_W/
    CPU_RSP_W` (the seam + port geometry).

### DV tap retargets (per the brief's table)

- `projects/components/cache-ip/jet-mesi-l1/dv/tbclasses/jet_core_tb.py`
  - `u.u_control` -> `u.u_coh.u_control` (x2), `u.u_snoop` ->
    `u.u_fab.u_snoop`, `u.u_fill` -> `u.u_coh.u_fill`, `u.u_wb` ->
    `u.u_coh.u_wb`, `u.u_mshr.occupancy_o` -> `u.u_coh.u_mshr.occupancy_o`,
    `d.u_top.u_control.*` -> `d.u_top.u_coh.u_control.*` (x4, including the
    `r_cmt_state` force in `_s_illegal_state`).
- `projects/components/cache-ip/jet-mesi-l1/dv/tbclasses/jet_pair_rig_tb.py`
  - `a.u_control` -> `a.u_coh.u_control` (x2), `a.u_snoop` ->
    `a.u_fab.u_snoop`, `a.u_fill` -> `a.u_coh.u_fill`, `a.u_wb` ->
    `a.u_coh.u_wb`, `u_jet0.u_tag.mem` -> `u_jet0.u_coh.u_tag.mem`.

### Filelists

- New: `rtl/filelists/plane/jet_cpu_plane.f` (frontend + gaxi_fifo_sync +
  jet_rsp_seq), `rtl/filelists/plane/jet_coh_core.f` (jet control closure
  minus the rsp sequencer + common-ip arrays/repl/engines + both monlite
  observers).
- `jet_top.f` / `jet_ace_top.f` now compose the three plane filelists +
  reset_sync + monbus_arbiter (+ the sdpram bench closure in `jet_top.f`,
  still carried for the pair-rig merge).
- `jet_all.f` gains the two plane filelists.
- `bin/filelists.toml`: the jet area's `filelist_dirs` gains
  `rtl/filelists/plane` (matching the Task 1 cache-common pattern); without
  it the new plane filelists were a registry blindspot.

## What I tested and results

### Verilator lint (house flow, both tops)

```bash
python3 bin/flatten_filelist.py .../filelists/jet_top.f --resolve-env \
  --absolute-paths -o /tmp/jet_top_flat.f && \
verilator --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal \
  -I$REPO_ROOT/rtl/amba/includes -f /tmp/jet_top_flat.f --top-module jet_top
```

- `jet_top`: EXIT 0. `jet_ace_top`: EXIT 0. Only baseline-class warnings
  (PINCONNECTEMPTY on intentionally-open pins, VARHIDDEN on package-shadowed
  params, the pre-existing `w_aresetn` SYNCASYNCNET, ocelus_common_pkg
  UNUSEDSIGNAL). Baseline comparison vs the pre-restructure `jet_top`:
  130 warnings before / 149 after, same warning classes (the delta is the
  new module scopes' own VARHIDDEN/PINCONNECTEMPTY instances).

### Move-fidelity check

Scripted block-by-block comparison of the moved integration logic
(fill-launch adapter, data W-port mux, coh_req replay, status roll-ups,
mon_state encoder, rsp/skid/frontend instances) against the
pre-restructure `jet_top.sv`: all blocks identical modulo the
`w_aresetn` -> `aresetn` reset rename and the intended seam renames
(`sn_*` -> `ctrl_snoop_*`/`ctrl_cr*`, `fub_*` -> `fub_axi_*` ports,
`i_mon_time` -> `mon_time`).

### Review-Focus-1 grep

`u_core.u_snoop|u_core.u_control|u_top.u_snoop|u_top.u_control|
u_frontend.stage` over the cache-ip dv/ and rtl/top/ sources: zero hits.
(The one repo hit for `u_frontend.stage` is the sanctioned internal
`stage_wr_ready` tap inside `jet_cpu_plane.sv` itself.)

### Gates

- `python3 bin/filelist_registry.py --check`: PASS (jet area: 10 modules,
  10 covered, 0 broken refs; plane dir registered).
- `bin/check_sv_decl_order.py` and `bin/check_sv_call_select.py` on the four
  new/rewritten .sv files: clean.
- Pre-commit hook ran on the commit (NO --no-verify): all checks passed
  (decl order, call-select, discarded-verdicts ratchet, doc examples, staged
  .sv parse, port-list consumers, markdown links, emoji, filelist contract).
- `bin/check_task_ids.py`: PASS (138 areas).
- Commit: `900f190cd` on main (13 files: 2 new planes, 2 recomposed tops,
  2 new plane filelists + 3 updated filelists, `bin/filelists.toml`, both
  jet tbclasses, this report force-added past the .gitignore per the T2
  ruling).

## Handoff notes

- The suite run was the default collection (gate + func cells; 60 tests,
  including the func-level parity seq/strided/walk/thrash/mix cells with the
  100k-replay mixes). The TEST_LEVEL=full sign-off sweep (geometry x
  MSHR_COUNT x VICTIM_DEPTH x policy corners) was NOT run — per the plan
  that complete re-run is Task 6's job.
- `jet_ace_top` has no DV consumer (elaboration-pinned by the filelist
  lint); it gains the J7 jet_monlite stream on its MonBus with the shared
  jet_coh_core (3-client arbiter {core, fab, j7}).
- Foreign pre-existing working-tree state was left untouched (unstaged
  merlin report deletions, `formal/stream/scheduler/scheduler_flat.v`).
- Main moved mid-run (owner merge); track this work by content: commit
  `900f190cd`.

### DV suite

```bash
cd projects/components/cache-ip/jet-mesi-l1/dv/tests && \
  source /mnt/data/github/RTLDesignSherpa/env_python && python -m pytest . -q
```

Result: **60 passed, 0 failed in 2768s** (the full default collection: gate +
func cells for jet_control, jet_core, jet_monlite, jet_mshr, jet_pair_rig,
jet_parity — including the 100k-replay mix cells — jet_pkg, jet_rsp_seq,
jet_wb_buffer). This matches the pre-restructure green baseline. The run
exercises the recomposed `jet_top` (core TB + pair rig) end-to-end through
the retargeted taps; `jet_ace_top` is elaboration-pinned by the Verilator
lint above (no DV consumer exists for it yet).
