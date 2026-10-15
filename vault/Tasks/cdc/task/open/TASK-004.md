# TASK-004: Finish the boundary-reset_sync sweep on hot-lane component tops

**Priority:** P2
**Status:** open
**Owner:** TBD
**Filed:** 2026-10-14

## Background

The 2026-10-14 repo-wide audit found `reset_sync` was instantiated in only 2
design sites (amber tops, legacy RTC) while every other component top consumed
its external reset asynchronously (async assert **and** async deassert — the
metastability/race hazard `reset_sync` exists to fix). The owner approved a
tops-only remediation: synchronize once per clock domain at each component's
top wrapper; leaf/library cells stay untouched.

Swept and committed the same day (gate/func green per component): rapids
(`rapids_top`, `rapids_beats_top`), bch (4 tops), reed-solomon (6 tops),
andesite (`andesite_core`, aclk+dfi_clk), scoria (`scoria_core`, `scoria_top`),
kestrel (`kestrel_core`). Convention documented in
`docs/markdown/rtl-cdc/reset_sync.md` § Repository Convention; idiom copied
from `cache-ip/amber-mesi-l1/rtl/top/amber_top.sv`.

## Remaining tops (blocked on active lanes at filing time)

- `dma-ip/stream/rtl/top/stream_top_ch8.sv`, `stream_config_block.sv` — stream lane hot
- `mem-ctrl-ip/product-ip/granite-ddr2-lpddr2/rtl/top/granite_core.sv`, `granite_top_geared.sv` — mem-ctrl lane hot (ddr2-char)
- `mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/rtl/top/pumice_core.sv`, `pumice_top.sv` — same lane
- `cache-ip/common-ip/rtl/top/l1_core.sv`, `cache-ip/amber-mesi-l1/rtl/top/amber_pair_fabric.sv` — amber lane hot (amber's own two wrappers already synchronize; the pair fabric does not)

## Also in scope (side-findings from the sweep)

- `scoria_top_geared.sv` routes raw `aresetn` to its AXI dwidth converters —
  add the boundary synchronizer there too.
- **BUG (pre-existing, unrelated to reset work):** `andesite` top-level tests
  fail to compile: `dv/tb/andesite_core_tb.sv:368` references
  `t_rfc_wait_i`, which `andesite_core.sv` exposes as an input but the TB
  never declares while using `.*` hookup. Every `dv/tests/top` test fails at
  Verilator elaboration. Fix the TB declaration, then the reset-validated
  `andesite_core` can run.

## Done when

- Every top in the "Remaining tops" list carries the boundary idiom (N=3,
  KEEP_ATTRS=1, polarities matching the port, one instance per clock domain)
  and its filelist closes with `rtl/cdc/filelists/reset_sync.f`.
- Gate tests pass per component (owner-set minimum for this change; func/full
  sweeps on touched areas are nice-to-have follow-on, recorded here).
- `scoria_top_geared` synchronized.
- andesite TB `t_rfc_wait_i` compile break fixed and `dv/tests/top` gate green.

## rtl/amba candidates (owner asked; lane was hot at filing)

Classification of the bigger `rtl/amba` blocks, deferred because the rtl/amba
lane had live uncommitted work in the tree. Owner decision needed on whether
these self-protect (subsystem-level, user-facing) or stay library leaves:

- **Likely self-protect (complete subsystems a user instantiates directly):**
  `shared/sdpram_slave_axi4_axi4.sv`, `shared/sdpram_slave_axi4_axil.sv`,
  `shared/sdpram_slave_axil_axi4.sv` (complete AXI memory slaves),
  `wb4/wb4_master.sv`, `wb4/wb4_slave.sv`, `wb4/wb4_retry.sv` (complete WB4
  bus agents), `shared/axi_master_rd_splitter.sv`,
  `shared/axi_master_wr_splitter.sv` (infrastructure masters).
- **Probably leaves (TB/verification infrastructure, driven by clean TB
  resets):** `shared/axi4_master_wr_injector.sv`,
  `shared/axi4_master_rd_crc_check.sv`,
  `shared/axi4_slave_wr_crc_check.sv`, `shared/axi4_slave_rd_injector.sv`,
  `shared/axis4_master_injector.sv`, `shared/axis4_slave_pattern_check.sv`.
- **No sync (passive observers/monitors — must track the observed domain's
  reset):** everything under `ocelus/`, the `axi4_{master,slave}_{rd,wr}_mon`
  protocol monitors, `gaxi_*` leaf FIFOs/skids/regslice.
