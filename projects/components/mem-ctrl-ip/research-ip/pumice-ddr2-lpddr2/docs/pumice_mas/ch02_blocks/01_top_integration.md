<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Top-Level Integration (`pumice_core` / `pumice_top`)

**Modules:** `pumice_core.sv`, `pumice_top.sv`
**Location:** `rtl/top/`
**Category:** Integration (structural wiring)
**Status:** Implemented

> **Note:** the early SWAG used a five-`*_macro` hierarchy
> (`pumice_core_macro`, `axi_frontend_macro`, `command_scheduler_macro`,
> `data_path_macro`, `dfi_v21_interface_macro`). That naming is retired. The
> live controller is a five-plane stack of common-ip macros instantiated
> directly by `pumice_core` (no pumice-local plane or wrapper), wrapped
> by `pumice_top` (which adds the PeakRDL CSR block) and optionally by
> `pumice_top_geared` (which adds a host-width AXI dwidth shim).

---

## Purpose

The controller top is structural wiring only — every behavioral statement lives
in a FUB or a plane macro. Two files make up the top:

- **`pumice_core`** — wires the five common-ip planes on their two clocks and
  exposes host AXI4 plus the DFI 2.1 pin bus. Config arrives on ports.
- **`pumice_top`** — instantiates `pumice_core` plus the PeakRDL-generated
  `pumice_csr` register block, and drives every core config port **by name** from
  the CSR `hwif_out.*` decode. It exposes the register cpuif, host AXI4, and the
  DFI pin bus.

An optional third file, `pumice_top_geared`, wraps `pumice_top` with a free
`HOST_AXI_DATA_WIDTH` and inserts the repo's formally-verified
`axi4_dwidth_converter_wr` / `axi4_dwidth_converter_rd` between a host-width AXI
slave and the fixed-`DW` core. `HOST == DW` is a generate bypass (bit-identical).
See [`docs/AXI_DRAM_GEARING_SCOPE.md`](../../AXI_DRAM_GEARING_SCOPE.md).

## `pumice_core` — the five planes

`pumice_core` instantiates exactly five plane modules, all from
`common-ip/rtl/macro/`, and the nets between them. There is no FSM and no CSR
decode. Beyond the packed-bus `assign` for the command word, the only logic is
small per-build arithmetic on config ports (the `t_ccd_i` floor at
`BURST_WORDS` and the active sub-command count / strides derived from `bl_i`
and `gear_i`).

```
pumice_core
+-- u_axi_plane    : mc_axi4_plane      (host AXI intakes + rd return ring)  [aclk]
+-- u_store_plane  : mc_storage_plane   (wr-data CAM + rd-cmd CAM)           [aclk]
+-- u_sched_plane  : mc_scheduler_plane (arbiter + timers + refresh/init/MR
|                                        + page policy, HAS_* defaults)      [aclk]
+-- u_train_plane  : mc_training_plane  (ZQ + DQ cal + trn_cmd mux + CDC,
|                                        HAS_LP_ZQ = HAS_LP_DQ_CAL = 1)      [aclk -> dfi_clk]
+-- u_dfi_plane    : mc_dfi_2p1_plane   (single async CDC + DFI datapath)    [aclk -> dfi_clk]
```

The interim pumice wrappers `pumice_scheduler_plane` and
`pumice_training_plane` were removed on 2026-10-11; their DDR2/LPDDR2 children
are now the common `mc_xddr2_*`, `mc_page_policy`, and `mc_lpddr2_*` FUBs,
composed by the common planes (`rtl/top/pumice_core.sv:601`, `:756`).

- Host AXI, the scheduler, and both CAMs run on **`aclk`** (`aresetn`).
- The DFI phase-packer and PHY interface run on **`dfi_clk`** (`dfi_rstn`).
- The datapath clock crossing is inside `mc_dfi_2p1_plane` (async gaxi FIFOs
  only); `mc_dfi_2p1_plane` is instantiated with `.ctl_clk(aclk)` /
  `.ctl_rstn(aresetn)` on the control side and `.dfi_clk` / `.dfi_rstn` on
  the PHY side. The training plane owns a second, sideband-only crossing
  in `mc_training_shell`
  (cal_expect down / captured data up for the read-aligner calibration
  capture) — see [ch02/25](../ch02_macros/05_training_plane_macro.md).

The internal data unit is the **DFI word** (`DFI_DATA_WIDTH = DRAM_BEAT_WIDTH *
DFI_RATE`, default 128). The host AXI data width equals the DFI word; a host that
runs a different AXI width uses the external `pumice_top_geared` shim (a separate
edge concern — the core does not gear internally).

### Plane instantiation inventory (`pumice_core`)

| Instance   | Module                        | Count | Clock              | Role                                            |
|------------|-------------------------------|-------|--------------------|-------------------------------------------------|
| `u_axi_plane`    | `mc_axi4_plane`             | 1     | `aclk`             | Host AXI4 face; wr/rd intakes (with `mc_addr_mapper`), splitter, chopper, rd return ring |
| `u_store_plane`  | `mc_storage_plane`          | 1     | `aclk`             | wr-data CAM + rd-cmd CAM; schedulable-entry vectors |
| `u_sched_plane`  | `mc_scheduler_plane`        | 1     | `aclk`             | `mc_cmd_arbiter` + bank/global timers + `mc_xddr2_refresh_ctrl` / `_init_sequencer` / `_mode_register` + `mc_page_policy` + cmd FIFO |
| `u_train_plane`  | `mc_training_plane`         | 1     | `aclk` → `dfi_clk` | `mc_lpddr2_zq_ctrl` + `mc_lpddr2_dq_cal` + `mc_training_shell` (slot mux + cal sideband CDC) |
| `u_dfi_plane`    | `mc_dfi_2p1_plane`            | 1     | `aclk` → `dfi_clk` | Single async CDC + DFI cmd/wr/rd datapath       |

There are **no** `generate` fan-out blocks in `pumice_core`. Per-(rank, bank)
fan-out (the bank timers) happens two levels down, in `mc_bank_timers` inside
`mc_scheduler_plane`.

### Inter-plane nets

`pumice_core` declares and wires these net groups (besides the
`mc_axi4_plane` ↔ `mc_storage_plane` descriptor-seam push and snarf ports):

1. **Scheduler ↔ storage CAM ports** — the per-entry schedulable vectors
   (`w_wr_sch_*`, `w_rd_sch_*`: valid, bank, row, col, older matrix,
   age-exceeded, qos, head-relative), the write commit handshake
   (`w_wr_commit_*`), and the read issue handshake (`w_rd_issue_*`).
2. **Storage commit-data → DFI wrdata** (`w_cm_*`: valid/ready/data/strb/last) and
   **DFI rddata → read return** (`w_ret_*`: valid/ready/data/resp/last).
3. **Scheduler command stream → DFI** — the abstract command
   `{mrr, ap, col, row, bank, rank, op}`, flattened into `w_cmd_data` (width
   `CMD_DW = $bits(dram_op_e) + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1 + 1`) by a
   single `assign`; `mrr` comes back from the scheduler's maintenance slot as
   `cmd_extra_o`.
4. **Scheduler ↔ training plane** — the `trn_cmd_*` channel (`w_trn_*`) onto
   the scheduler's generic `maint_*` slot, and `w_cal_busy` onto `maint_busy_i`.
5. **DFI plane ↔ training plane** — the calibration sideband
   (`w_cal_expect`, `w_cal_data`, `w_cal_valid`).
6. **Init handshake** — `w_init_start` / `w_init_complete` between the scheduler's
   init sequencer and the DFI plane's PHY-init side.

Note the burst-length mapping at the plane boundaries: `mc_axi4_plane` and
`mc_storage_plane` receive `.AXI_BEATS_PER_BURST(BURST_WORDS)` (the IFC/CAM view
of a burst is in DFI words), while `mc_dfi_2p1_plane` receives
`.DFI_BEATS_PER_BURST(BL_PUMICE)` (DRAM beats) plus the `N_SUBCMD` sub-burst
packing parameters.

## `pumice_top` — CSR + by-name config

`pumice_top` adds the register block and the config fan-out. It does two things:

1. Instantiates `pumice_csr` (PeakRDL passthrough cpuif) with the `hwif_in` /
   `hwif_out` struct pair. `hwif_in` defaults to `'{default:'0}` and the live
   telemetry members (stall counters, page/row-hit statistics, training-plane
   status and MRR data) are assigned over it in one `always_comb`.
2. Instantiates `pumice_core` and drives **every** config port by name from the
   decoded `hwif_out.*` fields. Representative mappings:

| Core port            | CSR field (`hwif_out.*`)                         |
|----------------------|--------------------------------------------------|
| `memtype_i`          | `PHY_TIMING.memtype` (0 = DDR2, 1 = LPDDR2)      |
| `page_policy_i`      | `REFRESH_TUNING.page_policy_or`                  |
| `bank_lsb_i`         | `ADDR_MAP.bank_lsb`                              |
| `hash_en_i`          | `ADDR_MAP.hash_en`                               |
| `hash_seed_i`        | `ADDR_MAP.hash_seed`                             |
| `t_rcd_i/t_rp_i/t_ras_i/t_rc_i` | `TIMINGS_RC_RCD_RP_RAS.*`             |
| `t_wr_i`             | `TIMINGS_CL_CWL_WR.tWR`                          |
| `t_rtp_i/t_rtw_i`    | `TIMINGS_RTP_RTW.*`                              |
| `t_faw_i/t_rrd_i/t_wtr_i/t_ccd_i` | `TIMINGS_RRD_FAW_WTR_CCD.*`         |
| `t_refi_i`           | `TIMINGS_RFC_REFI.tREFI`                         |
| `refresh_burst_i`    | `PHY_TIMING.refresh_burst`                       |
| `t_init_wait_i/t_dll_wait_i` | `INIT_TIMING0.*`                         |
| `t_mrd_wait_i/t_rp_wait_i/t_rfc_wait_i` | `INIT_TIMING1.*`              |
| `rd_phase_i/wr_phase_i` | `DFI_PHASE.*` (sliced to `[PHW-1:0]`)         |
| `t_phy_wrlat_i/t_rddata_en_i` | `PHY_TIMING.*`                          |

The CSR block is clocked on `aclk` with `.rst(~aresetn)` (PeakRDL uses an
active-high reset; the top inverts `aresetn`). See
[`rtl/macro/pumice_csr.rdl`](../../../rtl/macro/pumice_csr.rdl) for the full field
list.

## What the top does not do

- No datapath logic: `pumice_core` holds only the command-word `assign` and the
  config-port arithmetic noted above, and `pumice_top` only by-name field
  selects and the telemetry `hwif_in` assignments.
- No CSR field expansion in `pumice_core` (that is `pumice_csr`'s job; the top
  only reads decoded `hwif_out` fields).
- No clock gating (a synthesis-script concern).
- No reset synchronization in the top — each plane takes its own domain reset
  (`aresetn` for `aclk` logic, `dfi_rstn` for the PHY domain); the CDC inside
  `mc_dfi_2p1_plane` owns the cross-domain reset discipline.

This intentional poverty makes the top the obvious place for the structural-only
sanity check: every line is an instantiation, a net declaration, or a
port/field mapping.
