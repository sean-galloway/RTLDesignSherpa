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
> live controller is a three-layer stack instantiated by `pumice_core`, wrapped
> by `pumice_top` (which adds the PeakRDL CSR block) and optionally by
> `pumice_top_geared` (which adds a host-width AXI dwidth shim).

---

## Purpose

The controller top is structural wiring only — every behavioral statement lives
in a FUB or a layer macro. Two files make up the top:

- **`pumice_core`** — wires the three functional layers on their two clocks and
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

## `pumice_core` — the three layers

`pumice_core` instantiates exactly three layer modules and the nets between
them. There is no FSM, no CSR decode, and no arithmetic beyond the packed-bus
`assign` for the command word.

```
pumice_core
├── u_ifc   : pumice_axi4_ifc          (host AXI + wr/rd CAMs)          [aclk]
├── u_sched : pumice_mem_cmd_scheduler (arbiter + timers + refresh/init)[aclk]
└── u_dfi   : pumice_dfi_layer         (single async CDC + DFI datapath)[aclk→dfi_clk]
```

- Host AXI, the scheduler, and both CAMs run on **`aclk`** (`aresetn`).
- The DFI phase-packer and PHY interface run on **`dfi_clk`** (`dfi_rstn`).
- The **one** clock crossing in the whole controller is inside
  `pumice_dfi_layer` (async gaxi FIFOs only). `pumice_dfi_layer` is instantiated
  with `.ctl_clk(aclk)` / `.ctl_rstn(aresetn)` on the control side and
  `.dfi_clk` / `.dfi_rstn` on the PHY side.

The internal data unit is the **DFI word** (`DFI_DATA_WIDTH = DRAM_BEAT_WIDTH *
DFI_RATE`, default 128). The host AXI data width equals the DFI word; a host that
runs a different AXI width uses the external `pumice_top_geared` shim (a separate
edge concern — the core does not gear internally).

### Layer instantiation inventory (`pumice_core`)

| Instance   | Module                        | Count | Clock              | Role                                            |
|------------|-------------------------------|-------|--------------------|-------------------------------------------------|
| `u_ifc`    | `pumice_axi4_ifc`             | 1     | `aclk`             | Host AXI4 face; wr-data CAM + rd-cmd CAM        |
| `u_sched`  | `pumice_mem_cmd_scheduler`    | 1     | `aclk`             | Command arbiter + bank/global timers + refresh + init + mode-register shadow |
| `u_dfi`    | `pumice_dfi_layer`            | 1     | `aclk` → `dfi_clk` | Single async CDC + DFI cmd/wr/rd datapath       |

There are **no** `generate` fan-out blocks in `pumice_core`. Per-(rank, bank)
fan-out (the bank timers) happens one level down, inside
`pumice_mem_cmd_scheduler`.

### Inter-layer nets

`pumice_core` declares and wires four net groups:

1. **Scheduler ↔ IFC CAM ports** — the per-bank scheduler lookup buses
   (`w_wr_lu_*`, `w_rd_lu_*`), the oldest-entry ports (`w_wr_old_*`,
   `w_rd_old_*`), the write commit handshake (`w_wr_commit_*`), and the read
   issue handshake (`w_rd_issue_*`). `N_LU = NUM_BANKS` (one lookup per bank).
2. **IFC commit-data → DFI wrdata** (`w_cm_*`: valid/ready/data/strb/last) and
   **DFI rddata → IFC rd-return** (`w_ret_*`: valid/ready/data/resp/last).
3. **Scheduler command stream → DFI** — the abstract command
   `{op, rank, bank, row, col, ap}`, flattened into `w_cmd_data` (width
   `CMD_DW = 4 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1`) by a single `assign`.
4. **Init handshake** — `w_init_start` / `w_init_complete` between the scheduler's
   init sequencer and the DFI layer's PHY-init side.

Note the parameter mapping at the IFC boundary: `pumice_core` passes
`.BL(BL / DFI_RATE)` to `pumice_axi4_ifc` (the IFC/CAM view of burst length is in
DFI words), while `pumice_dfi_layer` receives the full `.BL(BL)` (DRAM beats).

## `pumice_top` — CSR + by-name config

`pumice_top` adds the register block and the config fan-out. It does two things:

1. Instantiates `pumice_csr` (PeakRDL passthrough cpuif) with the `hwif_in` /
   `hwif_out` struct pair. `hwif_in` is currently tied to `'{default:'0}` —
   status/observability readback is a follow-up; config-drive is wired first.
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
[`rtl/macro/pumice_csr.rdl`](../../rtl/macro/pumice_csr.rdl) for the full field
list.

## What the top does not do

- No combinational logic beyond the single command-word `assign` in
  `pumice_core` and the by-name field selects in `pumice_top`.
- No CSR field expansion in `pumice_core` (that is `pumice_csr`'s job; the top
  only reads decoded `hwif_out` fields).
- No clock gating (a synthesis-script concern).
- No reset synchronization in the top — each layer takes its own domain reset
  (`aresetn` for `aclk` logic, `dfi_rstn` for the PHY domain); the CDC inside
  `pumice_dfi_layer` owns the cross-domain reset discipline.

This intentional poverty makes the top the obvious place for the structural-only
sanity check: every line is an instantiation, a net declaration, or a
port/field mapping.
