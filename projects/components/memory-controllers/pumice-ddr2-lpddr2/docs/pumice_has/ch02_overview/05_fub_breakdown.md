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

# FUB Breakdown

This section documents the **actual** Functional Unit Block decomposition as
implemented in the rearchitected RTL: three integration layers under
`pumice_core`, each built from leaf FUBs, driven by a PeakRDL CSR block in
`pumice_top`.

## Component Layout

Per the standard component layout:

```
pumice/
├── docs/                      # this HAS, MAS, generated PDFs
├── dv/                        # cocotb tests, BFM glue, tbclasses
└── rtl/
    ├── top/                   # pumice_top, pumice_core, pumice_top_geared
    ├── macro/                 # the three layer macros + pumice_csr.rdl + generated/
    ├── fub/                   # leaf FUBs (this section)
    ├── includes/              # shared `defines, package files (pumice_pkg)
    └── filelists/
        ├── top/               # one .f per top
        ├── macro/             # one .f per layer
        └── fub/               # one .f per FUB
```

Each FUB has one top SystemVerilog file named `<fub>.sv` with module `<fub>`,
a filelist under `filelists/fub/`, and a cocotb testbench under `dv/tests/`.

## Layer Hierarchy

`pumice_top` instantiates the PeakRDL `pumice_csr` block (config by name) and
`pumice_core`, which wires the three layers:

```
pumice_top                                (CSR block + core)
└── pumice_core
    ├── pumice_axi4_ifc                        ("host AXI4 -> CAM-buffered requests")
    │   ├── pumice_wr_intake                   AXI4 slave wr + AW-meta FIFO + wr-data FIFO
    │   ├── pumice_rd_intake                   AXI4 slave rd + snarf probe
    │   ├── addr_mapper                        flat AXI addr -> (rank, bank, row, col)
    │   ├── pumice_wr_data_cam                 WR CAM + wr-data SRAM (fill/commit-drain/snarf)
    │   └── pumice_rd_cmd_cam                  RD CAM + rd SRAM (return-fill/drain)
    ├── pumice_mem_cmd_scheduler               ("what command to issue this cycle")
    │   ├── pumice_cmd_arbiter                 single pick core (open-page inline)
    │   ├── pumice_bank_timers (bank_timer)    per-(rank,bank) FSM-free JEDEC "safe" timers
    │   ├── global_timers                      tFAW / tRRD / tWTR / tRTW / tCCD turnaround
    │   ├── refresh_ctrl                       tREFI postponer, REFab/REFpb dispatch
    │   ├── init_sequencer                     DDR2 + LPDDR2 JEDEC MR init
    │   └── mode_register                      MR shadow -> live CL/CWL/BL/AL
    └── pumice_dfi_layer                       ("single CDC + DFI v2.1 datapath")
        ├── pumice_dfi_cdc                     the ONE clock crossing (async gaxi FIFOs)
        ├── pumice_dfi_cmd_path                unpack cmd, drive DFI via dfi_cmd_formatter
        │       (uses dfi_cmd_formatter + dfi_signal_pack)
        ├── pumice_dfi_wr_serializer           commit-drain WR CAM -> dfi_wrdata + mask
        └── pumice_dfi_rd_aligner              dfi_rddata capture -> return-fill RD CAM
```

Also present but not in the default top build: `page_predictor` and
`powerdown_ctrl` (referenced / optional; verify against the filelists).

## FUB Inventory

### `pumice_axi4_ifc`

#### `pumice_wr_intake`
- **Purpose**: AXI4 slave write engine. AW/W/B handshakes with an AW-meta FIFO
  and a wr-data FIFO; splits each host burst at DRAM-burst byte boundaries so
  each command maps to one DRAM burst.
- **Key params**: `AXI_DATA_WIDTH`, `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `BL`,
  `NUM_ENTRIES`.
- **Downstream**: `addr_mapper`, `pumice_wr_data_cam`.

#### `pumice_rd_intake`
- **Purpose**: AXI4 slave read engine; splits the read burst; probes the
  write-data CAM for a read-your-write snarf hit (unscheduled, same-id,
  same-BL) before committing the read command.
- **Key params**: `AXI_DATA_WIDTH`, `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `BL`,
  `NUM_ENTRIES`.

#### `addr_mapper`
- **Purpose**: Decode a flat AXI address into (rank, bank, row, col) using the
  single `bank_lsb` knob: the bank field slides within the byte-offset-stripped
  word address and the column auto-splits below (`col_lo`) and above (`col_hi`)
  it, with the row/rank positions invariant. An optional bank XOR-hash folds
  row bits (+ a seed) into the bank index. Combinational, single stage.
- **Key params**: `AXI_ADDR_WIDTH`, `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`,
  `COL_WIDTH`.
- **Runtime inputs**: `bank_lsb_i`, `hash_en_i`, `hash_seed_i`
  (`ADDR_MAP.bank_lsb` / `hash_en` / `hash_seed`).
- **Notable**: Mirrors the Python address-mapping class in the DV repo; the
  same decode drives RTL and BFM. There is no scheme selector.

#### `pumice_wr_data_cam`
- **Purpose**: Write-data CAM. Fills each write burst into an SRAM and records
  the command; provides scheduler lookup / oldest / commit ports; commit-drains
  the burst to the DFI write serializer; and is the snarf source for read
  forwarding. An `r_fdone` fill-complete flag gates schedulability and snarf.
  Streaming read engine is FIFO-fed / oldest-pick — no active-slot state latch.
- **Key params**: `NUM_ENTRIES`, `N_SRAM_SLOTS`, `NUM_RANKS`, `NUM_BANKS`,
  `ROW_WIDTH`, `BL`.

#### `pumice_rd_cmd_cam`
- **Purpose**: Read-command CAM / reorder buffer. Records read commands;
  return-fills DRAM read beats into an SRAM; oldest-first drain engine (gated
  on data-ready) streams beats back to `pumice_rd_intake`. No active-slot latch.
- **Key params**: `NUM_ENTRIES`, `N_SRAM_SLOTS`, `NUM_RANKS`, `NUM_BANKS`,
  `ROW_WIDTH`, `BL`.

### `pumice_mem_cmd_scheduler`

#### `pumice_cmd_arbiter`
- **Purpose**: The single command-pick core. Picks one abstract command per
  cycle from {ACT, RD/RDA, WR/WRA, PRE, REF, MRS, NOP} from the CAM lookups,
  gated by the per-(rank,bank) `safe_*` from `pumice_bank_timers` and the
  turnaround windows from `global_timers`. The open-page decision is inline.
- **Page policy**: OPEN (row-hit reuse + explicit PRE on miss), CLOSE (auto-pre
  on every column op via RDA/WRA), or HAPPY_HYBRID (predictor-selected).
  Programmed via `REFRESH_TUNING.page_policy_or`.
- **Key params**: `NUM_ENTRIES`, `NUM_RANKS`, `NUM_BANKS`, `AGE_WIDTH`.
- **Notable**: A combinational picker with registered feedback — always
  macro-test it, since registered-feedback latency created double-issue hazards
  caught only at the layer level.

#### `pumice_bank_timers` (instantiates `bank_timer`)
- **Purpose**: Stamps one `bank_timer` per (rank, bank) and fans the arbiter's
  command-event strobes to the addressed instance. `bank_timer` is FSM-free:
  preset/decrement countdown timers (tRCD, tRAS, tRC, tRP, precharge-block) +
  a row-open register + a single auto-precharge bit. The per-command `safe_*`
  outputs are combinational off the timers (one register stage), so the arbiter
  sees the just-issued command's effect one cycle later with no multi-stage lag.
- **Key params**: `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`.
- **Runtime inputs**: `t_rcd_i`, `t_rp_i`, `t_ras_i`, `t_rc_i`, `t_wr_i`,
  `t_rtp_i`.

#### `global_timers`
- **Purpose**: Cross-bank / cross-rank turnaround windows: tFAW (4-ACT window),
  tRRD, tWTR, tRTW, tCCD. ANDed by the arbiter.
- **Runtime inputs**: `t_faw_i`, `t_rrd_i`, `t_wtr_i`, `t_rtw_i`, `t_ccd_i`.

#### `refresh_ctrl`
- **Purpose**: tREFI down-counter; postponed-refresh accumulator (JEDEC max 8);
  refresh-pending signal to the arbiter; REFab / REFpb dispatch
  (`REFRESH_TUNING.refpb_policy_or`).
- **Runtime inputs**: `t_refi_i`, `refresh_burst_i`.

#### `init_sequencer`
- **Purpose**: Cold-boot engine that runs the memtype-specific JEDEC MR/init
  sequence (DDR2 and LPDDR2), driving CKE / RESET_N and MR-write strobes into
  `mode_register`, and holds off traffic until init completes.
- **Runtime inputs**: `t_init_wait_i`, `t_dll_wait_i`, `t_mrd_wait_i`,
  `t_rp_wait_i`, `t_rfc_wait_i`, `memtype_i`.

#### `mode_register`
- **Purpose**: Per-rank Mode Register shadow + live decode to CL / CWL / BL / AL
  (memtype-dependent), plus drive-strength and ODT-rule outputs consumed by the
  DFI layer.
- **Key params**: `NUM_RANKS`, `MAX_MR_IDX` (17; covers DDR2 MR0..3 and LPDDR2
  MR0..16).

### `pumice_dfi_layer`

#### `pumice_dfi_cdc`
- **Purpose**: The single controller-to-PHY clock crossing, built from
  asynchronous gaxi FIFOs (command, write-data, read-data). One FIFO word is
  one DFI cycle, so the datapaths are bubble-free.
- **Key params**: `CMD_FIFO_DEPTH`, `WD_FIFO_DEPTH`, `RD_FIFO_DEPTH`,
  `N_FLOP_CROSS`.

#### `pumice_dfi_cmd_path` (uses `dfi_cmd_formatter` + `dfi_signal_pack`)
- **Purpose**: DFI-domain command path. Pops the abstract command stream from
  the CDC FIFO, unpacks {op, rank, bank, row, col, ap}, and drives the
  multi-phase DFI command bus via `dfi_cmd_formatter`; emits wr_fire / rd_fire
  strobes so the serializer / aligner can schedule their data phases.
- **`dfi_cmd_formatter`**: JEDEC command encoding into DFI wires — DDR2 drives
  cs_n / ras_n / cas_n / we_n / address / bank (including the A10 auto-precharge
  bit and ODT rule); LPDDR2 packs the 10-bit CA-bus command (two edges) onto
  `dfi_address`, per a `memtype` branch. Swap this when moving DFI generations.
- **`dfi_signal_pack`**: multi-phase aggregation — widens each DFI control bus
  to per-phase × `DFI_RATE`.

#### `pumice_dfi_wr_serializer`
- **Purpose**: On wr_fire, commit-drains the write burst from
  `pumice_wr_data_cam`'s SRAM and drives `dfi_wrdata` / `dfi_wrdata_en` /
  `dfi_wrdata_mask` with PHY alignment.
- **AXI ↔ DFI mask polarity**: AXI `wstrb`=1 means write; DFI `mask`=1 means
  do-not-write → `dfi_wrdata_mask = ~wstrb`.

#### `pumice_dfi_rd_aligner`
- **Purpose**: Drives `dfi_rddata_en` `t_rddata_en` cycles after a READ command;
  captures `dfi_rddata` beats; return-fills them into `pumice_rd_cmd_cam`.
- **Runtime inputs**: `t_rddata_en_i`, `t_phy_wrlat_i`, `rd_phase_i`,
  `wr_phase_i`.

## Data Width and Gearing

Two distinct concepts:

1. **Internal DFI geometry.** `DW = DRAM_BEAT_WIDTH * DFI_RATE` (128 default).
   One AXI beat is one DFI word is `DFI_RATE` DRAM beats; one AXI burst is one
   DRAM burst. The DW → per-phase split happens in `dfi_signal_pack` / the DFI
   layer. The host AXI data width equals `DW` at `pumice_top`.
2. **Host-width freedom.** The optional `pumice_top_geared` wrapper adds a free
   `HOST_AXI_DATA_WIDTH` and inserts the repository's formally-verified
   `axi4_dwidth_converter_wr` / `_rd` between a host-width slave and the fixed-DW
   core. `HOST_AXI_DATA_WIDTH == DW` is a bit-identical generate bypass. Verified
   host ∈ {64, 128, 256}.

## What Changed vs the Earlier Architecture

The controller was rearchitected from an earlier FSM-based decomposition. The
following blocks were retired; their behavior now lives in the FUBs shown:

| Retired block             | Replaced by                                                                        |
|---------------------------|------------------------------------------------------------------------------------|
| `txn_queue`               | the two CAMs: `pumice_wr_data_cam` + `pumice_rd_cmd_cam`                            |
| `bank_machine`            | FSM-free `bank_timer`, stamped by `pumice_bank_timers`                              |
| `xbank_timers`            | `global_timers` (turnaround) + `pumice_bank_timers` (per-bank)                      |
| `cmd_encoder`             | `dfi_cmd_formatter` (+ `dfi_signal_pack`)                                           |
| `odt_ctrl`                | ODT inside `dfi_cmd_formatter` / `mode_register` (no standalone block)              |
| `page_predictor` (standalone) | open-page decision inline in `pumice_cmd_arbiter` (`page_predictor.sv` optional) |
| `wr_cmd_cam`              | `pumice_wr_data_cam`                                                                |
| `scheduler`               | `pumice_mem_cmd_scheduler` (`pumice_cmd_arbiter` + timers + refresh + init)         |
| `gear_dfi`                | `pumice_dfi_layer`                                                                  |
| `axi_frontend` / `axi_intake` / `*_macro`-as-architecture | `pumice_axi4_ifc`, generated `pumice_csr`, `pumice_core` |

The old names may still appear in retired sentinel tests; they are not part of
the current architecture.

## Integration

The three layer macros are structural wiring; behavioral logic lives in the
leaf FUBs. The principal wiring concerns:

1. **Arbiter ↔ timing fan-out**: `pumice_bank_timers` exposes per-(rank,bank)
   `safe_*` off single-stage timers; `global_timers` exposes turnaround-OK
   signals. `pumice_cmd_arbiter` reduces these into one command per cycle.
2. **CAM ↔ DFI-datapath coupling**: `pumice_wr_data_cam`'s commit-drain feeds
   `pumice_dfi_wr_serializer`; `pumice_dfi_rd_aligner`'s return-fill advances
   `pumice_rd_cmd_cam`.
3. **The single CDC**: everything up to `pumice_dfi_cdc` is on `aclk`; the
   command path, serializer, and aligner are on `dfi_clk`.
