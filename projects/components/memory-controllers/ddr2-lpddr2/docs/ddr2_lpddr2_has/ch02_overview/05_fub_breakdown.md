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
implemented in the RTL. It supersedes the early SWAG, which proposed ~14 FUBs
in a flat layout; the implementation converged on **16 leaf FUBs grouped under
5 macros**.

## Stream FUB Convention

Per the standard component layout:

```
ddr2-lpddr2/
├── docs/                      # this HAS, MAS, generated PDFs
├── dv/                        # cocotb tests, BFM glue, tbclasses
└── rtl/
    ├── fub/                   # 16 leaf FUBs (this section)
    ├── macro/                 # 5 integration macros
    ├── includes/              # shared `defines, package files
    ├── filelists/
    │   ├── fub/               # one .f per FUB
    │   └── macro/             # one .f per macro
    └── (no top/ — top-level is the outermost macro)
```

Each FUB has:
- One top SystemVerilog file named `<fub>.sv` with module `<fub>`
- A filelist `filelists/fub/<fub>.f`
- A cocotb testbench in `dv/tests/fub/test_<fub>.py`
- All outputs are **strict-flop registered** (Q of a dedicated flop, no
  combinational driver). See commit 97a91fb8.

## Macro Hierarchy

The 16 FUBs are grouped into **5 macros**. The top-of-tree is the outermost
macro that the SoC instantiates:

```
ddr2_lpddr2_core_macro                       (skeleton wrapper)
├── command_scheduler_macro                  ("what command to issue this cycle")
│   ├── scheduler                            FR-FCFS w/ closed-page policy
│   ├── xbank_timers                         per-(rank,bank) JEDEC timers
│   ├── global_timers                        tFAW / tRRD / tWTR / tRTW windows
│   ├── refresh_ctrl                         tREFI postponer, REFab/REFpb dispatch
│   ├── powerdown_ctrl                       Active / APD / SR / DPD FSM, CKE
│   ├── mode_register                        MR0/1/2/3 decode → live CL/CWL/BL/AL
│   └── init_sequencer                       cold-boot microprogram + MRS issue
├── data_path_macro                          ("move bytes between AXI and DFI")
│   ├── wr_beat_sequencer                    W-buf pull → DFI wrdata + mask
│   └── rd_cl_aligner                        DFI rddata capture → rd_inject beats
└── dfi_v21_interface_macro                  ("DFI v2.1 wire pack")
    ├── dfi_cmd_formatter                    JEDEC truth table for ACT/RD/WR/PRE/REF/MRS
    └── dfi_signal_pack                      multi-phase DFI signal aggregation

axi_frontend_macro                           ("host AXI4 → CAM-cached requests")
├── axi_intake                               AXI4 protocol + w_buf + b_fifo + R-emit
├── addr_mapper                              flat AXI addr → (rank, bank, row, col)
├── wr_cmd_cam                               W-side CAM (slot mgmt + match query)
├── rd_cmd_cam                               R-side CAM (slot mgmt + match query)
└── wr2rd_forward                            snarf-and-bypass for W-then-R same line
```

## FUB Inventory

The 16 FUBs by macro grouping.

### `axi_frontend_macro` (5 FUBs)

#### `axi_intake`
- **Purpose**: AXI4 slave protocol engine; AW/W/B and AR/R channel handshakes;
  w_buf for write data staging; b_fifo for ID-aware completion ordering;
  forwarded R-emit path from the wr2rd snarf bypass.
- **Key params**: `AXI_DATA_WIDTH`, `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`,
  `WR_CAM_DEPTH`, `RD_CAM_DEPTH`.
- **Upstream**: top-level AXI ports.
- **Downstream**: `addr_mapper` (address), `wr_cmd_cam` / `rd_cmd_cam`
  (slot push), `wr_beat_sequencer` (w_buf pull), `rd_cl_aligner` (rd_inject).

#### `addr_mapper`
- **Purpose**: Decode flat AXI address into (rank, bank, row, column) per the
  active address-mapping scheme.
- **Key params**: `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`, `COL_WIDTH`,
  `ADDR_MAP_SCHEMES_SYNTH`, `ADDR_MAP_SCHEME_DEFAULT`.
- **Notable**: Mirrors the Python `AddressMapping` class in the DV repo; the
  same decode function is used by RTL and BFM.

#### `wr_cmd_cam`
- **Purpose**: Per-write-op slot bank. Holds (rank, bank, row, len, slot
  metadata) for in-flight writes. Provides match-query output to the
  scheduler and beat-pull state to the wr_beat_sequencer.
- **Key params**: `WR_CAM_DEPTH`, `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`.

#### `rd_cmd_cam`
- **Purpose**: Per-read-op slot bank. Same role as wr_cmd_cam for reads,
  including the in-order-completion bookkeeping for the rd_cl_aligner.
- **Key params**: `RD_CAM_DEPTH`, `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`.

#### `wr2rd_forward`
- **Purpose**: Snarf-and-bypass path for a read that hits an in-flight write's
  staged data (same address). Returns data directly from `w_buf` without
  issuing the read on the DRAM, preserving AXI ordering.
- **Key params**: `WR_CAM_DEPTH`, `W_BUF_DEPTH`.

### `command_scheduler_macro` (7 FUBs)

#### `scheduler`
- **Purpose**: "What command to issue this cycle?" — picks one CMD per cycle
  from {ACT, RD/RDA, WR/WRA, PRE, REF, MRS, NOP} based on per-(rank,bank)
  ready, cross-bank windows, refresh priority, init/MR priority. Closed-page
  policy in v1 (RDA/WRA auto-precharge).
- **Key params**: `WR_CAM_DEPTH`, `RD_CAM_DEPTH`, `NUM_RANKS`, `NUM_BANKS`.
- **Notable**: The single hardest timing FUB. Outputs all strict-flop
  registered for hierarchical timing closure.

#### `xbank_timers`
- **Purpose**: Per-(rank, bank) JEDEC timing counters (tRCD, tRP, tWR, tRTP,
  tRC, tRAS); exposes per-bank `act_ready`, `rdwr_ready`, `pre_ready` to the
  scheduler.
- **Key params**: `NUM_RANKS`, `NUM_BANKS`.
- **Notable**: Absorbed what the early SWAG called `bank_machine_fub`; the
  per-bank FSM became distributed across the CAMs + scheduler + this FUB.

#### `global_timers`
- **Purpose**: Cross-bank / cross-rank timing windows: tFAW (4-ACT window),
  tRRD, tWTR, tRTW. Drives `_window_ok` signals into the scheduler.
- **Key params**: `NUM_RANKS`.
- **Storage**: 4-entry tFAW shift-register per rank.

#### `refresh_ctrl`
- **Purpose**: tREFI down-counter; postponed-refresh accumulator (JEDEC max 8);
  refresh-pending signal to scheduler.
- **Key params**: `NUM_RANKS`, `REFRESH_DEFER_MAX`.

#### `powerdown_ctrl`
- **Purpose**: Active / Active-Power-Down / Self-Refresh / Deep-Power-Down
  FSM; per-rank CKE drive; SR-entry / SR-exit coordination with
  `refresh_ctrl`.
- **Key params**: `NUM_RANKS`, `MEMTYPE` (DPD is LPDDR2 only).

#### `mode_register`
- **Purpose**: MR0/MR1/MR2/MR3 register file + decode to live CL/CWL/BL/AL,
  drive_strength, ODT values consumed by the data-path FUBs and scheduler.
- **Key params**: `MEMTYPE`.

#### `init_sequencer`
- **Purpose**: Cold-boot microprogram. Step-table per `MEMTYPE` driving CKE,
  RESET_N, MR-write strobes into `mode_register`. Emits `init_busy_o` to
  block the scheduler until init completes.
- **Key params**: `MEMTYPE`, `SIM_INIT_SCALE`.

### `data_path_macro` (2 FUBs)

#### `wr_beat_sequencer`
- **Purpose**: Pulls W beats out of `axi_intake.w_buf` via beat_pull; packs
  them into DFI_RATE DRAM beats per DFI cycle; drives `dfi_wrdata` /
  `dfi_wrdata_en` / `dfi_wrdata_mask` with PHY alignment; emits b_complete
  back to wr CAM.
- **Key params**: `DRAM_BEAT_WIDTH`, `DFI_RATE`, `MAX_BURST_LEN`,
  `WR_CAM_DEPTH`.
- **AXI ↔ DFI mask polarity**: AXI `wstrb`=1 means write; DFI `mask`=1 means
  do-not-write → `dfi_wrdata_mask = ~wstrb`.

#### `rd_cl_aligner`
- **Purpose**: Drives `dfi_rddata_en` t_rddata_en cycles after a READ command;
  captures `dfi_rddata` beats; streams them out as DRAM-beat-wide
  `rd_inject_*` handshakes to `axi_intake.R-emit`. Pulses `rd_beat_we`
  per accepted beat so the rd CAM slot retires.
- **Key params**: `DRAM_BEAT_WIDTH`, `DFI_RATE`, `MAX_BURST_LEN`,
  `RD_CAM_DEPTH`.

### `dfi_v21_interface_macro` (2 FUBs)

#### `dfi_cmd_formatter`
- **Purpose**: JEDEC truth table for ACT / RD / RDA / WR / WRA / PRE / PREA /
  REF / REFpb / MRS / NOP into DFI control wires (cs_n, ras_n, cas_n, we_n,
  address, bank). Includes ODT timing rule and A10 auto-precharge bit.
  Swap THIS FUB when moving to DFI v3/v4/v5/v6.
- **Key params**: `MEMTYPE`, `DFI_ADDR_WIDTH`, `DFI_BANK_WIDTH`, `DFI_RATE`.
- **Notable**: Absorbed what the SWAG called `cmd_encoder_fub` plus the
  `odt_ctrl_fub` rules.

#### `dfi_signal_pack`
- **Purpose**: Multi-phase DFI aggregation. For `DFI_RATE = N`, every DFI
  control bus is widened to per-phase × N; v1 uses phase 0 for the command,
  other phases drive NOP.
- **Key params**: `DFI_RATE`, `DFI_ADDR_WIDTH`, `DFI_BANK_WIDTH`,
  `DFI_CS_WIDTH`.

### `ddr2_lpddr2_core_macro`

Skeleton wrapper around the three sub-macros above. Pure structural — no
behavioral logic. Tie-offs in place for a future `ctrl_update_fub`
(quiet-point CSR update propagation).

## FUB Count Summary

| Macro                          | FUBs | Names                                                                       |
|--------------------------------|------|-----------------------------------------------------------------------------|
| `axi_frontend_macro`           | 5    | `axi_intake`, `addr_mapper`, `wr_cmd_cam`, `rd_cmd_cam`, `wr2rd_forward`    |
| `command_scheduler_macro`      | 7    | `scheduler`, `xbank_timers`, `global_timers`, `refresh_ctrl`, `powerdown_ctrl`, `mode_register`, `init_sequencer` |
| `data_path_macro`              | 2    | `wr_beat_sequencer`, `rd_cl_aligner`                                        |
| `dfi_v21_interface_macro`      | 2    | `dfi_cmd_formatter`, `dfi_signal_pack`                                      |
| `ddr2_lpddr2_core_macro`       | —    | (skeleton; wraps the three above)                                           |
| **Total leaf FUBs**            | **16** |                                                                           |

## Divergence from the Early SWAG

The early SWAG proposed a different decomposition. The implementation
diverged because the v1 scheduler policy (closed-page with RDA/WRA
auto-precharge) made several SWAG FUBs unnecessary:

| SWAG FUB                  | Status today                          | Why                                                                                   |
|---------------------------|---------------------------------------|---------------------------------------------------------------------------------------|
| `txn_queue_fub`           | Absorbed into `axi_intake` + CAMs     | Per-direction CAMs + b_fifo replace the unified queue                                 |
| `page_predictor_fub`      | Removed                               | Closed-page policy makes page prediction moot                                         |
| `bank_machine_fub`        | Absorbed into CAMs + `xbank_timers`   | Per-bank FSM became per-bank timing counters + per-slot CAM state                     |
| `odt_ctrl_fub`            | Absorbed into `dfi_cmd_formatter`     | ODT rules are part of the JEDEC command table, not a separate FSM                     |
| `dfi_master`              | Renamed → `dfi_signal_pack`           | Final wire packing only; protocol formatting is `dfi_cmd_formatter`                   |
| `csr_apb_fub`             | Not yet implemented                   | Planned for v2; CSR-load currently via testbench driver                               |
| (none)                    | NEW: `wr_cmd_cam`, `rd_cmd_cam`       | Split CAMs make per-direction match-query simpler                                     |
| (none)                    | NEW: `wr2rd_forward`                  | Snarf path for W-then-R same-line ordering                                            |
| (none)                    | NEW: `mode_register`                  | MR0/1/2/3 decode broken out (was conceptually inside `init_engine`)                   |
| (none)                    | NEW: `global_timers`                  | Cross-bank windows separated from per-bank counters                                   |

## Integration

The 5 macros are pure structural wiring; no behavioral logic. Every
behavioral statement belongs in a leaf FUB. The principal wiring concerns:

1. **Scheduler ↔ timing fan-out**: `xbank_timers` exposes per-(rank,bank)
   `act_ready` / `rdwr_ready` / `pre_ready` arrays; `global_timers`
   exposes per-rank window-OK signals. Scheduler reduces these into a
   single CMD decision per cycle.
2. **Per-rank fan-out** of CKE (from `powerdown_ctrl`) and CS_n / ODT
   (formatted by `dfi_cmd_formatter`).
3. **Per-phase fan-out** to `dfi_signal_pack`.
4. **CAM ↔ data-path coupling**: wr CAM's beat_pull controls
   `wr_beat_sequencer`'s pull state; rd CAM's slot bookkeeping is
   advanced by `rd_cl_aligner`'s per-beat strobe.

All inter-FUB outputs are strict-flop registered, so all macro-level
inter-FUB paths add one register stage per hop. This is a deliberate
trade for hierarchical timing closure.
