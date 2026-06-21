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

# FUB Breakdown (First-Pass SWAG)

This section is a **first-pass SWAG** — Some Wild-Ass Guess — at the controller's Functional Unit Block decomposition. It follows the RTLDesignSherpa stream convention of organizing RTL as small, independently-verifiable blocks under `rtl/fub/`, with a single top-level integration in `rtl/top/`. The boundary lines below will move during detailed design; the purpose here is to establish the SWAG so that file layout, filelist generation, and per-FUB verification plans can start in parallel with the architectural detail.

## Stream FUB Convention

Per the standard component layout:

```
ddr2-lpddr2/
├── bin/                       # build / regression scripts
├── coverage_combined/         # aggregated coverage reports
├── coverage_data/             # raw cocotb coverage drops
├── docs/                      # this HAS, generated PDFs
├── dv/                        # cocotb tests, BFM glue
├── regs/                      # CSR JSON/YAML → generated SV/headers
├── reports/                   # synth/timing reports
└── rtl/
    ├── top/                   # ddr2_lpddr2_ctrl.sv (integration only)
    ├── fub/                   # leaf FUBs (this section)
    ├── includes/              # shared `defines, parameter packages
    ├── macro/                 # SRAMs, latches, hard-IP wrappers
    └── filelists/             # *.f files per FUB and per top
```

Each FUB has:
- One top SystemVerilog file with the same name as the FUB
- An optional `_pkg.sv` for parameter typedefs / config structs
- A filelist `filelists/<fub_name>.f`
- A `dv/` testbench that drives that FUB standalone

## FUB Inventory

The 14 leaf FUBs proposed below are grouped by major architectural role. Each entry gives the FUB name, primary inputs/outputs (informal), the parameters that govern its size, and a one-line purpose. These FUBs map directly to the sub-modules called out in §3 (Architecture) but are the level at which the **filelist** and **synthesis boundary** are drawn.

### Group A — AXI Frontend

#### `axi4_slave_fub`
- **Purpose**: AXI4 slave protocol engine; AW / W / B and AR / R channel handshake; ID-aware out-of-order completion buffer.
- **Key params**: `AXI_DATA_WIDTH`, `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `AXI_OOO_ACROSS_IDS`, `SUPPORT_FIXED_BURST`, `SUPPORT_WRAP_BURST`.
- **Upstream**: top-level AXI ports.
- **Downstream**: `addr_mapper` (decoded address), `txn_queue_fub` (request push), data-path FUBs (`wr_data_path_fub`, `rd_data_path_fub`).

#### `addr_mapper`
- **Purpose**: Decode flat AXI address into (rank, bank, row, column) per the active address-mapping scheme.
- **Key params**: `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`, `COL_WIDTH`, `ADDR_MAP_SCHEMES_SYNTH`, `ADDR_MAP_SCHEME_DEFAULT`.
- **Notable**: Mirrors the Python `AddressMapping` class in the DV repo; the same decode function is used by RTL and BFM.

### Group B — Transaction Buffering and Scheduling

#### `txn_queue_fub`
- **Purpose**: Pending-transaction queue with `row_hit` caching and saturating age counters.
- **Key params**: `TXN_QUEUE_DEPTH`, `AGE_MAX`.
- **Storage**: Distributed registers; for `TXN_QUEUE_DEPTH ≥ 32` consider promoting to a small SRAM in `rtl/macro/`.

#### `scheduler`
- **Purpose**: FR-FCFS priority function, lookahead window, refresh-priority gating, runtime `force_inorder` collapse.
- **Key params**: `SCHEDULER_MODE`, `LOOKAHEAD_DEPTH_MAX`.
- **Notable**: The single hardest synthesis-timing FUB in the design; expected to dominate the path from `txn_queue` to command issue.

#### `page_predictor_fub` *(conditional)*
- **Purpose**: HAPPY hybrid page-conflict predictor; synthesized only when `PAGE_POLICY == HAPPY_HYBRID`.
- **Key params**: `PAGE_PREDICTOR_TABLE_BITS`.
- **Storage**: One small SRAM (`rtl/macro/page_pred_table_sram`) for table size ≥ 12 bits; distributed registers below.

### Group C — Per-Bank State and Cross-Bank Timing

#### `bank_machine_fub`
- **Purpose**: Per-(rank, bank) FSM; per-bank timing counters; refresh handshake.
- **Key params**: `ROW_WIDTH`. Instantiated `NUM_RANKS × NUM_BANKS` times by the top.
- **Synthesis note**: Replicated; an attempt at sharing across banks is rejected because per-bank state must be queryable in parallel by the scheduler.

#### `xbank_timers`
- **Purpose**: Cross-bank timing constraints (tRRD, tFAW, tCCD, tWTR, tRTW, tRTRS, tCS); per-rank vs. global scope as documented in §3.3.
- **Key params**: `NUM_RANKS`, `NUM_BANKS`.
- **Storage**: Per-rank 4-entry tFAW FIFOs; remaining state is small down-counters.

### Group D — Refresh, Init, Power

#### `refresh_mgr_fub`
- **Purpose**: tREFI postponer; REFab / REFpb dispatch; round-robin rank dispatch; DARP bank selection; periodic ZQCS piggyback; PASR mask propagation.
- **Key params**: `NUM_RANKS`, `NUM_BANKS`, `REFPB_POLICY`, `REFRESH_DEFER_MAX`.

#### `init_engine_fub`
- **Purpose**: Microprogram-driven cold-boot init sequence per `MEMTYPE`; step-table ROM lookup; sub-step timing.
- **Key params**: `MEMTYPE`, `SIM_INIT_SCALE`.
- **Storage**: Step-table ROMs in `rtl/macro/init_steps_<memtype>_rom`.

#### `power_state_fub`
- **Purpose**: Active / Active-Power-Down / Self-Refresh / Deep-Power-Down FSM; CKE per-rank control; SR-entry / SR-exit coordination with `refresh_mgr_fub`.
- **Key params**: `NUM_RANKS`, `MEMTYPE` (DPD is LPDDR2 only).

### Group E — Command Encoding and Output Gear

#### `cmd_encoder_fub`
- **Purpose**: Swap between DDR2 (ras/cas/we) and LPDDR2 (CA-bus packed) encoding; selected at elaboration by `MEMTYPE`.
- **Key params**: `MEMTYPE`, `DFI_ADDR_WIDTH`, `N_PHASES`.

#### `gear_dfi_fub`
- **Purpose**: Pack scheduler-issued commands and data into per-phase DFI slots according to `N_PHASES`, `WRPHASE`, `RDPHASE`.
- **Key params**: `N_PHASES`, `WRPHASE`, `RDPHASE`, `DFI_DATA_WIDTH`.

#### `odt_ctrl_fub`
- **Purpose**: Drive per-rank `dfi_odt[r]` per the multi-rank termination rule (`ODT_RULE_MULTIRANK`). Cross-rank read/write turn-on/turn-off windows.
- **Key params**: `NUM_RANKS`, `ODT_RULE_MULTIRANK`, `MEMTYPE`.
- **Notable**: This FUB is the home of the famous "ODT-on-other-rank during read" rule — see §3.6.

### Group F — Data Paths

#### `wr_data_path_fub`
- **Purpose**: AXI W-channel → write-data buffer → DFI wrdata. Width-conversion (AXI `DW` → `NP × DFI_DW`). Byte-mask propagation.
- **Key params**: `AXI_DATA_WIDTH`, `N_PHASES`, `DFI_DATA_WIDTH`.

#### `rd_data_path_fub`
- **Purpose**: DFI rddata → read-data buffer → AXI R-channel; CL / CWL-aware capture; ID-tagged completion buffer for OoO return.
- **Key params**: `AXI_DATA_WIDTH`, `N_PHASES`, `DFI_DATA_WIDTH`, `AXI_OOO_ACROSS_IDS`.

### Group G — CSR

#### `csr_apb_fub`
- **Purpose**: APB3 slave; register file; CDC between `apb_pclk` and `mc_clk`; runtime override propagation with quiet-point sync.
- **Key params**: derived from CSR YAML in `regs/`.
- **Notable**: The register fields themselves are generated; the FUB wrapper provides the APB protocol and the CDC.

## FUB Count Summary

| Group                        | FUBs | Notes                                        |
|------------------------------|------|----------------------------------------------|
| A — AXI Frontend             | 2    | `axi4_slave`, `addr_mapper`                  |
| B — Transaction / Scheduling | 3    | `txn_queue`, `scheduler`, `page_predictor`*  |
| C — Bank state               | 2    | `bank_machine`, `xbank_timers`               |
| D — Refresh / Init / Power   | 3    | `refresh_mgr`, `init_engine`, `power_state`  |
| E — Encoding / Output        | 3    | `cmd_encoder`, `gear_dfi`, `odt_ctrl`        |
| F — Data paths               | 2    | `wr_data_path`, `rd_data_path`               |
| G — CSR                      | 1    | `csr_apb`                                    |
| **Total**                    | **16** | (`page_predictor` conditional; effective floor 15) |

The number is a SWAG; expect ±2 during detailed design as the boundary between `scheduler` ↔ `xbank_timers` and between `gear_dfi` ↔ `cmd_encoder` is re-litigated.

## Integration

`rtl/top/ddr2_lpddr2_ctrl.sv` is integration-only — pure structural wiring across the FUBs above, with **no behavioral logic**. Every behavioral statement belongs in a FUB.

The top has three principal wiring concerns:

1. **Per-rank, per-bank fan-out** of `bank_machine_fub` instances; their state aggregation to `scheduler`.
2. **Per-rank fan-out** of `dfi_cs_n`, `dfi_cke`, `dfi_odt` from `odt_ctrl_fub` and `power_state_fub`.
3. **Per-phase fan-out** to `gear_dfi_fub` and `wr_data_path_fub` / `rd_data_path_fub`.

The integration file is mechanically generated by a build-time wrapper-generator script from the FUB filelists; hand-editing is only for the leaf FUB instantiation block.
