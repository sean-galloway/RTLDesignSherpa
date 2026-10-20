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

# DDR2 / LPDDR2 Family Controller Micro-Architecture Specification Index

**Version:** 0.10-draft
**Date:** 2026-10-20
**Purpose:** Implementation-level micro-architecture specification for the unified DDR2 / LPDDR2 memory controller family

> **Note (v0.9-draft, 2026-10-13):** the interim rock wrappers are gone.
> `pumice_core` now instantiates all five planes from common-ip directly —
> `mc_axi4_plane`, `mc_storage_plane`, `mc_scheduler_plane`,
> `mc_training_plane`, `mc_dfi_2p1_plane` — and every leaf FUB is common-ip
> too: the DDR2/LPDDR2 children moved on 2026-10-11 as `mc_xddr2_*`,
> `mc_page_policy`, and `mc_lpddr2_*`. `pumice_scheduler_plane`,
> `pumice_training_plane`, `dfi_signal_pack`, and `powerdown_ctrl` were
> removed. Pumice owns the tops, `pumice_pkg`, the `pumice_csr` RDL, and the
> parameter choices.

> **Note (v0.9-draft, 2026-10-10):** Phase-2 extraction. pumice_core now
> instantiates the common-ip blocks `mc_axi4_plane`, `mc_storage_plane`, and
> `mc_dfi_2p1_plane`; `pumice_scheduler_plane` and `pumice_training_plane`
> were thin rock wrappers around the common cores. Macro chapters describe
> the pumice integration and point at the owning common chapters; block
> chapters for moved FUBs carry a "lives in common-ip now" banner. The
> per-block microarchitecture of every moved block is owned by
> [common_mas](../../../../common-ip/docs/common_mas/common_mas_index.md);
> this book keeps pumice's provenance and measured history.

> **Note (v0.8):** LPDDR2 calibration and training landed in the RTL. New
> fourth plane `pumice_training_plane` (`pumice_zq_ctrl` + `pumice_lp_cal`)
> drives the scheduler's new `trn_cmd` maintenance channel (arbiter priority
> init > refresh > trn > demand); MRR rides the command FIFO as a 1-bit flag
> (`{mrr, ap, col, row, bank, rank, op}`), the formatter emits the MRR CA
> word, and the read aligner gained a cal-capture sideband. Seven CSRs at
> 0x0A0–0x0F0 (`CAL_*`) document it — see ch02 and ch04.

> **Note (v0.3):** Reconciled with the rearchitected RTL. The controller is a
> three-plane core — `pumice_axi4_plane` (intakes + wr_data_cam + rd_cmd_cam),
> `pumice_scheduler_plane` (arbiter + FSM-free bank_timer + global_timers +
> refresh + init + mode_register), `pumice_dfi_plane` (single async-FIFO CDC +
> cmd_path/wr_serializer/rd_aligner) — under `pumice_core`, plus optional
> `pumice_top_geared`. Chapters for SWAG-era blocks that no longer exist
> (`txn_queue`, `bank_machine`, `xbank_timers`, `cmd_encoder`, `odt_ctrl`,
> standalone `page_predictor`) have been rewritten to their replacement FUBs;
> the chapter filenames are unchanged. Address mapping is the single
> `ADDR_MAP.bank_lsb` knob; LPDDR2 is fully functional (bit-exact JESD209-2F CA).

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Architecture and Datapath](ch01_overview/01_architecture.md)
- [Top-Level Port List](ch01_overview/02_port_list.md)
- [Clocks and Reset](ch01_overview/03_clocks_and_reset.md)
- [Pipeline Latency and Mux-Level Schematics](ch01_overview/04_pipeline_latency.md)

### Chapter 2: Functional Blocks

**Integration (Macros — pure structural):**
- [Top-Level Integration (`pumice_core`)](ch02_blocks/01_top_integration.md)
- [AXI4 Interface (`mc_axi4_plane` via common-ip)](ch02_macros/01_axi_frontend_macro.md)
- [Command Scheduler (`mc_scheduler_plane` via common-ip)](ch02_macros/02_command_scheduler_macro.md)
- [Data Path (`mc_storage_plane` via common-ip)](ch02_macros/03_data_path_macro.md)
- [DFI v2.1 Plane (`mc_dfi_2p1_plane` via common-ip)](ch02_macros/04_dfi_v21_interface_macro.md)

**AXI4 Interface FUBs (`mc_axi4_plane` via common-ip — banners point to the owning common_mas chapters):**
- [AXI4 Intakes (`mc_wr_intake`, `mc_rd_intake`)](ch02_blocks/02_axi4_slave.md)
- [Address Mapper (`mc_addr_mapper`, bank_lsb)](ch02_blocks/03_addr_mapper.md)
- [Read Command CAM (`mc_rd_cmd_cam`)](ch02_blocks/04_rd_cmd_cam.md)
- [Read Return Ring (`mc_rd_return_ring`)](ch02_blocks/22_rd_return_ring.md)
- [Write Data CAM (`mc_wr_data_cam`)](ch02_blocks/05_wr_cmd_cam.md)
- [Write-to-Read Forward (snarf in `mc_wr_data_cam`)](ch02_blocks/21_wr2rd_forward.md)

**Scheduling FUBs (`mc_scheduler_plane` via common-ip):**
- [Command Arbiter (`mc_cmd_arbiter`)](ch02_blocks/07_scheduler.md) — CLOSE/OPEN/HAPPY_HYBRID
- [Page-policy engine (`mc_page_policy`)](ch02_blocks/08_page_policy.md)
- [Cross-bank Turnaround Timers (`mc_global_timers`)](ch02_blocks/10_xbank_timers.md)
- [Global Timers (`mc_global_timers`)](ch02_blocks/19_global_timers.md)
- [Refresh Controller (`mc_xddr2_refresh_ctrl`)](ch02_blocks/11_refresh_mgr.md)
- [Init Sequencer (`mc_xddr2_init_sequencer`)](ch02_blocks/12_init_engine.md)
- [Mode Register (`mc_xddr2_mode_register`)](ch02_blocks/20_mode_register.md)

**Data Path FUBs (CAMs + DFI plane — common-owned):**
- [Write Data Path (`mc_wr_data_cam` + `mc_dfi_wr_serializer`)](ch02_blocks/17_wr_data_path.md)
- [Read Data Path (`mc_dfi_rd_aligner` + `mc_rd_return_ring`)](ch02_blocks/18_rd_data_path.md)

**DFI v2.1 FUBs (`mc_dfi_2p1_plane` via common-ip):**
- [DFI Command Formatter (`mc_xddr2_cmd_formatter`)](ch02_blocks/14_cmd_encoder.md)
- [DFI Plane / Gearing (`mc_dfi_2p1_plane`)](ch02_blocks/15_gear_dfi.md)

**Training plane (LPDDR2 calibration / training):**
- [Training Plane (`mc_training_plane` via common-ip)](ch02_macros/05_training_plane_macro.md)
- [ZQ Calibration Controller (`mc_lpddr2_zq_ctrl`)](ch02_blocks/23_zq_ctrl.md)
- [DQ-Calibration Sequencer (`mc_lpddr2_dq_cal`)](ch02_blocks/24_lp_cal.md)

**Absorbed (kept for design rationale; no standalone FUB exists today):**
- [Transaction Queue — absorbed into intake+CAMs](ch02_blocks/06_txn_queue.md)
- [Bank Machine — replaced by FSM-free mc_bank_timer](ch02_blocks/09_bank_machine.md)
- [ODT Control — absorbed into mc_xddr2_cmd_formatter](ch02_blocks/16_odt_ctrl.md)
- [Power-Down Controller (`powerdown_ctrl`) — removed 2026-10-11](ch02_blocks/13_power_state.md)

### Chapter 3: AXI / DFI Interfaces

- [AXI4 Slave Protocol](ch03_interfaces/01_axi4_interface_spec.md)
- [DFI v2.1 Master Protocol](ch03_interfaces/02_dfi_v21_interface_spec.md)

### Chapter 4: APB and Configuration

- [APB CSR Slave Protocol](ch04_apb_config/01_apb_interface_spec.md)
- [Register Map](ch04_apb_config/02_csr_map.md)
- [Runtime Overrides and Quiet Points](ch04_apb_config/03_runtime_overrides.md)
- [Family-Wide Config-Bit Applicability](ch04_apb_config/04_family_config_bits.md)
- [Training-Plane Interface Contracts](ch04_apb_config/05_training_interface_contracts.md)

### Chapter 5: Programming

- [Initialization Sequence](ch05_programming/01_initialization.md)
- [Refresh and Power-State Programming](ch05_programming/02_refresh_power.md)
- [Multi-Rank Programming](ch05_programming/03_multi_rank.md)
- [Error Handling](ch05_programming/04_error_handling.md)

### Chapter 6: Configuration Reference

- [Build-Time Configuration Reference](ch06_configuration/01_build_config.md)
- [Runtime Configuration Reference](ch06_configuration/02_runtime_config.md)

### Chapter 7: Timing Diagrams

Generated from `design/waves/*.json` and rendered by `design/render_waves.py`;
none is drawn by hand.

- [Ideal Command Cadence](ch07_timing/01_ideal_cadence.md)
- [Performance Pathologies](ch07_timing/02_performance_pathologies.md)
