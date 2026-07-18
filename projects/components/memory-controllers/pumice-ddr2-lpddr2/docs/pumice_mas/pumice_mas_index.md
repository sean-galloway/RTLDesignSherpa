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

**Version:** 0.4
**Date:** 2026-07-12
**Purpose:** Implementation-level micro-architecture specification for the unified DDR2 / LPDDR2 memory controller family

> **Note (v0.3):** Reconciled with the rearchitected RTL. The controller is a
> three-layer core — `pumice_axi4_ifc` (intakes + wr_data_cam + rd_cmd_cam),
> `pumice_mem_cmd_scheduler` (arbiter + FSM-free bank_timer + global_timers +
> refresh + init + mode_register), `pumice_dfi_layer` (single async-FIFO CDC +
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

### Chapter 2: Functional Blocks

**Integration (Macros — pure structural):**
- [Top-Level Integration (`pumice_core`)](ch02_blocks/01_top_integration.md)
- [AXI4 Interface (`pumice_axi4_ifc`)](ch02_macros/01_axi_frontend_macro.md)
- [Command Scheduler (`pumice_mem_cmd_scheduler`)](ch02_macros/02_command_scheduler_macro.md)
- [Data Path (CAMs + DFI layer)](ch02_macros/03_data_path_macro.md)
- [DFI v2.1 Layer (`pumice_dfi_layer`)](ch02_macros/04_dfi_v21_interface_macro.md)

**AXI4 Interface FUBs (`pumice_axi4_ifc`):**
- [AXI4 Intakes (`pumice_wr_intake`, `pumice_rd_intake`)](ch02_blocks/02_axi4_slave.md)
- [Address Mapper (`addr_mapper`, bank_lsb)](ch02_blocks/03_addr_mapper.md)
- [Read Command CAM (`pumice_rd_cmd_cam`)](ch02_blocks/04_rd_cmd_cam.md)
- [Write Data CAM (`pumice_wr_data_cam`)](ch02_blocks/05_wr_cmd_cam.md)
- [Write-to-Read Forward (snarf in `pumice_wr_data_cam`)](ch02_blocks/21_wr2rd_forward.md)

**Scheduling FUBs (`pumice_mem_cmd_scheduler`):**
- [Command Arbiter (`pumice_cmd_arbiter`)](ch02_blocks/07_scheduler.md) — CLOSE/OPEN/HAPPY_HYBRID
- [Open-page decision (inline in `pumice_cmd_arbiter`)](ch02_blocks/08_page_predictor.md)
- [Cross-bank Turnaround Timers (`global_timers`)](ch02_blocks/10_xbank_timers.md)
- [Global Timers (`global_timers`)](ch02_blocks/19_global_timers.md)
- [Refresh Controller (`refresh_ctrl`)](ch02_blocks/11_refresh_mgr.md)
- [Init Sequencer (`init_sequencer`)](ch02_blocks/12_init_engine.md)
- [Power-Down Controller (`powerdown_ctrl`)](ch02_blocks/13_power_state.md)
- [Mode Register (`mode_register`)](ch02_blocks/20_mode_register.md)

**Data Path FUBs (in CAMs + DFI layer):**
- [Write Data Path (`pumice_wr_data_cam` + `pumice_dfi_wr_serializer`)](ch02_blocks/17_wr_data_path.md)
- [Read Data Path (`pumice_rd_cmd_cam` + `pumice_dfi_rd_aligner`)](ch02_blocks/18_rd_data_path.md)

**DFI v2.1 FUBs (`pumice_dfi_layer`):**
- [DFI Command Formatter (`dfi_cmd_formatter`)](ch02_blocks/14_cmd_encoder.md)
- [DFI Layer / Gearing (`pumice_dfi_layer`)](ch02_blocks/15_gear_dfi.md)

**Absorbed (kept for design rationale; no standalone FUB exists today):**
- [Transaction Queue — absorbed into intake+CAMs](ch02_blocks/06_txn_queue.md)
- [Bank Machine — replaced by FSM-free bank_timer](ch02_blocks/09_bank_machine.md)
- [ODT Control — absorbed into dfi_cmd_formatter](ch02_blocks/16_odt_ctrl.md)

### Chapter 3: AXI / DFI Interfaces

- [AXI4 Slave Protocol](ch03_interfaces/01_axi4_interface_spec.md)
- [DFI v2.1 Master Protocol](ch03_interfaces/02_dfi_v21_interface_spec.md)

### Chapter 4: APB and Configuration

- [APB CSR Slave Protocol](ch04_apb_config/01_apb_interface_spec.md)
- [Register Map](ch04_apb_config/02_csr_map.md)
- [Runtime Overrides and Quiet Points](ch04_apb_config/03_runtime_overrides.md)
- [Family-Wide Config-Bit Applicability](ch04_apb_config/04_family_config_bits.md)

### Chapter 5: Programming

- [Initialization Sequence](ch05_programming/01_initialization.md)
- [Refresh and Power-State Programming](ch05_programming/02_refresh_power.md)
- [Multi-Rank Programming](ch05_programming/03_multi_rank.md)
- [Error Handling](ch05_programming/04_error_handling.md)

### Chapter 6: Configuration Reference

- [Build-Time Configuration Reference](ch06_configuration/01_build_config.md)
- [Runtime Configuration Reference](ch06_configuration/02_runtime_config.md)
