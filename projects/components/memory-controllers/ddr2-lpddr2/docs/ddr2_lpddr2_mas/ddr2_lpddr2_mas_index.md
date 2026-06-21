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

**Version:** 0.2
**Date:** 2026-06-21
**Purpose:** Implementation-level micro-architecture specification for the unified DDR2 / LPDDR2 memory controller family

> **Note (v0.2):** The implementation converged on a **16 leaf FUB + 5 macro**
> structure. The chapter list below reflects the current RTL. Four chapters
> for SWAG-era blocks that no longer exist as standalone FUBs (`txn_queue`,
> `page_predictor`, `bank_machine`, `odt_ctrl`) are kept in place with a
> "absorbed into ..." header so the architectural reasoning isn't lost.

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
- [Top-Level Integration (`ddr2_lpddr2_core_macro`)](ch02_blocks/01_top_integration.md)
- [AXI Frontend Macro (`axi_frontend_macro`)](ch02_macros/01_axi_frontend_macro.md)
- [Command Scheduler Macro (`command_scheduler_macro`)](ch02_macros/02_command_scheduler_macro.md)
- [Data Path Macro (`data_path_macro`)](ch02_macros/03_data_path_macro.md)
- [DFI v2.1 Interface Macro (`dfi_v21_interface_macro`)](ch02_macros/04_dfi_v21_interface_macro.md)

**AXI Frontend (5 FUBs):**
- [AXI4 Intake (`axi_intake`)](ch02_blocks/02_axi4_slave.md)
- [Address XOR/Hash (`addr_mapper`)](ch02_blocks/03_addr_mapper.md)
- [Read Command CAM (`rd_cmd_cam`)](ch02_blocks/04_rd_cmd_cam.md)
- [Write Command CAM (`wr_cmd_cam`)](ch02_blocks/05_wr_cmd_cam.md)
- [Write-to-Read Forward (`wr2rd_forward`)](ch02_blocks/21_wr2rd_forward.md)

**Scheduling (8 FUBs in `command_scheduler_macro`):**
- [Scheduler (`scheduler`)](ch02_blocks/07_scheduler.md) — CLOSE/OPEN/HAPPY_HYBRID
- [HAPPY Page Predictor (`page_predictor`)](ch02_blocks/08_page_predictor.md)
- [Cross-Bank Timers (`xbank_timers`)](ch02_blocks/10_xbank_timers.md)
- [Global Timers (`global_timers`)](ch02_blocks/19_global_timers.md)
- [Refresh Controller (`refresh_ctrl`)](ch02_blocks/11_refresh_mgr.md)
- [Init Sequencer (`init_sequencer`)](ch02_blocks/12_init_engine.md)
- [Power-Down Controller (`powerdown_ctrl`)](ch02_blocks/13_power_state.md)
- [Mode Register (`mode_register`)](ch02_blocks/20_mode_register.md)

**Data Paths (2 FUBs in `data_path_macro`):**
- [Write Beat Sequencer (`wr_beat_sequencer`)](ch02_blocks/17_wr_data_path.md)
- [Read CL Aligner (`rd_cl_aligner`)](ch02_blocks/18_rd_data_path.md)

**DFI v2.1 Output (2 FUBs in `dfi_v21_interface_macro`):**
- [DFI Command Formatter (`dfi_cmd_formatter`)](ch02_blocks/14_cmd_encoder.md)
- [DFI Signal Pack (`dfi_signal_pack`)](ch02_blocks/15_gear_dfi.md)

**Absorbed (kept for design rationale; no standalone FUB exists today):**
- [Transaction Queue — absorbed into intake+CAMs](ch02_blocks/06_txn_queue.md)
- [Bank Machine — absorbed into CAMs+xbank_timers](ch02_blocks/09_bank_machine.md)
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
