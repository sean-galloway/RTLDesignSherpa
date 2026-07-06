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

# DDR2 / LPDDR2 Family Controller Hardware Architecture Specification Index

**Version:** 0.3
**Date:** 2026-06-21
**Purpose:** High-level hardware architecture specification for the unified DDR2 / LPDDR2 memory controller family

> **Note (v0.3):** The implementation has converged on a 16-FUB / 5-macro structure
> that differs from the early SWAG. `txn_queue`, `page_predictor`, `bank_machine`,
> and `odt_ctrl` were absorbed into surrounding FUBs; `mode_register`,
> `global_timers`, `wr2rd_forward`, `axi_intake`, `wr_cmd_cam`, `rd_cmd_cam` were
> added. See [FUB Breakdown](ch02_overview/05_fub_breakdown.md) for the current
> inventory and the macro hierarchy.

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Purpose and Scope](ch01_introduction/01_purpose.md)
- [Document Conventions](ch01_introduction/02_conventions.md)
- [Definitions and Acronyms](ch01_introduction/03_definitions.md)

### Chapter 2: System Overview

- [Scope and Goals](ch02_overview/01_scope.md)
- [Block Diagram](ch02_overview/02_block_diagram.md)
- [Module Hierarchy](ch02_overview/03_module_hierarchy.md)
- [Top-Level Interfaces](ch02_overview/04_top_level_ports.md)
- [FUB Breakdown (SWAG)](ch02_overview/05_fub_breakdown.md)

### Chapter 3: Architecture

- [AXI Frontend (`axi_frontend_macro`)](ch03_architecture/01_axi_frontend.md)
- [Scheduler (closed-page; per-(rank,bank) timing query)](ch03_architecture/02_scheduler.md)
- [Per-bank + cross-bank Timers (`xbank_timers`, `global_timers`)](ch03_architecture/03_bank_machines.md)
- [Refresh Controller (`refresh_ctrl`)](ch03_architecture/04_refresh.md)
- [Init Sequencer and Power-Down (`init_sequencer`, `powerdown_ctrl`, `mode_register`)](ch03_architecture/05_init_power.md)
- [DFI v2.1 Output Pipeline (`dfi_cmd_formatter`, `dfi_signal_pack`)](ch03_architecture/06_encoder_output.md)
- [Write / Read Data Paths (`wr_beat_sequencer`, `rd_cl_aligner`)](ch03_architecture/07_data_paths.md)
- [DFI v2.1 Wire Interface and CSR (planned)](ch03_architecture/08_dfi_csr.md)

### Chapter 4: Interfaces

- [AXI4 Slave Interface](ch04_interfaces/01_axi4.md)
- [DFI v2.1 Master Interface](ch04_interfaces/02_dfi_v21.md)
- [APB CSR Slave](ch04_interfaces/03_apb_csr.md)

### Chapter 5: Parameters

- [Build-Time vs. Runtime](ch05_parameters/01_build_vs_runtime.md)
- [Top-Level Parameter Table](ch05_parameters/02_parameters.md)
- [Characterization Knobs](ch05_parameters/03_characterization.md)
- [Family-Wide Config Bits](ch05_parameters/04_config_bits.md)

### Chapter 6: Integration

- [Clocks and Reset](ch06_integration/01_clocks_reset.md)
- [Init Sequences](ch06_integration/02_init_sequences.md)
- [CSR Register Map](ch06_integration/03_csr_map.md)
- [Verification Strategy](ch06_integration/04_verification.md)
- [Open Issues and TODOs](ch06_integration/05_open_issues.md)
