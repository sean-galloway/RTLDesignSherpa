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

**Version:** 1.0-draft
**Date:** 2026-10-10
**Purpose:** High-level hardware architecture specification for the unified DDR2 / LPDDR2 memory controller family

> **Note (v0.4):** This revision reconciles the spec with the rearchitected RTL. The
> controller is now a three-plane core (`pumice_axi4_plane` + `pumice_scheduler_plane`
> + `pumice_dfi_plane` under `pumice_core`), with an optional host-width wrapper
> `pumice_top_geared`. The early SWAG blocks `txn_queue`, `bank_machine`,
> `xbank_timers`, `cmd_encoder`, `odt_ctrl`, and a standalone `page_predictor` no
> longer exist as FUBs — they were replaced by the CAMs, the FSM-free `bank_timer`,
> `mc_global_timers`, `dfi_cmd_formatter`, and the arbiter's inline open-page logic.
> Address mapping is now the single `ADDR_MAP.bank_lsb` knob (the 3-scheme selector is
> retired); LPDDR2 is fully functional. See [FUB Breakdown](ch02_overview/05_fub_breakdown.md).

> **Note (v0.9):** The core gained its fourth plane, `pumice_training_plane`
> (LPDDR2 ZQ calibration, MRR-based DQ calibration, and the maintenance
> arbitration that carries both) — see
> [Training Plane](ch03_architecture/09_training.md). The core under
> `pumice_core` is therefore `pumice_axi4_plane` + `pumice_scheduler_plane` +
> `pumice_training_plane` + `pumice_dfi_plane`; the DFI pin bus and the
> host AXI interface are unchanged.

> **Note (v1.0-draft, 2026-10-10):** the Phase-2 extraction moved the shared
> logic to `mem-ctrl-ip/common-ip/` and pumice was re-integrated onto it.
> `pumice_core` now instantiates all five planes from common-ip directly:
> `mc_axi4_plane`, `mc_storage_plane`, `mc_scheduler_plane`,
> `mc_training_plane`, and `mc_dfi_2p1_plane`. (The interim thin rock wrappers
> `pumice_scheduler_plane` and `pumice_training_plane` were removed on
> 2026-10-11 once their DDR2/LPDDR2 children moved into common-ip as
> `mc_xddr2_*` and `mc_lpddr2_*`.) The old `pumice_axi4_plane`,
> `pumice_dfi_plane`, and `dfi_signal_pack` no longer exist as RTL. See
> [What Moved to Common](ch02_overview/06_what_moved_to_common.md) and the
> family books
> [common_has](../../../../common-ip/docs/common_has/common_has_index.md) /
> [common_mas](../../../../common-ip/docs/common_mas/common_mas_index.md),
> which now own the moved blocks' microarchitecture.

> **Warning:** all timing CSRs are counts of `aclk` cycles, correct only at
> the MC clock frequency they were derived for. Change the MC clock frequency
> and every one of them must be re-derived and reprogrammed before traffic
> resumes — see the [CSR Register Map](ch06_integration/03_csr_map.md).
> Stale values present as data corruption, not errors.

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
- [FUB Breakdown](ch02_overview/05_fub_breakdown.md)
- [What Moved to Common (Phase-2 extraction)](ch02_overview/06_what_moved_to_common.md)

### Chapter 3: Architecture

- [AXI4 Interface (`mc_axi4_plane` via common-ip; address-map configuration)](ch03_architecture/01_axi_frontend.md)
- [Scheduler (common `mc_scheduler_plane`)](ch03_architecture/02_scheduler.md)
- [Bank + Global Timers (`mc_bank_timer`, `mc_global_timers`)](ch03_architecture/03_bank_machines.md)
- [Refresh Controller (`mc_xddr2_refresh_ctrl`)](ch03_architecture/04_refresh.md)
- [Init Sequencer and Power-Down (`mc_xddr2_init_sequencer`, `mc_xddr2_mode_register`)](ch03_architecture/05_init_power.md)
- [DFI v2.1 Command Path (`mc_xddr2_cmd_formatter`, `mc_dfi_cmd_path`)](ch03_architecture/06_encoder_output.md)
- [Write / Read Data Paths (CAMs + DFI serializer/aligner)](ch03_architecture/07_data_paths.md)
- [DFI v2.1 Plane and CSR (`mc_dfi_2p1_plane` via common-ip; `pumice_csr`)](ch03_architecture/08_dfi_csr.md)
- [Training Plane (`mc_training_plane`, `mc_lpddr2_zq_ctrl`, `mc_lpddr2_dq_cal`) — LPDDR2](ch03_architecture/09_training.md)

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
