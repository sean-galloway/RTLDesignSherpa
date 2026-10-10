# Simplified DFI 2.1

**Source:** DFI Specification v2.1.1 (Denali Software, 17 June 2010) (paraphrased; section numbers cited per chapter)
**Edition:** Simplified for the pumice DDR2/LPDDR2 memory controller (its DFI layer is `rtl/macro/pumice_dfi_layer.sv`). Derived from the Memory Notes condensed study notes.
**Version:** 0.1
**Last Updated:** 2026-10-04
**Status:** Draft. Personal study notes.

---

## Overview

DFI 2.1 is the DDR PHY Interface specification that sits between a memory
controller and a PHY. This book condenses the signal groups, timing
parameters, initialization, command mapping, and system behavior of DFI 2.1
into the form needed to understand the pumice DDR2/LPDDR2 controller.

All signal tables follow the DFI 2.1 inventory. Special attention is given to
the LPDDR2 CA-bus mapping onto `dfi_address`, the optional update interface
that first appeared in DFI 2.1, and the fact that DFI 2.1 has no frequency
change interface beyond the optional `dfi_init_start` handshake.

## Document Structure

### Chapter 1: Introduction & Organization

- [01_introduction.md](ch01_introduction_organization/01_introduction.md) - What DFI is, MC/PHY split, edition lineage, optional features
- [02_organization.md](ch01_introduction_organization/02_organization.md) - Sub-interface map, clocking, frequency ratio, `_pN`/`_wN` replication
- [03_acronyms.md](ch01_introduction_organization/03_acronyms.md) - Terms used in this book

### Chapter 2: Sub-Interfaces

- [01_control.md](ch02_sub_interfaces/01_control.md) - Address, bank, RAS/CAS/WE, CKE, CS, ODT, reset signals
- [02_write_data.md](ch02_sub_interfaces/02_write_data.md) - `dfi_wrdata`, `dfi_wrdata_en`, `dfi_wrdata_mask`
- [03_read_data.md](ch02_sub_interfaces/03_read_data.md) - `dfi_rddata`, `dfi_rddata_en`, `dfi_rddata_valid`, `dfi_rddata_dnv`
- [04_update.md](ch02_sub_interfaces/04_update.md) - `dfi_ctrlupd_*` and `dfi_phyupd_*` idle-window handshakes
- [05_status.md](ch02_sub_interfaces/05_status.md) - Init, clock disable, frequency ratio, parity
- [06_training.md](ch02_sub_interfaces/06_training.md) - Read leveling and write leveling signals
- [07_low_power.md](ch02_sub_interfaces/07_low_power.md) - `dfi_lp_req`, `dfi_lp_wakeup`, `dfi_lp_ack`

### Chapter 3: Initialization & Training

- [01_initialization_and_training.md](ch03_initialization_training/01_initialization_and_training.md) - Power-up, init handshake, defaults, read/write leveling

### Chapter 4: Command & Data Carriage

- [01_command_mapping.md](ch04_command_data_carriage/01_command_mapping.md) - ACT/RD/WR/REF/PRE on control wires; LPDDR2 CA mapping
- [02_write_carriage.md](ch04_command_data_carriage/02_write_carriage.md) - Write enable and data timing
- [03_read_carriage.md](ch04_command_data_carriage/03_read_carriage.md) - Read enable and valid timing
- [04_walkthroughs.md](ch04_command_data_carriage/04_walkthroughs.md) - Wire-level ACT -> RD and ACT -> WR traces

### Chapter 5: Timing Parameters

- [01_families_and_ratio.md](ch05_timing_parameters/01_families_and_ratio.md) - `dfi_t*` naming, ownership, ratio phasing
- [02_parameter_tables.md](ch05_timing_parameters/02_parameter_tables.md) - Full DFI 2.1 timing parameter table

### Chapter 6: System Behavior

- [01_system_behavior.md](ch06_system_behavior/01_system_behavior.md) - Low power, update mechanism, and optional frequency change

### Chapter 7: Revision & Area Tie-In

- [01_revision_deltas.md](ch07_revision_and_area/01_revision_deltas.md) - 2.1 vs 2.0 and brief 3.1 preview
- [02_in_pumice.md](ch07_revision_and_area/02_in_pumice.md) - How pumice drives DFI 2.1 and what it leaves out

---

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 0.1 | 2026-10-04 | First draft |
: Version history
