# Simplified DFI 4.0

**Source:** DFI Specification v4.0 (Denali Software) (paraphrased; section numbers cited per chapter)
**Edition:** Simplified for the andesite DDR4/LPDDR4 memory controller. Derived from the
Memory Notes condensed study notes (a personal paraphrase of the DFI source); timing values
follow the controller's design-point configurations.
**Version:** 0.1
**Last Updated:** 2026-10-04
**Status:** Draft. Personal study notes.

---

## Overview

DFI 4.0 (DDR PHY Interface, Version 4.0) is the DDR4-era revision of the MC/PHY seam. It
adds the pins and protocols needed for DDR4 (bank groups, ACT_n, CA parity, DBI, gear-down),
LPDDR4 (SDR CA bus, CA VREF training, dual channels), and a set of system features (PHY master,
disconnect protocol, write DQ training, DB training, per-slice read leveling) that did not exist
in DFI 3.1.

This book condenses the spec into the signal definitions, initialization, command/data carriage,
training, timing parameters and system behavior needed to understand and drive the interface from
a memory controller. The andesite controller is the running example: it targets DFI 4.0 because
its predecessor's "deliberately unimplemented" list is exactly the 3.1 -> 4.0 delta.

All examples use a deliberately simplified teaching model: one rank, four DFI phases at 1:4
frequency ratio, x8/x16 data slices, and a small bank geometry. Real implementations are wider and
deeper; the wire-level rules are identical.

## Document Structure

### Chapter 1: Introduction & Organization

- [01_introduction.md](ch01_introduction_organization/01_introduction.md) - What DFI is, MC/PHY split, why the seam exists, edition lineage
- [02_organization.md](ch01_introduction_organization/02_organization.md) - Sub-interface map for DFI 4.0, clocking, frequency ratio and phase replication, slices and channels
- [03_acronyms.md](ch01_introduction_organization/03_acronyms.md) - Terms used precisely in this book

### Chapter 2: Sub-Interfaces

- [01_control.md](ch02_sub_interfaces/01_control.md) - Control interface: ACT_n, command pins, address/bank/bank-group, chip ID, CKE, CS, ODT, reset
- [02_write_and_read_data.md](ch02_sub_interfaces/02_write_and_read_data.md) - Write data and read data interfaces: data buses, enable, chip select, DBI, mask, valid
- [03_update_status_error_low_power.md](ch02_sub_interfaces/03_update_status_error_low_power.md) - Update, status, error and low-power control interfaces
- [04_training_db_phy_master_geardown_channels.md](ch02_sub_interfaces/04_training_db_phy_master_geardown_channels.md) - Training, DB training, PHY master, geardown and LPDDR4 channels

### Chapter 3: Initialization & Training

- [01_reset_init.md](ch03_initialization_training/01_reset_init.md) - Power-up, dfi_init_start, dfi_init_complete, initialization timing
- [02_training.md](ch03_initialization_training/02_training.md) - Gate training, read/write leveling, CA training, write DQ training, DB training, PHY master

### Chapter 4: Command & Data Carriage

- [01_command_mapping.md](ch04_command_data_carriage/01_command_mapping.md) - How ACT/RD/WR/REF/PRE map onto DFI control wires; LPDDR4 CA-bus story
- [02_write_carriage.md](ch04_command_data_carriage/02_write_carriage.md) - Write data timing: dfi_wrdata_en, dfi_wrdata, mask/DBI, preamble, CRC
- [03_read_carriage.md](ch04_command_data_carriage/03_read_carriage.md) - Read data timing: dfi_rddata_en, dfi_rddata_valid, dfi_rddata, DBI
- [04_walkthroughs.md](ch04_command_data_carriage/04_walkthroughs.md) - End-to-end wire-level walkthroughs on the simplified model

### Chapter 5: Timing Parameters

- [01_parameter_families.md](ch05_timing_parameters/01_parameter_families.md) - dfi_t* naming, PHY vs MC observable, what each family constrains
- [02_ratio_and_phasing.md](ch05_timing_parameters/02_ratio_and_phasing.md) - What 1:1, 1:2 and 1:4 do to scheduling
- [03_parameter_tables.md](ch05_timing_parameters/03_parameter_tables.md) - Full parameter table for DFI 4.0 with plain-English meaning

### Chapter 6: System Behavior

- [01_low_power_and_update.md](ch06_system_behavior/01_low_power_and_update.md) - Low-power handshake, self-refresh, update mechanism (ctrlupd/phyupd)
- [02_refresh_and_frequency.md](ch06_system_behavior/02_refresh_and_frequency.md) - Refresh interaction and frequency change

### Chapter 7: Revision & Area Tie-In

- [01_revision_and_area.md](ch07_revision_and_area/01_revision_and_area.md) - 3.1 -> 4.0 deltas and how the andesite controller drives this DFI version

---

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 0.1 | 2026-10-04 | First draft |

: Version history for the simplified DFI 4.0 notes

**Source:** DFI Specification v4.0 sections 1.0, 2.0, 2.2
