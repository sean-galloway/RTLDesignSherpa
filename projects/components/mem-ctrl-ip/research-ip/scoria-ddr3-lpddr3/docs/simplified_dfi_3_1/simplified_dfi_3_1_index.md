# Simplified DFI 3.1

**Source:** DFI Specification v3.1 (Denali Software) (paraphrased; section numbers cited per chapter)
**Edition:** Simplified for the scoria DDR3/LPDDR3 memory controller. Derived from the
Memory Notes condensed study notes (a personal paraphrase of the DFI source);
emphasis is on the features a DDR3/LPDDR3 controller actually uses.
**Version:** 0.1
**Last Updated:** 2026-10-04
**Status:** Draft. Personal study notes.

---

## Overview

The DDR PHY Interface (DFI) is the standard seam between a DDR memory
controller (MC) and its PHY. Version 3.1 widens the spec to support DDR4 and
LPDDR3 while keeping the same conceptual split: the MC issues commands and
data, the PHY retimes them to the DRAM interface, and both sides exchange
status, training, update, low-power and error handshakes.

This book condenses DFI 3.1 into the organization, signals, initialization,
command/data carriage, timing and revision material needed to understand the
scoria DDR3/LPDDR3 controller. It pays special attention to what changed from
the v2.1.1 baseline that scoria's predecessor inherited, and notes which
v3.1 features are DDR4- or LPDDR4-era and therefore absent from this
controller.

## Document Structure

### Chapter 1: Introduction & Organization

- [01_introduction.md](ch01_introduction_organization/01_introduction.md) - What DFI is, why the MC/PHY split exists, edition lineage
- [02_organization.md](ch01_introduction_organization/02_organization.md) - Sub-interface map, clocking, frequency ratios, slices/channels
- [03_acronyms.md](ch01_introduction_organization/03_acronyms.md) - Terms used precisely in this book

### Chapter 2: Sub-Interfaces

- [01_control.md](ch02_sub_interfaces/01_control.md) - Command/address/control signals from MC to PHY
- [02_write_data.md](ch02_sub_interfaces/02_write_data.md) - dfi_wrdata, dfi_wrdata_en, dfi_wrdata_mask, write chip select
- [03_read_data.md](ch02_sub_interfaces/03_read_data.md) - dfi_rddata_en, dfi_rddata, dfi_rddata_valid, read chip select
- [04_update.md](ch02_sub_interfaces/04_update.md) - MC-initiated and PHY-initiated update handshakes
- [05_status.md](ch02_sub_interfaces/05_status.md) - Init, frequency ratio, clock disable, parity and alert
- [06_training.md](ch02_sub_interfaces/06_training.md) - Gate training, read data eye training, write leveling, CA training
- [07_low_power.md](ch02_sub_interfaces/07_low_power.md) - dfi_lp_ctrl_req, dfi_lp_data_req, dfi_lp_ack, wakeup times
- [08_error.md](ch02_sub_interfaces/08_error.md) - dfi_error and dfi_error_info

### Chapter 3: Initialization & Training

- [01_reset_init.md](ch03_initialization_training/01_reset_init.md) - Power-up, dfi_init_start, dfi_init_complete, initialization timing
- [02_training.md](ch03_initialization_training/02_training.md) - Which training features exist in v3.1 and how they are requested

### Chapter 4: Command & Data Carriage

- [01_command_mapping.md](ch04_command_data_carriage/01_command_mapping.md) - How ACT/RD/WR/REF/PRE map onto DFI control wires; LPDDR CA bus
- [02_write_carriage.md](ch04_command_data_carriage/02_write_carriage.md) - Write data timing: tphy_wrlat, tphy_wrdata, contiguous vs gap
- [03_read_carriage.md](ch04_command_data_carriage/03_read_carriage.md) - Read data timing: trddata_en, tphy_rdlat, per-slice valid
- [04_walkthroughs.md](ch04_command_data_carriage/04_walkthroughs.md) - End-to-end wire-level examples on a tiny teaching model

### Chapter 5: Timing Parameters

- [01_parameter_families.md](ch05_timing_parameters/01_parameter_families.md) - dfi_t* naming, PHY vs MC observable, what each family constrains
- [02_ratio_and_phasing.md](ch05_timing_parameters/02_ratio_and_phasing.md) - What 1:1, 1:2 and 1:4 do to scheduling and signal replication
- [03_parameter_tables.md](ch05_timing_parameters/03_parameter_tables.md) - Full parameter table for v3.1 with plain-English meaning

### Chapter 6: System Behavior

- [01_low_power.md](ch06_system_behavior/01_low_power.md) - Low-power handshake, self-refresh and power-down interaction
- [02_update.md](ch06_system_behavior/02_update.md) - ctrlupd/phyupd and the idle-bus definition
- [03_frequency_change.md](ch06_system_behavior/03_frequency_change.md) - The v3.1 frequency-change protocol over dfi_init_start/init_complete
- [04_refresh_interaction.md](ch06_system_behavior/04_refresh_interaction.md) - How refresh fits around training, updates and low-power

### Chapter 7: Revision & Area Tie-In

- [01_revision_deltas.md](ch07_revision_and_area/01_revision_deltas.md) - v2.1.1 -> v3.1 delta and a brief v4.0 preview
- [02_in_scoria.md](ch07_revision_and_area/02_in_scoria.md) - How scoria uses this DFI version, and what it leaves out

---

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 0.1 | 2026-10-04 | First draft |

: Version history
