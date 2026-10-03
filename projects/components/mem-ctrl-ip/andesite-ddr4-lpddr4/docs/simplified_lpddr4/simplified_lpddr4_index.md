# Simplified LPDDR4

**Source:** JEDEC JESD209-4E (paraphrased; section numbers cited per chapter)
**Edition:** Simplified for the andesite DDR4/LPDDR4 memory controller. Derived from the
Memory Notes condensed study notes (a personal paraphrase of the JEDEC
source); timing values follow that book's fixed drill configurations.
**Version:** 0.1
**Last Updated:** 2026-10-03
**Status:** Draft. Personal study notes.

---

## Overview

LPDDR4 SDRAM (JESD209-4E): 16n-prefetch, dual-channel-per-die
low-power memory: 8 banks per channel, programmed RL/WL (no DLL), BL16
bursts, masked write, read/write DBI on the DMI pin, per-bank refresh
plus Refresh Management (RFM), frequency set points for DVFS, CA-bus
ODT, and the richest training/calibration set in this series.
This book condenses the spec into the organization, commands,
initialization, timing and operation material needed to understand and
schedule it.

All examples use a simplified single-channel address model (B0-B7,
R0-R7, C0-C7; BL16 wraps the 8-column model twice) - see Chapter 1.

## Document Structure

### Chapter 1: Introduction & Organization

- [01_introduction.md](ch01_introduction_organization/01_introduction.md) - What LPDDR4 is, family positioning, key features
- [02_organization.md](ch01_introduction_organization/02_organization.md) - Channels, banks, prefetch, IO widths, the drill model
- [03_acronyms.md](ch01_introduction_organization/03_acronyms.md) - Terms used precisely in this book

### Chapter 2: Initialization & Mode Registers

- [01_initialization.md](ch02_initialization_mode_registers/01_initialization.md) - Power-up, reset pin, init sequence, power-off
- [02_mode_registers.md](ch02_initialization_mode_registers/02_mode_registers.md) - The MR space: every register that matters

### Chapter 3: Commands Deep Dive

- [01_truth_tables.md](ch03_commands/01_truth_tables.md) - CA-bus command truth tables
- [02_commands.md](ch03_commands/02_commands.md) - Each command: rules, constraints, constraints on what may follow

### Chapter 4: AXI Sequence Walkthroughs

- [01_read_hit.md](ch04_axi_walkthroughs/01_read_hit.md) - AXI4 read to an open row (BL16)
- [02_read_miss.md](ch04_axi_walkthroughs/02_read_miss.md) - AXI4 read, wrong row open (PREpb)
- [03_write_miss.md](ch04_axi_walkthroughs/03_write_miss.md) - AXI4 write to an idle bank
- [04_mixed_traffic.md](ch04_axi_walkthroughs/04_mixed_traffic.md) - Interleaved reads and writes, named tRTW and tWTR

### Chapter 5: Data Path, DBI, Parity & ECC

- [01_data_path.md](ch05_data_path/01_data_path.md) - 16n prefetch, BL16/BL32, preambles, WDQS control, masked write, DM/DBI
- [02_odt.md](ch05_data_path/02_odt.md) - CA-bus ODT and DQ/DQS/DMI ODT; no write CRC

### Chapter 6: Electrical, Timing & Package

- [01_core_timing.md](ch06_electrical_timing_package/01_core_timing.md) - tRCD/tRPpb/tRPab, tRAS, tRC, tRRD, tFAW, tRTP, tWR
- [02_turnaround_timing.md](ch06_electrical_timing_package/02_turnaround_timing.md) - Named tRTW, tWTR, tCCD, programmed RL/WL tables
- [03_refresh_timing.md](ch06_electrical_timing_package/03_refresh_timing.md) - tREFW 32 ms / 8192 REFab, REFpb, RFM, self-refresh, power-down
- [04_package.md](ch06_electrical_timing_package/04_package.md) - Packages, dual-channel supplies, speed grades, FSP

### Chapter 7: Test, Repair & Boundary Scan

- [01_test_features.md](ch07_test_repair/01_test_features.md) - Command bus training, Vref trainings, write leveling, DQS oscillator, MPC, ZQ, PPR

---

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 0.1 | 2026-10-03 | First draft |
