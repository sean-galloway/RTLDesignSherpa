# Simplified LPDDR3

**Source:** JEDEC JESD209-3C (paraphrased; section numbers cited per chapter)
**Edition:** Simplified for the scoria DDR3/LPDDR3 memory controller. Derived from the
Memory Notes condensed study notes (a personal paraphrase of the JEDEC
source); timing values follow that book's fixed drill configurations.
**Version:** 0.1
**Last Updated:** 2026-10-03
**Status:** Draft. Personal study notes.

---

## Overview

LPDDR3 SDRAM (JESD209-3C): 8n-prefetch, 8-bank, double-data-rate
low-power memory for mobile: no DLL (programmed RL/WL), HSUL_12
unterminated signaling, per-bank refresh and precharge, MRR/MRW command
pair, CA training, deep power-down, package-on-package or discrete.
This book condenses the spec into the organization, commands,
initialization, timing and operation material needed to understand and
schedule it.

All examples use a simplified address model (B0-B7, R0-R7, C0-C7) - see
Chapter 1.

## Document Structure

### Chapter 1: Introduction & Organization

- [01_introduction.md](ch01_introduction_organization/01_introduction.md) - What LPDDR3 is, family positioning, key features
- [02_organization.md](ch01_introduction_organization/02_organization.md) - Banks, rows, columns, prefetch, IO widths, the simplified drill model
- [03_acronyms.md](ch01_introduction_organization/03_acronyms.md) - Terms used precisely in this book

### Chapter 2: Initialization & Mode Registers

- [01_initialization.md](ch02_initialization_mode_registers/01_initialization.md) - Power-up, init, reset command, power-off sequence
- [02_mode_registers.md](ch02_initialization_mode_registers/02_mode_registers.md) - The MR0-MR63 space: every register that matters

### Chapter 3: Commands Deep Dive

- [01_truth_tables.md](ch03_commands/01_truth_tables.md) - CA-bus command truth tables
- [02_commands.md](ch03_commands/02_commands.md) - Each command: rules, constraints, constraints on what may follow

### Chapter 4: AXI Sequence Walkthroughs

- [01_read_hit.md](ch04_axi_walkthroughs/01_read_hit.md) - AXI4 read to an open row
- [02_read_miss.md](ch04_axi_walkthroughs/02_read_miss.md) - AXI4 read, wrong row open (PREpb)
- [03_write_miss.md](ch04_axi_walkthroughs/03_write_miss.md) - AXI4 write to an idle bank
- [04_mixed_traffic.md](ch04_axi_walkthroughs/04_mixed_traffic.md) - Interleaved reads and writes, turnarounds

### Chapter 5: Data Path, DBI, Parity & ECC

- [01_data_path.md](ch05_data_path/01_data_path.md) - 8n prefetch, fixed BL8, no-DLL DQS, RL/WL programming
- [02_odt.md](ch05_data_path/02_odt.md) - Asynchronous ODT; no DBI/parity/ECC in LPDDR3

### Chapter 6: Electrical, Timing & Package

- [01_core_timing.md](ch06_electrical_timing_package/01_core_timing.md) - tRCD/tRPpb/tRPpab, tRAS, tRC, tRRD, tFAW, tRTP, tWR
- [02_turnaround_timing.md](ch06_electrical_timing_package/02_turnaround_timing.md) - tRTW (book symbol), tWTR, tCCD, strobe windows, derating
- [03_refresh_timing.md](ch06_electrical_timing_package/03_refresh_timing.md) - tREFW/tREFI, REFab/REFpb, self-refresh, power-down, DPD
- [04_package.md](ch06_electrical_timing_package/04_package.md) - Packages, supplies, speed grades

### Chapter 7: Test, Repair & Boundary Scan

- [01_test_features.md](ch07_test_repair/01_test_features.md) - CA training, write leveling, DQ/ZQ calibration, temperature sensor

---

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 0.1 | 2026-10-03 | First draft |
