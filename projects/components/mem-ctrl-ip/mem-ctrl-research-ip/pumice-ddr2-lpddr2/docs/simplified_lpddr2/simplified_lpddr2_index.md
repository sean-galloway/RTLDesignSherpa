# Simplified LPDDR2

**Source:** JEDEC JESD209-2F (paraphrased; section numbers cited per chapter)
**Edition:** Simplified for the pumice DDR2/LPDDR2 memory controller. Derived from the
Memory Notes condensed study notes (a personal paraphrase of the JEDEC
source); timing values follow that book's fixed drill configurations.
**Version:** 0.1
**Last Updated:** 2026-10-02
**Status:** Draft. Personal study notes.

---

## Overview

LPDDR2 SDRAM (JESD209-2F): low-power 4n-prefetch memory with a DDR
command/address (CA) interface, per-bank refresh and partial-array
self-refresh (PASR). This book condenses the spec into the organization,
commands, initialization, timing and operation material needed to understand
and schedule it.

All examples use a simplified address model (B0-B7, R0-R7, C0-C7) - see
Chapter 1.

## Document Structure

### Chapter 1: Introduction & Organization

- [01_introduction.md](ch01_introduction_organization/01_introduction.md) - What LPDDR2 is, family positioning, key features
- [02_organization.md](ch01_introduction_organization/02_organization.md) - Banks, rows, columns, prefetch, IO widths, the simplified drill model
- [03_acronyms.md](ch01_introduction_organization/03_acronyms.md) - Terms used precisely in this book

### Chapter 2: Initialization & Mode Registers

- [01_initialization.md](ch02_initialization_mode_registers/01_initialization.md) - Power-up and initialization sequence, step by step
- [02_mode_registers.md](ch02_initialization_mode_registers/02_mode_registers.md) - Mode registers: every field that matters

### Chapter 3: Commands Deep Dive

- [01_ca_interface.md](ch03_commands/01_ca_interface.md) - The DDR CA interface: how commands are encoded on CA0-CA9
- [02_truth_tables.md](ch03_commands/02_truth_tables.md) - Command truth tables
- [03_commands.md](ch03_commands/03_commands.md) - Each command: rules, constraints, what may follow

### Chapter 4: AXI Sequence Walkthroughs

- [01_read_hit.md](ch04_axi_walkthroughs/01_read_hit.md) - AXI4 read to an open row
- [02_read_miss.md](ch04_axi_walkthroughs/02_read_miss.md) - AXI4 read, wrong row open
- [03_write_miss.md](ch04_axi_walkthroughs/03_write_miss.md) - AXI4 write to an idle bank
- [04_mixed_traffic.md](ch04_axi_walkthroughs/04_mixed_traffic.md) - Interleaved reads and writes, turnarounds

### Chapter 5: Data Path, DBI, Parity & ECC

- [01_data_path.md](ch05_data_path/01_data_path.md) - 4n prefetch, burst ordering, DQS; no DBI/parity/ECC in LPDDR2

### Chapter 6: Electrical, Timing & Package

- [01_core_timing.md](ch06_electrical_timing_package/01_core_timing.md) - tRCD, tRP, tRAS, tRC, tRRD, tFAW, tRTP, tWR
- [02_turnaround_timing.md](ch06_electrical_timing_package/02_turnaround_timing.md) - tWTR, tRTW, tCCD, burst timing
- [03_refresh_timing.md](ch06_electrical_timing_package/03_refresh_timing.md) - tRFC, tREFI, per-bank refresh, PASR
- [04_package.md](ch06_electrical_timing_package/04_package.md) - Package and ballout notes (light)

### Chapter 7: Test, Repair & Boundary Scan

- [01_test_features.md](ch07_test_repair/01_test_features.md) - What test logic LPDDR2 has

---

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 0.1 | 2026-10-02 | First draft |
