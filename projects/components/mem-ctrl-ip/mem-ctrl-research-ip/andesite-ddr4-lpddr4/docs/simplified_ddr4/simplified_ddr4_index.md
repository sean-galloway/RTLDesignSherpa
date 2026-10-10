# Simplified DDR4

**Source:** JEDEC JESD79-4D (paraphrased; section numbers cited per chapter)
**Edition:** Simplified for the andesite DDR4/LPDDR4 memory controller. Derived from the
Memory Notes condensed study notes (a personal paraphrase of the JEDEC
source); timing values follow that book's fixed drill configurations.
**Version:** 0.1
**Last Updated:** 2026-10-03
**Status:** Draft. Personal study notes.

---

## Overview

DDR4 SDRAM (JESD79-4D): 8n-prefetch, bank-grouped, double-data-rate
memory. Bank groups split the column and activate timings into short/long
pairs (tCCD_S/L, tRRD_S/L, tWTR_S/L); fine-granularity refresh, per-bank-
free all-bank REF with 1x/2x/4x modes; DBI, write CRC and CA parity add
integrity; 1.2 V with a 2.5 V wordline boost.
This book condenses the spec into the organization, commands,
initialization, timing and operation material needed to understand and
schedule it.

All examples use a simplified address model: two bank groups
(BG0 = B0-B3, BG1 = B4-B7), rows R0-R7, columns C0-C7 - see Chapter 1.

## Document Structure

### Chapter 1: Introduction & Organization

- [01_introduction.md](ch01_introduction_organization/01_introduction.md) - What DDR4 is, family positioning, key features
- [02_organization.md](ch01_introduction_organization/02_organization.md) - Bank groups, banks, addressing, the drill model
- [03_acronyms.md](ch01_introduction_organization/03_acronyms.md) - Terms used precisely in this book

### Chapter 2: Initialization & Mode Registers

- [01_initialization.md](ch02_initialization_mode_registers/01_initialization.md) - Reset and initialization, MRS order, readiness waits
- [02_mode_registers.md](ch02_initialization_mode_registers/02_mode_registers.md) - MR0-MR6: every field that matters

### Chapter 3: Commands Deep Dive

- [01_truth_tables.md](ch03_commands/01_truth_tables.md) - Command and CKE truth tables
- [02_commands.md](ch03_commands/02_commands.md) - Each command: rules, constraints, constraints on what may follow

### Chapter 4: AXI Sequence Walkthroughs

- [01_read_hit.md](ch04_axi_walkthroughs/01_read_hit.md) - AXI4 read to an open row
- [02_read_miss.md](ch04_axi_walkthroughs/02_read_miss.md) - AXI4 read, wrong row open
- [03_write_miss.md](ch04_axi_walkthroughs/03_write_miss.md) - AXI4 write to an idle bank
- [04_mixed_traffic.md](ch04_axi_walkthroughs/04_mixed_traffic.md) - Interleaved reads and writes across bank groups

### Chapter 5: Data Path, DBI, Parity & ECC

- [01_data_path.md](ch05_data_path/01_data_path.md) - Prefetch, bursts, programmable preamble, DM/DBI/TDQS, write CRC
- [02_odt.md](ch05_data_path/02_odt.md) - Rtt_Nom/WR/Park, dynamic ODT, ZQ

### Chapter 6: Electrical, Timing & Package

- [01_core_timing.md](ch06_electrical_timing_package/01_core_timing.md) - tRCD/tRP/tRAS/tRC, tRRD_S/L, tFAW, tRTP, tWR
- [02_turnaround_timing.md](ch06_electrical_timing_package/02_turnaround_timing.md) - tCCD_S/L, tRTW (book symbol), tWTR_S/L
- [03_refresh_timing.md](ch06_electrical_timing_package/03_refresh_timing.md) - FGR 1x/2x/4x, tRFC1/2/4, self-refresh, power-down
- [04_package.md](ch06_electrical_timing_package/04_package.md) - Packages, supplies, speed bins

### Chapter 7: Test, Repair & Boundary Scan

- [01_test_features.md](ch07_test_repair/01_test_features.md) - MPR pages, write leveling, ZQ, DQ Vref training, CA parity, CAL, CRC

---

### Version History

| Version | Date | Change |
| --- | --- | --- |
| 0.1 | 2026-10-03 | First draft |
