# Introduction

## What LPDDR3 SDRAM is

LPDDR3 SDRAM is the third generation of JEDEC low-power double-data-rate
memory, standardized as JESD209-3C. It targets mobile and battery-powered
systems, typically in package-on-package (PoP) or discrete FBGA form. The
interface runs at 1.2 V and the devices carry a set of power-reduction modes
(power-down, self-refresh, deep power-down, per-bank refresh, clock stop)
that are not found on desktop DDR3.

Its defining architectural choice is the 10-bit double-data-rate
command/address (CA) bus. Instead of a wide SDR address bus with separate
RAS_n, CAS_n and WE_n strobes, commands and row/column/bank addresses are
packed onto two edges of a single clock cycle on CA0-CA9. CS_n and CKE
are the only control inputs sampled on a single clock edge.

## Family positioning

| Tech | Prefetch | IO voltage | DLL | Command/address style |
| --- | --- | --- | --- | --- |
| LPDDR2 (JESD209-2) | 4n (S4) / 2n (S2) | 1.2 V (HSUL_12) | No | 10-bit DDR CA bus |
| LPDDR3 (JESD209-3) | 8n | 1.2 V (HSUL_12) | No | 10-bit DDR CA bus |
| DDR3 (JESD79-3) | 8n | 1.5 V (SSTL_15) | Yes | Full parallel SDR CA + RAS/CAS/WE |

LPDDR3 is therefore best understood as an evolutionary step from LPDDR2:
same CA-bus concept, wider prefetch, faster data rates, and a richer set
of training/calibration features.

## Key features of LPDDR3

- 8n prefetch: a column access moves eight words internally per DQ per
  access; the DDR interface delivers two words per DQ per clock, so the
  minimum burst occupies four clocks.
- Burst length fixed at BL8. MR1 burst-length encoding is 011B for BL8;
  all other encodings are reserved. There is no burst chop.
- 8 banks flat, addressed by BA0-BA2. There are no bank groups and no
  stack IDs.
- x16 and x32 data widths; packages support single- or dual-channel
  arrangements, but the protocol in this book is per-channel.
- No DLL. Read data timing is given as a broad tDQSCK window relative to
  the clock; tDQSCK may extend across more than one clock period.
- Read latency (RL) and write latency (WL) are programmed through mode
  registers (MR0/MR2), not via additive latency.
- No dedicated RESET# pin. Reset is performed with an MRW RESET command.
- MRR and MRW commands replace the single MRS command used by desktop
  DDR3.
- Training and calibration: CA training, write leveling, DQ calibration,
  and ZQ calibration are all supported.
- Asynchronous ODT: DQ-bus termination follows the ODT pin and the MR11
  setting, and is turned off during reads, power-down, self-refresh, deep
  power-down and CA training.
- Deep power-down (DPD): lowest-power state; array contents are lost and
  exit requires full re-initialization.
- Per-bank refresh (REFpb) and all-bank refresh (REFab) both exist.
- Temperature sensor readable via MR4, used for refresh-rate scaling and
  AC timing de-rating decisions.
- Clock stop supported during CKE LOW and CKE HIGH under defined
  conditions.

## Supplies and voltage ranges

| Supply | Nominal | Function |
| --- | --- | --- |
| VDD1 | 1.80 V | Core power |
| VDD2 | 1.20 V | Core power |
| VDDCA | 1.20 V | CA/CKE/CS_n/CK input-buffer power |
| VDDQ | 1.20 V | DQ/DQS/DM I/O power |
| VREF(CA) | VDDCA/2 | Reference for CA, CKE, CS_n, CK |
| VREF(DQ) | VDDQ/2 | Reference for DQ inputs |

## Speed grades

Data-rate grades reach 1333, 1600, 1866 and 2133 MT/s at the high end
(Table 64); lower data rates are also supported. Core timings (tRCD,
tRP, tRAS) are specified in nanoseconds, while RL and WL are given in
clock counts that depend on data rate (Table 63).

## The simplified drill model

Real parts have thousands of rows and hundreds of columns. All examples
in this book use a deliberately tiny geometry so bank state is obvious at
a glance:

- Banks: B0-B7 (eight, as on 1 Gb and larger parts)
- Rows: R0-R7 per bank
- Columns: C0-C7 per row

This model is used by the ddr_drills training app. Every command trace,
walkthrough and timing example in later chapters uses it. Real address
maps are far larger; the scheduling rules are identical.

**Source:** JESD209-3C sections 1, 2.4, 3, Table 64
