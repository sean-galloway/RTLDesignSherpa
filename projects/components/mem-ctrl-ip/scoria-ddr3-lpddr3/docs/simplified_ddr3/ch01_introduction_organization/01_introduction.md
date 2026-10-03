# Introduction

## What DDR3 SDRAM is

DDR3 SDRAM is the third generation of double-data-rate synchronous DRAM,
standardized by JEDEC as JESD79-3F. For every column access it pulls eight
data words from the memory array (8n prefetch) and then transfers two words
per clock cycle at each DQ pin, so the internal array runs at roughly one
eighth of the data rate seen at the pins. The nominal supply is 1.5 V
(SSTL_15), a step down from DDR2's 1.8 V.

Family positioning, in one line each:

| Tech | Prefetch | Distinctives |
| --- | --- | --- |
| SDR SDRAM | 1n | Single data rate, one word per clock |
| DDR SDRAM | 2n | Double data rate, 2.5 V SSTL_2 |
| DDR2 SDRAM | 4n | ODT, posted CAS / additive latency, 1.8 V SSTL_1.8 |
| DDR3 SDRAM | 8n | 1.5 V, fly-by CA topology, ZQ calibration, write leveling |
| DDR4 SDRAM | 8n | Bank groups, lower voltage, higher data rates |

## Key features of DDR3

- 8n prefetch: every column access moves eight words internally.
- Burst length 8 (BL8) or burst chop 4 (BC4). BC4 can be chosen on-the-fly
  through A12/BC# during a read or write, or fixed in the mode register.
- Posted CAS with additive latency (AL) is retained. A read or write can be
  issued immediately after activate and is held inside the DRAM for AL clocks.
  Read latency RL = AL + CL; write latency WL = AL + CWL (not RL - 1 as in
  DDR2).
- The DLL is required and enabled during initialization; it aligns DQS to CK
  for reads and supports write leveling.
- A dedicated RESET# pin is new compared with DDR2. It performs an
  asynchronous hardware reset.
- ZQ calibration uses the external ZQ reference pin to set output driver
  impedance and on-die termination value.
- Dynamic ODT (Rtt_WR) lets the DRAM switch to a separate termination strength
  during writes.
- Write leveling lets each DRAM rank align its DQS output to the incoming
  CK/CK# in a fly-by topology.
- The multi-purpose register (MPR) is a read-only register used for read
  leveling and DQ eye training.
- Off-chip driver (OCD) calibration from DDR2 is removed; impedance calibration
  is now handled through ZQ calibration.
- No DBI, no parity, no on-die ECC. Data integrity is left to the controller
  and the rest of the system.
- Flat eight-bank organization on every standard density; bank groups are a
  later-generation concept.
- Refresh is all-bank only (no per-bank refresh command).
- Self-refresh includes a self-refresh temperature (SRT) option for extended
  temperature range.

## Densities and speed grades

Standard monolithic densities run from 512 Mb to 8 Gb in x4, x8 and x16
organizations. Every standard density uses eight banks selected by BA0-BA2.

Speed grades are named by data rate: DDR3-800, DDR3-1066, DDR3-1333,
DDR3-1600, DDR3-1866 and DDR3-2133. Each grade carries a letter suffix that
identifies the CL-tRCD-tRP bin (for example, DDR3-800E is a 6-6-6 bin).

## The simplified drill model

Real parts have thousands of rows and over a thousand columns per row. All
examples in this book use a deliberately tiny geometry so bank state is obvious
at a glance:

- Banks: B0-B7 (eight, as on all standard DDR3 devices)
- Rows: R0-R7 per bank
- Columns: C0-C7 per row

This model is used by the ddr_drills training app. Every command trace,
walkthrough and timing example in later chapters uses it. Real address maps are
far larger; the scheduling rules are identical.

**Source:** JESD79-3F sections 1, 2.11, 3.2
