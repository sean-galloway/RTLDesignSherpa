# Introduction

## What LPDDR2 SDRAM is

LPDDR2 SDRAM is the second generation of low-power double-data-rate
memory, standardized by JEDEC as JESD209-2F. It is designed for mobile
and battery-powered systems: the interface runs unterminated at 1.2 V,
and the device carries a family of power-reduction features (per-bank
refresh, partial-array self-refresh, deep power-down) that desktop
DDR2/DDR3 do not have.

Its most unusual trait, relative to the desktop DDR family, is the
command/address (CA) interface: instead of a wide SDR address bus with
dedicated RAS_n/CAS_n/WE_n strobes, all commands and addresses travel on
a 10-bit DDR bus (CA0-CA9), clocked in on both edges of the clock. One
command occupies one clock cycle, two CA edges.

The spec covers three device classes; this book is about the SDRAM ones:

| Class | What it is | Prefetch |
| --- | --- | --- |
| LPDDR2-S2 | SDRAM, 2n prefetch (lower speed grades) | 2n |
| LPDDR2-S4 | SDRAM, 4n prefetch (the mainstream part) | 4n |
| LPDDR2-N | Non-volatile memory on the same bus (out of scope here) | 4n |

Family positioning, in one line each:

| Tech | Command bus | Distinctives |
| --- | --- | --- |
| LPDDR (JESD209) | SDR | First low-power DDR, PASR and temperature-compensated refresh arrive |
| LPDDR2 (JESD209-2) | 10-bit DDR CA | Per-bank refresh, deep power-down, ZQ calibration, HSUL_12 IO |
| DDR2 (JESD79-2) | SDR | Desktop: ODT, posted CAS, DLL; none of which LPDDR2 has |
| LPDDR3 (JESD209-3) | 10-bit DDR CA | Successor; same CA concept, faster |

## Key features of LPDDR2

- 10-bit double-data-rate CA bus: command and address packed onto two
  edges of one clock cycle. CS_n and CKE are the only SDR control pins.
- 4n prefetch on S4 (2n on S2): an S4 column access moves 4 words
  internally per DQ per access.
- Burst lengths 4, 8 or 16; sequential or interleaved order; wrap or
  no-wrap (no-wrap exists only at BL4).
- No DLL. Read data timing is specified as tDQSCK from the clock, and
  tDQSCK may span multiple clock periods.
- No ODT. The IO is HSUL_12 (high-speed unterminated logic, 1.2 V), so
  bus turnarounds are contention-avoidance problems, not ODT switching
  problems.
- No bank groups. Banks are a flat set of 4 or 8.
- No DBI, no parity, no on-die ECC. Data integrity is entirely the
  controller's problem.
- Per-bank refresh (REFpb) on 8-bank devices, in addition to all-bank
  refresh (REFab).
- Partial Array Self-Refresh (PASR): refresh only selected banks or
  segments during self-refresh.
- Deep Power-Down (DPD): lowest power state; array contents are lost.
- Temperature sensor readable via MR4, used for refresh-rate scaling and
  AC timing de-rating (temperature-compensated self refresh).
- ZQ output-driver calibration (S4 and N only; S2 ignores it).
- Densities 64 Mb to 8 Gb (SDRAM), organizations x8, x16, x32.

## Speed grades

Speed grades are named by data rate: LPDDR2-1066, -933, -800, -667,
-533, -466, -400, -333, -266 and -200, corresponding to clock
frequencies of 533 MHz down to 100 MHz. Core timing (tRCD, tRP, tRAS)
is specified in nanoseconds with fast/typical/slow bins, not per-grade
clock counts.

## The simplified drill model

Real parts have 8K-16K rows and up to 2K columns per row. All examples
in this book instead use a deliberately tiny geometry so bank state is
obvious at a glance:

- Banks: B0-B7 (eight, as on 1 Gb and larger parts)
- Rows: R0-R7 per bank
- Columns: C0-C7 per row

This model is used by the ddr_drills training app. Every command trace,
walkthrough and timing example in Chapters 3, 4 and 6 uses it. Real
address maps are far larger; the scheduling rules are identical.

**Source:** JESD209-2F sections 1, 3, Table 103
