# Introduction

## What LPDDR4 SDRAM is

LPDDR4 SDRAM is the fourth generation of JEDEC low-power double-data-rate
memory, standardized as JESD209-4E. It is built for mobile and battery-powered
systems, usually in package-on-package (PoP) or discrete FBGA packages. The
interface operates at roughly 1.1 V, lower than the 1.2 V of LPDDR3, and adds
features aimed at higher bandwidth, lower power, and easier DVFS transitions.

The command/address path uses a 6-bit CA bus.
Commands, row/column addresses and bank select information are transferred on
the rising clock edge across CA0-CA5 over one, two or four clock cycles. CS_n
and CKE remain single-edge control inputs. A dedicated RESET_n pin is provided, unlike LPDDR3 where reset
was only available through an MRW command.

## Family positioning

| Tech | Prefetch | IO voltage | DLL | Command/address style |
| --- | --- | --- | --- | --- |
| LPDDR2 (JESD209-2) | 4n (S4) / 2n (S2) | 1.2 V | No | 10-bit DDR CA bus |
| LPDDR3 (JESD209-3) | 8n | 1.2 V | No | 10-bit DDR CA bus |
| LPDDR4 (JESD209-4) | 16n | 1.1 V | No | 6-bit DDR CA bus |

LPDDR4 is therefore the first low-power DDR generation to move to a 16n
prefetch, BL16 as the primary burst, and a dual-channel-per-die organization.

## Key features of LPDDR4

- Dual channel per die: a standard LPDDR4 die contains two fully independent
  channels, each with its own CA bus, clock, CKE, CS_n and DQ/DQS/DMI pins.
  This book treats one channel at a time; channel B behaves identically and
  independently.
- 16n prefetch: a column access moves sixteen words internally per DQ. With
  two words transferred per DQ per clock, the minimum burst is eight clocks.
  This is why tCCD = 8 clocks for BL16.
- Burst length: BL16 is the baseline. BL32 and on-the-fly BL16/BL32 are also
  programmable through MR1.
- 8 banks flat per channel, addressed by BA0-BA2. There are no bank groups and
  no stack IDs.
- x16 and x8 byte-mode data widths per channel; byte-mode dies can be combined
  into a x16 configuration.
- No DLL. Read data timing is specified as a tDQSCK window relative to the
  clock.
- Read latency (RL) and write latency (WL) are programmed through mode
  registers (MR1/MR2), not via additive latency.
- Dedicated RESET_n pin for hardware reset.
- Masked Write command (MWR) allows byte-lane masking on writes without a
  separate DM pin per byte. The DMI pin carries mask information during masked
  writes.
- DMI pins double as data mask (DM) and data bus inversion (DBIdc) signals.
- WDQS control modes let the controller manage DQS stability around writes and
  masked writes.
- Frequency Set Points (FSP) store two complete timing/register profiles and
  allow fast DVFS switching.
- Refresh Management (RFM) command mitigates row-address-access disturbance.
- Multi-Purpose Command (MPC) provides training, FIFO, oscillator and ZQ
  calibration operations through a single command opcode.
- CA-bus ODT plus DQ/DQS/DMI ODT for command/address and data termination.
- Vref training for both CA (MR12) and DQ (MR14).
- Command bus training to align CA/CS with CK and set internal VREF(CA).
- ZQ calibration and ZQCal reset for output driver and termination calibration.
- Post-package repair (PPR) to replace a defective row with a spare row after
  assembly.
- DQS interval oscillator for tracking clock-tree delay drift over temperature
  and voltage.
- Per-bank refresh (REFpb) and all-bank refresh (REFab) both exist.

## Supplies and voltage ranges

| Supply | Nominal | Function |
| --- | --- | --- |
| VDD1 | 1.80 V | Core power |
| VDD2 | 1.10 V | Core and input-buffer power |
| VDDQ | 1.10 V | DQ/DQS/DMI I/O power |

Vref inputs are generated and trained internally rather than supplied as
external reference pins.

## Speed grades

Data-rate grades cover 533 through 4267 MT/s, with clock frequencies from above
10 MHz up to 2133 MHz. RL and WL are selected from programmed tables that map
counts to frequency ranges. Core timings such as tRCD, tRP and tRAS are given
in nanoseconds, then converted to clock cycles by the controller.

## The simplified drill model

Real parts have thousands of rows and hundreds of columns. All examples in this
book use a deliberately tiny geometry so bank state is obvious at a glance:

- Banks: B0-B7 (eight, as on every LPDDR4 channel)
- Rows: R0-R7 per bank
- Columns: C0-C7 per row

Because the model only has eight columns, a BL16 access wraps the column space
twice: the burst starts at the issued column, visits C0-C7, then wraps back to
C0 and continues. Real parts use 64 fetch boundaries and many more columns;
the scheduling rules are identical.

**Source:** JESD209-4E sections 1, 2.1, 3.1, 4.12, 6.1
