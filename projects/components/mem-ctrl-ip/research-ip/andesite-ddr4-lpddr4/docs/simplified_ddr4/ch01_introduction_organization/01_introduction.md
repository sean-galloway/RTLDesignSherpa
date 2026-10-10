# Introduction

## What DDR4 SDRAM is

DDR4 SDRAM is the fourth generation of double-data-rate synchronous DRAM,
standardized by JEDEC as JESD79-4D. It keeps the 8n prefetch of DDR3 but splits
banks into groups, lowers the nominal supply to 1.2 V (SSTL_12), and adds a
separate 2.5 V wordline supply (VPP). Internally the array runs at roughly one
eighth of the data rate seen at the pins, moving two words per clock edge on
each DQ pin.

Family positioning, in one line each:

| Tech | Prefetch | Distinctives |
| --- | --- | --- |
| DDR2 SDRAM | 4n | 1.8 V, ODT, posted CAS, 4-bit prefetch |
| DDR3 SDRAM | 8n | 1.5 V, fly-by CA, ZQ calibration, write leveling |
| DDR4 SDRAM | 8n | 1.2 V + VPP 2.5 V, bank groups, higher data rates |
| DDR5 SDRAM | 16n | 1.1 V, two 32-bit channels per DIMM, on-die ECC |

## Key features of DDR4

- Bank groups: x4/x8 devices have four groups of four banks each (16 banks
total); x16 devices have two groups of four banks each (8 banks total). This is
the headline change: timing splits into "short" (different group) and "long"
(same group) versions - tCCD_S/tCCD_L, tRRD_S/tRRD_L, and tWTR_S/tWTR_L.
- 8n prefetch retained: every column access still moves eight words internally.
- Burst length 8 (BL8) or burst chop 4 (BC4). BC4 can be selected on-the-fly
through A12/BC_n during a column command, or fixed in the mode register.
- Gear-down mode: command/address timing can run in 1N (half-rate, default) or
2N (quarter-rate) mode, selected through MR3.
- Fine-granularity refresh: refresh can be configured as 1x, 2x, or 4x mode,
with corresponding tRFC1/tRFC2/tRFC4 recovery times and tREFI intervals of
7.8 us, 3.9 us, and 1.95 us at normal temperature.
- Refresh is all-bank only; JESD79-4D does not define a per-bank refresh
command (REFpb).
- Read and write data bus inversion (DBI) is supported on x8 and x16 parts,
controlled through MR5.
- Write CRC: a CRC word is appended to write bursts; CRC errors are reported as
a pulse on ALERT_n. Enabling CRC adds one clock to effective write latency.
- CA parity: an even parity input (PAR) covers the command/address bus; parity
errors are flagged on ALERT_n and logged in MPR page 1. Parity latency (PL) is
added to read and write latency.
- CAL mode: command/address latency delays chip-select assertion relative to
the command to save power.
- Programmable read preamble (1 tCK or 2 tCK) and write preamble (1 tCK or 2
tCK), selected in MR4. Two-clock preambles are valid at DDR4-2400 and above.
- DQ Vref training: MR6 lets the host set the internal DQ reference voltage
during training.
- Multi-purpose register (MPR) pages: four pages are available; page 0 is for
training patterns, page 1 logs CA parity errors, page 2 exposes mode-register
readback, and page 3 is vendor-specific.
- DLL-on is the normal mode; DLL-off mode is optional and limits speeds.
- Additive latency (AL) can be 0, CL-1, or CL-2.
- IO organizations are x4, x8, and x16; an x32 ballout is also described for
specialized packages but is outside the standard monolithic density scope.

## Densities and speed grades

Standard monolithic densities run from 2 Gb to 16 Gb in x4, x8, and x16
organizations. x4/x8 parts use 16 banks (four groups of four); x16 parts use 8
banks (two groups of four).

Speed grades span DDR4-1600 through DDR4-3200, including 1866, 2133, 2400,
2666, and 2933. Each grade carries a letter suffix that identifies the speed
bin (for example, DDR4-1600J/K/L are different CL-tRCD-tRP bins).

## The simplified drill model

Real parts have far more rows and columns than the model below. All examples in
this book use a deliberately tiny geometry so bank state is obvious at a
glance, and this is the first drill model that includes bank groups:

- Bank groups: BG0, BG1 (two groups)
- Banks per group: B0-B3 in BG0, B4-B7 in BG1
- Rows: R0-R7 per bank
- Columns: C0-C7 per row

This model is used by the ddr_drills training app. Every command trace,
walkthrough, and timing example in later chapters uses it. Real address maps
are far larger; the scheduling rules are identical.

**Source:** JESD79-4D sections 1, 2.7, 2.8, 3.2, 4.9, 4.10, 4.11, 4.13, 4.15, 4.16, 4.17, 4.18, 4.20
