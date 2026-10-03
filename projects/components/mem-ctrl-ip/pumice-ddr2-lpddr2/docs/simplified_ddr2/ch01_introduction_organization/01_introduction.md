# Introduction

## What DDR2 SDRAM is

DDR2 SDRAM is the second generation of double-data-rate synchronous DRAM,
standardized by JEDEC as JESD79-2F. It transfers two data words per clock
cycle per pin (one on each edge of the data strobe), and it quadruples the
internal prefetch relative to single-data-rate DRAM: the array is accessed
four words at a time (4n prefetch) so the IO can run at twice the data rate
of DDR while the core runs at roughly half the IO rate.

Family positioning, in one line each:

| Tech | Prefetch | Distinctives |
| --- | --- | --- |
| SDR SDRAM | 1n | Single data rate, one word per clock |
| DDR SDRAM | 2n | Double data rate, 2.5 V SSTL_2 |
| DDR2 SDRAM | 4n | ODT, posted CAS / additive latency, 1.8 V SSTL_1.8 |
| DDR3 SDRAM | 8n | Bank groups arrive later (DDR4), fly-by topology |

## Key features of DDR2

- 4n prefetch architecture: every column access moves 4 words internally.
- Burst length 4 or 8 only. There is no burst-chop and no Burst Terminate
  command; BL4 bursts can never be interrupted.
- Posted CAS with additive latency (AL): a Read or Write command may be
  issued immediately after Activate and is held inside the DRAM for AL
  clocks, so the command bus is freed early. Read latency RL = AL + CL,
  write latency WL = RL - 1.
- On-die termination (ODT): programmable termination resistance (off, 75,
  150, or 50 ohm nominal) on the DQ/DQS/DM pins, controlled by an ODT pin.
- Off-chip driver (OCD) impedance calibration: the DRAM can trim its own
  output driver strength against a system reference.
- Differential data strobes (DQS/DQS#), source-synchronous in both
  directions.
- DLL (delay-locked loop) aligns DQS to the external clock for reads; it
  is enabled at initialization and reset under software control.
- No bank groups (those are a DDR4 concept). Banks are a flat set of 4 or 8.
- No DBI, no parity, no on-die ECC. Data integrity is entirely the
  controller's problem.
- Supply: VDD = VDDQ = 1.8 V (SSTL_1.8), VREF = VDDQ/2, VTT termination
  rail at 0.9 V nominal.

## Densities and speed grades

Standard monolithic densities run from 128 Mb to 4 Gb, in x4, x8 and x16
organizations. Speed grades are named by data rate: DDR2-400, DDR2-533,
DDR2-667 and DDR2-800, each with one or more CL-tRCD-tRP bin combinations
(e.g. DDR2-800E is the 6-6-6 bin).

## The simplified drill model

Real parts have thousands of rows and over a thousand columns per row. All
examples in this book instead use a deliberately tiny geometry so bank
state is obvious at a glance:

- Banks: B0-B7 (eight, as on 1 Gb and larger parts)
- Rows: R0-R7 per bank
- Columns: C0-C7 per row

This model is used by the ddr_drills training app. Every command trace,
walkthrough and timing example in Chapters 3, 4 and 6 uses it. Real address
maps are far larger; the scheduling rules are identical.

**Source:** JESD79-2F sections 1, 3.2, 3.6.1
