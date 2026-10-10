# Package and Electrical Notes

A light pass: what matters when connecting an LPDDR3 device, deliberately
skipping the full ballout grids (consult the spec figures for those).

## Packages

- Two delivery forms: package-on-package (PoP, stacked above the
  application processor) and discrete FBGA; both use the same signal
  definitions with per-form ballouts in sec 2.1 and 2.2.
- Organizations are x16 and x32 on a single channel; 8 banks flat, no
  bank groups. Densities run 1 Gb to 32 Gb (the addressing table carries
  6 Gb and 12 Gb steps alongside the powers of two).
- No RESET# pin: reset is a command (MRW to the reset register). There
  IS a dedicated ZQ pin bonding to the external 240 ohm reference
  resistor.

## Supplies and signaling

| Rail | Nominal | Feeds |
| --- | --- | --- |
| VDD1 | 1.2 V class | core/array |
| VDD2 | 1.14-1.30 V | core power |
| VDDQ | 1.14-1.30 V | I/O buffers |
| VREFCA / VREFDQ | 0.5 x VDDQ | input references |

- HSUL_12 (High-Speed Unterminated Logic, 1.2 V): the bus is
  unterminated by design - no VTT rail, no board termination. Signal
  integrity comes from controlled drive strength (MR-programmed, ZQ-
  calibrated) plus the on-die termination for DQ, not from a terminated
  channel.
- CA bus: single-clock-rate command/address on a narrow, shared CA pin
  group (commands span two cycles); CK_t/CK_c differential; DQS_t/DQS_c
  differential per byte group, driven by the DRAM on reads and by the
  controller on writes.

## Speed grades

Per the latency table (Table 63): data rates 333 through 2133 MT/s
(tCK 6 ns down to 0.938 ns), with the programmed RL/WL pair tracking the
rate - RL 6 to 16, WL 3 to 8 (set A) across the mainstream range, plus
the optional RL=3/WL=1 low-latency pair and WL set B. Boot operation runs
from a 10-55 MHz clock (tCKb 18-100 ns) during initialization.

## Derating and characterization

Above 85 C the core timings take +1.875 ns derating and tDQSCK stretches
to 5620 ps max (see the turnaround chapter). Section 10 carries the IDD
measurement conditions (per-state current tables, the mobile power
budget); section 9 the pin capacitance budgets. Neither changes
scheduling; consult them when sizing the power delivery.

**Source:** JESD209-3C sections 2, 6.1, 11.3 (Table 63)
