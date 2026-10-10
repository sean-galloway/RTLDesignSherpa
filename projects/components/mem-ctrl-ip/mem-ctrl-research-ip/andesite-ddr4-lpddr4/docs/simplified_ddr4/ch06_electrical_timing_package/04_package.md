# Package and Electrical Notes

A light pass: what matters when connecting a DDR4 device, skipping the
full ballout grids (spec sec 2 has them).

## Packages

- FBGA per JEDEC MO-207; x4, x8 and x16 ballouts (an x32 grid exists
  for specialized parts; the standard density/addressing tables cover
  x4/x8/x16). Dual-die and stacked packages present multiple ranks
  behind one channel with per-rank chip select and ODT.
- New pins versus DDR3: ALERT# (error flag out / connectivity-test in),
  VPP (wordline boost supply), PAR (CA parity input when enabled), the
  bank-group address pins BG0-BG1, and the ACT# pin so RAS#/CAS#/WE#
  pins double as address bits (A16/A15/A14) during non-command cycles.

## Supplies and signaling

| Rail | Nominal | Feeds |
| --- | --- | --- |
| VDD | 1.2 V | core |
| VDDQ | 1.2 V | output drivers |
| VPP | 2.5 V | wordline activation boost (internal charge pump assist) |

- SSTL-class 1.2 V signaling; VREFCA at the receiver; the CA bus is the
  heavily loaded net and is where CAL mode and CA parity spend their
  effort.
- DQ integrity is now multi-layered: on-die termination per MR, DBI for
  power/DC balance, write CRC on the data, and CA parity on the command
  path - see the data-path and test chapters.

## Speed bins

| Grade | tCK (ns) | Nominal CL-nRCD-nRP examples |
| --- | --- | --- |
| DDR4-1600 | 1.25 | 10-10-10 ... 12-12-12 |
| DDR4-1866 | 1.071 | 12/13/14-14-14 |
| DDR4-2133 | 0.937 | 14/15/16-16-16 |
| DDR4-2400 | 0.833 | 15/16-16-16 ... 18-18-18 |
| DDR4-2666 / 2933 / 3200 | 0.75 / 0.682 / 0.625 | 17/18 up to 22-22-22 / 24-24-24 |

tCCD_L, tWTR_L, tRRD_L, nFAW and tRFC grow with the grade (the clock-
domain tables in sec 11.1 and the AC tables in sec 13 carry the per-bin
numbers); same-group and same-bank analog floors stay in nanoseconds,
so faster bins pay more clocks for them.

## Characterization

Section 11 defines the IDD/IPP/IDDQ measurement conditions, including
the Table 154 loop timings that double as a convenient clock-domain
summary of the core parameters. Consult it for power delivery sizing;
nothing there changes scheduling.

**Source:** JESD79-4D sections 2, 11.1, 12-13
