# Introduction

## What DFI is

The DDR PHY Interface (DFI) is the standard boundary between a memory controller (MC) and a
DRAM PHY. The MC schedules commands, manages refresh, and buffers read/write data; the PHY
clocks that information out to the DRAM devices, trains the data eyes, and returns read data. DFI
splits the problem at a well-defined seam so that MC and PHY can be designed, verified and
reused independently.

DFI 4.0 is the DDR4-era revision published in April 2018. It merged the 4.0 Spec Addendum into
DFI 3.1 and added support for LPDDR4, DDR4-specific features (bank groups, ACT_n, CA parity,
DBI, gear-down), and a set of system-level protocols (PHY master, disconnect, write DQ training,
DB training). It remains backward-compatible in spirit: the core control/write/read interface from
earlier revisions is still there, wrapped in the new signals.

## Why the seam exists

A memory controller is a traffic manager. It sees banks, rows, columns, refresh counters, and
arbitration. A PHY is a timing-and-electrical translator. It sees delay lines, FIFOs, phase
alignment, and single-ended vs differential receivers. The two sides operate on different time
scales and different abstractions. DFI standardizes the handoff:

- The MC presents commands, address, bank, and chip-select on the control interface.
- The MC presents write data and mask/DBI on the write data interface.
- The PHY returns read data and valid on the read data interface.
- A small set of status and training wires let the PHY report readiness and request calibration.

The MC does not need to know the PHY's internal delay settings; the PHY does not need to know
the MC's scheduling policy. Both must agree on DFI timing parameters.

## Edition lineage

| DFI revision | Distinctives |
| --- | --- |
| DFI 1.0 | Initial MC/PHY seam for DDR1/DDR2 |
| DFI 2.0/2.1 | DDR3 support, read/write leveling, frequency change, low-power control, 1:2 and 1:4 ratios |
| DFI 3.0/3.1 | DDR4 support (CRC, CA parity, DBI, ACT_n, bank groups), LPDDR3, PHY-requested training, split low-power requests |
| DFI 4.0 | LPDDR4, DB training, per-slice read leveling, read/write data chip selects, write DQ training, PHY master, frequency indicator, disconnect protocol, geardown mode, 3DS/inactive CS support |

: DFI revision lineage

## What this book covers

This book focuses on the DFI 4.0 signals, timing, and protocols that an andesite-style DDR4/LPDDR4
controller must drive. It is a study condensation, not a replacement for the spec. Every chapter cites
the DFI 4.0 section numbers that the material paraphrases. Signal names are used as-is because
they are the public vocabulary of the interface.

**Source:** DFI Specification v4.0 sections 1.0, 2.0, 2.2
