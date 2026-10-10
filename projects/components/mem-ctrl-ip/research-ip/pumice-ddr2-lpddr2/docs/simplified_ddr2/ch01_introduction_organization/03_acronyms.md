# Acronyms and Terms

Terms used with precise meanings throughout this book.

| Term | Meaning |
| --- | --- |
| ACT | Bank Activate command: opens a row in a bank |
| AL | Additive latency: clocks a posted CAS is held inside the DRAM (EMR1) |
| AP | Auto precharge flag, carried on address bit A10 with RD/WR |
| BA | Bank address pins (BA0-BA2) |
| BL | Burst length: 4 or 8 data words per column command |
| CAS | Column Address Strobe (command pin); also shorthand for a column command |
| CKE | Clock enable; gates power-down and self-refresh entry/exit |
| CL | CAS latency: read-command-to-data delay after the posted hold (MR) |
| DCC | Duty Cycle Corrector (optional, EMR2) |
| DES | Deselect command (CS high) |
| DLL | Delay-locked loop aligning read DQS to CK |
| DM | Data mask pin (write data masking, per byte) |
| DQS | Data strobe; source-synchronous clock for DQ in both directions |
| EMR(n) | Extended Mode Register n (1, 2, 3) |
| MRS / EMRS | Mode Register Set / Extended Mode Register Set commands |
| MR | Mode Register (burst, CL, WR, DLL reset, PD-exit mode) |
| NOP | No Operation command |
| OCD | Off-Chip Driver impedance calibration |
| ODT | On-Die Termination (Rtt on DQ/DQS/DM, per EMR1) |
| PASR | Partial Array Self Refresh (EMR2) |
| PD | Power-down (precharge PD or active PD) |
| PRE | Precharge command (A10=0: one bank; A10=1: all banks) |
| RD / WR | Read / Write commands (A10=0) |
| RDA / WRA | Read / Write with auto precharge (A10=1) |
| RDQS | Read data strobe (optional, replaces DM on x8 parts) |
| REF | Refresh command (auto refresh, one internal row per bank) |
| RL | Read latency = AL + CL |
| Rtt | ODT termination resistance value |
| SRE / SRX | Self-refresh entry / exit |
| SSTL_1.8 | 1.8 V stub-series-terminated logic IO standard |
| tCK | Clock period |
| WL | Write latency = RL - 1 |
| Bank group | A DDR4 concept; does not exist in DDR2 |
| Page / open row | The row currently held in a bank's sense amplifiers |

Command trace notation used in Chapters 3 and 4:

```
ACT B3 R5      # open row R5 in bank B3
RD  B3 C2      # read burst starting at column C2
WR  B1 C0      # write burst starting at column C0
RDA B2 C4      # read with auto precharge
PRE B3         # precharge bank B3
PREA           # precharge all banks
REF            # auto refresh
--- (tWTR bubble) ---   # forced idle bus time, reason named
```

**Source:** JESD79-2F sections 2.3, 3, 4.1
