# Acronyms and Terms

Terms used with precise meanings throughout this book.

| Term | Meaning |
| --- | --- |
| ACT | Bank Activate command: opens a row in a bank |
| AL | Additive latency: clocks a posted CAS is held inside the DRAM (MR1) |
| ALERT_n | Active-low alert pin: reports CRC and CA parity errors |
| AP | Auto precharge flag, carried on address bit A10 with RD/WR |
| BA | Bank address pins (BA0-BA1) |
| BC4 | Burst chop 4: a four-word burst from the first half of the 8n prefetch |
| BG | Bank group address pins (BG0-BG1 for x4/x8, BG0 for x16) |
| BL | Burst length: 8 words (BL8) or 4 words via burst chop (BC4) |
| CAL | Command/address latency: delay from CS_n assertion to valid command (MR4) |
| CAS | Column Address Strobe (command pin); shorthand for a column command |
| CA parity | Even parity checked over the command/address bus (MR5) |
| CKE | Clock enable; gates power-down and self-refresh entry/exit |
| CL | CAS latency: read-command-to-data delay after the posted hold (MR0) |
| CRC | Cyclic redundancy check appended to write bursts (MR2) |
| CWL | CAS write latency: write-command-to-first-DQS delay (MR2) |
| DBI | Data bus inversion: inverts a byte lane when it saves power (MR5) |
| DES | Deselect command (CS# high) |
| DLL | Delay-locked loop aligning read DQS to CK |
| DM | Data mask pin (write data masking, per byte) |
| DQS | Data strobe; source-synchronous clock for DQ in both directions |
| FGR | Fine-granularity refresh: 1x/2x/4x refresh modes (MR3) |
| Gear-down | 1N/2N command/address rate mode (MR3) |
| MPR | Multi-purpose register: four pages used for training and logging |
| MR / MRn | Mode Register n (0-6) |
| MRS | Mode Register Set command |
| NOP | No Operation command |
| ODT | On-die termination (Rtt on DQ/DQS/DM, per MR1) |
| OTF | On-the-fly: A12/BC_n selects BL8 or BC4 during a column command |
| PAR | Command and address parity input pin |
| PRE | Precharge command (A10=0: one bank; A10=1: all banks) |
| RD / WR | Read / Write commands (A10=0) |
| RDA / WRA | Read / Write with auto precharge (A10=1) |
| REF | Auto refresh command (all-bank, with 1x/2x/4x rate options) |
| RESET_n | Active-low asynchronous reset pin |
| RL | Read latency = AL + CL (+ PL when CA parity is enabled) |
| Rtt_NOM | Nominal on-die termination strength |
| Rtt_PARK | Parking termination strength (MR5) |
| Rtt_WR | Dynamic ODT strength used during writes |
| tCCD_L | Column-to-column delay for commands to the same bank group |
| tCCD_S | Column-to-column delay for commands to different bank groups |
| tRRD_L | Activate-to-Activate delay for banks in the same bank group |
| tRRD_S | Activate-to-Activate delay for Activates to different bank groups |
| tWTR_L | Write-to-read delay for reads in the same bank group |
| tWTR_S | Write-to-read delay for reads in a different bank group |
| VPP | 2.5 V DRAM activating (wordline) supply |
| VrefDQ | Internal DQ reference voltage, trained via MR6 |
| WL | Write latency = AL + CWL (+ PL when CA parity is enabled) |
| ZQ | Reference pin for ZQ calibration |
| ZQCL / ZQCS | ZQ calibration long / short commands |
| Bank group | A collection of banks that share the "long" timing path |
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
ZQCS / ZQCL    # ZQ calibration short / long
--- (tWTR bubble) ---   # forced idle bus time, reason named
```

**Source:** JESD79-4D sections 2.7, 2.8, 3.1, 3.2, 4.9, 4.10, 4.11, 4.13, 4.15, 4.16, 4.17, 4.18, 4.20
