# Acronyms and Terms

Terms used with precise meanings throughout this book.

| Term | Meaning |
| --- | --- |
| ACT | Bank Activate command: opens a row in a bank |
| AL | Additive latency: clocks a posted CAS is held inside the DRAM (MR1) |
| AP | Auto precharge flag, carried on address bit A10 with RD/WR |
| BA | Bank address pins (BA0-BA2) |
| BC4 | Burst chop 4: a four-word burst from the first half of the 8n prefetch |
| BL | Burst length: 8 words (BL8) or 4 words via burst chop (BC4) |
| CAS | Column Address Strobe (command pin); shorthand for a column command |
| CKE | Clock enable; gates power-down and self-refresh entry/exit |
| CL | CAS latency: read-command-to-data delay after the posted hold (MR0) |
| CWL | CAS write latency: write-command-to-first-DQS delay (MR2) |
| DES | Deselect command (CS# high) |
| DLL | Delay-locked loop aligning read DQS to CK |
| DM | Data mask pin (write data masking, per byte) |
| DQS | Data strobe; source-synchronous clock for DQ in both directions |
| MPR | Multi-purpose register: read-only register used for training |
| MR / MRn | Mode Register n (0, 1, 2, 3) |
| MRS | Mode Register Set command |
| NOP | No Operation command |
| ODT | On-die termination (Rtt on DQ/DQS/DM, per MR1) |
| OTF | On-the-fly: A12/BC# selects BL8 or BC4 during a column command |
| PRE | Precharge command (A10=0: one bank; A10=1: all banks) |
| RD / WR | Read / Write commands (A10=0) |
| RDA / WRA | Read / Write with auto precharge (A10=1) |
| REF | Refresh command (auto refresh, one internal row per bank) |
| RESET# | Active-low asynchronous reset pin |
| RL | Read latency = AL + CL |
| Rtt_NOM | Nominal on-die termination strength |
| Rtt_WR | Dynamic ODT strength used during writes |
| SRT | Self-refresh temperature option (MR2) |
| SRE / SRX | Self-refresh entry / exit |
| SSTL_15 | 1.5 V stub-series-terminated logic IO standard |
| tCK | Clock period |
| TDQS / TDQS# | Optional termination data strobe pair (x8 only, MR1) |
| WL | Write latency = AL + CWL |
| ZQ | Reference pin for ZQ calibration |
| ZQCL / ZQCS | ZQ calibration long / short commands |
| Bank group | A DDR4 concept; does not exist in DDR3 |
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

**Source:** JESD79-3F sections 2.10, 2.11, 3.1, 3.2
