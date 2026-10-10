# Command Truth Tables

LPDDR4 packs two independent channels per die; each channel has eight banks and no bank groups. There is no DLL, so read and write latencies are programmed through mode registers. Commands and addresses travel over the 6-bit CA bus across two clock cycles; a RESET_n pin is provided for full device reset. Examples in this book use the drill model (banks B0-B7, rows R0-R7, columns C0-C7) on one channel; the other channel is independent.

## Pin conventions

- CKE is sampled at rising CK edges and must be high for any command in the table below.
- CS is active high: a two-cycle command starts with CS high on the first rising edge and CS low on the second; Deselect is one cycle with CS low.
- CAxr is CA bit x on the first rising edge; CAxf is the same bit on the second rising edge.
- H/L are valid logic levels; V means a defined level whose value depends on the command; X means the pin may be floated.

## Command truth table

| Command | First cycle CA0-CA5 | Second cycle CA0-CA5 | Notes |
| --- | --- | --- | --- |
| Deselect (DES) | X | (none) | One cycle, CS = L |
| Multi-Purpose (MPC) | L L L L L OP6 | OP0 OP1 OP2 OP3 OP4 OP5 | NOP when OP6 = 0; training when OP6 = 1 |
| Precharge (PREpb/PREab) | L L L L H AB | BA0 BA1 BA2 V V V | AB = 1 closes all banks; AB = 0 closes the selected bank |
| Refresh (REFpb/REFab) | L L L H L AB | BA0 BA1 BA2 RFM V V | RFM bit is valid only when MR24 OP[0] = 1 |
| Self Refresh Entry (SRE) | L L L H H V | V V V V V V | CKE falls during SRE to enter |
| Write-1 (WR-1) | L L H L L BL | BA0 BA1 BA2 V C9 AP | Must be followed immediately by CAS-2 |
| Self Refresh Exit (SRX) | L L H L H V | V V V V V V | CKE rises to exit |
| Mask Write-1 (MWR-1) | L L H H L L | BA0 BA1 BA2 V C9 AP | BL is fixed at 16; followed by CAS-2 |
| Read-1 (RD-1) | L H L L L BL | BA0 BA1 BA2 V C9 AP | Must be followed immediately by CAS-2 |
| CAS-2 (WR-2/MWR-2/RD-2/MRR-2/MPC data) | L H L L H C8 | C2 C3 C4 C5 C6 C7 | Carries remaining column bits; C1-C0 are implied zero |
| Mode Register Write-1 (MRW-1) | L H H L L OP7 | MA0 MA1 MA2 MA3 MA4 MA5 | Must be followed immediately by MRW-2 |
| Mode Register Write-2 (MRW-2) | L H H L H OP6 | OP0 OP1 OP2 OP3 OP4 OP5 | Second half of MRW data |
| Mode Register Read-1 (MRR-1) | L H H H L V | MA0 MA1 MA2 MA3 MA4 MA5 | Must be followed immediately by CAS-2 |
| Activate-1 (ACT-1) | H L, then row and bank bits | BA0-BA2 plus row bits | Must be followed immediately by ACT-2 |
| Activate-2 (ACT-2) | H H, then remaining row bits | Remaining row bits | Completes row activation |

Load-bearing notes:

- Every command except DES spans two cycles and is defined by CA[5:0] sampled at the first rising edge while CS is high.
- WR-1, MWR-1, RD-1, MRR-1, and MPC read/write training commands must be immediately followed by CAS-2 with no command in between.
- ACT-1 must be immediately followed by ACT-2; MRW-1 must be immediately followed by MRW-2.
- The BL bit in WR-1/RD-1 selects burst length on-the-fly when that feature is enabled: low = BL16, high = BL32. LPDDR4 supports BL16 and BL32; the native prefetch is 16n.
- Auto-precharge is selected by AP = 1 in WR-1/MWR-1/RD-1.
- MWR-1 supports only BL16; in a BL32 configuration the controller supplies only a 16-bit data window for the masked write.

## CKE and power-state behavior

| Condition | Result |
| --- | --- |
| CKE falls while CS is low (DES on bus) | Enter power-down |
| CKE falls with SRE command on bus | Enter self refresh |
| CKE rises from power-down | Exit after tXP |
| CKE rises from self refresh | Exit after tXSR; abort path available via MR4 OP[3] |
| CKE falls during RD, WR, MWR, MRR, MRW, VREF MRW, CBT MRW, VRCG MRW, or Start DQS Oscillator | Illegal |

## What is not present

LPDDR4 has no single-cycle NOP command (MPC with OP6 = 0 acts as NOP), no burst terminate, no burst chop, no bank groups, and no MRS command; mode-register updates use MRW.

**Source:** JESD209-4E sections 4.1, 4.2, 4.3, 4.6, 4.10, 4.15, 4.16, 4.17, 4.19, 4.20, 4.23, 4.24, 4.35, 4.44, 4.45, 4.46, 4.47
