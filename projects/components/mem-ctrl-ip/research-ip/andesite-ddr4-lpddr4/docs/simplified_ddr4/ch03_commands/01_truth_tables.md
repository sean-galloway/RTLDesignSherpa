# Command Truth Tables

A command is latched on each rising CK edge from CS_n, ACT_n, RAS_n/A16, CAS_n/A15, WE_n/A14, the bank-group and bank addresses, plus the row or column address fields. H = high, L = low, X = do not care, V = a valid logic level. With ACT_n low the command pins serve as address bits A16-A14; with ACT_n high they serve as RAS_n, CAS_n, and WE_n.

## Command truth table

| Function | CKE prev | CKE cur | CS_n | ACT_n | RAS/A16 | CAS/A15 | WE/A14 | BG | BA | A12/BC_n | A10/AP | Notes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| MRS | H | H | L | H | L | L | L | BG | BA | OP code | OP code | BA/BG select MR0-MR6 |
| REF (all-bank) | H | H | L | H | L | L | H | V | V | V | V | all banks idle |
| SRE (self-refresh entry) | H | L | L | H | L | L | H | V | V | V | V | REF encoding + falling CKE |
| SRX (self-refresh exit) | L | H | H | X | X | X | X | X | X | X | X | DES only (NOP allowed for gear-down/MPSM exit) |
| PRE single bank | H | H | L | H | L | H | L | BG | BA | V | L | closes bank selected by BG/BA |
| PREA all banks | H | H | L | H | L | H | L | V | V | V | H | closes every bank |
| ACT | H | H | L | L | RA | RA | RA | BG | BA | V | V | row on A[16:0] when ACT_n = L |
| WR fixed BL8 or BC4 | H | H | L | H | H | L | L | BG | BA | V | L | A12 selects burst length when OTF is enabled |
| WRS4 (BC4 OTF) | H | H | L | H | H | L | L | BG | BA | L | L | BC4 on-the-fly |
| WRS8 (BL8 OTF) | H | H | L | H | H | L | L | BG | BA | H | L | BL8 on-the-fly |
| WRA | H | H | L | H | H | L | L | BG | BA | V | H | write + auto-precharge |
| RD fixed BL8 or BC4 | H | H | L | H | H | L | H | BG | BA | V | L | A12 selects burst length when OTF is enabled |
| RDS4 (BC4 OTF) | H | H | L | H | H | L | H | BG | BA | L | L | BC4 on-the-fly |
| RDS8 (BL8 OTF) | H | H | L | H | H | L | H | BG | BA | H | L | BL8 on-the-fly |
| RDA | H | H | L | H | H | L | H | BG | BA | V | H | read + auto-precharge |
| NOP | H | H | L | H | H | H | H | V | V | V | V | bus filler, CS_n low |
| DES | H | H | H | X | X | X | X | X | X | X | X | bus filler, CS_n high |
| PDE (power-down entry) | H | L | H | X | X | X | X | X | X | X | X | DES only |
| PDX (power-down exit) | L | H | H | X | X | X | X | X | X | X | X | DES only |
| ZQCL | H | H | L | H | H | H | L | V | V | V | H | long ZQ calibration |
| ZQCS | H | H | L | H | H | H | L | V | V | V | L | short ZQ calibration |
| RESET | X | X | X | X | X | X | X | X | X | X | X | RESET# = L, asynchronous override |

Key mnemonics:

- ACT = ACT_n low; the shared RAS/A16, CAS/A15, WE/A14 pins become address bits for the row.
- PRE/PREA = ACT_n and RAS/A16 low, CAS/A15 high, WE/A14 low; A10/AP chooses one bank vs all banks.
- RD = CAS/A15 low, WE/A14 high; WR = CAS/A15 and WE/A14 low; A10/AP adds auto-precharge.
- MRS = ACT_n, RAS/A16, CAS/A15, WE/A14 all low; BG1/BG0 and BA1/BA0 select the target mode register.
- REF = ACT_n, RAS/A16, CAS/A15 low and WE/A14 high; the same encoding with falling CKE becomes self-refresh entry.
- A12/BC_n is the burst-length control: H = BL8, L = BC4. It is ignored when the mode register fixes the burst length.

## CKE truth table

| Current state | CKE prev | CKE cur | Command at N | Result |
| --- | --- | --- | --- | --- |
| Power-down | L | L | X | remain in power-down |
| Power-down | L | H | DES | exit power-down |
| Self-refresh | L | L | X | remain in self-refresh |
| Self-refresh | L | H | DES (NOP for gear-down/MPSM exit) | exit self-refresh |
| Bank(s) active | H | L | DES | active power-down entry |
| Reading / writing / precharging / refreshing | H | L | DES | power-down entry after the operation finishes |
| All banks idle | H | L | DES | precharge power-down entry |
| All banks idle | H | L | REF | self-refresh entry |

## Burst length, type and order

Burst length and on-the-fly selection are controlled by MR0 A[1:0] and A12/BC_n during read/write commands. MR0 A3 chooses sequential (0) or interleaved (1) burst type. Burst chop 4 returns only the first four UI; the remaining positions are don't care on reads and ignored on writes. With write CRC enabled, fixed BL8 burst ordering is restricted to starting column A[2:0] = 000.

## Data mask, DBI and TDQS

DDR4 uses one DM_n/DBI_n/TDQS_t pin per byte lane on x8 and x16 devices; x4 devices do not support DM or DBI. MR1 A11 enables TDQS on x8; when TDQS is on, DM and DBI are unavailable. MR5 A10 enables DM, A11 enables write DBI, and A12 enables read DBI. Write DBI and DM cannot both be enabled. On reads the DRAM inverts a byte and drives DBI_n low when more than half of the eight data bits are 0.

## Not in the table

- No Burst Terminate command exists in DDR4 (DDR had one; DDR2 and later dropped it).
- No Off-Chip Driver Calibration (OCD) command exists in DDR4; OCD was removed.
- No per-bank refresh exists in JESD79-4D; a REF cycle always refreshes all banks.
- DBI, DM and TDQS are programmable mode-register features, not separate commands.

**Source:** JESD79-4D sections 4.1, 4.2, 4.3, 4.11, 4.16, 4.26
