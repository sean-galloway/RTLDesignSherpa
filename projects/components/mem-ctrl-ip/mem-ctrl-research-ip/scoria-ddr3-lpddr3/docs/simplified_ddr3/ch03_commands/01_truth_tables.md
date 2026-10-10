# Command Truth Tables

Every command is sampled on a rising CK edge from CS, RAS, CAS, WE, BA, and A. H = high, L = low, X = do not care (may float), V = a valid logic level. CKE transitions add power modes and self-refresh.

## Command truth table

| Function | CKE prev | CKE cur | CS | RAS | CAS | WE | A10 | A12 | BA / address | Notes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| MRS | H | H | L | L | L | L | OP | OP | BA = register, opcode on A | |
| REF | H | H | L | L | L | H | X | X | X | all banks idle |
| Self-refresh entry | H | L | L | L | L | H | X | X | X | REF encoding + falling CKE |
| Self-refresh exit | L | H | X | X | X | X | X | X | NOP or DES | asynchronous |
| Precharge one bank | H | H | L | L | H | L | L | X | BA = bank | |
| Precharge all | H | H | L | L | H | L | H | X | X | |
| Activate | H | H | L | L | H | H | row | X | BA = bank, row on A | |
| Write fixed BL8 or BC4 | H | H | L | H | L | L | L | V | BA + column | A12 selects burst length when OTF is enabled |
| Write BL8 on-the-fly | H | H | L | H | L | L | L | H | BA + column | |
| Write BC4 on-the-fly | H | H | L | H | L | L | L | L | BA + column | |
| Write w/ auto-precharge | H | H | L | H | L | L | H | V | BA + column | A10 = 1 |
| Read fixed BL8 or BC4 | H | H | L | H | L | H | L | V | BA + column | A12 selects burst length when OTF is enabled |
| Read BL8 on-the-fly | H | H | L | H | L | H | L | H | BA + column | |
| Read BC4 on-the-fly | H | H | L | H | L | H | L | L | BA + column | |
| Read w/ auto-precharge | H | H | L | H | L | H | H | V | BA + column | A10 = 1 |
| NOP | H | H | L | H | H | H | X | X | X | |
| Deselect | H | H | H | X | X | X | X | X | X | |
| Power-down entry | H | L | X | X | X | X | X | X | NOP or DES | |
| Power-down exit | L | H | X | X | X | X | X | X | NOP or DES | |
| ZQ calibration long | H | H | L | H | H | L | H | X | X | |
| ZQ calibration short | H | H | L | H | H | L | L | X | X | |
| RESET | X | X | X | X | X | X | X | X | RESET# = L | asynchronous, overrides command bus |

Key mnemonics:

- ACT = RAS low, CAS and WE high.
- PRE/PREA = RAS low, CAS high, WE low; A10 chooses one bank vs all banks.
- RD = CAS low, WE high; WR = CAS and WE low; A10 adds auto-precharge.
- MRS = all three command strobes low; BA selects MR0-MR3.
- REF = RAS and CAS low, WE high; the same encoding with falling CKE becomes self-refresh entry.
- A12/BC is the burst-length control: 1 = BL8, 0 = BC4. It is ignored when the mode register fixes the burst length.

## CKE truth table

| Current state | CKE prev | CKE cur | Command (N) | Result |
| --- | --- | --- | --- | --- |
| Power-down | L | L | X | remain in power-down |
| Power-down | L | H | NOP or DES | exit power-down |
| Self-refresh | L | L | X | remain in self-refresh |
| Self-refresh | L | H | NOP or DES | exit self-refresh |
| Bank(s) active | H | L | NOP or DES | active power-down entry |
| Reading / writing / precharging | H | L | NOP or DES | power-down entry after burst finishes |
| All banks idle | H | L | NOP or DES | precharge power-down entry |
| All banks idle | H | L | REF | self-refresh entry |

## Data mask

One DM pin per 8 DQ bits is sampled with the write data. DM = 0 writes the byte; DM = 1 masks it and the byte is not changed. DM is unused during reads. On x8 devices the same ball can be configured as TDQS instead of DM.

## Not in the table

- No Burst Terminate command exists in DDR3 (DDR had one; DDR2 and DDR3 dropped it).
- No Off-Chip Driver Calibration (OCD) command exists in DDR3; OCD was removed.
- No per-bank refresh exists; a REF cycle always refreshes all banks.
- DBI, parity, and ECC are not part of the base DDR3 command set.

**Source:** JESD79-3F sections 4.1, 4.2, 4.3, 4.4, 4.9
