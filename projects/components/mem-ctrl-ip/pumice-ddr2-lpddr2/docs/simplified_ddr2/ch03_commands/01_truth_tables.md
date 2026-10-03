# Command Truth Tables

All commands are registered on the rising edge of CK from the state of CS,
RAS, CAS, WE (and CKE across two cycles for power modes). H = high, L =
low, X = either (but a valid level). BA selects the bank, or the target
register for MRS/EMRS.

## Command truth table

| Command | CKE prev | CKE cur | CS | RAS | CAS | WE | A10 | Address |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| MRS / EMRS | H | H | L | L | L | L | OP | BA=reg, op code on A |
| Refresh (REF) | H | H | L | L | L | H | X | X |
| Self-refresh entry | H | L | L | L | L | H | X | X |
| Self-refresh exit | L | H | H/X or L | X/H | X/H | X/H | X | X |
| Precharge one bank | H | H | L | L | H | L | L | BA = bank |
| Precharge all (PREA) | H | H | L | L | H | L | H | X |
| Activate (ACT) | H | H | L | L | H | H | row | BA = bank, row on A |
| Write (WR) | H | H | L | H | L | L | L | BA, column |
| Write w/ auto pre (WRA) | H | H | L | H | L | L | H | BA, column |
| Read (RD) | H | H | L | H | L | H | L | BA, column |
| Read w/ auto pre (RDA) | H | H | L | H | L | H | H | BA, column |
| NOP | H | X | L | H | H | H | X | X |
| Deselect (DES) | H | X | H | X | X | X | X | X |
| Power-down entry | H | L | H/X or L | X/H | X/H | X/H | X | X |
| Power-down exit | L | H | H/X or L | X/H | X/H | X/H | X | X |

Mnemonics:

- ACT = RAS-only (RAS low, CAS and WE high).
- PRE = RAS + WE (CAS high); A10 picks one bank vs all banks.
- RD = CAS-only (WE high); WR = CAS + WE; A10 on either means "with auto
  precharge".
- MRS = all three strobes low; BA picks which of the four registers.
- REF = RAS + CAS low, WE high; same encoding with CKE falling is
  self-refresh entry instead.
- Power-down entry is any NOP/DES encoding with CKE falling; exit is CKE
  rising with NOP/DES.

## CKE truth table (synchronous transitions)

| Current state | CKE prev | CKE cur | Command | Result |
| --- | --- | --- | --- | --- |
| Power-down | L | L | X | stay in power-down |
| Power-down | L | H | DES or NOP | exit power-down |
| Self-refresh | L | L | X | stay in self-refresh |
| Self-refresh | L | H | DES or NOP | exit self-refresh |
| Bank(s) active | H | L | DES or NOP | active power-down entry |
| All banks idle | H | L | DES or NOP | precharge power-down entry |
| All banks idle | H | L | REF | self-refresh entry |

## Data mask truth table

DM is sampled with write data, one per byte lane: DM = 0 writes the byte,
DM = 1 masks it (the array keeps its old contents). There is no read data
masking. If RDQS is enabled (x8 parts), the pin is RDQS during reads and
DM is unavailable.

## Not in the table

No Burst Terminate command exists in DDR2 (DDR had one; DDR2 dropped it).
BL4 bursts are uninterruptible; BL8 bursts may only be interrupted by a
same-direction burst aligned to the 4-word boundary.

**Source:** JESD79-2F sections 4.1, 4.2, 4.3, 3.6.2
