# The DDR CA Interface

LPDDR2 has no RAS_n/CAS_n/WE_n and no wide address bus. Everything -
command, bank, row, column, mode-register address and data - travels on
CA0-CA9, clocked in on BOTH edges of one clock cycle. Understanding this
packing is the key to the whole protocol.

## One command = one clock = two edges

- Each command occupies exactly one clock cycle: ten CA bits on the
  rising edge (written CA0r..CA9r) and ten on the falling edge
  (CA0f..CA9f).
- CS_n and CKE are single-data-rate: they are sampled only on the
  rising edge.
- The command itself is decoded from CKE, CS_n and CA0r-CA3r (with CKE
  of the previous cycle for power-state entries). CA4r and above, and
  the whole falling edge, carry payload (addresses, bank, MR fields).
- CS_n high on the rising edge = Deselect (a form of NOP), regardless of
  the CA pins.

## Command codes (rising edge)

| CA0r CA1r CA2r CA3r | Command |
| --- | --- |
| L L L L | MRW |
| L L L H | MRR |
| L L H L | Refresh, per bank (REFpb) |
| L L H H | Refresh, all banks (REFab) |
| L H R8 R9 | ACT (CA2r-CA6r carry row bits) |
| H L L x | WR |
| H L H x | RD |
| H H L L | BST (burst terminate) |
| H H L H | PRE (CA4r = AB all-bank flag) |
| H H H x | NOP |

With CKE falling at this edge, three of these codes become power-state
entries instead: REF code -> self-refresh entry; PRE code -> deep
power-down entry; CS_n high (or NOP) -> power-down entry.

## Where the address bits live

Per command, rising/falling CA assignments (x = don't care):

| Command | Rising edge CA0-CA9 | Falling edge CA0-CA9 |
| --- | --- | --- |
| ACT | L H R8 R9 R10 R11 R12 BA0 BA1 BA2 | R0 R1 R2 R3 R4 R5 R6 R7 R13 R14 |
| RD / WR | H L cmd x x C1 C2 BA0 BA1 BA2 | AP C3 C4 C5 C6 C7 C8 C9 C10 C11 |
| PRE | H H L H AB x x BA0 BA1 BA2 | x x x x x x x x x x |
| MRW | L L L L MA0 MA1 MA2 MA3 MA4 MA5 | MA6 MA7 OP0 OP1 OP2 OP3 OP4 OP5 OP6 OP7 |
| MRR | L L L H MA0 MA1 MA2 MA3 MA4 MA5 | MA6 MA7 x x x x x x x x |

(cmd = H for RD, L for WR; x = don't care)

Consequences:

- A full row address (up to R0-R14) plus bank fits one ACT: upper row
  bits and bank on the rising edge, lower row bits and the top row bits
  (R13, R14) on the falling edge.
- A column address (C1-C11) plus bank plus the auto-precharge flag fits
  one RD/WR: C1, C2 and bank on the rising edge, AP and C3-C11 on the
  falling edge. C0 is implied zero and never transmitted.
- AP (auto-precharge) lives at CA0f of RD/WR. AP=1 closes the row when
  the burst completes.
- The mode-register address is split across edges: MA0-MA5 rising,
  MA6-MA7 falling. MRW data (OP0-OP7) rides CA2f-CA9f.

## Why this matters for a controller

- The CA bus is a scarce resource: every command costs a full clock,
  including NOPs, so scheduling is about packing useful commands into
  every cycle the timing rules allow.
- Bank bits move around per command (CA7r-CA9r on ACT/RD/WR/PRE), and
  the command decoder needs both edges before it knows the full address.
- Because CKE/CS_n are SDR, power-state transitions align to rising
  edges only; the CKE truth table (Chapter 3) is the authority for what
  a CKE edge means.

**Source:** JESD209-2F section 5.18.1 (Table 60 and notes), 5.1, 5.4, 5.5
