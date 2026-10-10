# Command Truth Tables

Two tables govern what the device does: the command truth table (what
the CA pins mean this cycle) and the CKE table (what a CKE edge means
given the device's current state). Both are paraphrased below.

## Command truth table

CKE(n-1) is CKE at the previous rising edge; CKE(n) and CS_n and CAxr
are sampled at the current rising edge; CAxf at the current falling
edge. H/L = logic level, X = don't care (but driven).

| Command | CKE(n-1) | CKE(n) | CS_n | CA0r | CA1r | CA2r | CA3r | Falling edge payload |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| MRW | H | H | L | L | L | L | L | MA6 MA7, OP0-OP7 |
| MRR | H | H | L | L | L | L | H | MA6 MA7 |
| REFpb | H | H | L | L | L | H | L | X |
| REFab | H | H | L | L | L | H | H | X |
| Enter self-refresh | H | L | L | L | L | H | X | X |
| ACT | H | H | L | L | H | R8 | R9 | R0-R7, R13, R14 |
| WR | H | H | L | H | L | L | X | AP, C3-C11 |
| RD | H | H | L | H | L | H | X | AP, C3-C11 |
| PRE (bank/all) | H | H | L | H | H | L | H | X |
| BST | H | H | L | H | H | L | L | X |
| Enter DPD | H | L | L | H | H | L | X | X |
| NOP | H | H | L | H | H | H | X | X |
| Deselect (NOP) | H | H | H | X | X | X | X | X |
| Enter power-down | H | L | H | X | X | X | X | X |
| Exit PD/SREF/DPD | L | H | H | X | X | X | X | X |
| Maintain PD/SREF/DPD | L | L | X | X | X | X | X | X |

Notes that load-bear:

- ACT rising edge: CA2r-CA6r = R8-R12, CA7r-CA9r = BA0-BA2; falling
  edge CA0f-CA7f = R0-R7, CA8f = R13, CA9f = R14.
- RD/WR rising edge: CA5r = C1, CA6r = C2, CA7r-CA9r = BA0-BA2; falling
  edge CA0f = AP, CA1f-CA9f = C3-C11.
- PRE rising edge: CA4r = AB (1 = all banks, bank address ignored),
  CA7r-CA9r = BA0-BA2 for the per-bank case.
- MRW/MRR rising edge: CA4r-CA9r = MA0-MA5; falling edge CA0f = MA6,
  CA1f = MA7; MRW falling edge CA2f-CA9f = OP0-OP7.
- REFpb exists only on 8-bank devices.
- Self-refresh and DPD exits are asynchronous (CKE rise); power-down
  exit is synchronous.

## CKE table (power-state transitions)

| Current state | CKE(n-1) | CKE(n) | CS_n | Command | Next state |
| --- | --- | --- | --- | --- | --- |
| Active power-down | L | L | X | X | Active power-down |
| Active power-down | L | H | H | NOP | Active (exit, wait tXP) |
| Idle power-down | L | L | X | X | Idle power-down |
| Idle power-down | L | H | H | NOP | Idle (exit, wait tXP) |
| Self refresh | L | L | X | X | Self refresh |
| Self refresh | L | H | H | NOP | Idle (exit, wait tXSR) |
| Deep power-down | L | L | X | X | Deep power-down |
| Deep power-down | L | H | H | NOP | Power on (full re-init) |
| Banks active | H | L | H | NOP | Active power-down |
| All banks idle | H | L | H | NOP | Idle power-down |
| All banks idle | H | L | L | REF code | Self refresh |
| All banks idle | H | L | L | DPD (PRE) code | Deep power-down |
| Any (CKE high) | H | H | - | per command truth table | - |

The clock must toggle at least twice during tXP and during tXSR. States
and sequences not shown are illegal.

## NOP encodings

NOP has two legal forms: CS_n high at the rising edge (Deselect), or
CS_n low with CA0r = CA1r = CA2r = H. A NOP never terminates an in-flight
operation; it just keeps the bus quiet. NOP is the mandatory follow-up
to every power-state entry and exit.

**Source:** JESD209-2F sections 5.17, 5.18.1 (Table 60), 5.19 (Table 61)
