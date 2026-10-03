# Command Truth Tables

LPDDR3 uses a flat, 8-bank topology with no bank groups and no stack IDs. Commands and addresses travel multiplexed over the 10-bit CA bus on both clock edges; a single command spans one full clock cycle. A hardware RESET# pin is also provided for full device reset.

## Pin conventions

- CKE(n-1) and CKE(n) are sampled at successive rising edges; CS_n is sampled at the rising edge.
- CAxr is CA bit x on the rising edge; CAxf is the same bit on the falling edge.
- H/L are valid logic levels; X means the pin is driven but its value does not matter.

## Command truth table

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
| PRE (per-bank/all) | H | H | L | H | H | L | H | X |
| Enter DPD | H | L | L | H | H | L | H | X |
| NOP | H | H | L | H | H | H | X | X |
| Deselect (NOP) | H | H | H | X | X | X | X | X |
| Enter power-down | H | L | H | X | X | X | X | X |
| Exit PD/SREF/DPD | L | H | H | X | X | X | X | X |
| Maintain PD/SREF/DPD | L | L | X | X | X | X | X | X |

Notes that load-bear:

- ACT: CA4r-CA6r carry R10-R12; CA7r-CA9r select BA0-BA2; the falling edge carries R0-R7, then R13-R14.
- RD/WR: CA5r-CA6r carry C1-C2, CA7r-CA9r select the bank; CA0f is AP and CA1f-CA9f carry C3-C11. C0 is implied zero and never transmitted.
- PRE: CA4r = AB (1 = precharge all banks); when AB = 0, CA7r-CA9r select the bank.
- MRW/MRR: CA4r-CA9r carry MA0-MA5; CA0f = MA6 and CA1f = MA7.
- Self-refresh and DPD exits use an asynchronous CKE rise; power-down exit is synchronous.
- NOP can be issued either by driving CS_n high or by driving CS_n low with CA0r-CA2r high.

## CKE table

| Current state | CKE(n-1) | CKE(n) | CS_n | Command | Next state |
| --- | --- | --- | --- | --- | --- |
| Active power-down | L | L | X | X | Active power-down |
| Active power-down | L | H | H | NOP | Active (wait tXP) |
| Idle power-down | L | L | X | X | Idle power-down |
| Idle power-down | L | H | H | NOP | Idle (wait tXP) |
| Resetting power-down | L | L | X | X | Resetting power-down |
| Resetting power-down | L | H | H | NOP | Idle if tINIT5 elapsed, else Resetting |
| Self refresh | L | L | X | X | Self refresh |
| Self refresh | L | H | H | NOP | Idle (wait tXSR) |
| Deep power-down | L | L | X | X | Deep power-down |
| Deep power-down | L | H | H | NOP | Power-on (re-init) |
| Banks active | H | L | H | NOP | Active power-down |
| All banks idle | H | L | H | NOP | Idle power-down |
| All banks idle | H | L | L | REF code | Self refresh |
| All banks idle | H | L | L | PRE code | Deep power-down |
| Any (CKE high) | H | H | - | per command table | - |

At least two clock transitions must occur while tXP or tXSR elapses. Sequences not shown are illegal.

## State table highlights

| Current state of bank n | Command to bank n | Next state |
| --- | --- | --- |
| Idle | ACT | Row active (after tRCD) |
| Idle | REFpb/REFab | Refreshing |
| Idle | MRW/MRR/Reset/PRE | As defined |
| Row active | RD/WR | Reading/Writing |
| Row active | PRE | Precharging -> Idle |
| Row active | MRR | Active MR reading |
| Reading | RD/WR (after current burst) | Reading/Writing |
| Writing | WR/RD (after current burst) | Writing/Reading |
| Refreshing | NOP only | Idle after tRFC |
| MR writing | NOP only | Idle after tMRW |

A command other than NOP must not interrupt an in-flight burst, refresh interval, or MRW window; NOPs are required on every rising edge during those intervals.

**Source:** JESD209-3C sections 4.1, 4.7, 4.8, 4.9, 4.10-4.11, 4.13-4.17
