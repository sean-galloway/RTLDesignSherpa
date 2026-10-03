# On-Die Termination

LPDDR3 exposes a dedicated ODT pin that turns termination on or off for each
DQ, DQS_t, DQS_c, and DM line. The pin is not sampled by the clock; the
decision is asynchronous. Termination is intended to improve channel signal
integrity and is controlled independently per device by the memory controller.

## Enabling and selecting the termination value

ODT is configured through MR11.

| MR11 OP<1:0> | RTT value | Notes |
| --- | --- | --- |
| 00B | Disabled | Default |
| 01B | RZQ/4 = 60 ohm | Required for 1866/2133; optional for 1333/1600 |
| 10B | RZQ/2 = 120 ohm | |
| 11B | RZQ/1 = 240 ohm | |

MR11 OP<2> selects whether ODT remains functional during CKE power-down:
0B disables it in power-down (default); 1B leaves it enabled, in which case
VDDQ must stay on during power-down.

The absolute accuracy of the on-die termination is maintained by ZQ
calibration (MRW ZQ init, long, or short) against the external 240 ohm RZQ
resistor.

## Asynchronous ODT timing

Because the ODT pin is asynchronous, the only pin-controlled delays are the
pure analog turn-on and turn-off windows.

| Symbol | Definition | Window |
| --- | --- | --- |
| tODTon | ODT pin high to RTT beginning to turn on / fully on | 1.75 ns min to 3.5 ns max |
| tODToff | ODT pin low to RTT beginning to turn off / at high-Z | 1.75 ns min to 3.5 ns max |

## ODT during reads

The DRAM automatically disables termination during any read (RD or MRR) and
re-enables it after the read data completes, even if the ODT pin stays
asserted. The automatic timing is referenced from the read-data clocks:

| Symbol | Definition |
| --- | --- |
| tAODToff | Automatic RTT turn-off after READ data: min = tDQSCK,min - 300 ps, referenced from RL - 2 CK |
| tAODTon | Automatic RTT turn-on after READ data: max = tDQSCK + 1.4 x tDQSQ,max + tCK(avg,min), referenced from RL + BL/2 CK |

## ODT during low-power states and training

| State | ODT behavior |
| --- | --- |
| CKE power-down, OP<2>=0 | Disabled within tODTd (max 12 ns); re-enabled within tODTe (max 12 ns) |
| Self-refresh entry | Disabled within tODTd (max 12 ns + 0.5 tCK) |
| Self-refresh exit | Re-enabled within tODTe (max 12 ns) |
| Deep power-down | Disabled within tODTd; full re-init required on exit |
| CA training | Disabled; ODT pin ignored |
| Write leveling | ODT pin high -> DQS_t/DQS_c termination ON, DQ termination OFF; ODT must be high if enabled |

## ODT states truth table

| Mode | DQ termination | DQS termination |
| --- | --- | --- |
| Write | Enabled (if MR11 enabled and ODT HIGH) | Enabled |
| Read / DQ calibration | Disabled | Disabled |
| ZQ calibration | Disabled | Disabled |
| CA training | Disabled | Disabled |
| Write leveling, ODT asserted | Disabled | Enabled |

## What LPDDR3 does not have

- No synchronous ODT latency (no ODTL-on/off as in DDR3/DDR4).
- No VTT termination rail; termination is purely on-die to VDDQ.
- No DBI, no parity, no CRC, and no on-die ECC.

**Source:** JESD209-3C sections 4.12, 4.12.1-4.12.7, Table 22, Table 23,
Table 54, Table 64
