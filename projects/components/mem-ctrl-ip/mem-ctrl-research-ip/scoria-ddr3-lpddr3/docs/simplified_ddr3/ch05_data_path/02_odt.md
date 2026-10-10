# ODT - On-Die Termination

## What it is

DDR3 keeps termination on the die, but adds a second programmable value. MR1
holds the normal termination strength Rtt_Nom; MR2 holds a separate write
termination strength Rtt_WR. During writes the device can switch from Rtt_Nom
to Rtt_WR automatically without a new MRS command. This is dynamic ODT, and it
is the big difference from DDR2.

The ODT pin still enables and disables termination cycle by cycle. When any of
MR1 {A9,A6,A2} or MR2 {A10,A9} are non-zero, ODT mode is enabled; otherwise the
DRAM ignores the ODT pin.

## Programming

MR1 bits A9:A6:A2 select Rtt_Nom. RZQ is the external 240 ohm reference resistor
connected to the ZQ pin.

| A9 A6 A2 | Rtt_Nom |
| --- | --- |
| 0 0 0 | disabled |
| 0 0 1 | RZQ/4 = 60 ohm |
| 0 1 0 | RZQ/2 = 120 ohm |
| 0 1 1 | RZQ/6 = 40 ohm |
| 1 0 0 | RZQ/12 = 20 ohm |
| 1 0 1 | RZQ/8 = 30 ohm |
| 1 1 0 | reserved |
| 1 1 1 | reserved |

If Rtt_Nom is used during writes, only RZQ/2, RZQ/4 and RZQ/6 are allowed.

MR2 bits A10:A9 select Rtt_WR:

| A10 A9 | Rtt_WR |
| --- | --- |
| 0 0 | dynamic ODT disabled |
| 0 1 | RZQ/4 = 60 ohm |
| 1 0 | RZQ/2 = 120 ohm |
| 1 1 | reserved |

Dynamic ODT requires the DLL to be on and locked. It is not available during
write leveling or DLL-off mode.

## ODT timing

In synchronous ODT mode (DLL on and locked), the ODT pin is sampled on rising
CK edges. Termination turns on ODTLon clocks after ODT is sampled high and turns
off ODTLoff clocks after ODT is sampled low, where ODTLon = ODTLoff = WL - 2.
With additive latency, this becomes CWL + AL - 2.

| Symbol | Meaning |
| --- | --- |
| ODTLon | ODT high sample -> termination begins to turn on |
| ODTLoff | ODT low sample -> termination begins to turn off |
| tAONmin/max | Rtt leaves high-Z / reaches full Rtt, measured from ODTLon |
| tAOFmin/max | Rtt starts to turn off / reaches high-Z, measured from ODTLoff |
| ODTH4 | minimum ODT high time after assertion or after a BC4 write = 4 tCK |
| ODTH8 | minimum ODT high time after a BL8 write = 6 tCK |

Dynamic ODT adds three more latencies measured from the write command:

| Symbol | Meaning |
| --- | --- |
| ODTLcnw | Rtt_Nom -> Rtt_WR switch = WL - 2 |
| ODTLcwn4 | Rtt_WR -> Rtt_Nom for BC4 = 4 + ODTLoff |
| ODTLcwn8 | Rtt_WR -> Rtt_Nom for BL8 = 6 + ODTLoff |
| tADC | skew window for the Rtt change = 0.3 to 0.7 tCK |

## System rules

- Reads: the DRAM cannot terminate and drive at the same time, so ODT must be
driven low at least half a clock before the read preamble and may only rise again
after the postamble.
- Power-down: synchronous ODT applies in active and idle power-down; in
precharge power-down the behavior depends on whether the DLL is kept enabled via
MR0 A12. In DLL-off mode ODT must be disabled by holding ODT low and/or clearing
Rtt_Nom.
- Reset: the reset pin forces the device into a known state; ODT is off during
reset and re-enabled later under normal MRS programming.
- Rtt changes by MRS require a quiet window. After any MRS that affects
termination, wait tMOD before the new value is reliable.

## ZQ calibration

The ZQCL command performs a long calibration of output driver and ODT values.
It is used at initialization and is allowed tZQinit for the first command after
reset and tZQoper for later long calibrations. The ZQCS command performs a short
periodic calibration and is allowed tZQCS. During any ZQ calibration the channel
must be quiet, CKE must be high, ODT disabled, all banks precharged with tRP met,
and all DQ pins high-impedance. ZQ calibration may be issued in parallel with DLL
lock time when exiting self-refresh, but an explicit command is required after
self-refresh exit (earliest time tXS).

## What DDR3 does NOT have

Stated plainly, because later generations add these and it is easy to back-port
them mentally:

- No DBI (data bus inversion). Every DQ drives its true value; there is no
  inversion flag pin.
- No write or command parity. A corrupted command or write is silently executed.
- No on-die ECC and no ECC storage mode. System-level ECC, if wanted, is the
  controller's job with extra DRAM devices for check bits.
- No CRC on the data bus (that arrives with DDR4).
- No OCD (off-chip driver calibration). ZQ calibration replaces that idea.

If your design needs any of these properties, build them above the DRAM.

**Source:** JESD79-3F sections 3.4.3, 3.4.4, 3.4.5, 4.8, 5.1, 5.2, 5.3, 5.5
