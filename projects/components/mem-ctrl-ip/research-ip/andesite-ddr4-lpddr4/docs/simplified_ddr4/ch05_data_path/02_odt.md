# ODT - On-Die Termination

## What it is

DDR4 keeps the data-bus termination on the die and adds a third programmable
value. MR1 holds the normal termination strength Rtt_Nom, MR2 holds the write
termination strength Rtt_WR, and MR5 holds the parked value Rtt_Park. The ODT
pin still enables and disables Rtt_Nom cycle by cycle; Rtt_Park applies when
ODT is low if it has been enabled. Dynamic ODT switches a rank that is being
written from its nominal/parked value to Rtt_WR without a new MRS command. ODT
mode is enabled if any of MR1 {A10,A9,A8}, MR2 {A11,A10,A9}, or MR5 {A8,A7,A6}
is non-zero.

## Programming

Rtt_Nom is selected by MR1 A10:A9:A8. RZQ is the external 240 ohm reference
resistor connected to the ZQ pin.

| A10 A9 A8 | Rtt_Nom |
| --- | --- |
| 0 0 0 | disabled |
| 0 0 1 | RZQ/4 = 60 ohm |
| 0 1 0 | RZQ/2 = 120 ohm |
| 0 1 1 | RZQ/6 = 40 ohm |
| 1 0 0 | RZQ/1 = 240 ohm |
| 1 0 1 | RZQ/5 = 48 ohm |
| 1 1 0 | RZQ/3 = 80 ohm |
| 1 1 1 | RZQ/7 = 34 ohm |

Rtt_WR is selected by MR2 A11:A10:A9:

| A11 A10 A9 | Rtt_WR |
| --- | --- |
| 0 0 0 | dynamic ODT off |
| 0 0 1 | RZQ/2 = 120 ohm |
| 0 1 0 | RZQ/1 = 240 ohm |
| 0 1 1 | Hi-Z |
| 1 0 0 | RZQ/3 = 80 ohm |
| 1 0 1 | reserved |
| 1 1 0 | reserved |
| 1 1 1 | reserved |

Rtt_Park is selected by MR5 A8:A7:A6:

| A8 A7 A6 | Rtt_Park |
| --- | --- |
| 0 0 0 | disabled |
| 0 0 1 | RZQ/4 = 60 ohm |
| 0 1 0 | RZQ/2 = 120 ohm |
| 0 1 1 | RZQ/6 = 40 ohm |
| 1 0 0 | RZQ/1 = 240 ohm |
| 1 0 1 | RZQ/5 = 48 ohm |
| 1 1 0 | RZQ/3 = 80 ohm |
| 1 1 1 | RZQ/7 = 34 ohm |

Dynamic ODT requires the DLL to be on and locked and is not available during
write leveling or DLL-off mode.

## Synchronous and dynamic ODT timing

In synchronous ODT mode (DLL on and locked), the ODT pin is sampled on rising
CK edges. Rtt_Nom turns on DODTLon clocks after ODT is sampled high and turns
off DODTLoff clocks after ODT is sampled low.

| Symbol | Meaning |
| --- | --- |
| DODTLon | ODT high sample -> termination begins to turn on = CWL + AL + PL - 2 (1tCK preamble) or -3 (2tCK preamble) |
| DODTLoff | ODT low sample -> termination begins to turn off = same as DODTLon |
| RODTLoff | Read command -> internal ODT turn off = CL + AL + PL - 2 (1tCK) or -3 (2tCK) |
| RODTLon4 | Read command -> Rtt_Park turn on for BC4 = RODTLoff + 4 (1tCK) or +5 (2tCK) |
| RODTLon8 | Read command -> Rtt_Park turn on for BL8 = RODTLoff + 6 (1tCK) or +7 (2tCK) |
| ODTH4 | Minimum ODT high after assertion or BC4 write = 4 tCK (1tCK preamble) or 5 tCK (2tCK preamble) |
| ODTH8 | Minimum ODT high after BL8 write = 6 tCK (1tCK preamble) or 7 tCK (2tCK preamble) |

Dynamic ODT adds the following latencies measured from the write command:

| Symbol | Meaning |
| --- | --- |
| ODTLcnw | Rtt_Nom/Park -> Rtt_WR switch = WL - 2 (1tCK) or WL - 3 (2tCK) |
| ODTLcwn4 | Rtt_WR -> Rtt_Nom/Park for BC4 = ODTLcnw + 4 (CRC off) or +7 (CRC on), plus 1 more for 2tCK preamble |
| ODTLcwn8 | Rtt_WR -> Rtt_Nom/Park for BL8 = ODTLcnw + 6 (CRC off) or +7 (CRC on), plus 1 more for 2tCK preamble |
| tADC | skew window for the Rtt change, about 0.3 to 0.7 tCK depending on speed bin |

A READ command overrides the ODT pin: termination is disabled around the read
burst so the DRAM can drive DQ without fighting its own termination.

## Power-down and asynchronous ODT

Synchronous ODT applies in active and idle states and in active/precharge
power-down. MR5 A5 can deactivate the ODT input buffer during power-down to
save power; when it does, Rtt_Nom is not provided during power-down but Rtt_Park
remains if enabled. In DLL-off mode ODT operates asynchronously with tAONAS and
tAOFAS turn-on/turn-off delays; Rtt_WR dynamic ODT is not available and Rtt_WR
must be disabled by MRS.

## ZQ calibration

ZQCL performs a long calibration of output driver and ODT values. The first
ZQCL after reset is allowed tZQinit (1024 nCK); later ZQCL commands are allowed
tZQoper (512 nCK). ZQCS performs a short periodic calibration allowed tZQCS
(128 nCK). During calibration the channel must be quiet, CKE must be high, ODT
must be low, all banks must be precharged with tRP met, and all DQ pins must be
high-impedance or in Rtt_Park. ZQ calibration may be issued in parallel with
DLL lock time when exiting self-refresh, but an explicit command is required
after self-refresh exit (earliest tXS/tXS_Abort/tXS_FAST).

## ALERT_n and data integrity

ALERT_n is not part of ODT but shares the same physical alert path. It reports
write CRC errors as a pulse of at least six clocks; on detection the DRAM sets
MR5 A3 (CRC Error Clear) and MPR page 1 status. ALERT_n also reports CA parity
errors; the two error types cannot be distinguished at the pin and require
reading the mode registers. CA parity latency and persistent-error reporting
are programmed in MR5.

## What DDR4 does NOT have

Stated plainly to avoid back-porting later features:

- No OCD (off-chip driver calibration). ZQ calibration takes its place.
- No on-die ECC and no link-ECC. System-level ECC, if needed, is built above
  the DRAM with extra devices.
- No VTT termination. DDR4 uses 1.2 V SSTL-class signaling, not POD.
- DBI is present, not absent; it is controlled by MR5 A11 and A12.

**Source:** JESD79-4D sections 3.5 (MR1/MR2/MR5), 4.12, 4.16, 5.1, 5.2, 5.3, 5.4, 5.5
