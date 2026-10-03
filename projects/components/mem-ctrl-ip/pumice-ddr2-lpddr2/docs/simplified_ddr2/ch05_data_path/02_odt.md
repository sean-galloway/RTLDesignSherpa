# ODT - On-Die Termination

## What it is

DDR2 moves bus termination onto the die. A programmable termination
resistor (Rtt) sits on every DQ, DQS, DQS#, DM, RDQS and RDQS# pin, and a
dedicated ODT pin switches it in or out. Before ODT, termination lived on
the motherboard and could not follow bus ownership; with ODT, the device
that is listening terminates, and the device that is driving does not.

## Programming

EMR1 bits A6 and A2 select the nominal value:

| A6 A2 | Rtt (nominal) |
| --- | --- |
| 0 0 | ODT disabled |
| 0 1 | 75 ohm |
| 1 0 | 150 ohm |
| 1 1 | 50 ohm (mandatory support at DDR2-800, optional below) |

The ODT pin then enables the programmed value dynamically, cycle by cycle.

## ODT timing

| Symbol | Meaning | Value |
| --- | --- | --- |
| tAOND | ODT pin high -> termination starts turning on | 2 clocks |
| tAON | termination actually in regulation | tAC(min) to tAC(max)+1 ns window |
| tAOFD | ODT pin low -> turn-off begins | 2.5 clocks |
| tAOF | termination released | tAC(min) to tAC(max)+0.6 ns |
| tAONPD / tAOFPD | same, in power-down (slower) | up to ~2-2.5 tCK + tAC |
| tANPD | ODT low before power-down entry | 3 clocks |
| tAXPD | ODT may be re-raised after PD exit | 8 clocks |
| tMOD | EMRS (Rtt change) -> new value live | 0-12 ns |

Changing Rtt by EMRS has a protocol to avoid impedance glitches on the
channel: ODT pin must be low tAOFD before the EMRS, stay low through the
whole tMOD window, and only then be raised again.

## System rules

- Reads: the controller side terminates (its own ODT or board Rtt); the
  DRAM's ODT is off while it drives.
- Writes: the target DRAM's ODT is on; in multi-rank systems the
  non-target rank usually terminates instead (rank-to-rank ODT steering),
  so the driver sees a clean load at the far end.
- ODT must be off before self-refresh entry and during the tXSRD exit
  window; the ODT pin is simply held low.
- ODT is not available at all during self-refresh.

## What DDR2 does NOT have

Stated plainly, because later generations add all of these and it is easy
to back-port them mentally:

- No DBI (data bus inversion). Every DQ bit drives its true value every
  cycle; there is no inversion flag pin and no power-saving inversion
  logic.
- No write or command parity. A corrupted command or write is silently
  executed.
- No on-die ECC and no ECC storage mode. System-level ECC, if wanted, is
  entirely the controller's job with extra DRAM devices for check bits.
- No CRC on the data bus (that arrives with DDR4's write CRC).

If your design needs any of these properties, it must build them above the
DRAM, in the controller or the interconnect.

**Source:** JESD79-2F sections 3.4.4, 3.4.5, 3.10
