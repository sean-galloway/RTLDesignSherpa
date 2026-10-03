# Test Features

LPDDR2 is a pre-boundary-scan mobile part: there is no JTAG boundary
scan, no OCD calibration engine like DDR2's, and no post-package repair
in the standard. What it does have:

## DQ calibration patterns (MR32 / MR40)

Two read-only mode registers return fixed, known data patterns on the
DQ bus. The controller issues an MRR to MR32 or MR40 and uses the known
pattern to train its read capture - essential because LPDDR2 has no DLL
and tDQSCK is an analog window of 2500-5500 ps rather than a fixed
clock count. Unlike a normal MRR (valid data on the first beat only),
the DQ calibration MRRs define content across the burst so timing can
be tuned on repeated edges.

## ZQ calibration (MR10)

Output-driver self-test and calibration against the external 240 ohm
ZQ resistor: initialization calibration (0xFF) at boot, long (0xAB) and
short (0x56) maintenance calibrations, and ZQ reset (0xC3) for default
calibration. MR0's RZQI field reports the ZQ pin connection self-test
result (floating/shorted/normal) after the initialization calibration.
S2 devices ignore all ZQ commands.

## Temperature sensor (MR4)

Covered in Chapters 2 and 6. From a test perspective it is also the
only on-die "measurement" the host can read: a 3-bit refresh-rate
recommendation plus the TUF change flag, updating no faster than
tTSI = 32 ms.

## Vendor test mode (MR9)

A write-only register reserved for vendor-specific test modes. The spec
defines no behavior; using it outside a vendor datasheet is undefined.

## Identity registers

MRR of MR0 (device info, DAI status), MR5 (manufacturer ID), MR6/MR7
(revision IDs) and MR8 (type, density, IO width) is the standard
bring-up sanity check: if the values decode sensibly, the CA interface,
the MRR path and the read capture are all working.

**Source:** JESD209-2F sections 3.5 (MR9, MR10, MR32/MR40), 5.12.2,
5.13.4
