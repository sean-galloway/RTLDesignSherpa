# Data Path

## Prefetch

- S4: 4n prefetch. One column access reads or writes 4 words per DQ
  inside the array; the interface serializes them as DDR data over 2
  clock cycles (minimum burst BL4 = 2 clocks on the bus).
- S2: 2n prefetch. The minimum burst occupies 1 clock (BL4 = 1 clock on
  the bus), which is why tCCD = 1 on S2 and 2 on S4.

The prefetch is what lets a 533 MHz / 1066 MT/s interface coexist with a
core that runs a fraction of that speed.

## Burst ordering

MR1 programs BL (4/8/16), burst type and wrap control:

| Mode | Behavior |
| --- | --- |
| Sequential + wrap | Addresses count up from the start column and wrap at the BL boundary |
| Interleaved + wrap | Two-word pairs swap order within the BL block (SDRAM only) |
| No-wrap | BL4 only: 4 words count straight up, may not cross page/sub-page boundaries |

Wrap exists for cache-line fills: the critical word comes first and the
rest of the line follows regardless of starting offset. BL16 with
interleaved order is not a legal combination.

## DQS: the bidirectional strobe

- One differential pair (DQS_t/DQS_c) per byte lane; x16 has 2 pairs,
  x32 has 4.
- Reads: the DRAM drives DQS edge-aligned with DQ, preceded by a tRPRE
  low preamble and followed by a tRPST postamble. The controller
  captures DQ on both DQS edges.
- Writes: the controller drives DQS center-aligned in the DQ eye, with
  a tWPRE preamble and tWPST postamble; the DRAM samples DQ on both DQS
  edges (tDS/tDH around each edge).
- There is no DLL. Read timing is bounded by tDQSCK (2.5-5.5 ns from
  the clock) and tDQSCK may span multiple clock periods - the
  controller must train its capture logic (e.g. with the MR32/MR40 DQ
  calibration patterns) rather than assume DQS is clock-aligned.

## DM - write data mask

One DM pin per byte lane, sampled on both DQS edges with the write
data: DM high masks that beat's byte from being written. DM is how a
controller implements partial writes (AW/ W with WSTRB gaps) without
read-modify-write. DM loading must match DQ/DQS loading. The DNV
(data-not-valid) variant of the pin is an NVM feature; LPDDR2 SDRAM
does not implement it and does not drive the pin.

## No DBI, no parity, no ECC

LPDDR2 has none of the data-integrity helpers of later standards:

- No DBI (data bus inversion) on reads or writes.
- No parity on the CA bus and no CRC on the data bus.
- No on-die ECC.

Every bit on DQ is exactly what the controller put there or exactly what
the array holds. If the system needs error detection or correction it
must be done in the controller (ECC over the data it writes), in the
interconnect, or not at all. This also means the DQ bus carries data
only - never sideband metadata - so every pin cycle of the bus is
payload.

## Termination and signaling

The IO is HSUL_12: unterminated, 1.2 V VDDQ, VREFDQ = VDDQ/2 at the
receiver. There is no ODT pin and no termination to switch - which is
why bus turnaround rules are simple contention-avoidance formulas
(Chapter 6) rather than ODT timing tables. Output drive strength is set
in MR3 and maintained by ZQ calibration against an external 240 ohm
resistor (S4/N only).

**Source:** JESD209-2F sections 2.12, 3 (functional description), 3.5
(Table 21), 5.4-5.7, 9
