# Data Path: Prefetch, Bursts, Strobes, and Data Integrity

## 8n prefetch

DDR4 keeps the 8n prefetch introduced with DDR3: every column access moves eight
words per DQ group between the array and the IO buffers in one internal
transfer. The array therefore runs at one eighth of the pin data rate. BL8 is
the natural transfer; BC4 (burst chop) is a BL8 transfer stopped after four
words on the bus. Rules such as tWR and tWTR are anchored to the second half of
the internal 8-word movement, which is why fixed-BC4 writes pull those timings
in by two clocks while OTF-BC4 writes behave like BL8.

## Burst length and burst order

Burst length is set by MR0 A1:A0 and can be fixed BL8, fixed BC4, or OTF via
A12/BC_n during each READ or WRITE. A12=1 selects BL8 and A12=0 selects BC4;
A12 is not a column address bit in OTF mode.

| MR0 A1:A0 | A12 (OTF) | Burst |
| --- | --- | --- |
| 00 | 1 | BL8 (fixed) |
| 01 | 0/1 | BL8 or BC4 selected by A12 |
| 10 | 0 | BC4 (fixed) |
| 11 | - | reserved |

Burst type (MR0 A3) selects sequential or interleaved ordering. The table below
shows the data word order inside the burst.

| BL | Start A2:A0 | Sequential | Interleaved |
| --- | --- | --- | --- |
| BC4 (read) | 000 | 0,1,2,3 | 0,1,2,3 |
| BC4 (read) | 001 | 1,2,3,0 | 1,0,3,2 |
| BC4 (read) | 010 | 2,3,0,1 | 2,3,0,1 |
| BC4 (read) | 011 | 3,0,1,2 | 3,2,1,0 |
| BC4 (read) | 100 | 4,5,6,7 | 4,5,6,7 |
| BC4 (read) | 101 | 5,6,7,4 | 5,4,7,6 |
| BC4 (read) | 110 | 6,7,4,5 | 6,7,4,5 |
| BC4 (read) | 111 | 7,4,5,6 | 7,6,5,4 |
| BC4 (write) | 0,V,V | 0,1,2,3 | 0,1,2,3 |
| BC4 (write) | 1,V,V | 4,5,6,7 | 4,5,6,7 |
| BL8 (read/write) | 000 | 0,1,2,3,4,5,6,7 | 0,1,2,3,4,5,6,7 |
| BL8 (read/write) | 001 | 1,2,3,0,5,6,7,4 | 1,0,3,2,5,4,7,6 |
| BL8 (read/write) | 010 | 2,3,0,1,6,7,4,5 | 2,3,0,1,6,7,4,5 |
| BL8 (read/write) | 011 | 3,0,1,2,7,4,5,6 | 3,2,1,0,7,6,5,4 |
| BL8 (read/write) | 100 | 4,5,6,7,0,1,2,3 | 4,5,6,7,0,1,2,3 |
| BL8 (read/write) | 101 | 5,6,7,4,1,2,3,0 | 5,4,7,6,1,0,3,2 |
| BL8 (read/write) | 110 | 6,7,4,5,2,3,0,1 | 6,7,4,5,2,3,0,1 |
| BL8 (read/write) | 111 | 7,4,5,6,3,0,1,2 | 7,6,5,4,3,2,1,0 |

When write CRC is enabled, fixed BL8 writes use A2:A1:A0=0:0:0. For BC4 writes
with CRC, A2 selects whether the lower or upper four data words are sent first.

## DQS: the source-synchronous strobe

DQ transitions are referenced to DQS_t/DQS_c, not directly to CK.

- Reads: the DRAM drives DQS edge-aligned with DQ. The read preamble is
  programmable to 1tCK or 2tCK via MR4 A11; the 2tCK mode is intended for
  DDR4-2400 and above. Minimum tRPRE is 0.9 tCK for 1tCK mode and 1.8 tCK for
  2tCK mode. The read postamble is fixed at a nominal 0.5tCK, with tRPST(min)
  0.33 tCK. tDQSCK bounds the strobe rising edge to CK, tDQSQ bounds the latest
  valid DQ transition to DQS, and tQH bounds the earliest invalid transition.
  tQSH and tQSL describe the high and low pulse widths of the differential
  strobe.
- Writes: the controller drives DQS and must keep its rising edge within tDQSS
  of CK (about +/-0.27 tCK). DQ setup and hold against DQS are tDS and tDH.
  Write preamble is programmable to 1tCK or 2tCK via MR4 A12; choosing 2tCK
  increments the first CWL set by two clocks and adds one clock to tWTR. Minimum
  tWPRE is 0.9 tCK in 1tCK mode and 1.8 tCK in 2tCK mode; tWPST(min) is 0.33
  tCK.
- Read preamble training is available in MPR mode via MR4 A10 and can be used
  for read leveling.

## DM and DBI

x8 and x16 devices share one DM_n/DBI_n/TDQS_t pin per byte lane; x4 devices do
not support DM or DBI. The pin is active low.

| Function | Control | Behavior |
| --- | --- | --- |
| DM | MR5 A10=1 | On writes, low DM_n masks that byte so the old value is kept. |
| Write DBI | MR5 A11=1 | On writes, low DBI_n tells the DRAM to invert the received DQ byte. |
| Read DBI | MR5 A12=1 | On reads, the DRAM inverts the DQ byte and drives DBI_n low when more than four bits in the byte are zero. |
| TDQS | MR1 A11=1 | x8 only; enables termination reference for the strobe. Mutually exclusive with DM and DBI. |

DM and write DBI cannot be enabled at the same time. When both are disabled,
the DRAM turns off the receiver on that pin during writes; when read DBI is
disabled, the DRAM turns off the driver on that pin during reads.

## Write CRC

DDR4 provides CRC for writes only, not for reads. The polynomial is the ATM-8
HEC, X^8 + X^2 + X + 1. The controller generates the 8-bit checksum and appends
it to the burst. When CRC is enabled the write frame is always 10 UI long for
both BL8 and BC4. A x8 device uses one 72-bit CRC tree (64 data bits plus the
DM/DBI lane or ones if neither is enabled); a x16 device uses two identical
72-bit trees; a x4 device uses a 32-bit tree. CRC mismatches are reported as a
pulse on ALERT_n. When both DM and write CRC are enabled, the DRAM checks CRC
before committing data and blocks the write on mismatch; timing parameters
switch to tWR_CRC_DM, tWTR_S_CRC_DM, and tWTR_L_CRC_DM.

The data bus does not carry conventional parity or ECC; CRC and CA parity are
the DDR4 integrity mechanisms. CA parity and the ALERT_n pin are discussed in
the ODT file in this chapter.

## Latency arithmetic, collected

| Quantity | Formula | Programmed by |
| --- | --- | --- |
| RL (read latency) | AL + CL + PL | MR1 (AL), MR0 (CL), MR5 (PL) |
| WL (write latency) | AL + CWL + PL | MR1 (AL), MR2 (CWL), MR5 (PL) |
| RD cmd -> data | RL clocks | |
| WR cmd -> first DQS | WL clocks | |
| RD->RD or WR->WR, same bank group | max(tCCD_L, BL/2) | |
| RD->RD or WR->WR, different bank group | max(tCCD_S, BL/2) | |
| RD -> WR | BL/2 + 2 clocks (book symbol tRTW; not named in JESD79-4D) | |

**Source:** JESD79-4D sections 4.3, 4.11, 4.16, 4.19, 4.20, 4.21
