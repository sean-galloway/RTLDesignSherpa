# Data Path: Prefetch, Bursts, Strobes

## 8n prefetch

Each column access fetches eight words per IO group between the array and the
IO buffers in one internal transfer. The array core therefore runs at one eighth
of the pin data rate. This is the architectural jump from DDR2 to DDR3: the
external bus doubled again while the core clock stayed behind.

Consequences that shape the rest of the protocol:

- BL8 is the natural burst; BC4 (burst chop) is a BL8 transfer truncated to four
  words on the bus.
- Timing measured from internal data movement is anchored to the last 4-word
  half of the burst, which is why BC4 and BL8 sometimes differ by 2 clocks in
  rules such as tWR and tWTR.
- The array only supports aligned 8-word transfers; the controller must still
  respect burst boundaries.

## Burst length and burst order

DDR3 supports BL8 and BC4, selected either by MR0 bits A1:A0 or on-the-fly via
A12/BC# during each READ or WRITE command. In the on-the-fly mode, A12=1 selects
BL8 and A12=0 selects BC4. A12 is used only for burst control, not as a column
address.

| MR0 A1:A0 | A12 (OTF) | Burst |
| --- | --- | --- |
| 00 | 1 | BL8 (fixed) |
| 01 | 0/1 | BL8 or BC4 selected via A12 |
| 10 | 0 | BC4 (fixed) |
| 11 | - | reserved |

Burst type (MR0 A3) selects sequential or interleaved address order. The table
below shows the data word order inside the burst.

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
| BL8 (read/write) | 011 | 3,0,1,2,7,4,5,6 | 3,2,1,0,7,6,5,4 |
| BL8 (read/write) | 101 | 5,6,7,4,1,2,3,0 | 5,4,7,6,1,0,3,2 |
| BL8 (read/write) | 111 | 7,4,5,6,3,0,1,2 | 7,6,5,4,3,2,1,0 |

For writes, only A2 is meaningful because the lower column bits are ignored.
When burst length is fixed to BC4 by MR0, the internal write starts two clocks
sooner than in BL8 mode, pulling in tWR and tWTR. When BC4 is selected OTF, the
internal timing follows BL8.

## DQS: the source-synchronous strobe

DQ data is referenced to DQS, not directly to CK.

- Reads: the DRAM drives DQS edge-aligned with DQ. The read preamble (tRPRE,
  minimum 0.9 tCK) places DQS low before the first data; the postamble (tRPST,
  minimum 0.3 tCK) marks the end. tDQSCK bounds the DQS rising edge against CK,
  tDQSQ bounds the latest valid DQ transition against DQS, and tQH bounds the
  earliest invalid transition. tQSH and tQSL describe the high and low pulse
  widths of the differential strobe.
- Writes: the controller drives DQS and must keep it within tDQSS of CK
  (roughly +/-0.25 tCK). DQ setup and hold against DQS are tDS and tDH. The
  write preamble tWPRE and postamble tWPST frame the burst; both have minimum
  values of 0.9 tCK and 0.3 tCK respectively.
- DQS is normally differential (DQS/DQS#). DDR3 also defines TDQS/TDQS# on x8
  parts as a termination reference for the strobe when enabled in MR1.

## Write leveling

Fly-by module routing creates different CK-to-DQS delays at each DRAM on a DIMM.
To let the controller compensate, DDR3 provides write leveling. The controller
sets MR1 A7=1 to enter leveling mode, then sweeps DQS delay while the DRAM feeds
back the sampled CK level on the DQ pins. The controller stops when a 0->1
transition is seen, establishing a DQS-to-CK relationship that satisfies tDQSS,
tDSS and tDSH. Only the DQS/DQS# terminations are controlled by the ODT pin in
this mode; normal read/write decode is suspended. Exit is via another MRS that
clears MR1 A7.

## Write data mask (DM)

One DM pin per byte lane is sampled with write data; a high level masks that
byte so the addressed cell keeps its old value. DM is not used during reads. On
x8 devices, the same pin may be repurposed as TDQS/TDQS# by MR1 A11, in which
case byte-level write masking is unavailable. There is no data bus inversion in
DDR3.

## Latency arithmetic, collected

| Quantity | Formula | Programmed by |
| --- | --- | --- |
| RL (read latency) | AL + CL | MR1 (AL), MR0 (CL) |
| WL (write latency) | AL + CWL | MR1 (AL), MR2 (CWL) |
| RD cmd -> data | RL clocks | |
| WR cmd -> first DQS | WL clocks | |
| RD -> RD, WR -> WR | max(tCCD=2, BL/2) | |
| RD -> WR | BL/2 + 2 clocks (book symbol tRTW) | |

**Source:** JESD79-3F sections 3.4.2, 3.4.3, 3.4.4, 4.8, 4.13, 4.14
