# Walkthrough 4: Mixed Traffic and Bus Turnarounds

Same controller configuration (CL=10, CWL=10, AL=0, RL=10, WL=10, BL8; tWTR_S=2, tWTR_L=4, tWR=12, tCCD_S=4, tCCD_L=6, tRRD_S=2, tRRD_L=3, tFAW=12). Bank groups are BG0 = {B0,B1,B2,B3} and BG1 = {B4,B5,B6,B7}.

The shared DQ bus can only face one way at a time. Read-to-write and write-to-read direction changes cost idle bus clocks - the turnaround bubbles - and they are where bandwidth goes to die in mixed traffic. Bank groups add a second lever: same-group spacing is tCCD_L/tRRD_L/tWTR_L; different-group spacing is the shorter tCCD_S/tRRD_S/tWTR_S.

## Scenario

Seven AXI4 requests, in arrival order:

1. Read B0 R5 C2 (B0 has R5 open - hit, BG0)
2. Read B1 R5 C6 (B1 has R5 open - hit, BG0, same group as #1)
3. Read B5 R5 C2 (B5 has R5 open - hit, BG1, different group from #2)
4. Write B5 R5 C0 (BG1, same group as #3)
5. Read B2 R5 C4 (B2 has R5 open - hit, BG0, different group from #4)
6. Write B2 R5 C7 (BG0, same group as #5)
7. Read B3 R5 C5 (B3 has R5 open - hit, BG0, same group as #6)

## Command trace

```
RD  B0 C2 (BG0)  # hit: data flows immediately, RL=10
--- (RD B0 -> RD B1: tCCD_L = 6, same bank group) ---
RD  B1 C6 (BG0)  # same group as B0 -> long CAS-to-CAS spacing
--- (RD B1 -> RD B5: tCCD_S = 4, different bank group) ---
RD  B5 C2 (BG1)  # different group -> short spacing; groups interleave
--- (RD B5 -> WR B5: tRTW = 6, read burst must clear the bus) ---
WR  B5 C0 (BG1)  # write to same group as the read
--- (WR B5 -> RD B2: tWTR_S = 2, different bank group -> 16 clk total) ---
RD  B2 C4 (BG0)
--- (RD B2 -> WR B2: tRTW = 6) ---
WR  B2 C7 (BG0)
--- (WR B2 -> RD B3: tWTR_L = 4, same bank group -> 18 clk total) ---
RD  B3 C5 (BG0)
```

Timeline (clock numbers follow the spacing rules above):

```
clk:     0    1    2    3    4    5    6    7    8    9   10   11   12   13   14   15   16   17   18   19   20
CMD:     RD   .    .    .    .    .   RD   .    .    .   RD   .    .    .    .    .   WR   .    .    .    .
         |<--tCCD_L=6-->|      |<--tCCD_S=4-->|      |<--- tRTW = 6 --->|
bus:     ........ D0-D7 ............... D0-D7 ....... D0-D7 ....... p  D0-D7

clk:    21   22   23   24   25   26   27   28   29   30   31   32   33   34   35   36   37   38   39   40   41
CMD:     .    .    .    .    .    .    .    .    .    .    .   RD   .    .    .    .    .   WR   .    .    .
                              |<-------- WL+BL/2+tWTR_S = 16 -------->|
bus:     ............................... p  D0-D7 ............................ p  D0-D7

clk:    42   43   44   45   46   47   48   49   50   51   52   53   54   55   56   57   58   59   60   61   62
CMD:     .    .    .    .    .    .    .    .    .    .    .    .    .    .   RD   .    .    .    .    .    .
                              |<-------- WL+BL/2+tWTR_L = 18 -------->|
bus:     ........................................................... p  D0-D7
```

## The turnaround rules

| Transition | Group relation | Command spacing | Why |
| --- | --- | --- | --- |
| RD -> RD | same | tCCD_L = 6 | Long CAS-to-CAS spacing inside one bank group |
| RD -> RD | different | tCCD_S = 4 | Short CAS-to-CAS spacing across bank groups |
| RD -> WR | either | tRTW = 6 (book symbol) | Read burst + postamble must clear before write preamble; JESD79-4D gives CL - CWL + RBL/2 + 1 + tWPRE, which is 6 here |
| WR -> RD | different | CWL + BL/2 + tWTR_S = 16 | tWTR_S measured from first CK edge after last write data; different group relaxes the delay |
| WR -> RD | same | CWL + BL/2 + tWTR_L = 18 | tWTR_L is longer because the read lands in the same group that is still finishing the write |

tWTR is internal and invisible on the bus, but the command spacing rule enforces it. CL does not appear in the WR->RD rule: with CWL programmed independently (MR2), the write tail is positioned by WL alone, and RL runs from the RD command itself.

## Scheduling takeaways

- Bank groups are the bandwidth lever: a read to B1 followed by a read to B5 saves 2 clocks over back-to-back reads in BG0 (tCCD_S=4 versus tCCD_L=6). The scheduler should interleave groups.
- tRRD splits the same way: ACT-to-ACT to different groups uses tRRD_S=2; to different banks inside the same group uses tRRD_L=3.
- tFAW still applies: a run of four ACT commands must fit inside a 12-clock window. If any of the requests above had been row misses, their ACTs would count toward that window; here all rows are hits so no ACTs appear.
- Refresh is another hidden consumer of bandwidth. In 1x mode a REF command is required on average every tREFI (7.8 us at normal temperature) and locks the channel for tRFC1; 2x and 4x fine-granularity refresh modes trade more frequent shorter pauses for the same total refresh load.
- Grouping reads with reads and writes with writes (write batching / read prioritization) is still the single biggest bandwidth lever in mixed traffic, but bank-group interleaving is the new lever DDR3 did not have.

## AXI side

The AXI fabric never sees any of this. Read masters see variable RVALID latency; write masters see variable WREADY/BVALID timing. A controller with enough queue depth reorders requests 1-7 (respecting AXI ordering rules per ID) to convert the trace above into group-interleaved bursts and park turnarounds.

**Source:** JESD79-4D sections 2.8, 4.9, 4.19, 4.22, 4.23, 4.24, 4.25, 4.25.6, 4.26
