# Walkthrough 4: Mixed Traffic and Bus Turnarounds

Same controller configuration (CL=5, CWL=5, AL=0, RL=5, WL=5, BL8; tWTR=5, tWR=10, tCCD=4, tRRD=4, tFAW=16).

The shared DQ bus can only face one way at a time. Read-to-write and write-to-read direction changes cost idle bus clocks - the turnaround bubbles - and they are where bandwidth goes to die in mixed traffic.

## Scenario

Four AXI4 requests, in arrival order:

1. Read B3 R5 C2 (B3 has R5 open - hit)
2. Write B1 R4 C0 (B1 idle)
3. Read B2 R1 C6 (B2 idle)
4. Read B3 R5 C7 (same open row as #1 - hit)

## Command trace

```
RD  B3 C2        # hit: data flows immediately, RL=5
--- (RD->WR: BL/2+2 = 6 clk command gap) ---   # bus must clear the read burst
ACT B1 R4        # schedule during the turnaround bubble - command bus is free
WR  B1 C0        # AL=0; first DIN at WR+WL(5); bus turned around
--- (WR->RD: WL+BL/2+tWTR = 14 clk) ---        # last DIN must reach the array
ACT B2 R1        # again hidden inside the bubble
RD  B2 C6        # next read legal 14 clks after the WR
RD  B3 C7        # hit; tCCD=4 after previous RD - seamless
```

Timeline (clock numbers approximate the spacing rules):

```
clk:    0    1    2    3    4    5    6    7    8    9   10   11   12   13   14   15   16   17   18   19   20   21   22   23
CMD:    RD   ACT                   WR                                                       ACT              RD              RD
             |<- 6 ->|                 |<------- 14 ------->|
bus:    ........ D0-D7 ....... p  D0-D7 ............................ p  D0-D7 D0-D7
dir:        RD->      (bubble)    WR->           (bubble)            RD->    RD->
```

## The two turnaround rules

| Transition | Command spacing | Why |
| --- | --- | --- |
| RD -> WR | BL/2 + 2 (6 clk at BL8) | Read burst + postamble must clear the bus before the write preamble |
| WR -> RD | WL + BL/2 + tWTR (14 clk here) | tWTR is measured from the first CK edge after the last write data; WL + BL/2 positions that edge from the WR command |

The RD->WR spacing is specified by JESD79-3F as RL + tCCD + 2 - WL, which simplifies to BL/2 + 2 when RL = WL. The spec does not name this rule; this book uses tRTW as a common book symbol.

tWTR is internal and invisible on the bus, but the command spacing rule enforces it. CL does not appear in the WR->RD rule: with CWL programmed independently (MR2), the write tail is positioned by WL alone, and RL runs from the RD command itself.

## Scheduling takeaways

- Turnarounds are more expensive than same-direction tCCD gaps: 6 and 14 clocks here versus 4. Grouping reads with reads and writes with writes (write batching / read prioritization) is the single biggest bandwidth lever in mixed traffic.
- ACT commands to other banks are nearly free: the command bus is idle during data turnarounds, so row misses on other banks hide completely.
- tFAW still applies: this trace's two ACTs (clk 1 and clk 19) are 18 clocks apart, fine; a burst of five ACTs within 16 clocks would stall the fifth.
- With only 8 banks in the drill model, tFAW (4 ACTs per 16 clocks) can bind before tRRD does on an activate-heavy stream - watch both.
- Maintenance commands such as ZQCS/ZQCL, REF, or any DLL re-lock step are all-bank and require the channel to be idle; a controller must reserve slots for them, adding further bubbles in sustained traffic.

## AXI side

The AXI fabric never sees any of this. Read masters see variable RVALID latency; write masters see variable WREADY/BVALID timing. A controller with enough queue depth reorders requests 1-4 (respecting AXI ordering rules per ID) to convert the trace above into two reads back-to-back and the write parked until the bus is free.

**Source:** JESD79-3F sections 3.4.2.1, 3.4.3.4, 3.4.4.2, 4.11, 4.12, 4.13.1, 4.14.1, 4.14.2, 5.5
