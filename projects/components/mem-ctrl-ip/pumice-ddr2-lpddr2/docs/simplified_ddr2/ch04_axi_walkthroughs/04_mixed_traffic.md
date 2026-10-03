# Walkthrough 4: Mixed Traffic and Bus Turnarounds

Same controller configuration (CL=3, AL=2, RL=5, WL=4, BL4; tWTR=3,
tWR=6, tCCD=2, tRRD=2, tFAW=10).

The shared DQ bus can only face one way at a time. Read-to-write and
write-to-read direction changes cost idle bus clocks - the turnaround
bubbles - and they are where bandwidth goes to die in mixed traffic.

## Scenario

Four AXI4 requests, in arrival order:

1. Read B3 R5 C2 (B3 has R5 open - hit)
2. Write B1 R4 C0 (B1 idle)
3. Read B2 R1 C6 (B2 idle)
4. Read B3 R5 C7 (same open row as #1 - hit)

## Command trace

```
RD  B3 C2        # hit: data flows immediately, RL=5
--- (RD->WR: BL/2+2 = 4 clk command gap) ---   # bus must clear the read burst
ACT B1 R4        # schedule during the turnaround bubble - command bus is free
WR  B1 C0        # posted; first DIN at WR+WL(4); bus turned around
--- (WR->RD: CL-1+BL/2+tWTR = 7 clk) ---       # last DIN must reach the array
ACT B2 R1        # again hidden inside the bubble
RD  B2 C6        # next read legal 7 clks after the WR
RD  B3 C7        # hit; tCCD=2 after previous RD - seamless
```

Timeline (clock numbers approximate the spacing rules):

```
clk:    0    1    2    3    4    5    6    7    8    9   10   11   12   13   14
CMD:    RD                        WR                                   RD   RD
             |<- 4 ->|                 |<------ 7 ------>|
bus:    .... D0-D3 .. ..    p  D0-D3 .. .. .. ..    p  D0-D3 D0-D3
dir:        RD->   (bubble)  WR->      (bubble)   RD->    RD->
```

## The two turnaround rules

| Transition | Command spacing | Why |
| --- | --- | --- |
| RD -> WR | BL/2 + 2 (4 clk at BL4) | Read burst + postamble must clear the bus before the write preamble |
| WR -> RD | CL - 1 + BL/2 + tWTR | Last write data must travel from the input buffer into the sense amps before a read reuses them |

tWTR is internal and invisible on the bus, but the command spacing rule
enforces it. Note it does NOT include WL: the spacing is expressed from
the WR command, and CL - 1 already accounts for WL = RL - 1 = AL + CL - 1
with AL cancelled against the posted-CAS hold.

## Scheduling takeaways

- Turnarounds are more expensive than same-direction tCCD gaps: 4 and 7
  clocks here versus 2. Grouping reads with reads and writes with writes
  (write batching / read prioritization) is the single biggest bandwidth
  lever in mixed traffic.
- ACT commands to other banks are nearly free: the command bus is idle
  during data turnarounds, so row misses on other banks hide completely.
- tFAW still applies: this trace's two ACTs are 9 clocks apart, fine; a
  burst of five ACTs within 10 clocks would stall the fifth.
- With only 8 banks in the drill model, tFAW (4 ACTs per 10 clocks) can
  bind before tRRD does on an activate-heavy stream - watch both.

## AXI side

The AXI fabric never sees any of this. Read masters see variable RVALID
latency; write masters see variable WREADY/BVALID timing. A controller
with enough queue depth reorders requests 1-4 (respecting AXI ordering
rules per ID) to convert the trace above into two reads back-to-back and
the write parked until the bus is free.

**Source:** JESD79-2F sections 3.5, 3.6.3, 3.6.4
