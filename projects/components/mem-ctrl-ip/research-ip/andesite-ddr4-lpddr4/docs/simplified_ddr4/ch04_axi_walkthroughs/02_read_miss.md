# Walkthrough 2: AXI4 Read, Row Miss

Same controller configuration as Walkthrough 1 (CL=10, CWL=10, AL=0, RL=10, WL=10, BL8; tRCD=5, tRP=5, tRAS=15). Bank groups are BG0 = {B0,B1,B2,B3} and BG1 = {B4,B5,B6,B7}.

## Scenario

Initial bank state: B5 has row R6 open (from earlier traffic). AXI4 read arrives: ARADDR maps to bank B5, row R2, column C1, ARLEN=7.

Row R2 is not the open row -> row miss. The bank must be closed and the right row opened before the read.

## Command trace

```
PRE B5 (BG1)     # close R6 - wrong row is open in B5, precharge before re-activating
--- (tRP = 5) ---# sense amps need tRP to finish restoring before the next ACT
ACT B5 R2 (BG1)  # open the requested row R2
--- (tRCD = 5) ---# row decode needs tRCD before a CAS command is legal
RD  B5 C1 (BG1)  # AL=0: no posted CAS, issue exactly at ACT+tRCD
```

Timeline:

```
clk:      0     1    2    3    4     5     6     7     8     9    10   11   12   13   14   15   16   17   18   19   20   21   22   23   24   25
CMD:      PRE                              ACT                     RD
                |<----- tRP=5 ----->|       |<----- tRCD=5 ----->|
DQ:                                                                         D0   D1   D2   D3   D4   D5   D6   D7
```

- PRE at clk 0, ACT legal at clk 5 (tRP).
- RD issued at clk 10 (tRCD after ACT at clk 5).
- Read data starts at clk 10 + RL = clk 20.

## Cost accounting

Row miss penalty = tRP + tRCD of pure dead time on this bank before data can flow: 10 clocks here, versus 0 for a hit. With AL=0, posted CAS is off, so the RD command slot is spent at ACT+tRCD; nothing hides the latency.

## AXI side

- The AR channel accepts the request; the controller cannot produce R beats until the DRAM data comes back, so the master just sees a longer RVALID latency. Nothing on the AXI interface changes - all of this is hidden inside the controller.
- If the master had a second read outstanding to a different (idle) bank, a good scheduler would run that one first during the tRP/tRCD bubble.

## Variation: read with auto precharge (RDA)

If the controller predicts no further use of R2 soon, it issues `RDA B5 C1 (BG1)` (A10=1) instead. The bank then precharges itself after the read burst completes and tRTP is satisfied, and is idle for the next tenant without a separate PRE command slot. In DDR4 the minimum read-to-precharge spacing for auto-precharge is AL + tRTP clocks after the RD command, delayed if tRAS is not yet met.

**Source:** JESD79-4D sections 2.8, 4.19, 4.22, 4.23, 4.24, 4.24.3
