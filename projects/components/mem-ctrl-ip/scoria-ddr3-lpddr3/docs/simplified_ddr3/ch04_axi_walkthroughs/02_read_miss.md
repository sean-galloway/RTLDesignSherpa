# Walkthrough 2: AXI4 Read, Row Miss

Same controller configuration as Walkthrough 1 (CL=5, CWL=5, AL=0, RL=5, WL=5, BL8; tRCD=5, tRP=5, tRAS=15).

## Scenario

Initial bank state: B5 has row R6 open (from earlier traffic). AXI4 read arrives: ARADDR maps to bank B5, row R2, column C1, ARLEN=7.

Row R2 is not the open row -> row miss. The bank must be closed and the right row opened before the read.

## Command trace

```
PRE B5           # close R6 - wrong row is open in B5, precharge before re-activating
--- (tRP = 5) ---# sense amps need tRP to finish restoring before the next ACT
ACT B5 R2        # open the requested row R2
--- (tRCD = 5) ---# row decode needs tRCD before a CAS command is legal
RD  B5 C1        # AL=0: no posted CAS, issue exactly at ACT+tRCD
```

Timeline:

```
clk:      0     1    2    3    4     5     6     7     8     9    10   11   12   13   14   15   16   17   18   19   20
CMD:      PRE                              ACT                     RD
                |<----- tRP=5 ----->|       |<----- tRCD=5 ----->|
DQ:                                                                         D0   D1   D2   D3   D4   D5   D6   D7
```

- PRE at clk 0, ACT legal at clk 5 (tRP).
- RD issued at clk 10 (tRCD after ACT at clk 5).
- Read data starts at clk 10 + RL = clk 15.

## Cost accounting

Row miss penalty = tRP + tRCD of pure dead time on this bank before data can flow: 10 clocks here, versus 0 for a hit. With AL=0, posted CAS is off, so the RD command slot is spent at ACT+tRCD; nothing hides the latency.

## AXI side

- The AR channel accepts the request; the controller cannot produce R beats until the DRAM data comes back, so the master just sees a longer RVALID latency. Nothing on the AXI interface changes - all of this is hidden inside the controller.
- If the master had a second read outstanding to a different (idle) bank, a good scheduler would run that one first during the tRP/tRCD bubble.

## Variation: read with auto precharge (RDA)

If the controller predicts no further use of R2 soon, it issues `RDA B5 C1` (A10=1) instead. The bank then precharges itself after the read burst completes and tRTP is satisfied, and is idle for the next tenant without a separate PRE command slot. In DDR3 the minimum read-to-precharge spacing for auto-precharge is AL + tRTP clocks after the RD command, delayed if tRAS is not yet met.

**Source:** JESD79-3F sections 3.4.2.1, 3.4.3.4, 4.11, 4.12, 4.13.1, 4.13.3
