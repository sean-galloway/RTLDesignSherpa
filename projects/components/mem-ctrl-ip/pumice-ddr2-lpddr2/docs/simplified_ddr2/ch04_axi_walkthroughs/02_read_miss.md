# Walkthrough 2: AXI4 Read, Row Miss

Same controller configuration as Walkthrough 1 (CL=3, AL=2, RL=5, WL=4,
BL4; tRCD=3, tRP=3, tRAS=6).

## Scenario

Initial bank state: B5 has row R6 open (from earlier traffic). AXI4 read
arrives: ARADDR maps to bank B5, row R2, column C1, ARLEN=3.

Row R2 is not the open row -> row miss. The bank must be closed and the
right row opened before the read.

## Command trace

```
PRE B5           # close R6 - wrong row is open in B5, precharge before re-activating
--- (tRP = 3) ---# sense amps need tRP to finish restoring before the next ACT
ACT B5 R2        # open the requested row R2
RD  B5 C1        # posted CAS: issued 1 clk after ACT, DRAM holds it AL=2 clks;
                 # internal CAS lands at ACT+3, exactly tRCD
```

Timeline:

```
clk:      0     1    2    3     4     5     6    7    8    9   10   11
CMD:      PRE                    ACT   RD
                |<-- tRP=3 -->|       |AL=2|
                                  |<------ tRCD=3 (internal) ------>|
DQ:                                                              D0 ... D3
```

- PRE at clk 0, ACT legal at clk 3 (tRP).
- RD posted at clk 4 (one after ACT); additive latency holds it to
  clk 4 + 2 = clk 6 internally, satisfying tRCD = 3 from ACT at clk 3.
- Read data starts at clk 4 + RL = clk 9.

## Cost accounting

Row miss penalty = tRP + tRCD of pure dead time on this bank before data
can flow: 6 clocks here, versus 0 for a hit. Posted CAS hides the command
bus occupancy (the RD command slot is spent early, at clk 4), but it does
not hide the latency - internal CAS still cannot beat tRCD.

## AXI side

- The AR channel accepts the request; the controller cannot produce R
  beats until the DRAM data comes back, so the master just sees a longer
  RVALID latency. Nothing on the AXI interface changes - all of this is
  hidden inside the controller.
- If the master had a second read outstanding to a different (idle) bank,
  a good scheduler would run that one first during the tRP/tRCD bubble.

## Variation: read with auto precharge (RDA)

If the controller predicts no further use of R2 soon, it issues
`RDA B5 C1` (A10=1) instead. The bank then precharges itself
(AL + BL/2 = 4 clocks after the RD command, delayed if tRAS or tRTP is
not yet met) and is idle for the next tenant without a separate PRE
command slot.

**Source:** JESD79-2F sections 3.5, 3.6.1, 3.6.3, 3.7.1, 3.8.1
