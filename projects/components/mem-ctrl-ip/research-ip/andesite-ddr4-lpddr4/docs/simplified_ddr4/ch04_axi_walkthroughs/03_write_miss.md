# Walkthrough 3: AXI4 Write to an Idle Bank

Same controller configuration (CL=10, CWL=10, AL=0, RL=10, WL=10, BL8; tRCD=5, tRP=5, tWR=12). Bank groups are BG0 = {B0,B1,B2,B3} and BG1 = {B4,B5,B6,B7}.

## Scenario

Initial state: all banks idle. AXI4 write arrives: AWADDR maps to bank B1, row R4, column C0, AWLEN=7, followed by 8 W-channel beats.

An idle bank needs no precharge - miss-to-idle is cheaper than miss-to-open-row by tRP.

## Command trace

```
ACT B1 R4 (BG0)  # open the row; bank was idle so no PRE needed
--- (tRCD = 5) ---# wait for row decode before issuing CAS
WR  B1 C0 (BG0)  # AL=0; issued exactly at ACT+tRCD
--- (WL = 10) --- # write latency: first DQS edge lands 10 clks after the WR command
--- (tWR = 12) ---# write recovery: last data must soak into the array before PRE
PRE B1 (BG0)     # close the row (only if the controller wants the bank back)
```

Timeline:

```
clk:      0     1     2    3    4    5     6    7    8    9   10   11   12   13   14   15   16   17   18   19   20   21   22   23   24   25   26   27   28   29   30   31
CMD:      ACT                           WR                                                                                                                               PRE
                                    |<---- WL=10 ---->|
DQS:                                          pre -DQS toggling-
DQ:                                            D0   D1   D2   D3   D4   D5   D6   D7
                                                                                    |<--- tWR=12 --->|
PRE legal at clk 5 + 10(WL) + 4(BL/2) + 12(tWR) = clk 31 from ACT,
i.e. WL + BL/2 + tWR = 26 clocks after the WR command.
```

## AXI side

- AW and W are independent channels; the controller buffers the 8 W beats (or streams them) while the DRAM side runs ACT + WR.
- BREADY goes back to the master once the controller has accepted responsibility for the data - typically after the write is safely in flight to the DRAM, not after tWR completes.
- Write data is strobed in with DQS driven by the controller/PHY; tDQSS alignment to CK is the PHY's job.

## Write recovery is the trap

tWR is not a turnaround nicety; it is array physics. Precharging B1 before tWR expires destroys the data just written - the bits never finish committing from the sense amps to the cells. This is why WR is a mode-register field: the DRAM itself uses the programmed WR value to time auto precharge after a WRA, and tDAL = WR + roundup(tRP/tCK) is the real "write to next activate" cost when auto precharge is used.

## Comparison against the read miss

| | Read miss (walkthrough 2) | Write to idle bank |
| --- | --- | --- |
| Commands before data | PRE, ACT, RD | ACT, WR |
| Dead time before data | tRP + tRCD | tRCD (hidden by WL buffering) |
| Tail cost | none (bank left open) | tWR before PRE |

**Source:** JESD79-4D sections 2.8, 4.19, 4.22, 4.23, 4.25, 4.25.5
