# Walkthrough 3: AXI4 Write to an Idle Bank

Same controller configuration (CL=3, AL=2, RL=5, WL=4, BL4; tRCD=3,
tRP=3, tWR=6).

## Scenario

Initial state: all banks idle. AXI4 write arrives: AWADDR maps to bank B1,
row R4, column C0, AWLEN=3, followed by 4 W-channel beats.

An idle bank needs no precharge - miss-to-idle is cheaper than
miss-to-open-row by tRP.

## Command trace

```
ACT B1 R4        # open the row; bank was idle so no PRE needed
WR  B1 C0        # posted CAS, 1 clk after ACT; internal CAS at ACT+3 = tRCD
--- (WL = 4) --- # write latency: first DQS edge lands 4 clks after the WR command
--- (tWR = 6) ---# write recovery: last data must soak into the array before PRE
PRE B1           # close the row (only if the controller wants the bank back)
```

Timeline:

```
clk:      0     1     2    3    4    5    6    7    8    9   ...  13
CMD:      ACT   WR
                          |<---- WL=4 ---->|
DQS:                                 pre -DQS toggling-
DQ:                                   D0   D1   D2   D3
                                                        |<- tWR=6 ->|
PRE legal at clk 4 + 4(WL) + 2(BL/2) + 6(tWR) = clk 16 from ACT,
i.e. WL + BL/2 + tWR = 12 clocks after the WR command.
```

## AXI side

- AW and W are independent channels; the controller buffers the 4 W beats
  (or streams them) while the DRAM side runs ACT + posted WR.
- BREADY goes back to the master once the controller has accepted
  responsibility for the data - typically after the write is safely in
  flight to the DRAM, not after tWR completes.
- Write data is strobed in with DQS driven by the controller/PHY; tDQSS
  alignment to CK is the PHY's job.

## Write recovery is the trap

tWR is not a turnaround nicety; it is array physics. Precharging B1 before
tWR expires destroys the data just written - the bits never finish
committing from the sense amps to the cells. This is why WR is a
mode-register field: the DRAM itself uses the programmed WR value to time
auto precharge after a WRA, and tDAL = WR + tRP is the real "write to next
activate" cost when auto precharge is used.

## Comparison against the read miss

| | Read miss (walkthrough 2) | Write to idle bank |
| --- | --- | --- |
| Commands before data | PRE, ACT, RD | ACT, WR |
| Dead time before data | tRP + tRCD | tRCD (hidden by WL buffering) |
| Tail cost | none (bank left open) | tWR before PRE |

**Source:** JESD79-2F sections 3.5, 3.6.1, 3.6.4, 3.7.2, 3.8.2
