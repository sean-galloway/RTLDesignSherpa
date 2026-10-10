# Walkthrough 1: AXI4 Read, Row Hit

## Controller configuration used in all Chapter 4 walkthroughs

Drill model geometry (B0-B7, R0-R7, C0-C7), BL8, additive latency off (AL=0; AL is a programmable field in MR1, but this drill keeps it disabled). Two bank groups are used: BG0 = {B0,B1,B2,B3}, BG1 = {B4,B5,B6,B7}.

| Parameter | Value (clocks) |
| --- | --- |
| CL / CWL / AL / RL / WL | 10 / 10 / 0 / 10 / 10 |
| tRCD / tRP / tRAS / tRC | 5 / 5 / 15 / 20 |
| tRRD_S / tRRD_L / tFAW | 2 / 3 / 12 |
| tCCD_S / tCCD_L | 4 / 6 |
| tWTR_S / tWTR_L | 2 / 4 |
| tWR / tRTP | 12 / 6 |

The AXI4 data bus is assumed as wide as one DRAM burst, so one AXI4 beat maps to one DRAM burst word: an AXI4 burst of 8 beats is exactly one BL8 DRAM burst. Real controllers slice and dice; the drill model does not. Burst chop (BC4) versus BL8 can be chosen on-the-fly via A12 when MR0 allows it; these walkthroughs keep A12 high for BL8.

## Scenario

Initial bank state: B3 has row R5 open. All other banks idle.

AXI4 master issues: ARADDR mapping to bank B3, row R5, column C2, ARLEN=7 (8 beats), ARSIZE matching full bus width.

## Command trace

```
RD  B3 C2 (BG0)  # row R5 already open in B3 - no ACT needed, go straight to CAS
```

One command. That is the whole point of a row hit.

Timeline:

```
clk:      0        1    2    3    4    5    6    7    8    9   10   11   12   13   14   15   16
CMD:      RD
DQS:                        pre  ----DQS toggling----
DQ:                              D0   D1   D2   D3   D4   D5   D6   D7
```

Data appears RL = AL + CL = 10 clocks after the RD command. AL is programmed to zero in this drill, so the CAS is executed immediately; there is nothing to post against. DDR4 computes write latency as AL + CWL, not the RL-1 shortcut used in DDR2.

## What happens on the AXI side

- AR handshake completes; the controller's address mapper splits the address into {BG0, B3, R5, C2}.
- The bank machine for B3 reports R5 open -> issue RD immediately, skipping ACT entirely.
- At RL the DRAM drives DQS/DQ; the PHY returns 8 data words; the controller streams them out as 8 AXI R beats with RLAST on the final word.

## Scheduling takeaways

- Row-hit reads are the cheapest DRAM transaction: 1 command, latency RL.
- The bank stays open afterwards (A10=0). A follow-up access to R5 is another hit; an access to a different row of B3 now costs a PRE + ACT (see Walkthrough 2).
- A controller doing FR-FCFS scheduling reorders the queue exactly to manufacture this case.

**Source:** JESD79-4D sections 2.8, 4.19, 4.22, 4.23, 4.24
