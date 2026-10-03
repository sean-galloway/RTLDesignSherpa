# Walkthrough 1: AXI4 Read, Row Hit

## Controller configuration used in all Chapter 4 walkthroughs

Drill model geometry (B0-B7, R0-R7, C0-C7), BL4, posted CAS enabled:

| Parameter | Value (clocks) |
| --- | --- |
| CL / AL / RL / WL | 3 / 2 / 5 / 4 |
| tRCD / tRP / tRAS / tRC | 3 / 3 / 6 / 9 |
| tRRD / tFAW / tCCD | 2 / 10 / 2 |
| tWTR / tWR / tRTP | 3 / 6 / 3 |

The AXI4 data bus is assumed as wide as one DRAM burst, so one AXI4 beat
maps to one DRAM burst word: an AXI4 burst of 4 beats is exactly one BL4
DRAM burst. Real controllers slice and dice; the drill model does not.

## Scenario

Initial bank state: B3 has row R5 open. All other banks idle.

AXI4 master issues: ARADDR mapping to bank B3, row R5, column C2,
ARLEN=3 (4 beats), ARSIZE matching full bus width.

## Command trace

```
RD  B3 C2        # row R5 already open in B3 - no ACT needed, go straight to CAS
```

One command. That is the whole point of a row hit.

Timeline:

```
clk:      0        1    2    3    4    5    6    7
CMD:      RD
DQS:                        pre  ----DQS toggling----
DQ:                              D0   D1   D2   D3
```

Data appears RL = AL + CL = 5 clocks after the RD command (AL=2 was
programmed, but with no ACT in front there is nothing to post against; the
DRAM still applies RL from the RD command itself).

## What happens on the AXI side

- AR handshake completes; the controller's address mapper splits the
  address into {B3, R5, C2}.
- The bank machine for B3 reports R5 open -> issue RD immediately,
  skipping ACT entirely.
- At RL the DRAM drives DQS/DQ; the PHY returns 4 data words; the
  controller streams them out as 4 AXI R beats with RLAST on the final
  word.

## Scheduling takeaways

- Row-hit reads are the cheapest DRAM transaction: 1 command, latency RL.
- The bank stays open afterwards (A10=0). A follow-up access to R5 is
  another hit; an access to a different row of B3 now costs a PRE + ACT
  (see Walkthrough 2).
- A controller doing FR-FCFS scheduling reorders the queue exactly to
  manufacture this case.

**Source:** JESD79-2F sections 3.5, 3.6.1, 3.6.3
