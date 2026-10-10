# Walkthrough: AXI Read, Wrong Row Open

Configuration used in all Chapter 4 traces (the drill model): RL = 10, WL = 6,
BL = 16, flat 8-bank device, single channel view (channel A).

## Scenario

An AXI4 read request maps to bank B3, row R6, column C0 - but row R5 is
currently open in B3. This is a row conflict (miss): the wrong row must be
closed before the requested row can be opened.

## Command trace

```
PREpb B3         ; close the wrong row (tRAS from its ACT already met)
--- (tRPpb) ---  ; single-bank precharge time: bank unavailable
ACT B3 R6        ; open the requested row
--- (tRCD) ---   ; row-to-column delay
RD  B3 C0        ; burst read, AP=0, row stays open
NOP
NOP
NOP
NOP
NOP
NOP
NOP
```

## Why each command

- `PREpb B3` - a bank holds exactly one open row. AB=0, so only B3 is
  precharged; every other bank is untouched. This is the per-bank precharge
  path, which uses the shorter tRPpb recovery.
- `--- (tRPpb) ---` - single-bank precharge time. A PREpb to one bank uses
  tRPpb; a PREab would cost tRPab and close banks that might still be doing
  useful work.
- `ACT B3 R6` - opens the requested row. The ACT-to-ACT spacing to B3 (prior
  ACT -> PREpb -> this ACT) satisfies tRC = tRAS + tRPpb by construction if
  tRAS was met before the PREpb.
- `--- (tRCD) ---` - row-to-column delay; the column circuitry cannot be
  driven until the row's data is in the sense amps.
- `RD B3 C0` - the read itself, identical to the hit case once the row is
  open. The BL16 burst wraps the C0-C7 drill columns twice.

## AXI view

Same single AR request as the hit walkthrough - but the latency the master
sees is now tRPpb + tRCD longer. Nothing on the AXI side changes; the penalty
is entirely in DRAM scheduling.

## What to notice

- Miss cost = tRPpb + tRCD before the first data can even start its RL
  journey.
- If the previous access to B3 had used AP=1, the bank would already be idle
  and only tRCD would be owed - that is the close-page trade in one line.
- PREpb may not be issued earlier than tRAS after the ACT that opened R5, nor
  earlier than tRTP after a read from R5. A scheduler that wants the earliest
  PREpb starts the tRAS/tRTP counters at the ACT/RD, not at the miss.

**Source:** JESD209-4E sections 4.1, 4.6, 4.17, 4.17.1 (derived walkthrough)
