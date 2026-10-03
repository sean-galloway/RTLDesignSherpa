# Walkthrough: AXI Read, Wrong Row Open

## Scenario

An AXI4 read request maps to bank B3, row R6, column C0 - but row R5 is
currently open in B3. This is a row conflict (miss): the open row must
be closed before the new one can be opened.

## Command trace

```
PRE B3           ; close the wrong row (tRAS since its ACT already met)
--- (tRPpb) ---  ; precharge time: bank unavailable
ACT B3 R6        ; open the requested row
--- (tRCD) ---   ; row-to-column delay
RD  B3 C0        ; burst read, AP=0, row stays open
NOP
NOP
```

## Why each command

- `PRE B3` - a bank holds exactly one open row. AB=0 (CA4r), so only B3
  is precharged; every other bank is untouched.
- `--- (tRPpb) ---` - single-bank precharge time (typ 18 ns). A PRE to
  one bank used tRPpb; a PRE-all would have cost tRPab (3 ns more on
  8-bank parts) and closed banks that were doing useful work.
- `ACT B3 R6` - opens the requested row. The ACT-to-ACT spacing to B3
  (prior ACT -> PRE -> this ACT) satisfies tRC = tRAS + tRPpb by
  construction if tRAS was met before the PRE.
- `--- (tRCD) ---` - row-to-column delay (typ 18 ns); the column
  circuitry cannot be driven until the row's data is in the sense amps.
- `RD B3 C0` - the read itself, identical to the hit case.

## AXI view

Same single 16-byte AR request as the hit walkthrough - but the latency
the master sees is now tRPpb + tRCD longer. Nothing on the AXI side
changes; the penalty is entirely in DRAM scheduling.

## What to notice

- Miss cost = tRPpb + tRCD (typ 36 ns at typical bin) before the first
  data can even start its RL journey.
- If the access had been issued with AP=1 on the PREVIOUS access to B3,
  the bank would already be idle and only tRCD would be owed - that is
  the close-page trade in one line.
- PRE may not be issued earlier than tRAS after the ACT that opened R5,
  nor earlier than tRTP after a read from R5. A scheduler that wants the
  earliest PRE starts the tRAS/tRTP clocks at the ACT/RD, not at the
  miss.

**Source:** JESD209-2F sections 5.1, 5.9 (derived walkthrough)
