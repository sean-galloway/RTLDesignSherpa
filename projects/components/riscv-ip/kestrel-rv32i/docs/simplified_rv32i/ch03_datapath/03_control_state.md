# Control State

## Why there is no FSM

Classic processor control is a finite-state machine walking fetch,
decode, execute, memory, writeback. kestrel doesn't have those phases:
they are spatial, not temporal. Fetch is a wire off the PC register;
decode is a truth table; execute is an ALU; memory access is a
combinational port; writeback is a mux feeding a clocked register file.
There is nothing to sequence, so there is no FSM — and no microcode, no
control ROM, no phase counter.

The two places where a naive design would reach for an FSM — halting
and the misaligned retry — are handled by single holding flops with
plain set/clear conditions.

## The halt holding register

`halt_q` is a one-bit flop that latches any nonzero `halt_cause_eff`:

```
halt_q <= halt_q | halt_now;
```

`halt_now` is the combinational OR of decode's causes (ecall, ebreak,
illegal) and the core's own misaligned-target condition. The external
`halt` output is `halt_q | halt_now` so the first halting cycle is
visible immediately. Once latched:

- The PC freezes (`pc <= halt ? pc : ...`).
- Writeback is suppressed (`rd_wen_eff`, `rd_wb` both gate on `halt`).
- Retirement stops: `rvfi_valid = rst_n & ~halt_q & ~ls_first`, and
  since `halt_q` latches on the halting cycle, the halting instruction
  itself is the last beat — a trap beat with `rvfi_trap = halt_now`.
- The testbench watches halt-hold: after the trap beat, four more
  cycles of `halt` raised, `rvfi_valid` low, `rvfi_pc_rdata` frozen
  (Chapter 6).

A holding register rather than a pulse matters for verification: an
external observer sampling any time after the halt sees a stable,
unambiguous stopped state with the cause still on the port.

## The retry bit and the merge register

A cross-word load/store needs two memory beats but retires one
instruction, so something must remember which beat is which. That
something is `ls_retry`, set exactly when the first beat of a crossing
access is in flight (`ls_retry <= ls_first`) and clear otherwise — one
flop, no states beyond it, explicitly control state. On the retry
cycle the datapath shifts to the next word (`dmem_addr = word + 1`), the
strobes become the head-byte mask, and the load path merges the captured
first-word tail (`ls_rdata_lo`, captured when `ls_first`) with the
second word's head into the assembled value. The PC holds during the
first beat (`pc <= ls_first ? pc : next_pc`), so the instruction simply
takes one more cycle and retires once, on the final beat.

`ls_rdata_lo` is the fifth flop in the inventory — a pipeline register
in the most minimal sense, and the only place in kestrel where data is
captured mid-instruction. Chapter 5 gives the byte-level detail.

## The retirement counter

`retire_count` increments whenever `rvfi_valid` is high and backs
`rvfi_order`, so retired instructions are numbered 0, 1, 2, ... in
program order forever. It is 64 bits wide — a 32-bit core will not wrap
it — and it exists for exactly one consumer: riscv-formal's
consistency checks, which use the order field to relate beats across
cycles.

## What this buys

Five flops with one-line next-state equations are reviewable in minutes
and provable in bounded model checking with shallow depths (Chapter 6's
formal checks run at depth 6 and cover reset plus a two-cycle memory
access with headroom). The discipline the suite's style brief imposes —
datapath logic is truth tables and muxes; FSMs only where control is
unavoidable — shows up here as the reason kestrel's control can be
exhaustively checked rather than merely simulated.

**Source:** `rtl/kestrel_core.sv` (halt register, PC register, retry
bit, merge register, retirement counter); falcon-suite RTL style brief
