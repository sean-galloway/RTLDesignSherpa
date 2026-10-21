# Control State

## Why there is no FSM

Classic processor control is a finite-state machine walking fetch,
decode, execute, memory, writeback. kestrel doesn't have those phases:
they are spatial, not temporal. Fetch is a wire off the PC register;
decode is a truth table; execute is an ALU; memory access is a
combinational port; writeback is a mux feeding a clocked register file.
There is nothing to sequence, so there is no FSM — and no microcode, no
control ROM, no phase counter.

The one place where a naive design would reach for an FSM — halting — is
handled by a single holding flop with a plain set condition.

## The halt holding register

`halt_q` is a one-bit flop that latches any nonzero `halt_cause_eff`:

```
halt_q <= halt_q | halt_now;
```

`halt_now` is the combinational OR of decode's causes (ecall, ebreak,
illegal) and the core's own misaligned-target and misaligned-access
conditions, masked while the memory holds the core (`mem_wait`). The external
`halt` output is `halt_q | halt_now` so the first halting cycle is
visible immediately. Once latched:

- The PC freezes (`pc <= (halt || mem_wait) ? pc : next_pc`).
- Writeback is suppressed (`rd_wen_eff`, `rd_wb` both gate on `halt`).
- Retirement stops: `rvfi_valid = rst_n & ~halt_q & ~mem_wait`, and
  since `halt_q` latches on the halting cycle, the halting instruction
  itself is the last beat — a trap beat with `rvfi_trap = halt_now`.
- The testbench watches halt-hold: after the trap beat, four more
  cycles of `halt` raised, `rvfi_valid` low, `rvfi_pc_rdata` frozen
  (Chapter 6).

A holding register rather than a pulse matters for verification: an
external observer sampling any time after the halt sees a stable,
unambiguous stopped state with the cause still on the port.

## No retry bit, no merge register

Until 2026-10-20 kestrel completed misaligned loads and stores in hardware:
a cross-word access took two memory beats, remembered by a retry flop
(`ls_retry`) and a 32-bit merge register (`ls_rdata_lo`) holding the first
word's bytes. On block RAM that retry logic sat on the critical path, so
it was removed: a misaligned access now halts (Chapter 5), and those two
flops left the inventory. No data is captured mid-instruction anywhere in
kestrel.

## The retirement counter

`retire_count` increments whenever `rvfi_valid` is high and backs
`rvfi_order`, so retired instructions are numbered 0, 1, 2, ... in
program order forever. It is 64 bits wide — a 32-bit core will not wrap
it — and it exists for exactly one consumer: riscv-formal's
consistency checks, which use the order field to relate beats across
cycles.

## What this buys

Three flops with one-line next-state equations are reviewable in minutes
and provable in bounded model checking with shallow depths (Chapter 6's
formal checks run at depth 6 and cover reset plus memory wait states with
headroom). The discipline the suite's style brief imposes —
datapath logic is truth tables and muxes; FSMs only where control is
unavoidable — shows up here as the reason kestrel's control can be
exhaustively checked rather than merely simulated.

**Source:** `rtl/top/kestrel_core.sv` (halt register, PC register,
retirement counter); falcon-suite RTL style brief
