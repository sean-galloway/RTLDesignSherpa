# Introduction

## What this book is

This book is the condensed study-notes edition of RV32I as implemented by
kestrel, the single-cycle core at rung 1 of the falcon suite. It is not a
replacement for the RISC-V specification — the specification
(`references/riscv-spec.pdf`, Volume I: Unprivileged Architecture) is the
authority, and this book cites it by chapter and section throughout. What
this book adds is the mapping from spec prose to silicon: which decode
rows kestrel actually implements, what its memory contract pins down, how
its retire interface reports execution, and how it was verified hard
enough to trust.

Everything here describes the as-built core in
`rtl/kestrel_pkg.sv`, `rtl/kestrel_regfile.sv`, `rtl/kestrel_alu.sv`,
`rtl/kestrel_imm_gen.sv`, `rtl/kestrel_decode.sv`, and
`rtl/kestrel_core.sv`. Where a design decision was made that the spec
leaves open — and RV32I leaves several doors open — the decision is stated
plainly and labeled as a decision, with the spec's own permission cited.

## What kestrel is

kestrel is a single-cycle RV32I core:

- One instruction retires per clock; the entire datapath completes in one
  cycle, with exactly one documented exception (a cross-word misaligned
  load or store takes a second cycle; see Chapter 5).
- Control is a combinational decode truth table, not a finite-state
  machine. There is no time dimension to control yet.
- The complete architectural state is the PC register, the 32-entry
  register file, and a handful of bookkeeping flops — five in total.
- There is no trap machinery. ECALL, EBREAK, illegal instructions, and
  misaligned control-flow targets halt the core with a cause code on a
  dedicated port, and the halting instruction retires as an RVFI trap
  beat (see Chapters 3 and 5).
- Retirement is observed through a first-class RISC-V Formal Interface
  (RVFI) port bundle, so an external checker can diff the core against a
  golden model instruction by instruction.

The name follows the suite's convention: falcon species in strict size
order, one per rung. The kestrel is the smallest falcon — the hovering
falcon — and kestrel the core is the smallest machine in the suite: the
whole of it is visible in one cycle.

## Why single-cycle comes first

A single-cycle core is the honest starting point for the ladder because
it removes every confound. When one instruction occupies the entire
clock, there are no pipeline registers to reason about, no hazards, no
forwarding priority, no speculation, no precise-exception problem. The
register file either read the right operands or it didn't; the ALU either
computed the right value or it didn't; the truth table either decoded the
right controls or it didn't. Every verification failure points at exactly
one combinational block.

That transparency is bought with a cost, and the cost is the subject of
Chapter 7: the clock period must cover the slowest instruction's path
through the whole machine, so the single-cycle discipline taxes every
other instruction. Rung 2 (merlin) exists precisely because of that tax.
But you cannot appreciate what a pipeline buys until you have traced one
full cycle by hand, and you cannot debug a pipeline's hazard logic until
you know what the correct answer was. kestrel is where the correct answer
lives.

## How to read this book

Chapters 2 through 5 are reference: the ISA, the datapath, the truth
table, the memory contract. Chapter 6 is the verification record — read
it even if you skip the RTL chapters, because it is also the story of
what each verification method can and cannot see. Chapter 7 is the
argument for the next rung.

RTL identifiers appear in code font exactly as they do in the sources
(`ls_retry`, `rd_wen_eff`, `HALT_IALIGN`), so statements in this book can
be checked against the code mechanically.

**Source:** RISC-V Instruction Set Manual, Volume I, chapters 1-2
(specification edition riscv-spec.pdf); falcon-suite design spec
`docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md`
