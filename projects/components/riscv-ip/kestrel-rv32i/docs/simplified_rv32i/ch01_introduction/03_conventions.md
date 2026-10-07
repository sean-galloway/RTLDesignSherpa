# Conventions

## Numbers and identifiers

- Hexadecimal values are written with a `0x` prefix or SystemVerilog
  style (`32'hFFFF_FFFE`); binary encodings use SystemVerilog sized
  literals (`7'b0110011`).
- RTL signal and parameter names appear in code font exactly as in the
  sources (`dmem_wstrb`, `RESET_ADDR`), so every claim can be grepped.
- Instruction names (ADD, JALR) are uppercase; assembly mnemonics in
  prose are lowercase (`add x3, x1, x2`).

## Register names

RV32I defines thirty-two 32-bit registers, x0 through x31 (spec
Volume I, section 2.1.1). This book uses the ABI names where they aid
recognition — x1 is `ra` (return address), x2 is `sp`, x3 is `gp`, x10
and x11 are `a0`/`a1` — and the bare numbers elsewhere. One register is
special: x0 always reads as zero, and writes to it are discarded. kestrel
enforces both properties in the register file itself.

## Halt versus trap

This book uses the two words the way the core uses its ports:

- A **trap**, per the spec (Volume I, section 1.6), is a control transfer
  to a handler. kestrel has no trap machinery and never traps.
- A **halt** is kestrel's stop condition: the core freezes the PC,
  suppresses writeback, and raises a cause code on `halt`/`halt_cause`.
  ECALL, EBREAK, illegal instructions, and misaligned control-flow
  targets all halt. On RVFI the halting instruction still retires — as a
  beat with `rvfi_trap` set — so observers see the architecturally final
  state.

When the spec mandates a trap and kestrel substitutes a halt, the text
says so explicitly, because that substitution is a documented design
decision with a verification consequence (Chapter 6).

## RVFI

RVFI (RISC-V Formal Interface) is the retire-port convention from the
riscv-formal project: one record per retired instruction carrying PC,
instruction word, register read/write, and memory access details.
kestrel's RVFI aggregation rules are given in Chapter 3; the field-level
semantics follow riscv-formal's `rvfi.md`.

## Citations

The specification is cited by chapter and section
(`Volume I, section 2.1.6`), never by page — the pinned PDF is a rolling
intermediate release whose pagination can drift. Research literature is
cited by entry in `references/microarchitecture-papers.md`, the suite's
reading list, in the form (papers, entry N).

**Source:** RISC-V Instruction Set Manual, Volume I, sections 1.6 and
2.1.1; vendor/riscv-formal/docs/rvfi.md
