<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---


# Programmer's Model

## Contexts

Each context is a complete RV32I hart: a PC, registers x0-x31 and its own program/data memory. A program cannot see the other contexts' registers or memory, and cannot tell which context it runs on (context visibility is implicit, PRD 7). All four start at the same RESET_ADDR.

## ISA

RV32I exactly as kestrel implements it (PRD 3): every base instruction; FENCE and FENCE.I retire as no-ops; MRET falls through to the next instruction; the SYSTEM CSR instructions read zero and discard writes (there is no CSR state). Self-modifying code works without FENCE.I: a store is visible to the context's next fetch.

## Halts

There are no traps. These stop the context that raises them, and only that context (context-lock, PRD 7):

| Cause | Event |
|---|---|
| 1 | ECALL |
| 2 | EBREAK |
| 3 | Taken branch, JAL or JALR to an address that is not 4-byte aligned |
| 4 | Misaligned load (LH/LHU off a half-word, LW off a word) |
| 5 | Misaligned store |
| 0xF | Illegal instruction (including the custom-0 opcode until Xcell is built) |

: Table 2.1: Halt causes (kestrel's encoding)

The halting instruction does not write a register or memory. The riscv-tests verdict on a context is its last write to gp (x3) at the ECALL halt: 1 is a pass.

## Timing a program can rely on

None, by design: a context's speed depends on nothing it does. Every instruction -- ALU, load, store, taken or not-taken branch -- takes exactly four clocks of its context, whatever the other contexts are doing.
