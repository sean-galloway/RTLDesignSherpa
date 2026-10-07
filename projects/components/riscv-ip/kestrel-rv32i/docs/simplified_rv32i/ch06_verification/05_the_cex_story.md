# The CEX Story: What Formal Caught That Forty-Two Tests Missed

This section is the verification chapter's lesson, and it deserves its
own space: the riscv-formal counterexamples found a real, architecturally
visible core bug that the entire directed battery, two lockstep methods,
and code review had all missed. The suite keeps this story on record
because it is the strongest argument for the ladder's verification
doctrine — simulation shows what you thought of; proof covers what you
didn't.

## The failure

The first full formal run returned **34/42 PASS, 8 FAIL** — the six
branch models plus `jal` and `jalr`, every one counterexampled the same
way at the same line: `rvfi_insn_check.sv:178`,
`assert(spec_trap == trap)`, at check step 6. The evidence chain, shown
for `insn_beq_ch0`, is identical for all eight:

1. sby: `failed assertion ... at rvfi_insn_check.sv:178.6 step 6`.
2. That line compares the model's expected trap against the core's
   reported `rvfi_trap`. The checker assumed a valid BEQ beat; the ISA
   model says it traps; the core reported no trap.
3. The VCD at the check step shows `spec_valid=1, spec_trap=1,
   rvfi_trap=0`, with retired instruction `0x980001E3` — a
   `beq x0, x0` (opcode `1100011`, funct3 `000`), taken by construction,
   whose B-immediate targets `0xFFFFF996`: an address with
   `next_pc[1:0] = 2`. (The sibling checks carry their own stimuli —
   `insn_bne_ch0`'s trace, for instance, retires `0x80121163`, a taken
   `bne` to another misaligned target.)
4. The model source (`vendor/riscv-formal/insns/insn_beq.v`) computes
   `spec_trap = (next_pc[1:0] != 0) || !misa_ok` for IALIGN=32: any
   taken control transfer to a non-4-aligned target must trap. The JAL
   and JALR models carry the identical condition.
5. rvfi.md is unambiguous: "`rvfi_trap` must also be set for ... a jump
   instruction that jumps to a misaligned instruction."
6. The spec (Volume I, section 2.1.5) names the event:
   instruction-address-misaligned.

kestrel at the time silently jumped: `pc <= pc + imm` (or the JALR
target masked to `~1`) with `rvfi_trap = 0`, then fetched and executed
at the misaligned address. A taken branch to address 0x2 executed
garbage as if nothing were wrong.

## Why the battery missed it

Forty-two directed tests, a golden interpreter, and a second emulator
all passed — because not one of them ever targeted a misaligned
instruction address. The rv32ui programs are linked code; every branch
and jump target is assembler-controlled and 4-byte aligned by
construction. The bug lived exactly where directed tests cannot reach:
in the space of operands and targets no test author writes. Formal
verification's contribution is not diligence but *coverage of the
absurd*: the model checker gleefully retires BEQ with every immediate,
including the ones that land on `next_pc[1:0] != 00`, and it found the
hole on depth 6 of an unconstrained search.

## The fix

The fix is small, follows the core's existing idiom, and is the
HALT_IALIGN material of Chapter 5: `halt_cause` encoding moves into
`kestrel_pkg` as the single source of truth with the new `HALT_IALIGN =
4'h3`; `kestrel_core` computes
`misalign_target = (jump | jalr | branch_taken) & (next_pc[1:0] != 2'b00)`
and OR-s it into the existing halt path — same holding register, same
trap beat, same PC freeze. The one delicate point is the link register:
decode keeps `rd_wen = 1` for JAL/JALR, so both the register write and
the RVFI report are gated by `halt` itself, not by decode's `rd_wen`.
The golden interpreter models the same halt (cause 3, `pc_wdata` equal
to the misaligned target), and a directed program — `system_misalign_jmp`
— pins it: an aligned JAL regression (link value `pc+4` retires
normally), then `jal x0, .+2` must halt with cause 3, trap beat
`pc_wdata = 0x12`, no register write.

## Aftermath

Re-run against the patched RTL: riscv-formal **42/42 PASS**, the rv32ui
battery **42/42 PASS** with spike lockstep intact (no rv32ui test
targets a misaligned PC, so the battery stayed green as predicted), and
every pre-existing regression — core, branch, load/store, decode suites
at gate and func — green. The task's mandated commit message reported
the intermediate 34/42 honestly rather than claiming green; the fix
round is the commit that earns the claim.

## The lesson, stated once

Each method in this chapter sees a different slice of behavior. The
golden interpreter sees the same conventions the RTL was written with.
Spike sees the same programs, independently implemented. The battery
sees real compiled code. riscv-formal sees everything the ISA permits up
to a depth — and at this core's scale (depth 6, minutes per check) that
"everything" is cheap enough to run on every RTL change. The ladder's
doctrine follows directly: directed tests for the common case, lockstep
for independence, and formal proofs as the gate that keeps honest
optimizations honest.

**Source:** task-9 report (counterexample chain, proposed fix) and fix
round 1 (fix, directed test, re-run evidence); `rtl/includes/kestrel_pkg.sv`,
`rtl/top/kestrel_core.sv`; `dv/tests/programs/system_misalign_jmp.s`
