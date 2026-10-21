# Misaligned Data Accesses

## What the spec permits

RV32I does not require misaligned load/store support, but it explicitly
permits it: an execution environment may handle misaligned accesses in
hardware, invisibly trap and emulate them, or trap and refuse, and it
may treat accesses to side-effecting regions differently (spec Volume I,
section 2.1.6). Naturally aligned accesses are guaranteed atomic;
misaligned accesses are explicitly *not* required to be atomic. The
design space is open, and kestrel takes the plainest corner of it:
**a misaligned load or store halts the core.** Trap-and-refuse is the
spec's own option; kestrel has no trap machinery, so, like every other
trap, it halts (cause 4 for a load, 5 for a store).

This is a *data* policy. Instruction-side misalignment is never handled
in hardware by anything, and section 3 of this chapter covers that halt.

## The rotation model

Naturally aligned sub-word accesses are implemented by byte-lane
rotation. For an access at byte offset `o` with size bytes `s`:

- **Offset:** `o = rs1[1:0] + imm[1:0]`, the address's low bits from their
  own two-bit add, so the rotation and the halt test do not wait for the
  32-bit address.
- **Store:** `dmem_wdata = rs2_data << (8*o)` — the value slides into
  the addressed lanes; `dmem_wstrb = size_mask << o` — the byte enables
  slide with it. The memory merges enabled bytes into the word.
- **Load:** `rdata_shifted = dmem_rdata >> (8*o)` — the addressed bytes
  slide down to bit 0, and a final case implements LB (sign-extend from
  bit 7), LBU/LHU (zero-extend), LH, LW.

Bytes are always aligned. Halves are aligned at offsets 0 and 2, words at
0. Every aligned access fits inside one word, so the rotation is the
entire mechanism and the access completes in the single cycle.

## The misaligned halt

A half at an odd offset, or a word at any nonzero offset, raises
`ls_misalign`. The access performs nothing: the store strobes are forced
to zero, the load does not write rd, and the instruction retires as the
usual RVFI trap beat with empty memory fields, then the core holds
(section 3). rv32ui-p-ma_data, which needs hardware support, halts on its
first misaligned load; spike, which traps misaligned accesses too, takes
`trap_load_address_misaligned` at the same instruction, so the lockstep
still lines up (Chapter 6).

## Why not hardware?

Until 2026-10-20 kestrel did complete misaligned accesses in hardware:
in-word ones by rotation, cross-word ones in two beats, with a retry flop,
a 32-bit merge register for the first word's bytes, and the PC held for
the extra cycle. On block RAM that logic sat on the critical path — it
gated the register write and the PC hold, between the address add and the
register file — and it was most of kestrel's control state. Dropping it
leaves a rotation and one compare, which is the smaller and simpler design
a rung-1 core should be. A program that needs misaligned access can split
it into aligned byte or half accesses, as compilers already do.

**Source:** RISC-V Instruction Set Manual, Volume I, section 2.1.6;
`rtl/top/kestrel_core.sv` (L/S rotation and the misaligned halt);
`dv/tests/programs/ls_misaligned.s`, `ls_misalign_store.s`, `ls_chain.s`
