# What kestrel Costs

## CPI 1, honestly stated

kestrel retires one instruction per clock — CPI 1 — for every instruction
in the ISA. Two honesty clauses attach to that claim. First, a
cross-word misaligned load or store occupies two clocks and retires
once, so memory-heavy code with unaligned data averages slightly above 1
(Chapter 5); the battery's ma_data and ld_st rows exercise exactly that
case. Second, CPI 1 is *per instruction*, and instructions are not the
unit anyone asked for — programs are. The single-cycle discipline taxes
the fast instructions to pay for the slow ones, and the tax collector is
the clock period.

## The critical path is the whole machine

In a single-cycle design, the clock period must span the slowest
instruction's path through *every* block, because every block sits
between the same two edges. Trace kestrel's worst case, an ALU
instruction, and count what the clock must cover:

1. The PC register updates and presents `imem_addr`.
2. The instruction memory reads combinationally; the instruction word
   settles.
3. Decode (`{opcode, funct3, funct7}` case) and the immediate generator
   settle in parallel with the register file's combinational reads.
4. The source muxes feed the ALU; the ALU result settles. (For a load,
   the address then crosses the data memory, and the read data rotates
   and sign-extends into the writeback mux.)
5. The next-PC mux selects; for branches, the dedicated comparator's
   decision must also settle to drive that selection.
6. The writeback data reaches the register file's data input and the PC
   data reaches the PC register, both meeting setup before the edge.

Every one of those stages — two memories, a truth table, a register
file, an ALU, three muxes, a comparator — is on the critical path for
*some* instruction, so the clock is limited by their *sum*, not their
slowest member. The ADD that could have run at the ALU's speed is
clocked at the LW's speed, and both are clocked below what a leaner
machine could do. Patterson and Séquin's RISC I made this trade
deliberately in 1981: one instruction, one cycle, clock be damned,
because a machine whose every instruction completes in one cycle is a
machine you can reason about completely (papers, entry 1). Kestrel
inherits the reasoning and, this chapter argues, should not inherit the
clock.

## The accounting, instruction by instruction

| Instruction class | Path the clock must span |
| --- | --- |
| ALU (OP/OP-IMM) | imem + decode + regfile + ALU + writeback setup |
| Branch | imem + decode + regfile + comparator + next-PC mux + PC setup |
| Load | imem + decode + regfile + ALU + dmem + rotate/sign + writeback setup |
| Store | imem + decode + regfile + ALU + dmem + strobe setup |
| JAL/JALR | imem + decode + regfile (JALR) + add + next-PC mux + PC setup |
| Cross-word L/S | all of load/store, plus the retry cycle (two clocks, by design) |

: Critical-path content per instruction class

The table's lesson: there is no clock frequency at which this machine is
fast, only a frequency at which it is correct, and that frequency is set
by the longest row — almost always the load, which crosses both
memories and the datapath between them.

## What would have to give

The single-cycle tax has exactly one root cause: every stage serves
every instruction every cycle. Relax that and the frequency rises, but
the reasoning burden rises with it — which is the trade the ladder is
built to teach. The moment work is spread across multiple cycles, the
stages need boundaries (pipeline registers), the boundaries create
overlaps (hazards), and the hazards need policy (forwarding, stalls,
flushes). That is not a defect of the next design; it is the price of
the frequency, and merlin exists to teach how to pay it deliberately.

**Source:** `rtl/kestrel_core.sv` (datapath structure); Patterson and
Séquin, "RISC I" (ISCA 1981) and Hennessy et al., "MIPS: A
Microprocessor Architecture" (MICRO 1982) — papers entries 1 and 3;
Flynn, "Very High-Speed Computing Systems" (1966) for the
throughput-versus-clock framing (papers, entry 2)
