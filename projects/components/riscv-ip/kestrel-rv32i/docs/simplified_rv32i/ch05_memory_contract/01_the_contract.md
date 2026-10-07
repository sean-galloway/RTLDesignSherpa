# The Memory Contract

## The interface

kestrel talks to memory through two ports that are deliberately
minimal. There is no bus fabric, no wait states, no byte enables on the
instruction side, and no burst machinery — at this rung the memory
system is expected to keep up with the core, and the contract says so
out loud.

| Port | Direction | Width | Contract |
| --- | --- | --- | --- |
| `imem_addr` | out | 32 | Instruction fetch address, driven by the PC |
| `imem_rdata` | in | 32 | Combinational read data: the word at `imem_addr`, valid in the same cycle |
| `dmem_req` | out | 1 | A load or store is accessing data memory this cycle |
| `dmem_we` | out | 1 | The access is a store |
| `dmem_addr` | out | 32 | Word-aligned byte address (`{alu_y[31:2], 2'b00}`) |
| `dmem_wstrb` | out | 4 | Per-byte write enables, rotated into position for stores |
| `dmem_wdata` | out | 32 | Store data, rotated into position |
| `dmem_rdata` | in | 32 | Combinational read data for loads |

: The kestrel memory interface

Three properties define the contract:

1. **Harvard at the core.** Instruction fetch and data access are
   separate ports backed by whatever the integrator provides. The core
   never issues a data access to the instruction memory or vice versa,
   and it never sees coherence between them.
2. **Combinational reads.** Both memories answer in the same cycle the
   address is presented. This is the load-bearing simplification of the
   single-cycle design: an instruction's full path — fetch, decode,
   register read, ALU, data read, writeback — must fit in one clock, so
   the memories are forbidden from adding latency. Synchronous-read
   RAM macros (e.g. block RAM) would break the contract; the suite's
   style brief calls for distributed-RAM inference when a real macro is
   needed.
3. **Word-wide buses with byte strobes.** Data memory is 32 bits wide;
   sub-word stores rotate the data and strobe into the addressed byte
   lanes, and sub-word loads rotate read data back before size/sign
   selection. The testbench memory honors `dmem_wstrb` per byte, which
   is the contract that pins the rotation convention (Chapter 6).

## Timing: one cycle, except when documented

An instruction that touches memory completes in exactly one clock when
its access lies within one word; a cross-word access takes two clocks
via the documented retry (next section of this chapter). There are no
other exceptions: no wait states, no arbitration stalls, no refresh
interference. The PC holds only for the retry's first beat and for
halts. Everything else advances every cycle.

`RESET_ADDR` (default `32'h0000_0000`, a module parameter) selects the
fetch address out of reset; the testbench also parameterizes it to prove
the core starts anywhere.

## What the contract deliberately excludes

- **No instruction-side data access.** Self-modifying code is invisible
  to the core unless the *memory system* unifies the ports. The kestrel
  testbench does exactly that — one array serving both fetch and
  load/store — as a testbench choice so rv32ui-p-fence_i runs without a
  coherence path. That unification is documented here so no integrator
  mistakes it for a core feature.
- **No misaligned instruction fetch.** IALIGN=32: fetch addresses are
  always 4-byte aligned, and the low PC bits are guaranteed by the
  next-PC logic plus the halt of section 3 of this chapter.
- **No memory protection, ordering, or atomicity.** RVWMO (spec Volume
  I, chapter 3) is satisfied vacuously by a core that issues at most one
  access at a time and never reorders; there is nothing to model.

**Source:** `rtl/kestrel_core.sv` (port list, L/S datapath);
`dv/tb/kestrel_tb_top.sv` (unified testbench memory, wstrb-honoring
store port); falcon-suite RTL style brief
