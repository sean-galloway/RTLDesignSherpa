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

<!-- End Header -->

# Memory Contract

## The Contract

kestrel talks to memory through two ports that are deliberately minimal. There is no bus fabric, no wait states, no byte enables on the instruction side, and no burst machinery. At this rung the memory system is expected to keep up with the core, and the contract says so out loud. An integrator replacing the memories must preserve all three properties below, or use the one sanctioned exception: holding the core with `mem_wait` (property 2).

1. **Harvard at the core.** Fetch and data access are separate ports backed by whatever the integrator provides. The core never issues a data access to the instruction memory or vice versa, and it never sees coherence between them.
2. **Combinational reads, or an explicit wait.** Both memories answer in the same cycle the address is presented. This is the load-bearing simplification: an instruction's full path — fetch, decode, register read, ALU, data read, writeback — must fit in one clock. `kestrel_mem_loader` honors it with `(* ram_style = "distributed" *)` arrays. A memory with registered reads (block RAM) may instead raise `mem_wait` until its data is valid (owner, 2026-10-20): the core holds every piece of state while `mem_wait` is high, so the ISA is unchanged and only the cycle count grows. `kestrel_mem_bram` is that memory system: it fetches one clock early at the core's `imem_addr_next` (the PC after the coming edge), so an instruction still takes one clock, and it holds the core for one cycle per load (CPI 2 for a load). riscv-formal proves the core under arbitrary wait patterns (formal/kestrel/riscv-formal drives `mem_wait` freely, at most two waits in a row).
3. **Word-wide buses with byte strobes.** Data memory is 32 bits wide. Sub-word stores rotate data and strobe into the addressed byte lanes; sub-word loads rotate read data back before size/sign selection. The memory must merge `dmem_wstrb` per byte (write only the strobed bytes of `dmem_wdata`).

## Timing Rules

- An instruction that touches memory completes in exactly one clock. Accesses are naturally aligned; a misaligned load or store halts (cause 4 or 5) and performs nothing (below). Each `mem_wait` cycle adds one clock and changes nothing else.
- The PC holds only for halts and while `mem_wait` is high. `imem_addr_next` always equals the PC the core will hold after the coming edge (`RESET_ADDR` in reset), so a registered-read instruction memory addressed by it presents the word at `pc` one clock later.
- A store is visible to the very next cycle's load (pinned by testplan scenario CORE-11).
- `dmem_req` qualifies the access; `dmem_we` distinguishes store from load. Loads drive `dmem_addr` and sample `dmem_rdata` in the same cycle; stores drive `dmem_addr`, `dmem_wstrb`, `dmem_wdata` and commit on the clock edge.

## Misaligned Data Accesses Halt

A half access at an odd byte, or a word access off a 4-byte boundary, halts the core (2026-10-20): cause 4 for a load, 5 for a store. The store's strobes are all zero, the load writes nothing, and the instruction retires as the usual trap beat. RISC-V lets an implementation handle misaligned accesses in hardware or trap them (unpriv §2.1.6); kestrel has no trap machinery, so it halts, as it does for every other trap. Until 2026-10-20 kestrel completed misaligned accesses in hardware with a two-beat cross-word retry; that logic sat on the block-RAM critical path and is gone. `rv32ui-p-ma_data`, which needs hardware support, now halts on its first misaligned load.

## What the Contract Deliberately Excludes

- **No instruction-side data access.** Self-modifying code is invisible to the core unless the memory system unifies the ports. The simulation testbench unifies them (one array serving both fetch and load/store) so `rv32ui-p-fence_i` runs without a coherence path — a testbench choice, not a core feature. The loader provides the same unification by address (Chapter 6).
- **No misaligned instruction fetch.** IALIGN=32 keeps fetch 4-byte aligned; the low PC bits are guaranteed by the next-PC logic plus the cause-`0x3` halt.
- **No memory protection, ordering, or atomicity.** RVWMO (unpriv ch. 3) is satisfied vacuously by a core that issues at most one access at a time and never reorders.

---

**Last Updated:** 2026-10-20
