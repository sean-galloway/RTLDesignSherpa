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

kestrel talks to memory through two ports that are deliberately minimal. There is no bus fabric, no wait states, no byte enables on the instruction side, and no burst machinery. At this rung the memory system is expected to keep up with the core, and the contract says so out loud. An integrator replacing the memories must preserve all three properties below; violating any of them breaks the single-cycle design.

1. **Harvard at the core.** Fetch and data access are separate ports backed by whatever the integrator provides. The core never issues a data access to the instruction memory or vice versa, and it never sees coherence between them.
2. **Combinational reads.** Both memories answer in the same cycle the address is presented. This is the load-bearing simplification: an instruction's full path — fetch, decode, register read, ALU, data read, writeback — must fit in one clock, so the memories are forbidden from adding latency. Synchronous-read macros (e.g. block RAM) violate the contract; the loader honors it with `(* ram_style = "distributed" *)` arrays.
3. **Word-wide buses with byte strobes.** Data memory is 32 bits wide. Sub-word stores rotate data and strobe into the addressed byte lanes; sub-word loads rotate read data back before size/sign selection. The memory must merge `dmem_wstrb` per byte (write only the strobed bytes of `dmem_wdata`).

## Timing Rules

- An instruction that touches memory completes in exactly one clock when its access lies within one word; a cross-word access takes two clocks via the documented retry (below). There are no other exceptions.
- The PC holds only for the retry's first beat and for halts. Everything else advances every cycle.
- A store is visible to the very next cycle's load (a cross-word store immediately followed by the load of the same address returns the full assembled value — pinned by testplan scenario CORE-11).
- `dmem_req` qualifies the access; `dmem_we` distinguishes store from load. Loads drive `dmem_addr` and sample `dmem_rdata` in the same cycle; stores drive `dmem_addr`, `dmem_wstrb`, `dmem_wdata` and commit on the clock edge.

## The Cross-Word Retry

When `addr[1:0] + access_size > 4`, the access straddles two words and one 32-bit beat cannot carry it. The core splits it:

1. **Beat 1 (`ls_first`).** Address is the aligned word containing the access start. Stores write the tail bytes (`4 - addr[1:0]` of them) with the left-rotated strobe; loads capture the shifted first word. The PC holds; no retirement (`rvfi_valid` low).
2. **Beat 2 (`ls_second`).** Address is the next word (`word + 1`). Stores write the remaining head bytes with a head-only strobe and right-rotated data; loads merge the captured tail with the second word's head into the assembled value. The instruction retires now, with exactly one RVFI beat.

During both beats `dmem_req` (and `dmem_we` for stores) stays high; `dmem_addr` steps by one word. Everything else in the core is unaware the retry happened.

## What the Contract Deliberately Excludes

- **No instruction-side data access.** Self-modifying code is invisible to the core unless the memory system unifies the ports. The simulation testbench unifies them (one array serving both fetch and load/store) so `rv32ui-p-fence_i` runs without a coherence path — a testbench choice, not a core feature. The loader provides the same unification by address (Chapter 6).
- **No misaligned instruction fetch.** IALIGN=32 keeps fetch 4-byte aligned; the low PC bits are guaranteed by the next-PC logic plus the cause-`0x3` halt.
- **No memory protection, ordering, or atomicity.** RVWMO (unpriv ch. 3) is satisfied vacuously by a core that issues at most one access at a time and never reorders. Cross-word accesses are not atomic.

---

**Last Updated:** 2026-10-07
