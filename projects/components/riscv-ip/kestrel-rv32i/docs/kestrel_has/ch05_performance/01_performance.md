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

# Performance Characteristics

## Cycles per Instruction

| Case | Cycles | Notes |
|------|--------|-------|
| Any aligned instruction, including loads/stores that stay within one word | 1 | CPI 1.0; taken and not-taken branches cost the same |
| Cross-word misaligned load/store (`addr[1:0] + size > 4`) | 2 | One retry cycle; still one retired instruction (CPI 2.0 for that instruction) |
| Halt | 0 extra | The halting instruction retires on its own cycle as the trap beat; the hold afterwards is not execution |

: CPI by access class

CPI 1 is per instruction, and the single-cycle discipline taxes every instruction at the rate of the slowest path (below). Code with unaligned data averages slightly above 1.0 — the battery's `ma_data` and `ld_st` programs exercise exactly that case.

## Critical Path Analysis

In a single-cycle design, the clock period must span the slowest instruction's path through *every* block, because every block sits between the same two edges. There is no clock frequency at which this machine is fast, only a frequency at which it is correct; that frequency is set by the longest row below — almost always the load, which crosses both memories and the datapath between them.

| Instruction class | Path the clock must span |
|-------------------|--------------------------|
| ALU (OP/OP-IMM) | imem + decode + regfile + ALU + writeback setup |
| Branch | imem + decode + regfile + comparator + next-PC mux + PC setup |
| Load | imem + decode + regfile + ALU + dmem + rotate/sign-extend + writeback setup |
| Store | imem + decode + regfile + ALU + dmem + strobe setup |
| JAL/JALR | imem + decode + regfile (JALR) + add + next-PC mux + PC setup |
| Cross-word L/S | all of load/store, plus the retry cycle (two clocks, by design) |

: Critical-path content per instruction class

Design consequence for integrators: timing closure must be proven against the load row with the *actual* memory macros. Synchronous-read RAM (block RAM) on either port breaks the single-cycle contract outright; the loader honors the contract with `(* ram_style = "distributed" *)` arrays.

## Resource Sketch

An honest sketch, from the RTL rather than synthesis:

| Resource | Content |
|----------|---------|
| State (core, outside the register file) | Five state elements: `pc` (32b), `retire_count` (64b), `halt_q` (1b), `ls_retry` (1b), `ls_rdata_lo` (32b) — the entire sequential content besides the register file |
| Register file | 32 x 32 bits, 2 combinational read ports, 1 synchronous write port; inferred as distributed RAM/LUTRAM |
| Decode | One `unique casez` truth table keyed on `{opcode, funct3, funct7}` — no FSM, no microcode, no control ROM |
| Datapath | ALU (10 ops), immediate generator, source muxes, writeback mux, next-PC mux, dedicated branch comparator, byte-lane rotators |
| Loader addition | Two 16K-word distributed-RAM arrays (2 x 64 KB), AXIL leaf slaves with skid buffers, one run bit and two write-side holding registers |

: Resource sketch (no committed synthesis numbers at v0.1)

No LUT/FF synthesis numbers are claimed in this revision; the core's small fixed state and absence of pipeline registers are the structural facts that bound its area.

## Throughput Context

One instruction per clock at frequency f. The suite's rung 2 (merlin, a five-stage pipeline) exists precisely because this machine's clock is capped by the sum of all stages rather than their slowest member — kestrel trades every fast instruction's speed for total visibility. For the education and small-control use cases kestrel targets, that trade is the point.

---

**Last Updated:** 2026-10-07
