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


# Overview

## Machine organization

gatling is one RV32I datapath shared by four hardware contexts. Each context owns a PC, a 32-entry register file, a halt state (halted, cause) and a run bit; everything else -- decode, immediates, ALU, branch comparator, load/store alignment -- exists once.

The four contexts are interleaved through a four-stage pipeline in strict rotation. A two-bit counter, `sel_q`, names the context in F; D, X and W hold the contexts one, two and three before it. Every cycle each stage holds a different context, so a context has exactly one instruction in flight. That single fact removes every hazard a pipeline normally has to manage:

| Hazard | Why it cannot happen |
|---|---|
| Data (RAW) | A context's next instruction is in D at t+5; its previous instruction wrote its register at the end of W, t+3 |
| Control | The branch target is written to the context's PC at the end of X, t+2; the next fetch is at t+4 |
| Structural | Each stage is used by one context per cycle; each memory port by one stage |

: Table 1.1: Hazards the rotation removes by construction

Each context retires one instruction per window (CPI 4); with all four running the core retires one instruction per clock.

## What is reused

gatling's ISA contract is kestrel's (PRD 3): the same opcode map, the same trap/halt causes, the same CSR stub, FENCE/FENCE.I as NOPs, MRET falling through. The blocks that implement it are kestrel's, used unchanged through kestrel's own filelists: `kestrel_decode`, `kestrel_imm_gen`, `kestrel_alu` and `kestrel_pkg`. One ISA has one source; a fix to kestrel's decode is a fix to gatling's.

New for the barrel: `gatling_core` (the rotation, the per-context state and the stage registers), `gatling_regfile` (four register files in one block RAM) and `gatling_mem_bram` (one memory bank per context, the AXIL loader, per-context run and status).

## Owner decisions this build implements

| Decision (PRD v0.3) | As built |
|---|---|
| Context visibility: implicit | No context-ID read; software cannot tell contexts apart |
| Program placement: separate | One 16 KB program/data bank per context, seen at every address |
| Illegal instruction: context-lock | Every halt stops only its context; the other three keep running |
| Scope: RV32I barrel first | Xcell (custom-0) decodes as illegal until the cell seam exists |

: Table 1.2: PRD decisions realized in the RTL
