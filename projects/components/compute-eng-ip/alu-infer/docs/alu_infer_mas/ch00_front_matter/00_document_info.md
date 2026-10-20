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

# Document Information

## Overview

### ALU-INFER Micro-Architecture Specification

| Property | Value |
|---|---|
| Document Title | ALU-INFER Micro-Architecture Specification |
| Version | 0.50 (pinned per owner, "for now") |
| Date | 2026-10-17 |
| Status | Draft — v1 RTL landed in `cell/rtl/` on 2026-10-17/18 (func+gate green): `alu_infer_top.sv`, `alu_infer_rows.sv`, `alu_infer_pipe.sv`, `alu_infer_acc.sv`. The MAS's planned submodules `alu_infer_decompose`/`select`/`compose`/`decode` are folded into `alu_infer_rows.sv` in the as-built RTL; `ROW_LATENCY` defaults to 4 with range [1,6]. Chapters 2–4 are reconciled to the as-built code and carry the open decision IDs M1–M8. |
| Classification | Open Source - MIT License |

: Document information

### Document Purpose

This Micro-Architecture Specification (MAS) documents how the cell's
inference ALU is built:

- The `alu_infer_top` module tree and its parameters
- The seven function rows, each with the `rtl/math` block it
  instantiates and its wiring decisions
- The fp32 MAC accumulator — the block's only state — and its
  CLEAR / ACCUMULATE / DRAIN semantics
- The signal-level ALU↔FSM interface and its valid/ready
  elastic-pipeline handshake
- Cycle-level behavior per opcode class, with timing diagrams
- Verification hooks: the golden model, the built-in library
  cross-check, and the coverage matrix
- The configuration surface: encodings, parameters, and the open-items
  register

Yes, the "(planned)" markers of earlier drafts get called out up front
rather than left for you to discover. The v1 RTL landed in `cell/rtl/`
on 2026-10-17/18 (func+gate green): `alu_infer_top.sv`,
`alu_infer_rows.sv`, `alu_infer_pipe.sv`, `alu_infer_acc.sv`. The MAS's
planned submodules `alu_infer_decompose`/`select`/`compose`/`decode` are
folded into `alu_infer_rows.sv` in the as-built RTL; `ROW_LATENCY`
defaults to 4 with range [1,6]. This book now documents the as-built
implementation that the cell's RTL is checked against. For what the ALU
must do and why, see the companion **alu-infer PRD** (normative for the
ALU block); for the cell around it, see the **cell PRD**.

**Addendum 2026-10-19:** the tag-based alignment mechanism described in
Chapter 4 is a ratified target, not yet in the as-built RTL; the v1
implementation realizes the same uniform-presentation contract with the
alignment-timer mailbox inside `alu_infer_pipe.sv`.

### Intended Audience

- RTL designers implementing the ALU inside the cell's `rtl/`
- Verification engineers developing the cell's testbenches
- Design reviewers checking the future implementation against intent
- Students reading the bf16 inference datapath top to bottom

## Design Notes

### Revision History

| Version | Date | Author | Description |
|---|---|---|---|
| 0.50 | 2026-10-18 | RTL Design Sherpa | Revs pinned at 0.50 per owner ("for now," while the ALU heads to the board). Content: tag-based elastic alignment ruling (PRD v0.50) — 8-bit tag per loaded invocation, common to all ops that must run in parallel; FIFO-tracked; op valid asserts only when all valids of its tag group are ready. Alignment architecture for deep-pipelined rows; as-built mailbox/timers remain the v1 realization (ch04 note). v1 RTL landed in `cell/rtl/` on 2026-10-17/18 (func+gate green): `alu_infer_top.sv`, `alu_infer_rows.sv`, `alu_infer_pipe.sv`, `alu_infer_acc.sv`; planned `alu_infer_decompose`/`select`/`compose`/`decode` submodules folded into `alu_infer_rows.sv`; `ROW_LATENCY` defaults to 4, range [1,6]. No interface change. Carries Rev 0.5's port-width correction. |
| 0.5 | 2026-10-17 | RTL Design Sherpa | Port-width correction (PRD v0.9): operand ports stay `LINE_W` each — a binary/mac invocation pops one line per side (OP_LINES counts the A+B pair); the v0.7 widening was a line/lane mis-count. Same-clock capture ruling unchanged. |
| 0.4 | 2026-10-17 | RTL Design Sherpa | Owner accept-and-defer pass (PRD v0.8): M7 and the `acc_ctrl` encoding accepted as drafted ("works for now"); per-row latency minimization deferred to FPGA bring-up (M8); PRD §8 result-flag question closed (packed low, one bit per lane). |
| 0.3 | 2026-10-17 | RTL Design Sherpa | Owner rulings closing the implementation gaps (PRD v0.7): `OP_LINES × LINE_W` operand ports with same-clock capture; scheduler-paced feedback (the ALU makes no autonomous pacing decisions); CLEAR and errored opcodes retire their slots; `result_flags` = one mask bit per lane, packed low (M5 closed). |
| 0.2 | 2026-10-17 | RTL Design Sherpa | Elastic-pipeline interface (owner direction, PRD v0.6): the ALU↔FSM seam is a valid/ready elastic pipeline — `valid`/`ready` issue, `result_valid`/`result_ready` retire, backpressure freezes the alignment timer; Waveform 3.1 redrawn with backpressure at both ends. Carries Rev 0.1's decisions. |
| 0.1 | 2026-10-17 | RTL Design Sherpa | Initial MAS release, drafted with the PRD v0.3 decisions: bf16 element model on the `math_bf16_*` library, fp32 MAC accumulation (presentation semantics decided as M7), per-tetrad kestrel-class control interface, in-band config/programming. |

: Revision history

## References

### Related Documents

- **alu-infer PRD** ([../../../PRD.md](../../../PRD.md)) — product
  definition, normative for the ALU block
- **cell PRD** ([../../../../cell/docs/PRD.md](../../../../cell/docs/PRD.md)) —
  the cell around the ALU: memories, execution FSM, packetizer, credit
  logic, §7 register map
- **TILE_SPEC §11.13** ([../../../../tile/docs/TILE_SPEC.md](../../../../tile/docs/TILE_SPEC.md)) —
  the tetrad control core's place in the tile
- **KESTREL-RV32I MAS** ([../../../../../riscv-ip/kestrel-rv32i/docs/kestrel_mas/kestrel_mas_index.md](../../../../../riscv-ip/kestrel-rv32i/docs/kestrel_mas/kestrel_mas_index.md)) —
  the tetrad control core's reference core
- **rtl-math book** ([../../../../../../../docs/markdown/rtl-math/index.md](../../../../../../../docs/markdown/rtl-math/index.md)) —
  the library the function rows instantiate
- **rtl-math references index** ([../../../../../../../rtl/math/references/README.md](../../../../../../../rtl/math/references/README.md)) —
  the math-paper archive (bf16 format, activations, quantization)

---

**Last Updated:** 2026-10-19
