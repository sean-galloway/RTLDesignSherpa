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
| Date | 2026-10-20 |
| Status | Draft, reconciled to the as-built RTL in `alu-infer/rtl/`. Every row of the PRD's v1 table, function-set roadmap and growth list is implemented and verified, except what the PRD rules out (a true divider; the integer B4–B32 companion mode; the CGRA replacement). Open decisions are carried as M1–M8 (Chapter 6). |
| Classification | Open Source - MIT License |

: Document information

### Document Purpose

This Micro-Architecture Specification (MAS) documents how the cell's
inference ALU is built:

- The `alu_infer_top` module tree and its parameters
- Every function row: the `rtl/math` block it instantiates, its lanes per
  element format, and its wiring decisions
- The accumulator rows (MAC, REDUCE), the block's main state
- Decode and the four natural-latency result ports
- The PWL lookup-table activation and the format conversions
- The issue seam between the gatling core and the ALU
- Cycle-level behavior per opcode class, with timing diagrams
- Verification hooks: the library cross-check, the test scenarios and the
  build configurations
- The configuration surface: parameters, encodings, open items

For what the ALU must do and why, see the **alu-infer PRD** (normative for
the ALU block). For the issuer, see the **gatling PRD**. For the cell
around both, see the **cell PRD**.

### Intended Audience

- RTL designers integrating the ALU into the cell
- Verification engineers extending its testbench
- Firmware authors writing gatling programs that issue it
- Students reading an inference datapath top to bottom

## Design Notes

### Revision History

| Version | Date | Author | Description |
|---|---|---|---|
| 0.50 | 2026-10-20 | RTL Design Sherpa | Roadmap and growth rows implemented and verified: element formats on `func_sel[8:7]` (int8, fp32, fp8 e4m3), REDUCE sum/max with cross-lane fold, PWL LUT, const, library activations, conversions, MAC in every format. Four natural-latency result ports; `MUL_LATENCY`, `MAC_LATENCY`, `EN_*` parameters; `err_opcode`. Issuer is gatling throughout; the execution-FSM framing is retired. Library bug math BUG-009 (exp2) found and fixed. |
| 0.50 | 2026-10-18 | RTL Design Sherpa | Revs pinned at 0.50 per owner. Tag-based elastic alignment (implemented 2026-10-19): `alu_infer_pipe` is a tag FIFO with an arrival join; `PIPE_DEPTH` and `ADDER_LATENCY` replace `ROW_LATENCY`. |
| 0.5 | 2026-10-17 | RTL Design Sherpa | Operand ports stay `LINE_W` each (the v0.7 widening was a line/lane mis-count). |
| 0.4 | 2026-10-17 | RTL Design Sherpa | M7 and the `acc_ctrl` encoding accepted; per-row latency deferred to FPGA bring-up (M8); result flags packed low. |
| 0.3 | 2026-10-17 | RTL Design Sherpa | Same-clock operand capture; scheduler-paced feedback; CLEAR and errored opcodes retire their slots; M5 closed. |
| 0.2 | 2026-10-17 | RTL Design Sherpa | Elastic valid/ready seam at both ends. |
| 0.1 | 2026-10-17 | RTL Design Sherpa | Initial MAS: bf16 lanes on the `math_bf16_*` library, fp32 MAC accumulation (M7). |

: Revision history

## References

### Related Documents

- **alu-infer PRD** ([../../../PRD.md](../../../PRD.md)) — product
  definition, normative for the ALU block
- **gatling PRD** ([../../../../../riscv-ip/gatling-rv32i/PRD.md](../../../../../riscv-ip/gatling-rv32i/PRD.md)) —
  the barrel RV32I core that issues the ALU
- **cell PRD** ([../../../../cell/docs/PRD.md](../../../../cell/docs/PRD.md)) —
  the cell around the ALU
- **rtl-math book** ([../../../../../../../docs/markdown/rtl-math/index.md](../../../../../../../docs/markdown/rtl-math/index.md)) —
  the library the rows instantiate
- **rtl-math references index** ([../../../../../../../rtl/math/references/README.md](../../../../../../../rtl/math/references/README.md)) —
  bf16, activation and quantization papers

---

**Last Updated:** 2026-10-20
