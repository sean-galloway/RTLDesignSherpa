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

# ALU-INFER Micro-Architecture Specification Index

**Component:** ALU-INFER — the cell's inference ALU, issued by the tetrad's
gatling core
**Version:** 0.50 (pinned — revs held at 0.50 per owner, "for now," while
the ALU heads to the board)
**Date:** 2026-10-20
**Purpose:** Detailed micro-architecture specification for the ALU-INFER
block: what the datapath does, block by block, as built

---

## Overview

ALU-INFER is the compute engine of the **cell**. The tetrad's **gatling**
barrel RV32I core issues it one invocation at a time over an elastic
valid/ready seam: two operand lines, a function select, and accumulator
control in; one result line and a flag line out, in issue order. Everything
behind the seam — the function rows, the accumulator, the alignment FIFO —
is this document.

The rows are built from the `rtl/math` library (`math_bf16_*`, the IEEE
754-2008 fp32 blocks, `math_fp8_e4m3_*`, the converters) plus a little
integer logic for int8. The block holds two pieces of architectural state:
the per-lane accumulator bank and the PWL lookup table.

### Key Features

- **Four element formats** on `func_sel[8:7]`: bf16 (2 lanes per 32-bit
  line), int8 (4), fp32 (1), fp8 e4m3 (4). Every lane is computed in
  parallel and independently.
- **23 opcodes**: the v1 rows (copy, add, sub, mul, mac, min/max,
  compare, relu), the roadmap rows (reduce, PWL LUT activation, const),
  the library activations (leaky-relu, gelu, sigmoid, silu, tanh,
  reciprocal, exp2, log2, log2-scale) and format conversions.
- **Accumulator rows** (MAC, REDUCE) on a 32-bit-per-lane bank: fp32 for
  the float formats, int32 for int8; one-cycle accumulate loop, so a
  dependent chain sustains one step per clock.
- **Natural-latency result ports** (combinational, adder, multiplier,
  accumulator) joined by an 8-bit tag FIFO: in-order retirement, II=1, no
  padded stages.
- **Build-out parameters** (`EN_INT8`, `EN_FP32`, `EN_FP8`, `EN_REDUCE`,
  `EN_PWL`, `EN_ACT`, `EN_CVT`): a family built out decodes as illegal,
  and the lean build is the v1 bf16 ALU.
- **A hard boundary:** the ALU originates no config traffic, exposes no
  monitor taps, and speaks only across the issue seam plus one
  `err_opcode` status pulse.

### Design Philosophy

**The math library is the datapath.** New arithmetic lands in `rtl/math`
first and is consumed here second. The rows inherit each block's
structure, numerics and special-value behavior, and the testbench checks
each row against that block's own reference model.

**FMA-first.** Inference time is multiply-accumulate time. The
accumulator loop is one fused operation per cycle; depth goes into the
operand stages ahead of it, never into the loop.

**A function table, not a function zoo.** Decode routes an invocation to
one row and one result port; there is no arbitration, so nothing can
starve.

## Design Notes

### Version History

**Rev 0.50, 2026-10-20 update (revs pinned at 0.50):** the PRD's
function-set roadmap and growth rows implemented and verified — element
formats on `func_sel[8:7]` (int8, fp32, fp8 e4m3 alongside bf16), REDUCE
sum/max with a cross-lane fold, the 256-entry PWL LUT activation loaded
in-band, const, the library activations and conversions, MAC in every
format. The single combinational/late port pair became four
natural-latency ports (`MUL_LATENCY`, `MAC_LATENCY` added), the
accumulator gained an operand pipeline ahead of a one-cycle loop, illegal
invocations pulse `err_opcode`, and `EN_*` parameters build families out.
The issuer is gatling throughout. The exp2 row exposed a library bug
(math BUG-009, `math_bf16_exp2` returned 0 for every x >= 256), fixed in
`rtl/math`.

**Rev 0.50 (2026-10-18/19):** tag-based elastic alignment (owner ruling
2026-10-18), implemented 2026-10-19: the alignment-timer mailbox became a
tag FIFO with an arrival join; `ROW_LATENCY` became `PIPE_DEPTH` and
`ADDER_LATENCY`.

**Rev 0.1–0.5 (2026-10-17):** initial MAS with the PRD v0.3 decisions
(bf16 lanes on the `math_bf16_*` library, fp32 MAC accumulation, M7);
elastic valid/ready seam; same-clock operand capture; scheduler-paced
feedback; `result_flags` packed low (M5 closed); operand ports `LINE_W`
each.

## References

### Visual Assets

Diagram and waveform sources and their renders live in `assets/`:

- `assets/graphviz/*.dot` — block-diagram sources, derived from the
  PRD-canonical copies in `../../assets/graphviz/`; `.png` renders beside
  them
- `assets/wavedrom/*.json` — timing-diagram sources; `.png` renders

`gen_alu_infer_figures.py` (one directory up) regenerates the waveforms and
copies the diagrams; each `graphviz/` directory's `regenerate_all_graphviz.sh`
re-renders the `.dot` files.

#### Diagrams

1. **Datapath overview** — [assets/graphviz/01_alu_infer_datapath.png](assets/graphviz/01_alu_infer_datapath.png)
2. **Full block diagram** — [assets/graphviz/02_alu_infer_block.png](assets/graphviz/02_alu_infer_block.png)

#### Waveforms

1. **Elastic handshake** — [assets/wavedrom/wvf_3_1_invocation_handshake.png](assets/wavedrom/wvf_3_1_invocation_handshake.png)
2. **Back-to-back issue** — [assets/wavedrom/wvf_3_2_back_to_back.png](assets/wavedrom/wvf_3_2_back_to_back.png)
3. **MAC chain** — [assets/wavedrom/wvf_4_1_mac_chain.png](assets/wavedrom/wvf_4_1_mac_chain.png)

### Companion Specifications

- **[alu-infer PRD](../../PRD.md)** — product definition (normative for the
  ALU block; this MAS implements it)
- **[gatling PRD](../../../../riscv-ip/gatling-rv32i/PRD.md)** — the
  tetrad barrel core that issues the ALU
- **[cell PRD](../../../cell/docs/PRD.md)** — the cell around the ALU:
  memories, packetizer, credits, register map

### Project-Level

- **README:** [../../README.md](../../README.md) — component pointer page
- **rtl-math book:** [../../../../../../docs/markdown/rtl-math/index.md](../../../../../../docs/markdown/rtl-math/index.md) — the library the rows instantiate

## Navigation

### Document Organization

Each chapter below is one source file.

#### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

#### Chapter 1: Overview

- [Design Philosophy and Datapath Organization](ch01_overview/01_overview.md)

#### Chapter 2: Functional Blocks

- [alu_infer_top (module tree)](ch02_blocks/01_module_tree.md)
- [The Function Rows](ch02_blocks/02_function_rows.md)
- [The Accumulator Rows: MAC and REDUCE](ch02_blocks/03_mac_accumulate.md)
- [Decode and Result Ports](ch02_blocks/04_decode_and_ports.md)
- [The PWL LUT Activation](ch02_blocks/05_pwl_lut.md)
- [Format Conversions](ch02_blocks/06_conversions.md)

#### Chapter 3: Internal Interfaces

- [The Issue Seam](ch03_interfaces/01_issue_seam.md)

#### Chapter 4: Micro-Architecture Behavior

- [The Compute Cycle, per Opcode Class](ch04_behavior/01_compute_cycle.md)

#### Chapter 5: Verification Hooks

- [Verification Hooks and Observability](ch05_verification/01_verification_hooks.md)

#### Chapter 6: Configuration

- [Parameters, Encodings, and Open Items](ch06_configuration/01_configuration.md)

### Quick Navigation

#### For New Users

1. Start with [Overview](ch01_overview/01_overview.md) for the commitments
   and the dataflow in one paragraph
2. Read the [module tree](ch02_blocks/01_module_tree.md) for the blocks and
   parameters
3. Study [the issue seam](ch03_interfaces/01_issue_seam.md) for the
   handshake that brackets every invocation
4. Reference [Configuration](ch06_configuration/01_configuration.md) for
   the opcode map and encodings

#### For Implementers

- **A row:** [Function Rows](ch02_blocks/02_function_rows.md)
- **The accumulator:** [MAC and REDUCE](ch02_blocks/03_mac_accumulate.md)
- **Timing:** [Decode and Result Ports](ch02_blocks/04_decode_and_ports.md)
  and [Compute Cycle](ch04_behavior/01_compute_cycle.md)
- **Testbenches:** [Verification Hooks](ch05_verification/01_verification_hooks.md)

---

**Last Updated:** 2026-10-20
**Maintained By:** RTL Design Sherpa Project
