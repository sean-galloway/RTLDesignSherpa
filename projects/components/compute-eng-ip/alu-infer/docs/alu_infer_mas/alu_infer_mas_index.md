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

**Component:** ALU-INFER — the cell's bf16 inference ALU (the cell PRD's
"ALU + execution FSM" block, implemented inside the cell component)
**Version:** 0.50 (pinned — revs held at 0.50 per owner, "for now," while
the ALU heads to the board)
**Date:** 2026-10-17
**Purpose:** Detailed micro-architecture specification for the ALU-INFER
block: what the datapath actually does, block by block

---

## Overview

ALU-INFER is the compute engine of the **cell**: a bf16 function array
that the cell's execution FSM drives with a pop → compute → push loop,
turning input-memory lines into result-memory lines under a
config-selected function. It is built mostly from the `math_bf16_*`
family of `rtl/math` — the adder, multiplier, FMA, comparator, min/max,
and ReLU blocks are instantiated, not reinvented — and it holds exactly
one piece of state: a per-lane fp32 MAC accumulator. This is the
internals document, the one you open when you need to know what the
datapath does rather than what the product definition
([PRD](../../PRD.md)) requires of it.

### Key Features

- **bf16 packed lanes:** a 32-bit line is two bf16 elements; every row
  computes both lanes in parallel, independently
- **Library-instantiated rows:** each of the seven v1 rows names its
  `rtl/math` block (`math_bf16_adder`, `math_bf16_multiplier`,
  `math_bf16_fma`, `math_bf16_comparator`, `math_bf16_min`,
  `math_bf16_max`, `math_bf16_relu`) — structure, latency, and
  special-value behavior are inherited from the library's own
  documentation and dv
- **fp32 MAC accumulation:** bf16×bf16 products are exact in fp32, so
  the FMA row accumulates in fp32 and rounds to bf16 once per result
  presentation — the production pattern, decided 2026-10-17
- **Function-table growth:** opcodes 8–31 and new sub-ops are RTL table
  rows behind the same valid/ready elastic pipeline; activations,
  reciprocal/divide, and conversions are the queued growth set
- **A hard boundary:** the ALU originates no config traffic (the stream
  is the programmer), exposes no monitor taps (observability is
  Ocelus's job), and speaks only to the cell FSM across one interface

### Design Philosophy

**The math library is the datapath.** New arithmetic lands in
`rtl/math` first and is consumed here second; the ALU is the library's
inference consumer the way the falcon suite's garuda rung is its
IEEE-fp32 consumer.

**FMA-first.** Inference time is multiply-accumulate time; every other
row is sized to sit beside the FMA without dwarfing it, and the one
piece of state in the block exists for the FMA's accumulator.

**A function table, not a function zoo.** The result select is a
port-driven mode mux — no arbitration, no starvation — and the house
block diagram correctly shows a plain box, not a trapezium.

## Design Notes

### Version History

**Rev 0.50 (2026-10-18, current — revs pinned at 0.50 per owner, "for
now," while the ALU heads to the board):** tag-based elastic alignment
ruling (PRD v0.50) — each loaded invocation takes an 8-bit tag, common to
all ops that must execute in parallel; a FIFO tracks tags in flight; an
op's valid asserts only when every op of its tag group is ready.
**Implemented 2026-10-19** (func+gate green, 13 cocotb tests ×
{gate,func} × `PIPE_DEPTH` {4,8}): `alu_infer_pipe` is the tag FIFO with
an arrival join; results retire in issue order at natural per-row
latency; a stalled consumer no longer blocks issue until the FIFO fills;
`ROW_LATENCY` is replaced by `PIPE_DEPTH` (default 8, [2,16]) and
`ADDER_LATENCY` (default 3, [0,4]). The PRD's "exactly `ROW_LATENCY`
cycles" phrasing described the retired mailbox realization; the seam
contract is unchanged — tags stay inside the block. Carries Rev 0.5's
port-width correction.

**Rev 0.5 (2026-10-17):** port-width correction (PRD v0.9) —
the v0.7 "widening" of `op_line_a/b` to `OP_LINES × LINE_W` was
premised on a mis-count of operand lines vs lanes; a binary/mac
invocation pops one line per side (OP_LINES counts the A+B pair), so
the ports stay `LINE_W` each. The owner ruling underneath — both
operand lines in the same clock — is unchanged. Diagram port labels
re-rendered. Carries Rev 0.4's accept-and-defer pass and Rev 0.3's
rulings.

**Rev 0.4 (2026-10-17):** owner accept-and-defer pass —
M7 and the `acc_ctrl` encoding accepted as drafted ("works for now");
per-row latency work deferred to FPGA bring-up (M8), where aggressive
per-function latency minimization is expected — the alignment-timer
contract absorbs faster rows without interface churn (noted at
`alu_infer_pipe`). PRD §8's result-flag question closed (packed low).
Carries Rev 0.3's rulings.

**Rev 0.3 (2026-10-17):** owner rulings closing the
implementation gaps (PRD v0.7) — operand ports are `OP_LINES × LINE_W`
so all operand lines present **in the same clock** and are captured at
the issue edge (Waveform 3.1 redrawn; block-diagram port labels
updated); **scheduler-paced feedback**: the ALU makes no autonomous
pacing decisions; CLEAR flows through the pipe and retires a don't-care
slot; an errored opcode retires its slot behind the IRQ; `result_flags`
closed — one mask bit per lane, packed low (**M5 closed**).

**Rev 0.2 (2026-10-17):** elastic-pipeline interface (owner
direction, PRD v0.6) — the ALU↔FSM seam is documented as a valid/ready
elastic pipeline: `valid`/`ready` issue handshake, `result_valid`/
`result_ready` retire handshake, backpressure propagates upstream and
freezes the alignment timer; Waveform 3.1 redrawn to show backpressure
at both ends. Carries Rev 0.1's decisions unchanged.

**Rev 0.1 (2026-10-17):** initial MAS, drafted alongside the
PRD v0.3 decisions — bf16 element model on the `math_bf16_*` library,
fp32 MAC accumulation (presentation semantics decided as M7), per-tetrad
control interface, in-band config/programming. v1 RTL landed in
`cell/rtl/` on 2026-10-17/18 (func+gate green) and moved to
`alu-infer/rtl/` on 2026-10-20; chapters 2–4 document the
as-built implementation and carry the open decisions M1–M8 of Chapter 6
in their labels.

## References

### Visual Assets

Diagram and waveform sources and their renders live in `assets/`:

- **Source Files:**
  - `assets/graphviz/*.dot` — Graphviz block-diagram sources (derived
    from the PRD-canonical copies in `../../assets/graphviz/`)
  - `assets/wavedrom/*.json` — WaveDrom timing-diagram sources

- **Rendered Files:**
  - `assets/graphviz/*.png` — Rendered block diagrams
  - `assets/wavedrom/*.png` — Rendered timing diagrams

`gen_alu_infer_figures.py` (one directory up) regenerates the waveforms
and copies the diagrams; each `graphviz/` directory's
`regenerate_all_graphviz.sh` re-renders the `.dot` files.

#### Diagrams

1. **Datapath overview** — [assets/graphviz/01_alu_infer_datapath.png](assets/graphviz/01_alu_infer_datapath.png)
2. **Full block diagram** — [assets/graphviz/02_alu_infer_block.png](assets/graphviz/02_alu_infer_block.png)

#### Waveforms

1. **Elastic handshake (backpressure at both ends)** — [assets/wavedrom/wvf_3_1_invocation_handshake.png](assets/wavedrom/wvf_3_1_invocation_handshake.png)
2. **Back-to-back issue (streaming)** — [assets/wavedrom/wvf_3_2_back_to_back.png](assets/wavedrom/wvf_3_2_back_to_back.png)
3. **MAC chain** — [assets/wavedrom/wvf_4_1_mac_chain.png](assets/wavedrom/wvf_4_1_mac_chain.png)

### Companion Specifications

- **[alu-infer PRD](../../PRD.md)** — product definition (normative for
  the ALU block; this MAS implements it)
- **[cell PRD](../../../cell/docs/PRD.md)** — the cell around the ALU:
  memories, FSM seam, packetizer, credit logic, §7 register map

### Project-Level

- **README:** [../../README.md](../../README.md) — component pointer page
- **TILE_SPEC §11.13:** [../../../tile/docs/TILE_SPEC.md](../../../tile/docs/TILE_SPEC.md) — the tetrad control core's place in the tile
- **KESTREL MAS:** [../../../../riscv-ip/kestrel-rv32i/docs/kestrel_mas/kestrel_mas_index.md](../../../../riscv-ip/kestrel-rv32i/docs/kestrel_mas/kestrel_mas_index.md) — the tetrad control core's reference core
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
- [The Seven Function Rows](ch02_blocks/02_function_rows.md)
- [The FP32 MAC Accumulator](ch02_blocks/03_mac_accumulate.md)
- [Result Select and Line Composer](ch02_blocks/04_select_and_compose.md)

#### Chapter 3: Internal Interfaces

- [The ALU↔FSM Interface](ch03_interfaces/01_alu_fsm_interface.md)

#### Chapter 4: Micro-Architecture Behavior

- [The Compute Cycle, per Opcode Class](ch04_behavior/01_compute_cycle.md)

#### Chapter 5: Verification Hooks

- [Verification Hooks and Observability](ch05_verification/01_verification_hooks.md)

#### Chapter 6: Configuration

- [Parameters, Encodings, and Open Items](ch06_configuration/01_configuration.md)

### Quick Navigation

#### For New Users

1. Start with [Overview](ch01_overview/01_overview.md) for the design
   commitments and the dataflow in one paragraph
2. Read the [full block diagram chapter](ch02_blocks/01_module_tree.md)
   for the module tree and parameters
3. Study the [ALU↔FSM interface](ch03_interfaces/01_alu_fsm_interface.md)
   for the handshake that brackets every invocation
4. Reference [Configuration](ch06_configuration/01_configuration.md)
   for encodings and the open-items register

#### For Implementers

- **A row's datapath:** see [Function Rows](ch02_blocks/02_function_rows.md)
  for the library block per opcode and its wiring
- **The accumulator:** see [FP32 MAC Accumulator](ch02_blocks/03_mac_accumulate.md)
  for CLEAR/ACCUMULATE/DRAIN semantics and isolation invariants
- **Timing:** see [Compute Cycle](ch04_behavior/01_compute_cycle.md) with
  the MAC-chain waveform
- **Testbenches:** see [Verification Hooks](ch05_verification/01_verification_hooks.md)
  for the golden model, the built-in library cross-check, and the
  coverage matrix

---

**Last Updated:** 2026-10-19
**Maintained By:** RTL Design Sherpa Project
