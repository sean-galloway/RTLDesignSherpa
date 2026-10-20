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

# Design Philosophy and Datapath Organization

## What This Block Is

`alu_infer` is the cell's compute engine: a bf16 function array that the
cell's execution FSM drives with a simple pop → compute → push loop. It is
deliberately *not* a processor — no fetch, no program counter, no
branches. Its programmability lives one level up: a per-tetrad RV32I
control core (gatling-class barrel RISC-V) reacts to the cells' status,
and the tile's data/config/programming stream arrives in-band on delta.
The ALU's only job is to turn operand lines into result lines, one
config-selected function at a time.

The v1 RTL lives in `alu-infer/rtl/` (landed 2026-10-17/18, func+gate
green; moved from `cell/rtl/` to the alu-infer component on 2026-10-20):
`alu_infer_top.sv`, `alu_infer_rows.sv`, `alu_infer_pipe.sv`,
`alu_infer_acc.sv`. The planned submodules
`alu_infer_decompose`/`select`/`compose`/`decode` of earlier MAS drafts
are folded into `alu_infer_rows.sv` in the as-built code. The alignment
mechanism is the owner-ruled tag FIFO (2026-10-18, implemented
2026-10-19): each issue takes an 8-bit tag, `alu_infer_pipe` tracks the
tags in flight, and a result is offered only when every op of its tag
group has arrived — so quick rows compute at their natural speed and
align at the join instead of carrying padded pipe stages.

Three commitments shape every decision in this specification.

**1. The math library is the datapath.** Nearly every function row
instantiates an existing `rtl/math` block — `math_bf16_adder`,
`math_bf16_multiplier`, `math_bf16_fma`, `math_bf16_comparator`,
`math_bf16_min`, `math_bf16_max`, `math_bf16_relu`. The ALU therefore
inherits three things for free: structure already documented in the
rtl-math book, verification already done by the library's own dv, and
convergent-thinking citations already archived in
`rtl/math/references/`. New arithmetic is added to the library first and
consumed here second; rows without a block (copy, mask packing) are wires
and glue. This is the same consumption pattern as the falcon suite's
garuda rung, which takes the library's IEEE-fp32 blocks behind its
reservation stations.

**2. FMA-first, fp32 accumulate.** Inference time is dominated by
multiply-accumulate, so the mac row is the workhorse: `math_bf16_fma`
computes the bf16 product exactly in fp32 (8×8 significand bits fit
fp32's 24) and adds it into a per-lane fp32 accumulator — one rounding
per operation, one rounding to bf16 at result presentation. Every other
row is sized to sit beside the FMA without dwarfing it.

**3. A function table, not a function zoo.** Opcodes 0–7 are RTL table
rows — the select is a mode mux driven by `func_sel`, never an arbiter,
and growth rows (activations, reciprocal/divide, conversions) are added
as rows without disturbing the handshake, the lanes, or the
verification scaffolding.

## The Dataflow in One Paragraph

Both operand lines — A and B, one per side — arrive **in the same
clock** from the execution FSM's input-memory pops. The
element decompose block splits each 32-bit line into two bf16 lanes. All
seven function rows see the same lanes; the row named by
`func_sel.opcode` computes, and the result select forwards that row's
two lanes to the line composer, which packs them back into a 32-bit
result line. The compare row additionally emits a per-lane mask as
`result_flags`. State exists in exactly one place — the fp32 MAC
accumulator, private to opcode 4, managed by `acc_ctrl` — so every other
row is a pure function of its operands, which is what makes the
verification story (Chapter 5) tractable.

### Figure 1.1: ALU-INFER datapath overview (definition level)

![Figure 1.1: ALU-INFER datapath overview](../assets/graphviz/01_alu_infer_datapath.png)

The figure above is the context view — operand flow down the center,
`FUNC_SEL` and the MAC accumulator dashed as sideband. The full block
diagram with every row and its library block is Figure 2.1 in the next
chapter.

## Relationship to the Cell and the Tetrad Core

The ALU speaks only to the cell's execution FSM (Chapter 3): operands,
result, handshake, and two config inputs (`func_sel`, `acc_ctrl`). The
FSM owns sequencing, the memories, and the credit loop. The tetrad
control core — one gatling-class barrel RV32I per tetrad — is out of
this block entirely: it reads cell status and IRQs over the AXIL register
plane and exercises operational registers; per the owner ruling of
2026-10-17 it originates no config traffic, and cell *programming*
(including this ALU's `FUNC_SEL` register) arrives in-band with the
delta traffic. Observability is the Ocelus MonBus plane's job, not the
ALU's; this block exposes no monitor taps by default (open item M2
asks whether the library blocks' IEEE exception outputs should surface
as `result_flags`).

## Status of This Specification

The v1 RTL is built and green. Chapters 2–4 document the as-built
implementation in `alu-infer/rtl/` (`alu_infer_top.sv`, `alu_infer_rows.sv`,
`alu_infer_pipe.sv`, `alu_infer_acc.sv`, landed 2026-10-17/18, func+gate
green). Where the PRD left a choice open, this specification either
decides it (and records the decision) or carries it as an open item M1–M8
in Chapter 6. The tag-based alignment mechanism of Chapter 4 is the
as-built realization since 2026-10-19; it superseded the alignment-timer
mailbox of the first v1 build without any interface change — the PRD's
"presented exactly `ROW_LATENCY` cycles after issue" phrasing described
that mailbox and is superseded with it (the seam contract it sat under —
two valid/ready pairs, in-order retirement, II=1 — is unchanged).

---

**Last Updated:** 2026-10-19
