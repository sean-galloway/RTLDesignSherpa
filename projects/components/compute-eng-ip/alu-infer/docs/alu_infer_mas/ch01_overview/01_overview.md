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

`alu_infer` is the cell's compute engine: a function table over packed
element lanes. It is deliberately *not* a processor — no fetch, no program
counter, no branches. Programmability lives in the issuer: the tetrad's
**gatling** core, a barrel RV32I with the Xcell extension, runs one context
per cell. A context's program presents operands and a function select to
this block's issue seam and takes results back in order (gatling PRD §1,
owner ruling 2026-10-19: *the program is the schedule*). The ALU turns
operand lines into result lines, one invocation at a time, and makes no
pacing decisions of its own.

Three commitments shape every decision in this specification.

**1. The math library is the datapath.** Every floating-point row
instantiates an existing `rtl/math` block — `math_bf16_*` for bf16, the IEEE
754-2008 fp32 adder/multiplier/FMA and `math_fp32_*` for fp32,
`math_fp8_e4m3_*` for fp8, the `*_to_*` converters. The ALU inherits each
block's structure, numerics and special-value behavior. The int8 rows are
plain saturating integer logic; there is no int8 library family.

**2. FMA-first, one-cycle loop.** Inference time is multiply-accumulate
time. The accumulator is a per-lane 32-bit bank (fp32 for the float
formats, int32 for int8). The bf16 FMA computes the product exactly in
fp32 and rounds once, and the accumulate loop is that one fused operation
per cycle, so a dependent chain sustains one step per clock at any operand
pipeline depth.

**3. A function table, not a function zoo.** `func_sel` names an element
format, a row and a sub-op. Decode routes the invocation to one row and to
one of four result ports by latency class; nothing arbitrates. New rows
are table entries behind the same seam.

## The Dataflow in One Paragraph

Gatling presents an invocation: operand lines A and B (`LINE_W` each,
captured in the same clock), a 16-bit immediate, `func_sel`, `acc_ctrl`,
and `valid`. On the issue edge (`valid && ready`) the invocation takes the
next 8-bit tag. Decode checks that the (opcode, format) pair is legal in
this build and routes it. A combinational row lands its result in the tag
FIFO at the issue edge. The adders land `ADDER_LATENCY` cycles later, the
multipliers `MUL_LATENCY` later, and the accumulator rows `MAC_LATENCY`
later. Each carries its tag and joins its FIFO entry by tag compare. The
FIFO offers results strictly in issue order. An illegal invocation still
retires its slot, with a zero line, and pulses `err_opcode`.

### Figure 1.1: ALU-INFER datapath overview

![Figure 1.1: ALU-INFER datapath overview](../assets/graphviz/01_alu_infer_datapath.png)

The full block diagram, with every row family and result port, is Figure
2.1 in the next chapter.

## Element Formats

| `func_sel[8:7]` | Format | Lanes per 32-bit line | Accumulator lane |
|---|---|---|---|
| 0 | bf16 | 2 | fp32 |
| 1 | int8 (two's complement) | 4 | int32 |
| 2 | fp32 | 1 | fp32 |
| 3 | fp8 e4m3 | 4 | fp32 |

: Table 1.1: element formats

bf16 is the v1 format and the one every row supports. int8 is the PRD
roadmap's first added format (4 MACs per clock on a 32-bit line), and fp32
the second. fp8 e4m3 is the §7 element-model extension. Wider lines scale
the lane count, never the element width.

## Relationship to Gatling and the Cell

The ALU speaks only across the issue seam (Chapter 3) and one status
output. Gatling owns sequencing and pacing: it shapes the `valid` stream,
obeys `ready`, and pairs results with invocations by counting. Cell
configuration — including anything that sets an ALU mode for a layer —
arrives in-band on delta, and gatling never originates config traffic
(gatling PRD §1). Observability belongs to the Ocelus MonBus plane, and
this block exposes no monitor taps.

## Status of This Specification

The RTL is built and verified at gate and func levels, in four build
configurations (Chapter 5). Chapters 2–4 document the as-built code. Where
the PRD left a choice open, this specification records the as-built choice
or carries it as M1–M8 (Chapter 6).

---

**Last Updated:** 2026-10-20
