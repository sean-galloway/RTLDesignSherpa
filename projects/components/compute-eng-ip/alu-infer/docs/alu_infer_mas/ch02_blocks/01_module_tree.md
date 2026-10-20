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

# alu_infer_top (module tree)

## Purpose

`alu_infer_top` is the ALU block instantiated inside the cell, at the
seam the cell PRD calls "ALU + execution FSM". It owns everything
between the operand-line inputs and the result-line outputs: element
decompose, the seven function rows, the fp32 MAC accumulator, the
result select, and the line composer.

## Module Tree

```text
alu_infer_top                               — the ALU block at the cell seam
├── alu_infer_rows                          — the function table
│   ├── row_copy                            — bypass (wires)
│   ├── row_addsub    (math_bf16_adder)     — opcode 1/2
│   ├── row_mul       (math_bf16_multiplier)— opcode 3
│   ├── row_mac       (math_bf16_fma)       — opcode 4, with alu_infer_acc
│   ├── row_minmax    (math_bf16_min/max)   — opcode 5
│   ├── row_compare   (math_bf16_comparator)— opcode 6
│   └── row_relu      (math_bf16_relu)      — opcode 7
├── alu_infer_pipe                          — tag FIFO + arrival join
└── alu_infer_acc                           — fp32 accumulator bank (2 lanes)
```

The as-built RTL folds the planned `alu_infer_decompose`,
`alu_infer_select`, `alu_infer_compose`, and `alu_infer_decode`
submodules of earlier drafts into `alu_infer_rows.sv`. The four source
files are `alu_infer_top.sv`, `alu_infer_rows.sv`, `alu_infer_pipe.sv`,
and `alu_infer_acc.sv` in `projects/components/compute-eng-ip/alu-infer/rtl/`.

The tree is flat on purpose: every child is one rank of the block
diagram, the data flows strictly top-down through them, and growth rows
extend `alu_infer_rows` without touching any sibling — the CGRA
replacement boundary of the cell PRD §11 runs around this whole tree.

`alu_infer_pipe` is what makes the elastic handshake (Chapter 3) true
— and it is deliberately *not* a bank of padding stages. It is a **tag
FIFO with an arrival join** (owner ruling 2026-10-18, as-built since
2026-10-19): each issue takes the next 8-bit tag from a free-running
counter, common to every op the invocation loads into the pipeline; the
FIFO tracks the tags in flight in issue order; and an entry's result is
offered only when every op of its tag group has arrived. v1 issues one
row-op per invocation, so a tag group is a single arrival — the join is
exercised structurally and multi-op groups (parallel issue of ops that
must finish together) are the growth path the mechanism was ruled for.
Quick rows (copy, mul, min/max, compare, relu, mac) compute
combinationally and land at the issue edge; the add/sub row lands
`ADDER_LATENCY` cycles later and re-joins its entry by tag compare —
not by position — so a row's pipeline depth is its own business. The
join yields group-aligned, strictly in-order retirement at natural
per-row latency, and it "naturally takes care of the elastic nature"
(owner, ibid.): a stalled consumer simply leaves the head entry offered
while rows behind it keep landing, and `ready` falls only when the FIFO
is genuinely full — never earlier. Only rows whose *timing* genuinely
requires depth carry real stages: the adder as configured (its
`PIPE_STAGE_1..4` = `ADDER_LATENCY`), and whatever the integration clock
demands of the multiplier/FMA (§7 growth — the join absorbs deeper rows
unchanged). Per-row natural latency is deliberately a knob: an
aggressively optimized row (a faster multiplier or FMA, say) lands in
`rtl/math` and simply joins earlier — the interface never changes
(owner direction 2026-10-17: latency work happens on FPGA).

### Figure 2.1: ALU-INFER full block diagram

![Figure 2.1: ALU-INFER full block diagram](../assets/graphviz/02_alu_infer_block.png)

White boxes are ports (the top rank is the interface of Chapter 3);
blue boxes are this block's logic — double-bordered where registered
(the adder row, the tag FIFO + arrival join); dashed boxes are state
(`alu_infer_acc`) and sideband (`clk, rst_n`). Every arrow is labeled
with what it carries — the operand trunk splits once at the decompose
output and fans to the seven rows, exactly the shared-trunk pattern of
the house style.

## Parameters

| Parameter | Default | Meaning |
|-----------|---------|---------|
| `LINE_W` | 32 | Line width in bits; wider lines scale the lane count, never the element width (PRD §2) |
| `N_LANES` | `LINE_W / 16` | bf16 lanes per line (2 at `LINE_W = 32`) |
| `ACC_W` | 32 | fp32 accumulator width per lane |
| `PIPE_DEPTH` | 8 | Tag-FIFO entries = maximum invocations in flight; valid range [2,16]. Sizes the stall tolerance, never a latency — presentation is at natural per-row speed |
| `ADDER_LATENCY` | 3 | Pipe stages of the add/sub row's `math_bf16_adder` (`PIPE_STAGE_1..4`); valid range [0,4] |
| `TAG_W` | 8 | Alignment tag width in bits (owner ruling 2026-10-18); 256 values can never alias the ≤16 entries in flight |

: Table 2.1: `alu_infer_top` parameters

No behavior-switch parameters exist in v1: the element model is bf16
only, and the `func_sel` element-width field is reserved (Chapter 6).

## Clock and Reset

Single clock, active-low async `aresetn` (house `ALWAYS_FF_RST`) —
matching the cell and the tile's single-clock-domain decision (TILE_SPEC
§9). Reset clears the accumulator bank and the registered config
snapshot (`func_sel`, `acc_ctrl`); it does not clear anything else,
because nothing else is state.

---

**Last Updated:** 2026-10-19
