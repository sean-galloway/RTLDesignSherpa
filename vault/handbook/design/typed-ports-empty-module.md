---
title: Typed ports synthesize to an empty module in Vivado
summary: A module whose ports use `parameter type` (addr_t, data_t ...) simulates and lints clean, and Vivado 2025.1 synthesizes it to an EMPTY module with no error -- its instances become black boxes that fail at opt_design (CVA6 tc_sram_wrapper, 2026-11-11).
---

# Typed ports synthesize to an empty module in Vivado

CVA6's `tc_sram_wrapper` declares its ports with type parameters,

```systemverilog
parameter type addr_t = logic [AddrWidth-1:0],
parameter type data_t = logic [DataWidth-1:0],
...
input  addr_t [NumPorts-1:0] addr_i,
input  data_t [NumPorts-1:0] wdata_i,
```

and instantiates the technology cell `tc_sram` inside. Verilator elaborates
it, the house gate passed, and Vivado 2025.1 reported

```
INFO: [Synth 8-6157] synthesizing module 'tc_sram_wrapper'
INFO: [Synth 8-6155] done synthesizing module 'tc_sram_wrapper' (0#1)
```

with nothing in between: no `synthesizing module 'tc_sram'`, no warning.
The wrapper came out empty, its 37 instances were black boxes, and the
build died at `opt_design` with `[DRC INBB-3] Black Box Instances`
(cache-ip common-ip TASK-003, ref cva6 bin 1). Synthesizing the wrapper
alone says it plainly -- `[Synth 8-3330] design tc_sram_wrapper has an
empty top module` -- and renaming the cell changes nothing; the same cell
with plain vector ports synthesizes to one RAMB36. The cause is the typed
ports: Vivado drops the body of a module whose port types come from
`parameter type` declarations with defaults computed from other parameters.

Rule: ports are plain packed vectors (`logic [NumPorts-1:0][AddrWidth-1:0]
addr_i`), and `parameter type` stays inside a module or in a package typedef
the ports do not depend on. When a vendored block uses typed ports, provide
a plain-vector copy of the thin wrapper beside the consumer (the rig's
`tc_sram_wrapper.sv`), and say so in its PROVENANCE. Diagnosis when a build
dies on black boxes: synthesize the black-boxed module alone out of
context; an empty-top warning there is this failure, a missing-module
warning is a filelist gap.

Related: [[static-loop-bounds]], [[select-on-function-call]] (the other two
constructs Verilator accepts and Vivado does not), [[sram-and-memories]]
(the record-typed array the same build also hit).
