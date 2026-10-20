---
title: No select on a function call
summary: f(x)[0] lints and simulates clean in Verilator; it is not IEEE 1800, and Vivado refuses it.
---

# No select on a function call

A bit- or part-select applied straight to a function's return value
(`f_sb(addr, seed)[0]`, `f(x)[7:0]`) is not legal SystemVerilog: IEEE 1800
allows selects on variables and nets, not on a call. Verilator accepts it --
with `-Wall`, without a warning -- and simulates it, so a block can pass its
whole test suite and then stop synthesis:

    ERROR: [Synth 8-12513] select on function call violates IEEE 1800 syntax

Give the result a name first:

```systemverilog
logic [31:0] w_uq_h;
assign w_uq_h = f_sb(t_addr ^ 32'h7F4A_7C15, cfg_hash_seed);
assign w_uq   = ... && w_uq_h[0];
```

A width cast of the whole call (`8'(f(x))`) is legal and is fine.

**Checked mechanically:** `bin/check_sv_call_select.py` (unit tests in
`bin/tests/test_check_sv_call_select.py`) runs on staged `.sv` files in the
pre-commit hook, over a build's whole filelist closure in `make lint`
(`lint-call-select`, packages and generated code included), and on every
`.sv` in CI. The tree had none when it landed; it stays at none.

Found 2026-10-19 in `axi_stress_mst_{rd,wr}` (the AXI5 IDUNQ pick): 63/63
pair-test cells and a 9/9 harness simulation passed, and the first Vivado run
failed at read time. Same family as [[static-loop-bounds]] and the
context-sized subtraction in [[sizing-invariants]]: Verilator is not a
synthesis-legality check, so a change to synthesizable RTL is not done until
Vivado has read it (a `make bitstream` or the area's synth lint).
