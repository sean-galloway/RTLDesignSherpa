---
title: Consuming library arithmetic
summary: A block built on rtl/math rows is checked against each block's OWN reference model, and a fused op is never split without a bit-equivalence run.
---

# Consuming library arithmetic

A block that instantiates `rtl/math` rows (alu-infer, garuda) inherits each
block's numerics. Two rules follow.

- **Check each row against the library block's own reference model**, at
  that block's own tolerance -- not against a fresh float model. The
  reference classes in `bin/TBClasses/common/fp_testing.py` and
  `bf16_testing.py` are TB classes, but their `compute_expected` methods
  only read format attributes, so a DUT-less instance
  (`cls.__new__(cls)` plus `fmt`) evaluates them; alu-infer's
  `dv/tbclasses/alu_infer_golden.py` is the pattern. A divergence is then
  a wiring bug in the consumer or a bug in the block, never a modeling
  argument -- and the consumer's sweep reaches inputs the block's own test
  skipped.

  *Case (2026-10-20): the alu-infer exp2 row returned 0 for x = max-finite
  bf16 where the reference said +inf. The block was wrong, not the ALU:
  `math_bf16_exp2` saturated a 9-bit signed integer part to `9'sd256`,
  which wraps to -256, so every x >= 256 underflowed (math BUG-009). The
  library test only probed 2^128, which takes the other branch.*

- **Never split a fused operation without a bit-equivalence run.** "Exact
  product, then one fp32 add" reads like `fma(a, b, c)` when the product
  is exact (bf16 x bf16 in fp32), and it is not: a product that overflows
  fp32 against an infinite addend returns NaN where the fused block
  returns the addend, and the fused block passes a subnormal addend
  through where the FTZ adder flushes it. A random-equivalence run over
  4 M vectors found 24,987 differences in minutes (a Verilator `--binary`
  testbench with both forms side by side). alu-infer kept the fused loop
  and put its pipeline depth in operand stages ahead of it instead.
