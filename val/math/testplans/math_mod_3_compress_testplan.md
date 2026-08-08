# Test Plan: math_mod_3_compress

## Module: rtl/math/math_mod_3_compress.sv
## Test File: val/math/test_math_mod_3_compress.py
## Current Coverage: NO DATA in the 2026-08-07 run (see COVERAGE_REPORT.md)

**This plan did not exist until 2026-08-07**, and the module was one of two
with external test-audit findings and no plan of its own.

## Module Overview

Carry-save reduction computing `d_in % 3` combinationally. No clock, no reset.
Depends on `math_adder_carry_save_nbit` from `rtl/math/`, which is why its
filelist `-f` includes the math closure rather than listing sources by hand.

## Scenarios

| ID | Scenario | Description | Tested | Note |
|----|----------|-------------|--------|------|
| M3-01 | Exhaustive sweep | Every value in the 16-bit space | full | `full` is exhaustive: 65536 values |
| M3-02 | Strided sweep | Every 8th / 64th value | func / gate | strided still exercises every carry-save path |
| M3-03 | Residue classes | Results are exactly 0, 1 or 2 | YES | implied by the equality check |

## Depth

`STRIDE = {'gate': 64, 'func': 8, 'full': 1}` -- gate 1024 values, func 8192,
full 65536. The levels differ in exhaustiveness, which is what the knob is for.

## Notes

The TB implements the contract lifecycle as honest no-ops: the DUT is purely
combinational, so `assert_reset`/`deassert_reset` have nothing to drive. They
exist because every TB implements them (/GLOBAL_REQUIREMENTS.md 2.2), and a
caller driving the standard sequence gets correct behaviour rather than a
base-class stub that silently does nothing.
