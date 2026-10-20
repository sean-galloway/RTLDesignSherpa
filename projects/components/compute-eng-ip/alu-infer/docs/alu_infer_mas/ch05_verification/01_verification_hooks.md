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

# Verification Hooks and Observability

The tests live in `alu-infer/dv/`. `tbclasses/alu_infer_tb.py` is the
testbench (`AluInferTB` on the repo's `TBBase`), with the extended
scenarios mixed in from `alu_infer_ext_tests.py`. `alu_infer_golden.py`
holds the golden models, and `tests/test_alu_infer.py` is a thin
`TEST_TYPE` dispatcher (the stream-area standard pattern).

Both valid/ready interfaces are owned by RDS-DV GAXI BFMs: a `GAXIMaster`
drives issue, a `GAXISlave` receives results, and passive `GAXIMonitor`s
record both. Timing checks use the BFMs' packet timestamps. The extended
scenarios issue invocations as bursts, so the elastic pipeline streams
while every retired line is checked.

## The Golden Models: the Library's Own

Every floating-point row instantiates an `rtl/math` block, so its expected
value comes from **the same reference model that block's unit test uses**
(`bin/TBClasses/common/fp_testing.py`, `bf16_testing.py`), at that test's
tolerance. Exact rows (copy, const, min/max, relu) must match exactly;
arithmetic rows within 1 ULP; reciprocal 2, exp2 and log2 16 (log2 200
near zero), as their library tests allow. This is the MAS's built-in
cross-check made literal: an ALU/library divergence is a wiring bug in
exactly one of them.

It has already paid off. The exp2 row's check exposed **math BUG-009**:
`math_bf16_exp2` returned 0 for every x ≥ 256, because a 9-bit signed
"+256" saturate wrapped to −256. It was fixed in `rtl/math`, and the
library's own test gained the cases that failed.

- **int8**: the exact saturating model (no library family).
- **Accumulators**: the bank is modeled bit-exactly for bf16, fp8 and int8
  (the `math_bf16_fma` contract, including its FTZ of an underflowing
  product). The fp32 bank is checked against the library FMA reference at
  its tolerance and then re-synced from the DUT, which presents the fp32
  bank exactly.
- **PWL**: bit-exact against the row model in `bin/alu_infer_pwl.py`, plus
  an approximation bound per function (Table 2.7, with margin).

## Scenarios

| TEST_TYPE | Proves |
|---|---|
| copy_timing, tag_join, backpressure | handshake, natural latency, II=1, the tag join, the elastic hold |
| add_sub, mul, minmax, compare, relu, special_grid, sub_ulp_corner | the v1 bf16 rows, special-value grid, the adder's 1-ULP corner |
| mac, mac_chain | bf16 CLEAR/ACC/DRAIN/HOLD; a 104–512-step dependent chain at II=1, every step exact |
| fmt_int8, fmt_fp32, fmt_fp8 | every elementwise row per format, specials and random values |
| const, act, cvt, pwl | const in every format; activations; every CVT pair and ALTFMT; PWL load, read-back, evaluation and accuracy |
| reduce, mac_formats | REDUCE sum/max with identity CLEAR and fold, every format; MAC in int8/fp32/fp8 |
| latency | each port at its parameterized latency, every format that uses it; in-order retirement behind the slowest port |
| error_opcode | every illegal class retires a zero line in order and pulses `err_opcode` exactly once |
| mixed_soak | random mixed opcodes under the GAXI delay profiles |
| softmax | the roadmap rows composed as a program would: REDUCE max + fold, SUB, PWL exp, REDUCE sum + fold, RECIP, MUL, each step fed by the last; within 2e-2 of float softmax (measured 1.6e-3) |

: Table 5.1: test scenarios

## Build Configurations

| Config | Parameters | Runs |
|---|---|---|
| default | RTL defaults (`ADDER_LATENCY` 3, `MUL_LATENCY` 0, `MAC_LATENCY` 0) | every scenario at `PIPE_DEPTH` 4 and 8 |
| deep | `ADDER_LATENCY` 4, `MUL_LATENCY` 2, `MAC_LATENCY` 2 | the timing and accumulator scenarios |
| flat | every latency 0 | the timing and accumulator scenarios (exercises the latency-0 tag bypass) |
| lean | every `EN_*` off | the v1 suite, and every built-out family must decode illegal |

: Table 5.2: build configurations

The house gate/func/full grid applies: gate runs every cell lightly, and
func and full deepen the value sets and chains and sweep the mixed soak
across the standard GAXI delay profiles.

## Coverage Matrix

| Axis | Values |
|------|--------|
| Opcode × format | every legal pair of Table 2.2; every illegal class |
| Special-value class | ±0, ±inf (fp8: ±max-normal), NaN, ±min-subnormal, ±1, per format (`special_value_grid`) |
| Lane position | every lane of every format |
| Accumulator | CLEAR/ACC/DRAIN/HOLD; chains over 100 steps; REDUCE fold sum and max |
| Latency | 0, the defaults, and deep for each port |

: Table 5.3: coverage matrix

`dv/testplans/alu_infer_top_testplan.yaml` maps each scenario to the RTL
lines its own merged coverage data covers (generated, never hand-edited),
and `bin/cov_utils/verify_testplan_coverage.py --strict` re-checks it.

## Observability

- **No internal monitor taps.** Observability is the Ocelus MonBus plane's
  job.
- **State is readable through the seam**: the accumulator by DRAIN and the
  PWL table by `OP_PWL_LUT` read.
- **M2** (whether the library blocks' IEEE exception outputs should reach
  `result_flags`) stays open; `err_opcode` covers illegal invocations only.

---

**Last Updated:** 2026-10-20
