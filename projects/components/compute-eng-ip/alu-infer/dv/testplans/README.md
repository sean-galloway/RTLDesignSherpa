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

# ALU-INFER Testplan Directory

YAML testplan mapping the functional test scenarios to Verilator coverage
points for the ALU-INFER block. Format follows
`projects/components/dma-ip/stream/dv/testplans/` conventions (which follow
`val/amba/testplans/`).

## Testplans

| Testplan | Modules | Status | Test File |
|----------|---------|--------|-----------|
| `alu_infer_top_testplan.yaml` | alu_infer_top.sv and its 12 submodules (rows, pipe, acc, decode, delay, the four format row families, act, pwl, cvt) | Tested | `../tests/test_alu_infer.py` |

One testplan covers the whole pipeline: the RTL modules are a single
inseparable unit (top wiring + row compute + tag-FIFO alignment pipe + FP32
accumulator) and are only meaningful tested together through the top-level
GAXI interfaces. This is the same multi-module pattern as stream's
`axi_engines_testplan.yaml`.

## Scenarios (25)

All scenarios run at gate/func/full across PIPE_DEPTH {4, 8} on the default
build; the timing and accumulator scenarios also run on the `deep` and `flat`
latency builds, and the v1 suite plus the illegal sweep on the `lean` build
(every `EN_*` off). The mixed soak
additionally sweeps the standard `GAXI_RANDOMIZER_CONFIGS` delay profiles at
func (`fast`, `slow_producer`, `slow_consumer`, `gaxi_realistic`,
`gaxi_backpressure`) and full (adds `constrained`, `burst_pause`,
`high_throughput`, `gaxi_stress`). The per-type default is `backtoback`.

| ID | TEST_TYPE | What it proves |
|----|-----------|----------------|
| ALUINF-01 | copy_timing | Handshake shell, copy opcode, natural per-row latency, in-order II=1 |
| ALUINF-02 | add_sub | BF16 add/sub lanes vs float RNE golden (1-ULP library contract) |
| ALUINF-03 | mul | BF16 mul lanes vs float RNE golden (1-ULP library contract) |
| ALUINF-04 | minmax | Min and max sub-ops, both lanes |
| ALUINF-05 | compare | Compare vs B and vs threshold_imm; mask packed low in result_flags |
| ALUINF-06 | relu | ReLU incl. negative, -0, +0, -inf, NaN |
| ALUINF-07 | mac | MAC CLEAR/ACC/DRAIN/HOLD vs FP32 accumulator golden |
| ALUINF-08 | backpressure | Elastic hold: tag FIFO fills, issue stalls, in-order resume |
| ALUINF-09 | error_opcode | Reserved opcode retires in order, returns zero |
| ALUINF-10 | special_grid | Special-value grid across add/sub/mul/minmax/compare/relu |
| ALUINF-11 | mixed_soak | Random mixed opcodes, in-order golden check, timing-profile sweep |
| ALUINF-12 | sub_ulp_corner | Directed SUB corner at the library adder's 1-ULP boundary |
| ALUINF-13 | tag_join | Tag-FIFO arrival join: fast rows wait behind an earlier slow row |
| ALUINF-14 | fmt_int8 | int8 rows (saturating add/sub/mul, min/max, compare, relu, const) |
| ALUINF-15 | fmt_fp32 | fp32 rows on the IEEE 754-2008 blocks vs library references |
| ALUINF-16 | fmt_fp8 | fp8 e4m3 rows vs library references |
| ALUINF-17 | const | immediate broadcast in every format |
| ALUINF-18 | act | library activations (bf16/fp32/fp8) and bf16 recip/exp2/log2/qscale |
| ALUINF-19 | cvt | every CVT pair (narrow/widen packing) and ALTFMT |
| ALUINF-20 | reduce | REDUCE sum/max, identity CLEAR, cross-lane fold, every format |
| ALUINF-21 | mac_formats | MAC in int8 (requantize), fp32, fp8 |
| ALUINF-22 | mac_chain | >100-step dependent bf16 MAC chain at II=1 |
| ALUINF-23 | pwl | PWL LUT load, read-back, bit-exact evaluation, accuracy bound |
| ALUINF-24 | latency | each result port at its parameterized latency |
| ALUINF-25 | softmax | the roadmap rows composed into softmax vs float |

## covers_lines Are Generated From Data

`covers_lines` in the testplan are **not hand-maintained**: each scenario's
list is the covered-line set of that scenario's own merged coverage data
(`verilator_coverage --annotate` numbering — the same semantics the verifier
checks with), unioned across the RTL files, levels, PIPE_DEPTHs, and
timing profiles.

Regenerate after RTL or test changes:

```bash
# 1. Fresh coverage run (writes per-test coverage.dat under local_sim_build/
#    and coverage_data/merged/latest_merged_coverage.dat)
cd projects/components/compute-eng-ip/alu-infer/dv/tests
rm -rf local_sim_build coverage_data
COVERAGE=1 make run-all-func-parallel

# 2. Regenerate the YAML (per-scenario merges + annotate; paths resolve
#    from the script's location, run from anywhere)
python3 projects/components/compute-eng-ip/alu-infer/dv/testplans/gen_alu_infer_testplan.py
```

The checked-in generator (`gen_alu_infer_testplan.py`, beside this README)
merges the per-TEST_TYPE coverage.dat files with `verilator_coverage
--write`, annotates, extracts covered lines and port hit counts, and emits
the YAML. Hand-edit only the `SCENARIOS` description table at the top when
a TEST_TYPE is added or retargeted, then re-run and re-verify.

## Verify

```bash
# Scenario line-coverage check against the latest merged coverage data
python3 bin/cov_utils/verify_testplan_coverage.py --all \
    projects/components/compute-eng-ip/alu-infer/dv/testplans/ \
    projects/components/compute-eng-ip/alu-infer/dv/tests/coverage_data/merged/ \
    --strict
```

Expected: 25/25 scenarios VERIFIED. The repo-wide ref ratchet
(`bin/filelist_registry.py --check`) separately guarantees the testplan's
`rtl_files`/`test_file` refs resolve.

## Notes

- The multi-line-statement caveat: Verilator records a statement's coverage
  point at its continuation line while `--annotate` displays the count on the
  statement's first line. The generated `covers_lines` use the annotate
  numbering, so they match the verifier exactly.
- `~`-prefixed (partially covered) annotate lines count as covered when the
  hit count is > 0 — the verifier's documented rule.
- The math-library internals (`math_bf16_adder`, `math_bf16_multiplier`,
  `math_bf16_fma`, Han-Carlson adders, CLZ) appear in the merged coverage but
  belong to the `rtl/math` area's own testplans; they are intentionally out
  of scope here.
