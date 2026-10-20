# TASK-009: alu-infer testplan coverage map + standard delay-profile sweep

**Priority:** P2
**Status:** CLOSED 2026-10-20
**Owner:** sean galloway

## Why

Two owner directives:

1. Scaffold the `dv/testplans/` coverage map for alu-infer (the stream areas
   carry one per module; alu-infer had none), make it robust, and ensure the
   existing tests are hitting it.
2. The timing-profile sweep must use the standard delay configs from
   `GAXI_RANDOMIZER_CONFIGS` (bin/TBClasses/amba/amba_random_configs.py) —
   b2b, fast, the producer/consumer delays, etc. — not an ad-hoc subset.

## What

- `dv/testplans/alu_infer_top_testplan.yaml`: one multi-module testplan
  (top + rows + pipe + acc, the axi_engines pattern — the pipeline is one
  inseparable unit tested through the top's GAXI interfaces). 13
  functional_scenarios (ALUINF-01..13, one per TEST_TYPE), port
  coverage_points with real hit counts, parameters block.
- `covers_lines` are **generated from data**, not hand-maintained:
  `dv/testplans/gen_alu_infer_testplan.py` merges each scenario's own
  coverage.dat files (`verilator_coverage --write`), annotates, and records
  the covered lines in annotate numbering — the same semantics
  `bin/cov_utils/verify_testplan_coverage.py` checks with. Regeneration flow
  documented in `dv/testplans/README.md`.
- Runner sweep now uses standard profiles: FUNC sweeps mixed_soak over
  `fast`, `slow_producer`, `slow_consumer`, `gaxi_realistic`,
  `gaxi_backpressure`; FULL adds `constrained`, `burst_pause`,
  `high_throughput`, `gaxi_stress`. Per-type default remains `backtoback`.
- Verifier bug fix (shared tool): `verify_testplan_coverage.py`'s annotate
  regex `[ %]` missed the `~` prefix (partially-covered line — some toggle
  points hit, some not). Any line with hit count > 0 is covered per the
  tool's own documented rule; regex now `[ %~]`. Only widens covered sets —
  other areas' verdicts can improve, never regress.
- MAS ch05 names the testplan, the verify command, and the profile list.

## Evidence

- `COVERAGE=1 make run-all-func-parallel` (fresh build dirs): **62/62 pass**
  (13 types x {gate,func} x PIPE_DEPTH {4,8} + 5 soak profiles x 2 levels).
- `verify_testplan_coverage.py --all .../testplans/ .../coverage_data/merged/
  --strict`: **13/13 scenarios VERIFIED**, exit 0.
- `bin/filelist_registry.py --check`: testplan ref ratchet PASS (new
  testplan's rtl_files/test_file refs resolve).
- All 13 alu_infer_top ports covered (hit counts in the YAML).

## Notes

- Multi-line-statement caveat found during bring-up: Verilator records a
  statement's coverage point at its continuation line while `--annotate`
  displays the count on the statement's first line. The generator uses
  annotate numbering so the testplan and verifier agree by construction.
- math-library internals (math_bf16_*, Han-Carlson, CLZ) show up in the
  merged coverage but belong to the rtl/math area's own testplans — out of
  scope here by design.
