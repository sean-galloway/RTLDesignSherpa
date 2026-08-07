# Coverage Report - val/common

**Measured 2026-08-07.** Verilator line/toggle, `COVERAGE=1 make run-all-full`
followed by `make coverage-report`. 925 tests, 925 `coverage.dat` files, 922
merged.

## Headline

| Metric | Result | Target |
|---|---|---|
| Line (Verilator) | **92.8%** | 80% |
| RTL files with data | 40 of 49 modules | 49 |
| Files at 100% | 20 | - |
| Files below 90% | 10 | 0 |

## This is the area's FIRST line-coverage measurement

Not "first in a while" -- the first. Every prior coverage figure in these test
plans (`~85%`, `~90%`, `100% (VERIFIED 2026-01-17)`) was written without a
measurement behind it, because **coverage was never collectable here**:

    wrappers calling get_coverage_compile_args: 0 of 48

`COVERAGE=1` was honoured by `conftest.py` and documented in its docstring, and
`make coverage-report` existed and ran -- but no wrapper ever passed Verilator
the `--coverage` flags, so no `coverage.dat` was ever written. The first run of
this exercise reported `Line: 0.0% (.dat merged: 0)` and passed 925 tests while
measuring nothing. All 48 wrappers now extend `extra_args` with
`get_coverage_compile_args()`.

That is the same defect class the test audit kept finding: a mechanism that
exists, is documented, is invoked, and does nothing.

## Files below 90%

| File | % |
|---|---|
| counter_bin_load.sv | 64.3% |
| counter_freq_invariant.sv | 71.1% |
| shifter_lfsr.sv | 78.9% |
| find_last_set.sv | 80.0% |
| find_first_set.sv | 80.0% |
| pwm.sv | 80.0% |
| encoder_priority_enable.sv | 83.3% |
| shifter_lfsr_fibonacci.sv | 84.2% |
| leading_one_trailing_one.sv | 87.5% |
| shifter_universal.sv | 89.5% |

## Gap: 10 modules produced no coverage rows

These have tests and passed, but contributed no line-coverage data to the
merge, so the 92.8% above is computed over 40 files rather than all 49:

`arbiter_single_client.sv`, `counter_bin.sv`, `counter_ring.sv`, `counter.sv`, `dataint_parity.sv`, `debounce.sv`, `fifo_sync.sv`, `mod_3_compress.sv`, `reverse_vector.sv`, `sync_pulse.sv`

**This is not evidence that they are uncovered** -- it is a hole in the
collection or merge path that has to be chased before the headline number can
be called complete. `counter_bin.sv` is the sharpest case: it was the first
wrapper wired, and a manual run confirmed it writes `coverage.dat`, yet it is
absent from `line_files`.

## Protocol (functional) coverage: 0.0%

Reported as FAIL against an 80% target. The protocol-coverage path is for
monbus packet-type matrices and similar, and nothing in `val/common` feeds it.
Either wire it or scope the target to the areas it applies to; a permanently
failing metric nobody acts on is noise.

## Next

1. Chase the 10 absent modules -- collection or merge, not RTL.
2. Triage the 10 files below 90% into per-module plan scenarios.
3. Decide whether protocol coverage applies to this area at all.
