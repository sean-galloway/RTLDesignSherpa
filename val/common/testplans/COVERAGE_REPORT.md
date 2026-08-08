# Coverage Report - val/common

**Measured 2026-08-07.** Verilator line/toggle: `COVERAGE=1 make run-all-full`
then `make coverage-report`. 925 tests, 932 `coverage.dat` files merged.

## Headline

| Metric | Result | Target |
|---|---|---|
| Line (Verilator) | **93.4%** | 80% |
| rtl/common modules with data | **48 of 49** | 49 |
| Files at 100% | 32 | - |
| Files below 90% | 10 | 0 |

The one module without data is `arbiter_single_client.sv`, and that is a
decision rather than a gap: its only instantiation anywhere is
`projects/components/dmas/stream/rtl/macro/scheduler_group_array.sv:434`, so it
is exercised one level up in STREAM and wants no val/common test (Sean,
2026-08-07). Recorded in `bin/filelists.toml`'s exempt ledger.

## This was the area's first line-coverage measurement, and it took three fixes

**1. Coverage was never collectable.** `conftest.py` honoured `COVERAGE=1`,
documented it, and re-exported `get_coverage_compile_args` -- and 0 of 48
wrappers called it, so Verilator never got `--coverage` and no `coverage.dat`
was ever written. The first attempt passed 925 tests and reported
`Line: 0.0% (.dat merged: 0)`.

**2. The merge silently dropped files.** A single
`verilator_coverage --write` over all 925 `.dat` files annotated 42 sources;
the same data in batches annotated those plus seven more -- `counter_bin`,
`counter`, `counter_ring`, `dataint_parity`, `debounce`, `fifo_sync`,
`reverse_vector`. Merging `counter_bin`'s 24 files alone works; adding the rest
makes it vanish. The merge now runs in batches and unions per POINT, so a
module exercised by several tests gets credit for every hit rather than the
best single batch.

**3. One wrapper built outside the glob.** `test_mod_3_compress.py` wrote its
build under `logs/` instead of `local_sim_build/`, so its coverage never
reached the merge -- and `make clean-all` never cleaned it either, leaving
stale `.dat` files behind. Conformed to the area convention.

Each of these reported a plausible number while measuring less than it claimed.

## Files below 90%

| File | % |
|---|---|
| math_adder_carry_save_nbit.sv | 0.0% |
| mod_3_compress.sv | 16.7% |
| counter_bin_load.sv | 67.9% |
| counter_freq_invariant.sv | 71.1% |
| find_last_set.sv | 80.0% |
| find_first_set.sv | 80.0% |
| encoder_priority_enable.sv | 83.3% |
| leading_one_trailing_one.sv | 87.5% |
| shifter_lfsr.sv | 89.5% |
| shifter_universal.sv | 89.5% |

## Protocol (functional) coverage: 0.0%

Reported as FAIL against an 80% target. That path is for monbus packet-type
matrices and similar, and nothing in `val/common` feeds it. Either wire it or
scope the target to the areas it applies to -- a permanently failing metric
nobody acts on is noise.

## Next

1. Triage the 10 files below 90% into per-module plan scenarios. Worst:
   math_adder_carry_save_nbit.sv (0.0%), mod_3_compress.sv (16.7%), counter_bin_load.sv (67.9%).
2. Decide whether protocol coverage applies to this area at all.
