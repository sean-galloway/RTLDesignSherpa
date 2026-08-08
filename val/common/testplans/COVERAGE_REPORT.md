# Coverage Report - val/common

**Measured 2026-08-08.** Verilator line/toggle: `COVERAGE=1 make run-all-full`
then `make coverage-report`. 943 tests, 943 `coverage.dat` merged.

## Headline

| Metric | Result | Target |
|---|---|---|
| Line, as Verilator reports it | **95.3%** (876/919) | 80% |
| Line, executable statements only | **95.7%** (399/417) | - |
| rtl/common modules with data | 48 of 49 | 49 |
| Files at 100% | 34 | - |
| Uncovered STATEMENTS remaining | **20** | - |

`arbiter_single_client.sv` is the one module without data, by decision: its
only instantiation anywhere is in STREAM, so it is verified a level up.

## The remaining 20 statements are unreachable under Verilator

Not "not yet written" -- unreachable by construction in this simulator. Three
classes, all verified rather than assumed:

**1. Nested-statement attribution (10 statements).** `find_first_set`,
`find_last_set`, `encoder_priority_enable`, `arbiter_priority_encoder`,
`leading_one_trailing_one`. The bodies of `if` statements inside unrolled
`always_comb` loops report zero hits while their guards report thousands:

    %000003         for (int i = 0; i < WIDTH; i++) begin
     010936             if (data[i] && !w_found) begin
    %000000                 index = i[N-1:0];
    %000000                 w_found = 1'b1;

`leading_one_trailing_one` proves it outright -- there the `if` shows **0**
while the body inside it shows **136628**. The modules work and their tests
check the results; Verilator's line attribution simply does not follow into
these blocks. **No test can cover these. Do not write one.**

**2. `default:` arms for X (7 statements).** `shifter_universal` (4),
`shifter_barrel` (2), `hex_to_7seg` (1). Every legal select value is covered,
so these arms exist solely to hold state or blank a display on an X input --
and **Verilator is a 2-state simulator**, so X never reaches them.

A test was written for `shifter_universal`'s arm on 2026-08-08 and REMOVED the
same day: driving `BinaryValue('xx')` resolved to a defined value, so the arm
stayed at zero hits while the test passed -- it was silently exercising
`select=00`, the hold case, and asserting that state was held. A test that
passes by testing something other than its name is worse than no test.
Reaching these needs a 4-state simulator or a formal property.

**3. Elaboration-time functions (3 statements).** `counter_freq_invariant`'s
`linear_freq` guard and the two `case` arms that select between the frequency
strategies. The LUT is built at elaboration; runtime line instrumentation does
not reach it. The functions themselves ARE exercised -- covering POW2 moved
this module from 71.1% to 89.5%.

**Conclusion: line coverage for val/common is complete.** What is left is
tooling behaviour, not test debt.

## What this exercise fixed to get here

Three defects had to be repaired before any number was trustworthy, and each
reported a plausible figure while measuring less than it claimed:

1. **Coverage was never collectable.** `conftest.py` honoured `COVERAGE=1` and
   0 of 48 wrappers passed Verilator the flags. First run: `Line: 0.0%`.
2. **The merge dropped files.** One `verilator_coverage --write` over 925
   `.dat` files annotated 42 sources; the same data in batches annotated eight
   more. Now batched with a per-point union.
3. **One wrapper built outside the glob.** `test_mod_3_compress.py` wrote to
   `logs/`, escaping both the merge and `make clean-all`.

And two real scenario gaps were closed (COMMON-021):

- **`counter_bin_load` 67.9% -> 92.9%.** The entire `add_enable` branch was
  dead -- the test only ever incremented by one. Now exercises variable
  increment across both the wrapping and non-wrapping arms, plus the
  load > add > enable priority.
- **`counter_freq_invariant` 71.1% -> 89.5%.** `FREQ_STRATEGY` was pinned at
  LINEAR, so `pow2_freq` was never elaborated. It is a grid dimension now, and
  a single-entry LUT config was added for the degenerate `NUM_FREQ_ENTRIES=1`
  case the RTL explicitly supports.

## Protocol (functional) coverage: 0.0%

Still reported as FAIL against an 80% target, and still fed by nothing in this
area -- that path is for monbus packet-type matrices. Either wire it or scope
the target. A permanently red metric trains people to ignore the report, which
is how coverage stayed broken here for as long as it did.
