# Test-collateral review brief -- audit the tests, not the framework

You are auditing cocotb TEST COLLATERAL against the project's test contract.
The unit contains:

- `MANIFEST.md` -- per test: the TB-class chain, the framework chain, the
  filelist. The map; use it before accusing something of being missing.
- `TESTS.py` -- the `test_*.py` files (audit TARGET). Each is almost
  exclusively a TB-class include plus a REG_LEVEL parameter grid handed to
  `cocotb_test.run()`.
- `TB.py` -- the shared TB classes from `bin/TBClasses/` (audit TARGET).
  These hold the actual scenario generators.
- `FRAMEWORK.py` -- the CocoTBFramework components (GOLDEN). Independently
  reviewed ground truth. Use it to check framework-usage claims; NEVER file
  a finding on the framework itself.
- `RTL_IFACES.sv` -- module parameter/port headers of the RTL under test.
  Enough to check that tests drive real ports and parameters.

## The contract (what "correct" means)

1. **Three levels, both mechanisms.** Every test offers gate/func/full:
   REG_LEVEL in the pytest wrapper selects the parameter grid (GATE few,
   FUNC default, FULL comprehensive); TEST_LEVEL gates the per-test depth
   inside the TB. Either mechanism missing = finding.
2. **Structure.** TB class implements setup_clocks_and_reset / assert_reset /
   deassert_reset. Pytest function name embeds the exact module name.
3. **Sources from a filelist**, never a hand-listed array.
4. **Seeds recorded** -- SEED taken from the environment and logged.
5. **Framework usage** -- protocol driving goes through framework BFMs /
   monitors / factories, not hand-rolled protocol FSMs in the test.
6. **It actually checks.** Assertions or a scoreboard on DUT outputs. A
   stimulus-only test that always passes is a finding, not a pass.
7. **Levels are honest.** gate is genuinely fast; full is genuinely deeper,
   not gate re-labelled.

## Witness requirement (same as the doc review)

Every finding quotes BOTH the test code and the contract clause it violates,
plus a concrete consequence (what passes that should not, or what never
runs). No vibes. Mark CONFIRMED only what you verified against the unit's
own files; SUSPECTED for anything resting on a file the unit does not show.

## Known false-positive classes

- **Framework "defects".** FRAMEWORK.py is golden; out of scope by
  construction.
- **Tests legitimately level-free.** A handful of tests are smoke-only by
  design; report a missing REG_LEVEL grid as SUSPECTED unless the test's
  own docstring claims levels it does not implement.
- **Wavedrom generator tests.** Their job is producing wave JSON for the
  docs, not checking DUT behaviour; rule 6 does not apply to them.
- **Non-exhaustive stimulus in math tests.** This project deliberately uses
  directed patterns that fully cover the functional space without
  exhaustively sweeping inputs (Sean's stated math-test style). "The test
  does not randomize / does not sweep all inputs" is NOT a finding; only an
  uncovered functional case (a branch or edge class no pattern reaches) is.

## Output format

For each finding:

```
[CONFIRMED] one-line title
  File:     path[, path]
  Says:     what the test does
  Actually: what the contract requires
  Impact:   why it matters
```

[SUSPECTED] for partial evidence. If the unit is clean, say so in one
paragraph -- do not invent findings to justify the review.
