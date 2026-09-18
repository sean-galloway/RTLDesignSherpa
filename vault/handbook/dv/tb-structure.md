---
title: TB structure
summary: How one module's verification is composed - the wrapper owns the
  parameter grid, a separate TB class owns the stimulus, and REG_LEVEL x
  TEST_LEVEL turn one module into a graded matrix. Worked end to end on
  val/common/counter_bin.
---

# TB structure

Verifying one module means writing **two** files, not one. [[test-runner]] is
the reference for the four-layer stack; this note is the walkthrough - how the
pieces are composed, using `counter_bin` because it is small enough to hold in
your head and every `val/common` test is the same shape.

    val/common/test_counter_bin.py        the runner: parameter grid + run()
    bin/TBClasses/common/counter_bin_tb.py  the TB: stimulus and checks

## The runner holds the grid; the TB holds the test

The split is not cosmetic. `counter_bin_tb.py` says so in its own header:

> Extracted from `val/common/test_counter_bin.py` so the runner holds only the
> parameter grid and the `cocotb_test.run()` call.

A runner that grows stimulus into it becomes unreadable at 27 parameter
combinations, and the stimulus becomes untestable anywhere else. Keep the
runner boring: build a matrix, name a build directory, launch.

The handoff is four lines, and it is the whole of Pattern A:

    @cocotb.test(timeout_time=30000, timeout_unit="us")
    async def counter_bin_test(dut):
        tb = CounterBinTB(dut)
        passed = await tb.run_all_tests()
        assert passed, f"Counter bin test FAILED - {len(tb.test_failures)} failures"

`run()` is given `module` (the runner's own basename) and `toplevel`, and for
Pattern A **no** `testcase=` - cocotb discovers the one `@cocotb.test()` in the
module. Two cocotb tests in one runner without `testcase=` is a real defect
with a real scar; see [[test-runner]].

- **Pattern A** (`val/common`, `val/amba`): plain `@cocotb.test()` functions
  plus a pytest wrapper.
- **Pattern B** (`projects/components/**`): cocotb functions prefixed
  `cocotb_test_*`, each pytest wrapper selecting one via `testcase=`.
- **Never mix them in one file.**

TB classes live in the project area (`projects/<comp>/dv/tbclasses/`); only
genuinely shared infrastructure belongs in `bin/TBClasses/`. Every TB class
implements `setup_clocks_and_reset` / `assert_reset` / `deassert_reset`, and
configures before reset where a block latches config during reset. Pytest
function names embed the exact module name - generic names collide across
related modules.

## Parameters are how one module becomes many tests

The runner builds a list of tuples and hands it to `parametrize`. Each tuple is
one test, one Verilator build, one log:

    def generate_params():
        reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
        if reg_level == 'GATE':
            params = [(5, 10, 'gate'), (8, 128, 'gate')]
        elif reg_level == 'FUNC':
            widths, maxs, test_levels = [4, 5, 8], [8, 10, 16], ['gate']
            ...
        else:  # FULL
            widths, maxs, test_levels = [4, 5, 8], [8, 10, 16], ['gate', 'func', 'full']
        return params

    @pytest.mark.parametrize("width, max_val, test_level", generate_params())
    def test_counter_bin(request, width, max_val, test_level):

Three things to copy from this, all load-bearing:

1. **Illegal combinations are pruned in the generator**, not asserted in the
   TB: `counter_bin` keeps only `max_val < (1 << (width - 1))` because the MSB
   is special. That is why FULL is 27 and not 3x3x3=27-minus-nothing - the
   prune is what keeps the grid honest.
2. **Every axis that changes the elaboration goes in the identifier.**
   `test_name_plus_params = f"test_counter_bin_w{width}_max{max_val}_{test_level}_{reg_level}"`
   derives the build dir, the log and the results XML. This uniqueness is the
   entire mechanism that makes `-n 48` safe ([[test-runner]]).
3. **RTL parameters and env are different channels.** The `parameters` dict
   (`WIDTH`, `MAX`) reaches Verilator and changes the hardware; the
   `extra_env` dict (`TEST_LEVEL`, `TEST_WIDTH`, `TEST_MAX`, `SEED`) reaches
   the TB and changes the stimulus. The same width appears in both, for
   different reasons.

Timeouts scale off the level rather than being one flat number:
`timeout_multipliers = {'gate': 1, 'func': 3, 'full': 6}`, times a factor from
the parameters themselves. A test that times out only at FULL is usually a
missing multiplier, not a hang.

## gate / func / full, as val/common actually uses them

`REG_LEVEL` selects the grid; `TEST_LEVEL` sets the depth of each cell. They
are independent and **both are a hard requirement** - the rule, the rationale
and the 2026-08-01 audit are in [[test-runner]].

For `counter_bin` the grid is 2 / 9 / 27. Measured across the whole area
(2026-09-17):

| REG_LEVEL | val/common cells |
|---|---|
| GATE | 77 |
| FUNC | 220 |
| FULL | 945 |

The spread is deliberately uneven - at FULL, `dataint_crc` (250),
`shifter_beat_pack` (165) and `dataint_parity` (96) are over half the area,
because those are the modules where combinations genuinely buy coverage.
Do not "balance" a grid; size it to what the module needs.

The TB reads the depth knob in `__init__`, validates it, and says so:

    self.TEST_LEVEL = os.environ.get('TEST_LEVEL', 'gate').lower()
    if self.TEST_LEVEL not in ('gate', 'func', 'full'):
        self.log.warning(f"Invalid TEST_LEVEL '{self.TEST_LEVEL}', using 'gate'")
        self.TEST_LEVEL = 'gate'
    self.log.info(f"SEED={self.SEED}, TEST_LEVEL={self.TEST_LEVEL}")

**That banner is the evidence.** Three cells logging the same level are one
cell wearing three names, which is how a re-labelled tier gets caught.

Depth then has to vary *measurably*, not decoratively. In `CounterBinTB`:

| | gate | func | full |
|---|---|---|---|
| `test_basic_counting` cycles | 20 | up to 100 | 2x full sequence |
| `test_wrap_behavior` | skipped | runs | runs |
| `test_edge_cases` | skipped | skipped | runs |

Skipping whole phases at gate is legitimate and preferred over running them
shallowly - but a `full` tier that is `func` re-labelled is the defect this
whole mechanism exists to prevent.

## val/common hand-rolls its generators; the component areas do not

All 48 `val/common` runners read `REG_LEVEL` directly and build the grid inline,
as above. **None of them use `reg_level_grid()` / `level_env()`** from
`TBClasses.shared.test_levels` - that shared helper is what the converted
component areas use, and it exists because those areas also had to remove a
conftest `TEST_LEVEL` stamp that silently beat every per-cell export.

Both forms are correct. Do not "fix" a `val/common` runner into the helper
form in isolation, and do not copy a `val/common` runner as the template for a
component area. The conversion rule, the stamp trap, and the requirement that
an area converts in one commit are in [[test-runner]].

## The bar

100 percent pass. Partial success is a bug, not tolerance. For complex modules
write ONE comprehensive test graded by `TEST_LEVEL`, not a family of
near-duplicate tests. Use background-monitor coroutines for asynchronous
outputs - point checks miss data that lands between them.

Related: [[test-runner]], [[running-regressions]], [[silent-fallbacks]],
[[seeds-and-determinism]].

Authority: /GLOBAL_REQUIREMENTS.md section 2.
