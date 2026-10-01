# TASK-025: cocotb 2.x needs cocotb-bus 0.3.0 and a `.value.integer` sweep -- the blocker is measured, not guessed

**Priority:** P3
**Status:** open -- steps 1-3 DONE and RELEASED as cocotb-framework 0.6.9. Step 4 shows cocotb 2.x is reachable for ONE suite, not broadly: three further layers measured below.
**Owner:** TBD
**Filed:** 2026-10-01 (question 2 of [[TASK-020]], split out as that task instructed)

cocotb 2.x has been "never tested" since the 2026-09-30 outage. It has now been
tested. This is what it would actually take.

## Measured, in an isolated venv

Every row below was run, not predicted. The venv was built from
`requirements.txt` and moved one package at a time.

| Configuration | Result |
| --- | --- |
| cocotb 2.1.0 + cocotb-test 0.3.0 + **cocotb-bus 0.2.1** | **Collection dies.** `ModuleNotFoundError: No module named 'cocotb.decorators'` |
| cocotb 2.1.0 + cocotb-test 0.3.0 + **cocotb-bus 0.3.0** | Imports clean; suite RUNS: **40 passed / 15 failed** (`dma-ip/stream`) |

**The import blocker is cocotb-bus, not CocoTBFramework**, which nobody had
established. `cocotb_bus/drivers/__init__.py:13` does
`from cocotb.decorators import coroutine`; 2.x removed that module. The chain
reaching it is
`CocoTBFramework.components.gaxi.gaxi_master` -> `from cocotb_bus.drivers import
BusDriver`. cocotb-bus **0.3.0 is already on PyPI** and fixes it outright.

## What remains, and it is one dominant cause

With the import fixed, the failures are overwhelmingly one thing:

    AttributeError: 'Logic' object has no attribute 'integer'      (1896)

cocotb 2.x returns a `Logic`/`LogicArray` from `handle.value`; `.value.integer`
no longer exists. Example site, `CocoTBFramework/components/gaxi/gaxi_slave.py:393`:

    self.valid_sig.value.integer == 1 and

Two deprecations ride along. They are warnings today and errors eventually:

    DeprecationWarning: The 'units' argument has been renamed to 'unit'.   (1884)
    DeprecationWarning: Use `handle.set(Immediate(...))` ... instead.      (1152)

## Size

| Where | `.value.integer` | `units=` |
| --- | --- | --- |
| CocoTBFramework (RTLDesignSherpa-DV) | 60 sites, 8 files | 43 sites |
| This repo's own TB code | 18 sites, 7 files | -- |

Mechanical but wide, and it spans **both repositories**.

## A cap of our own is on the critical path

RTLDesignSherpa-DV `pyproject.toml:50` currently reads

    "cocotb-bus>=0.2.1,<0.3",

added 2026-09-30 (commit `ed6defb`), with a stated reason: 0.2.x
`cocotb_bus._add_signal` case-sensitivity behaviour that the framework relies on.
**That cap forbids the exact version that unblocks cocotb 2.x.** It was correct
for cocotb 1.x and it is the first thing this task has to revisit -- specifically,
whether 0.3.0 kept the case-sensitivity behaviour the cap was protecting. Do not
simply lift it; establish that first, because the cap exists for a measured
reason and not a defensive one.

## Suggested order

1. **Settle the cocotb-bus cap.** Does 0.3.0 preserve the `_add_signal`
   case-sensitivity behaviour? If yes, the cap becomes `>=0.3.0` and cocotb 1.x
   must be re-verified against it (0.3.0 under cocotb 1.9.2 is **untested** --
   the pilot only exercised it under 2.x).
2. **Sweep `.value.integer`** in CocoTBFramework, then in this repo's TB code.
   The replacement must work under BOTH cocotb versions if the two repos are to
   stay installable side by side during the transition.
3. **`units=` -> `unit=`**, same constraint.
4. Only then re-run the TASK-020 matrix under cocotb 2.x.

## Hazards

- **Two repositories, one venv.** A framework change lands in RTLDesignSherpa-DV
  and reaches this tree only on a release; the `.value.integer` sites here must
  move in step or the tree breaks between them.
- **`.value.integer` is not blindly replaceable.** Some sites compare, some do
  arithmetic, some index. Confirm each, and remember that a sweep needs a
  mechanical check -- the classifier is what invents the diffs.
- **A pass under 2.x proves nothing without a 1.x control**, which is the lesson
  TASK-020 already paid for: an API check there reported 13 missing `run()`
  parameters that were missing in the working version too.

## References

- [[TASK-020]] -- the pilot this came out of, with the full 0.2.5 vs 0.3.0 matrix
- [[TASK-021]] -- the DV version drift, same release
- RTLDesignSherpa-DV `pyproject.toml:46-50` -- the cap and its stated reason
- `CocoTBFramework/components/gaxi/gaxi_slave.py:393` -- a representative site

## Progress 2026-10-01: steps 1-3 done, and step 3 was wrong as written

### Step 1: the cocotb-bus cap -- LIFTED, and its stated reason was wrong

The cap read `cocotb-bus>=0.2.1,<0.3` because the 0.2.x `_add_signal`
case-sensitivity asymmetry was "load-bearing in apb_components". **Wrong word.**
The framework does not DEPEND on the asymmetry, it WORKS AROUND it:
`APBSignalMixin._match_optional_case` exists because 0.2.x gates optional signals
on a case-SENSITIVE `hasattr`, so a lowercase-port DUT silently loses
PSTRB/PPROT/PSLVERR -- writes carry zero byte strobes and the register reads back
its reset value with no error. **0.3.0 fixes that upstream**, making the
workaround redundant rather than broken.

A cap written to protect a workaround outlived the bug it compensated for, and
would have blocked the fix.

Measured on the APB suite the cap protected, cocotb 1.9.2 both sides:

| cocotb-bus | Result |
| --- | --- |
| 0.2.1 | **45 passed** |
| 0.3.0 | **45 passed** |

Lifted in RTLDesignSherpa-DV `57e3e8d`. `cocotb-coverage` stays capped at `<2`.

One control run failed once with `SystemExit: Process make terminated with
error 2` -- a BUILD failure, not an assertion, at +26% wall clock while three
suites ran concurrently; the same configuration passed 45/45 alone. Recorded
rather than dismissed, and being the control it is not evidence about 0.3.0.

### Step 2: the `.value.integer` sweep -- DONE in BOTH repos

| Repo | Sites | Commit |
| --- | --- | --- |
| RTLDesignSherpa-DV | 71 (60 adjacent + 9 split, + 2 binstr) | `daa87b1` |
| RTLDesignSherpa | 18 | `89e8220c3` |

`int()` is correct on every type cocotb returns here and was verified equal to
`.integer` on 1.9.2 **before** the change. `.is_resolvable` needed no change --
it exists on both 2.x types, so its 54 uses stand.

Baselined, because an "obviously equivalent" substitution still needs it: RLB at
gate from `clean-all`, same seed -- **27 passed before, 27 passed after**.

Four unit-test doubles had to gain `__int__`/`__str__` (67 tests failed until
they did). They modelled `.integer` only, a type cocotb 2.x does not have.

### Step 3: `units=` -> `unit=` would BREAK PRODUCTION. Do not do it.

This task said to rename and keep it working on both versions. **There is no such
rename.** Measured across both:

| Form | cocotb 1.9.2 | cocotb 2.1.0 |
| --- | --- | --- |
| `Timer(200, 'ps')` positional | clean | **clean** |
| `units='ps'` | clean | DeprecationWarning |
| `unit='ps'` | **TypeError** | clean |

`unit=` does not exist in 1.9.2. Positional is the only form clean on both, and
that is what landed (`5a9c39c`, 34 sites across `Timer`/`Clock`/`get_sim_time`).
`TBBase.start_clock(units=...)` is OUR method and keeps its keyword.

## Step 4 is blocked by a layer this work revealed

Re-running the matrix under cocotb 2.x now fails differently, which is progress
through the layers rather than a regression:

| | errors |
| --- | --- |
| Before the sweep | **1896** x `AttributeError: 'Logic' object has no attribute 'integer'` |
| After the sweep | **0** of those; **464** x `TypeError: unsupported operand type(s) for >>: 'LogicArray' and 'int'` |

cocotb 1.x `BinaryValue` supports `>>`, `&` and friends; 2.x `LogicArray` does
not. The pattern is a local assigned from `.value` and then used arithmetically:

    current_apb_addr = self.dut.apb_addr.value
    ... (current_apb_addr >> (i * self.addr_width)) & mask

**True size: 10 sites** -- 8 in this repo, 2 in RTLDesignSherpa-DV. The 464 is a
few sites firing inside loops; do not size this from the error count.

The fix shape is `int(...)` at the ASSIGNMENT, so the arithmetic operates on an
int: `current_apb_addr = int(self.dut.apb_addr.value)`.

| File | Lines |
| --- | --- |
| `stream/dv/tbclasses/stream_core_tb.py` | 1564, 1566, 1586 |
| `stream/dv/tests/macro/test_datapath_rd_test.py` | 679, 748, 790 |
| `retro_legacy_blocks/dv/tbclasses/pit_8254/pit_tb.py` | 514 |
| `bin/TBClasses/monbus/monbus_types.py` | 83 |
| RDS-DV `components/dfi/ca_map.py` | 178 |
| RDS-DV `components/dfi/dfi_monitor.py` | 182 |

**Use an AST pass, not a grep.** Three separate regexes missed the split form
today -- including one that reported `0` sites in a file whose traceback named
line 1564. The assignment and the use are different statements, so no regex over
a line sees both. The finder used is in the session log; it tracks names bound
from `<x>.value` and flags their later use under `>>`, `<<`, `&`, `|`, `+`, `-`
or `*`.

## Still open

- The 10 arithmetic sites above.
- Then re-run [[TASK-020]]'s matrix under cocotb 2.x.
- `cocotb-coverage` 2.0 remains untested and capped.

## Released 2026-10-01: cocotb-framework 0.6.9

Steps 1-3 shipped. RDS-DV issue **#83** records the four incompatibilities with
their measurements; the release went out through the repo's `publish.yml` on a
green CI, and the published artifact was verified rather than the repo:

- `pip metadata` and `__version__` both read **0.6.9** from a throwaway install,
  which is [[TASK-021]]'s single-source mechanism working end to end.
- The published source carries the fixes; `cocotb-bus>=0.2.1` uncapped,
  `cocotb-coverage<2` still capped.
- `requirements.txt` here bumped 0.6.8 -> 0.6.9 and the shared venv synced.

**Verifying the artifact rather than the repo immediately paid.** A grep of
site-packages for cocotb-API `units=` returned **8** after I had confirmed zero in
the source: all 8 were `.md` files, because the sweep only touched `*.py`, and
two of them ship INSIDE the package -- so they went out in 0.6.9 teaching the
idiom the release existed to remove. Fixed for the next release (50 examples
across 17 files). "Clean" had been measured over a narrower file set than the one
shipped.

## Step 4: cocotb 2.x is reachable for ONE suite, not broadly

| Suite under cocotb 2.1.0 | Result | vs its 1.9.2 baseline |
| --- | --- | --- |
| `dma-ip/stream` | **15 passed, rc=0** | identical (15) |
| `val/amba` | **600 passed / 239 failed**, rc=2 | 839 |

So the stream result does NOT generalise, and reporting "cocotb 2.x works" off
that one suite would have been exactly the scope error [[TASK-020]] already
corrected once.

### Three further layers, from the val/amba failures

| Error | Count | Meaning |
| --- | --- | --- |
| `This object cannot be cast to bool or used in conditionals` | **932** | `if sig.value:` -- 2.x refuses the implicit bool |
| `'LogicObject' object has no attribute 'name'` | 28 | handle attribute is `._name` in 2.x |
| `contains no child object named cmd_valid / cmd_id` | 8 | handle lookup differs; needs its own look |

**The bool layer is the big one: 89 sites in this repo, 6 in RTLDesignSherpa-DV**
(before triage). Measured with `bin/find_bool_value.py`, added alongside
`bin/find_value_arith.py` for the same reason -- the pattern spans statements and
a grep cannot see it.

The fix shape is an explicit comparison: `if sig.value:` becomes
`if int(sig.value):` or `if sig.value == 1:`, which also reads better.

## What is left

1. The **bool-cast layer** (89 + 6 sites) -- the largest remaining.
2. `.name` -> `._name` on handles (28 occurrences, site count not yet taken).
3. The `contains no child object` cases, which are not obviously mechanical.
4. Then re-measure the [[TASK-020]] matrix.
5. `cocotb-coverage` 2.0 still untested and capped.

## Two tools, and why they exist

`bin/find_value_arith.py` and `bin/find_bool_value.py` are AST passes, not greps,
because every regex tried on these patterns was wrong:

- Three regexes missed the **split form** (`v = sig.value` then `v >> n`), one
  reporting 0 hits in a file whose own traceback named line 1564.
- The raw AST hit count **over-reports**: `.value` is also an Enum member and a
  dataclass field. 10 hits, 3 false, 7 real -- so both tools print the source
  line and say so in their docstrings.
- Sizing from the **error count** over-reports badly too: 464 runtime errors came
  from 7 sites firing inside loops, a 46x overstatement.

Neither a grep, nor an AST hit count, nor an error count is the measurement on
its own.
