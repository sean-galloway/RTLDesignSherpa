# TASK-025: cocotb 2.x needs cocotb-bus 0.3.0 and a `.value.integer` sweep -- the blocker is measured, not guessed

**Priority:** P3
**Status:** open
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
