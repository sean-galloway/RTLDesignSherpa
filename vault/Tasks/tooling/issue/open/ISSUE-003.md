# ISSUE-003: cocotb-framework 1.0.0 — external dependency major rev; IRQ BFM promoted into the package

**Priority:** P2
**Status:** open
**Owner:** TBD
**Filed:** 2026-10-04
**Refs:** RTLDesignSherpa-DV release `v1.0.0`; RDS commits `3fcff894e`, `a144e8b1d`; tooling TASK-025

## What changed

The DV framework shipped a **major** rev to PyPI on 2026-10-04 (was 0.6.9).
This is a tracking/advisory item so the size of the external change is on
record, not discovered by accident in a venv rebuild.

1. **IRQ BFM moved out of this repo into the package**
   (`CocoTBFramework.components.irq`: `IRQMonitor`, `IRQMonitorGroup`,
   `IRQPacket`). It lived at `bin/TBClasses/irq/` since 2026-09-28 as a
   deliberate iteration shortcut (RLB TASK-017's placement note); the owner
   reversed that decision and promoted it with full docs
   (`docs/components/irq/`, five pages) and its unit tests
   (`tests/unit/test_irq_logic.py`, 16 tests).

2. **cocotb 2.x compatibility fixes shipped** — the cancellation-swallow in
   the compliance checkers' `cycle_counter()`, explicit `int()` on handle
   truthiness, and the `cocotb.logging` SimLog import + logger fallback.
   Verified over the bridge/math/common/cdc BKM coverage set under cocotb
   2.1.0 (TASK-025): cdc 349/349, math 401/401, common 945/945, bridge at
   exact parity with 1.9.2.

3. **Partial `signal_map` merges with automatic pattern discovery** also
   rides in this rev (RDS-DV `4d59f73`).

## What RDS already did about it

- `requirements.txt` bumped to `cocotb-framework==1.0.0` (`3fcff894e`).
- `bin/TBClasses/irq/` deleted; `rlb_top_tb.py` imports from the package
  (`a144e8b1d`). RLB bringup verified 2/2 against the **released** 1.0.0
  artifact, not the repo.
- Shared venv synced and the installed wheel spot-checked (version, irq
  exports).

## The breaking-change note

Anything outside this repo that imported `TBClasses.irq` — old checkouts,
forks, in-flight branches — breaks against 1.0.0 until it switches to
`from CocoTBFramework.components.irq import ...` (which needs 1.0.0
installed). Within this repo the only consumer was `rlb_top_tb.py`, already
switched; `pic_8259_tests_medium.py` only mentions the old path in a comment.

## What would close this

Recorded no-action at the next tooling triage once everyone's local venvs
have been rebuilt or synced past 1.0.0 — there is no remaining code work
here. The telltale symptom of a stale venv is
`ModuleNotFoundError: No module named 'CocoTBFramework.components.irq'`
in the RLB suite.

## Known gaps carried in this rev (recorded in TASK-025, not new work)

- `cocotb-coverage` remains capped `<2` (2.0 untested).
- The amba-only residue from the first 2.x matrix (28 `.name`, 8
  child-object cases) was deferred per the BKM coverage-set scoping.
