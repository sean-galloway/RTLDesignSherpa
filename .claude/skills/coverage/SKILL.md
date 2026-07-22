---
name: coverage
description: Coverage methodology - Verilator line/toggle coverage per component, functional coverage expectations, and the monbus packet-type coverage matrix. Use when adding tests, closing coverage, or preparing a board-gate sign-off.
---

# Coverage

Long-form guidelines: docs/guides/rtl_coverage_guidelines.md (methodology,
what to waive and why). Rollout tracker: val/COVERAGE_TODO.md.

Working rules:
- Code coverage: Verilator --coverage via the per-component coverage helpers
  (COVERAGE=1 in the component test flows; reports under dv/tests/coverage_*).
  Target is meaningful line+toggle on the RTL under test, not the TB.
- Functional coverage: tests target >95 percent functional coverage of the
  block contract; 100 percent pass rate is the bar - partial success is a
  bug, not a tolerance.
- Packet-type coverage (monitors): MONBUS_COVERAGE=1 during a val/amba run
  records every decoded (protocol, pkt_type, event_code) tuple;
  bin/monbus_coverage_report.py diffs against the enum ground truth and
  emits the NONE work list. This is the pre-board sign-off artifact -
  every NONE row gets a provoking test or a documented unreachable
  rationale. Decode must go through TBClasses.monbus.parse or the hook
  cannot see it.
- Seeds pinned always; exploration is a deliberate mode (seed-sweep knobs),
  not ambient randomness.
