---
title: Coverage
summary: Verilator code coverage, functional bar, monbus packet-type matrix.
---

# Coverage

- Code coverage: Verilator --coverage via component flows (COVERAGE=1);
  measure the RTL under test, not the TB. Rollout tracker: val/COVERAGE_TODO.md.
  Long-form methodology: docs/guides/rtl_coverage_guidelines.md.
- Functional: >95 percent of the block contract, 100 percent pass rate.
- Packet-type matrix (monitor board gate): MONBUS_COVERAGE=1 during val/amba
  records every decoded (protocol, pkt_type, event_code) tuple;
  bin/monbus_coverage_report.py diffs against the enum ground truth
  (monbus_types.py), splits reserved padding (real space 171 codes), and
  emits the NONE work list - each row gets a provoking test or a documented
  unreachable rationale. Decode must go through parse() or the hook is blind.
  Emitter-grep first: most NONE rows have no RTL emitter at all (143/160 at
  baseline) - triage before writing tests.
- The board twin is the counting-histogram SRAM (CAM/cache + expected counts
  computed from descriptor programming) - see the monitor board plan.
