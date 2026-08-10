---
title: Coverage
summary: Verilator code coverage, functional bar, monbus packet-type matrix.
---

# Coverage

- Code coverage: Verilator --coverage, measure the RTL under test, not the TB.
  Long-form methodology: docs/user-guides/rtl_coverage_guidelines.md.
- How to run it (GENERIC, one implementation): the toggle and the report both
  live in the base `make/tests.mk`, so every area that includes it (val/common,
  val/amba, cdc, math, and each stream fub/macro/top) gets them with no
  per-area/per-component replication:
    - collect: `COVERAGE=1 make run-all-<gate|func|full>[-parallel]` -- injects
      the `COVERAGE` env every area's conftest already reads (Verilator line
      coverage). Off by default = byte-for-byte unchanged.
    - report: `make coverage-report` -> `bin/cov_utils/merge_testlevel_coverage.py`
      (recursive globs, so it works at a leaf area AND at a dispatcher that spans
      sub-areas -> a merged component report). Output:
      `coverage_reports/latest_coverage_report.md`.
    - area-specific extras stay OUT of the base: e.g. STREAM's legal-set mode is
      `COVERAGE=1 COVERAGE_LEGAL=1 make ...` (shell env), inert to val areas.
  Do NOT re-add copied `coverage-*` run targets or per-Makefile `coverage-report`
  targets -- that replication is exactly what the base file replaced.
- One conftest implementation too: every area's `conftest.py` delegates coverage
  collection + session-end aggregation to `bin/cov_utils/conftest_base.py`
  (`configure` / `sessionfinish` / `ignore_collect`) + `conftest_coverage.py`
  (`aggregate_verilator_coverage` for line, `aggregate_protocol_coverage`, and
  `get_coverage_compile_args` re-exported for test wrappers). bridge, converters,
  val/common|cdc|amba|math and stream fub/macro/top all use it; an area conftest
  keeps ONLY its local bits (sys.path for its test-helper imports, area fixtures
  like `test_level`). Do NOT paste an `_aggregate_coverage` /
  `_generate_coverage_report` block into a conftest -- that per-area duplication
  (stream was 3x274 lines, the val family 4x154) is what the shared base replaced.
- Functional: >95 percent of the block contract, 100 percent pass rate.
- READ THE NUMBER FOR WHAT IT IS: Verilator tracks TOGGLE coverage (bits
  flipping), not line coverage. Multi-bit signals (addresses, data) can read
  0 percent while functionally exercised; continuous assigns are not tracked
  at all; instantiated building blocks (skid buffers) are counted separately
  from the module that wires them. So a 40 percent Verilator figure can be
  100 percent functional coverage — prove scenarios were hit with the other
  signals: single-bit valid/ready hit counts, test phase-completion logs,
  TB transaction statistics, and the timing-profile sweep. The YAML
  testplans (val/<area>/testplans/) carry an `implied_coverage` block making
  that argument explicitly per module, and
  `bin/cov_utils/calc_coverage_excluding_building_blocks.py --level <area>` separates
  building-block coverage from integration-logic coverage. (Folded from
  val/amba/testplans/VERIFICATION_METHODOLOGY.md, retired 2026-08-09.)
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
