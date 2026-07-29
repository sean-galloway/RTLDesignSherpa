---
name: test-review
description: Auditing test collateral with the review pipeline - what to grab from val/<area>, bin/TBClasses, and the RTLDesignSherpa-DV framework (golden), the bundle layout, and the audit checklist (three levels, structure, filelists, seeds, BFM usage, real checks). Use when reviewing/auditing tests in an area, or building the test-review bundle.
---

# test-review

READ FIRST: [vault/handbook/dv/test-review.md](../../vault/handbook/dv/test-review.md)
(the canonical note - grab algorithm, bundle layout, audit checklist, review flow).

All validation collateral descends from one cocotb-based source:
`$RDS_DV_REPO` (default `/home/seang/github/RTLDesignSherpa-DV`). A
`val/<area>/test_*.py` is almost exclusively a TB-class include (inline or
`bin/TBClasses/`, holding the tests/scenario generators) plus a REG_LEVEL
parameter generator for `cocotb_test.run()`. Every test must offer three
run levels - gate/func/full - via BOTH the REG_LEVEL grid (how many tests)
and TEST_LEVEL depth (how much each does).

Bundle per area: TESTS.py + TB.py + FRAMEWORK.py (GOLDEN, never a finding
target) + RTL_IFACES.sv + MANIFEST.md. Review through the same pipeline as
docs (qc round -> verify_findings.py -> triage), stop by the impact rule.
