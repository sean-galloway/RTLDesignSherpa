---
title: TB structure
summary: Pattern A/B, TB location, three mandatory methods, naming.
---

# TB structure

- Pattern A (val/common, val/amba): plain @cocotb.test functions + pytest
  wrapper. Pattern B (projects/components/**): cocotb functions prefixed
  cocotb_test_*, each pytest wrapper selects one via testcase=. Never mix.
- TB classes: project area (projects/<comp>/dv/tbclasses/); only genuinely
  shared infrastructure goes in the framework.
- Every TB class implements setup_clocks_and_reset / assert_reset /
  deassert_reset. Config-before-reset where blocks latch cfg during reset.
- Pytest function names embed the exact module name (test_<module>...) -
  generic names collide across related modules.
- Complex modules: ONE comprehensive test with TEST_LEVEL=gate/func/full
  levels, not a family of near-duplicate tests.
- 100 percent pass is the bar; partial success is a bug, not tolerance.
- Background-monitor coroutines for async outputs (descriptors, packets) -
  point checks miss data that lands between them.

Authority: /GLOBAL_REQUIREMENTS.md section 2.
