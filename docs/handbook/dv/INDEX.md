---
title: DV notes
summary: Verification practice - frameworks, determinism, coverage, formal.
---

# DV

- [[running-regressions]] - ALWAYS clean-all first; the Makefile targets, the levels
- [[rds-dv-axes]] - BFM / sequence / randomization are ORTHOGONAL; where the RDS-DV docs live
- [[bfm-usage]] - use RDS-DV BFMs, never re-roll; the factory map + trap list
- [[randomization]] - the 19 FlexConfigGen profiles; random traffic does NOT prove fairness
- [[registers-by-name]] - PeakRDL regmaps; offsets are forbidden
- [[seeds-and-determinism]] - pin seeds; corpus + exploration pattern
- [[tb-structure]] - Pattern A/B, TB location, the three mandatory methods
- [[test-runner]] - the Makefile/pytest/run() stack; REG_LEVEL vs TEST_LEVEL, build-dir uniqueness
- [[coverage]] - Verilator, functional bar, the monbus packet-type matrix
- [[formal]] - sv2v/SBY flow, mutation rule, vacuity traps
- [[cloud-sandbox]] - running sims off the workstation; the Verilator pin, the PyPI pin
