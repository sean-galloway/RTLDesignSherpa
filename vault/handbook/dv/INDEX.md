---
title: DV notes
summary: Verification practice - frameworks, determinism, coverage, formal.
---

# DV

- [[escape-analysis]] - the RTL defects that got past a green suite, and the
  exact test-gap that let each one through
- [[running-regressions]] - ALWAYS clean-all first; the Makefile targets, the levels
- [[rds-dv-axes]] - BFM / sequence / randomization are ORTHOGONAL; where the RDS-DV docs live
- [[bfm-usage]] - use RDS-DV BFMs, never re-roll; the factory map + trap list
- [[randomization]] - the 19 FlexConfigGen profiles; random traffic does NOT prove fairness
- [[arbiter-compliance-model]] - it advances during REPLAY, not live; the three
  defects that made a correct arbiter look broken; never quiet it by name
- [[measure-over-the-window]] - phase assertions read that phase's deltas; a
  cumulative metric scores whatever ran before it
- [[registers-by-name]] - PeakRDL regmaps; offsets are forbidden
- [[seeds-and-determinism]] - random seed per run, recorded and overridable;
  there is no such thing as a failing seed
- [[tb-structure]] - Pattern A/B, TB location, the three mandatory methods
- [[test-runner]] - the Makefile/pytest/run() stack; REG_LEVEL vs TEST_LEVEL, build-dir uniqueness
- [[test-review]] - auditing test collateral with the review pipeline: what to grab, bundle layout, checklist
- [[coverage]] - Verilator, functional bar, the monbus packet-type matrix
- [[formal]] - sv2v/SBY flow, mutation rule, vacuity traps
- [[cloud-sandbox]] - running sims off the workstation; the Verilator pin, the PyPI pin
- [[silent-fallbacks]] - why almost every wrong DV conclusion is something that did not happen without saying so
- [[wavedrom-generators]] - the deliverable is the JSON, so empty = FAIL; the clock-group-name and add_interface-prefix traps; the gaxi reference
- [[register-testing]] - walk every register before anything is programmed; if the registers do not work, nothing above them can
