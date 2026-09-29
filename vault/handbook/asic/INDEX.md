---
title: ASIC notes
summary: Open-source ASIC flow method - the ASAP7 predictive-PDK path and what its numbers mean.
---

# ASIC

- [[rtl-to-asap7-oss-flow]] - RTL to an ASAP7 gate-level netlist (and optional GDS)
  with yosys/slang, OpenROAD-flow-scripts or yosys + OpenSTA; install on Ubuntu,
  the two paths, and the reality check that ASAP7 is a predictive PDK whose
  numbers compare against each other, not against silicon.

The design that drives this flow, and the timing-prediction methodology built on
it, live in `projects/asic-trials/timing_characterization/` (README.md is the
ASIC white paper source; README_FPGA.md its FPGA companion).
