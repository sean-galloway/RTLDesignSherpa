<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# 1.1 Purpose and Scope

## Purpose

The Timing Characterization component is a **synthesis benchmarking harness**
designed to answer a fundamental question in digital design: *How fast can a
given combinational structure operate on a specific technology target?*

The harness forces synthesis tools to build specific combinational structures
between registered endpoints. The resulting timing reports provide empirical
measurements of gate delay, carry-chain speed, multiplier performance, and
memory inference behavior across FPGA families and ASIC standard-cell libraries.

## Problem Solved

When designing production datapaths, engineers must make decisions about:

1. **Pipeline depth** -- How many logic levels fit in a single clock period?
2. **Operator selection** -- Should a multiplier use DSP slices or LUT fabric?
3. **Memory type** -- At what depth does the tool switch from LUTRAM to BRAM?
4. **Technology tradeoffs** -- How does the same RTL perform on Artix-7 vs. UltraScale+?

These questions are traditionally answered by experience, vendor documentation,
or ad-hoc synthesis experiments. The Timing Characterization harness provides a
**systematic, repeatable** way to collect this data across technologies.

## Scope

This specification covers:

- The `char_top` top-level wrapper and its 9 Functional Unit Blocks (FUBs)
- The shared LFSR anti-optimization engine
- SDC constraint strategy for multi-tool synthesis
- Parameter sweep methodology
- Expected synthesis result trends

This specification does **not** cover:

- Specific synthesis results (these depend on target technology)
- Vendor-specific synthesis tool operation
- Post-place-and-route timing analysis (future extension)

## Design Philosophy

The harness follows three core principles:

1. **Anti-optimization** -- Synthesis tools must not simplify the logic under test
2. **Registered endpoints** -- All paths are register-to-register for clean timing analysis
3. **Parameterization** -- Every FUB has depth/width parameters for sweep testing
