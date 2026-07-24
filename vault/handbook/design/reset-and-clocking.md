---
title: Reset and clocking
summary: ALWAYS_FF_RST macros, aresetn active-low async, clock naming.
---

# Reset and clocking

- All resets are active-low asynchronous `aresetn` (common blocks may use
  `i_rst_n`). Never `rst`/positive reset; never mixed polarity in one file.
- In projects/**, sequential logic uses the reset macros from
  `rtl/amba/includes/reset_defs.svh`:
  `ALWAYS_FF_RST(clk, rst_n, ...)` with `RST_ASSERTED(rst_n)` - not bare
  always_ff with hand-written reset. Bulk conversion: `bin/update_resets.py`
  (writes to UPDATED/ mirror for review).
- Clocks: `aclk` on AMBA-facing logic, `i_clk` in common primitives. Derived
  clocks come from MMCM/PLL, not dividers, on FPGA tops; reset release is
  synchronized to MMCM lock (see stream_char_genesys2_top.sv).
- Config-before-reset: some blocks latch configuration during reset
  (credit/init values). TBs set those cfg signals BEFORE deasserting reset.

Authority: /GLOBAL_REQUIREMENTS.md section 1.1.
