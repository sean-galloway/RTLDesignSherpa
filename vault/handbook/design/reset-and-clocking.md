---
title: Reset and clocking
summary: ALWAYS_FF_RST macros, aresetn active-low async, clock naming.
---

# Reset and clocking

- All resets are active-low asynchronous. The PORT NAME varies by area and
  the tree is the authority: AMBA and projects use `aresetn`; `rtl/common`
  uses **`rst_n`**. Measured 2026-08-21 across 48 `rtl/common` modules: 25
  expose `rst_n`, one exposes `aresetn` (`clock_gate_ctrl`), 22 have no reset
  port, and **none expose `i_rst_n`** -- an `.i_rst_n(...)` connection will
  not elaborate against them. (This note previously said common blocks "may
  use `i_rst_n`"; that was wrong where it had been checked.) Never
  `rst`/positive reset; never mixed polarity in one file.
- In projects/**, sequential logic uses the reset macros from
  `rtl/amba/includes/reset_defs.svh`:
  `ALWAYS_FF_RST(clk, rst_n, ...)` with `RST_ASSERTED(rst_n)` - not bare
  always_ff with hand-written reset. Bulk conversion: `bin/update_resets.py`
  (writes to UPDATED/ mirror for review).
  **The macro alone is not the fix.** `ALWAYS_FF_RST` picks the reset EDGE
  from `RESET_ACTIVE_HIGH`; a body that still tests `if (!rst_n)` picks the
  LEVEL by hand, and under an active-high build it holds the block in reset
  whenever the reset is released. The FIFO family had this (common BUG-012,
  2026-09-10) and twelve more files did (common BUG-013, fixed 2026-09-29:
  the apb4/apb5/axis5 clock-gated wrappers, axil5_opt_slave,
  amba_clock_gate_ctrl, clock_divider, dataint_checksum -- 16 sites). The
  residue check is mechanical; run it after any reset edit:

      grep -rn -A1 'ALWAYS_FF_RST(' rtl --include=*.sv | grep -v /OLD/ \
        | grep -E 'if \(\s*!\s*\w*(rst|reset)'

  It must print nothing. A synchronous soft reset tested inside the body
  (`pwm.sv`'s `sync_rst_n`) is a data signal, not the async reset, and is
  correctly outside the macro.
- Clocks: `aclk` on AMBA-facing logic, `i_clk` in common primitives. Derived
  clocks come from MMCM/PLL, not dividers, on FPGA tops; reset release is
  synchronized to MMCM lock (see stream_char_genesys2_top.sv).
- Config-before-reset: some blocks latch configuration during reset
  (credit/init values). TBs set those cfg signals BEFORE deasserting reset.

Authority: /GLOBAL_REQUIREMENTS.md section 1.1.
