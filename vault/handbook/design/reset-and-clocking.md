---
title: Reset and clocking
summary: ALWAYS_FF_RST macros, aresetn active-low async, clock naming; the reset synchronizer's output net is a recovery-timed path (REPLICATED_OUT).
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

## The synchronizer's last flop is one net driving every CLR pin (2026-11-07)

On the FPGA the deassert edge of an async reset is a timed path: every
`ALWAYS_FF_RST` flop checks recovery/removal of its CLR pin against the
clock, and all of them hang on the one net the top's `reset_sync` drives.
jet on the Genesys2 (bins 7-9 of the cache-ip FPGA review): once the tag
array, data array, WB buffer, victim line and response ring were RAMs, the
worst setup path of the design was `u_reset_sync/.../r_sync_reg[2]/C` to a
`jet_monlite` timestamp flop's CLR -- slack 0.139 ns at 100 MHz, 24k
endpoints, route-dominated. amber on the same board did not show it only
because it has fewer flops (WNS 0.567 ns on a logic path).

The tools cannot fix it on their own. The chain carries `ASYNC_REG` and
`syn_preserve`, which is correct for a synchronizer and also forbids
replication, so neither `synth_design` nor `phys_opt_design` will copy the
last stage. Two things follow:

- **A top that resets a whole domain sets `reset_sync` `REPLICATED_OUT=1`.**
  The parameter adds one output flop in the output polarity, outside the
  ASYNC_REG group, with a `max_fanout` hint, and the tools replicate THAT
  toward the loads. Deassert latency becomes N+1; nothing else changes.
  amber_top, amber_ace_top, jet_top and jet_ace_top carry it. A leaf that
  synchronizes for a handful of flops leaves it off.
  Measured (jet bin 10, 2026-11-07): the recovery path went from 0.139 ns
  to 1.446 ns slack and the design WNS from 0.139 to 0.517 ns (a logic path
  now), cycle-identical on the board. Vivado did NOT replicate the flop
  (one `r_out_reg` per core; physopt found no high-fanout candidate once
  the slack was positive) -- the whole gain was letting the placer own an
  un-pinned output flop that already carries the output polarity, instead
  of a preserved ASYNC_REG stage behind an inverter. The `max_fanout` hint
  is there for the design that still needs copies.
- **Payload under the reset macro is still fan-out.** Each flop that did not
  need a reset (a RAM word qualified by a valid bit, a timestamp qualified
  by an entry's valid) is one more CLR pin on this net as well as one more
  flop; the [[sram-and-memories]] rule (payload reset-free, control reset)
  shortens this path too.

The check is in the timing summary, not the utilization table: after a
build look at the worst path's endpoint pin. `/CLR` or `/PRE` with a
`reset_sync` startpoint is this item.

Authority: /GLOBAL_REQUIREMENTS.md section 1.1.
