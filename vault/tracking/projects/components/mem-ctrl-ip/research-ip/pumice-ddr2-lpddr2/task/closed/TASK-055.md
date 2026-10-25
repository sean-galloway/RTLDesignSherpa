# TASK-055: granite scheduler and DFI planes -- the runtime page-policy engine and the DFI FIFO depths, measured

> Source: the ranked list closing TASK-054 (owner: "Continue"): the
> scheduler plane is 45 percent of the core, the runtime page-policy engine
> 2 500 ASAP7 cells / 688 flops of it; the DFI FIFOs in the same-clock form
> are sized to the whole read-return window. Related: TASK-053 (the
> same-clock DFI form), TASK-054 (the knob method), TASK-048 (tr_init 0).


> **Correction (2026-10-24 evening, pumice BUG-031 / TASK-058):** the board
> LUT / FF figures in this file were measured on bitstreams whose read path
> synthesis had removed -- a double continuous driver on `mc_rd_intake.map_req_o`
> (TASK-054) tied the AR valid to GND, no read ever issued on silicon, and
> Vivado folded the dead read side of the store, ring and intake away. The
> honest board trend is TASK-053 text 6 090 LUT / 4 417 FF -> fixed final text
> 5 631 LUT / 3 532 FF (report 5.18). Every cycle-count and bandwidth claim in
> this file stands: the net was dead in simulation, so the simulator measured
> the real design. The ASAP7 per-plane numbers move only in the read intake
> (1 045 -> 1 210 cells).


> **Correction (TASK-059):** "fixed_open, tr_init 0" below is the CSR reset value; the open_page configuration the host programs for every granite measurement writes `tr_init` 1, so the engine's measured value here is the idle-timeout close, not close-on-drain (whose mask the pick core never reads).

**Priority:** P2
**Status:** closed 2026-10-24 (DFI FIFO depths 4 / 16 / 4 as granite's default: board 4 171 -> 4 107 LUT, cycle-identical everywhere; the page-policy engine measured and kept: -8 percent on 8-thread streams without it)
**Owner:** TBD

## What landed

Knobs on `granite_core`, plumbed through `granite_top_geared`, the char
macro / harness / top (`GRANITE_*`), the UART tb top and perf proxy
(`TEST_*`), the two granite tests and both `create_project.tcl` hooks;
pumice untouched:

- **`HAS_PAGE_POLICY`** (the scheduler plane already had the generate and a
  pass-through; granite now sets it). 0 = no runtime page-policy engine:
  the auto-precharge decision is the build's close-on-drain term
  (`CLOSE_ON_DRAIN && !behind_same_row`), no idle-timeout PRE request, no
  page / stall telemetry. Note what the default does on granite today:
  `PAGE_POLICY_CFG.policy_mode` resets to 3 (fixed_open), which makes the
  engine own the AP decision with `ap_close = 0` -- the pick core never
  auto-precharges, and rows close through the engine's idle-timeout request
  with `tr_init` reset to 0 (TASK-048).
- **`DFI_CMD_FIFO_DEPTH` / `DFI_WD_FIFO_DEPTH` / `DFI_RD_FIFO_DEPTH`**
  (defaults 8 / 32 / 0 = `RD_RET_DEPTH x BURST_WORDS`, today's build).

## Measured

ASAP7 (planes kept, dead ports pruned, comb cells / flops / RAM bits):

| | TASK-054 defaults | `HAS_PAGE_POLICY = 0` | DFI FIFOs 2 / 8 / 2 |
|---|---|---|---|
| scheduler plane | 10 982 / 1 743 / 544 | 8 130 / 1 047 / 544 (engine 2 522 / 688 gone; pick 5 009 -> 4 695, its idle-timeout path) | same |
| DFI plane / u_cdc | 931 / 246 / 4 752, 304 / 54 | same | 792 / 226 / 786, 165 / 34 |
| granite_top_geared | 24 999 / 4 226 / 9 438 | 21 861 / 3 530 / 9 438 | 24 860 / 4 206 / 5 472 |

Board (Nexys A7, 75 MHz, granite_core LUT / FF, WNS, 0 failing endpoints):

| build | LUT / FF | WNS |
|---|---|---|
| TASK-054 defaults | 4 171 / 2 709 | +0.206 ns |
| `HAS_PAGE_POLICY = 0` | 3 964 / 2 517 | +0.295 ns |
| DFI FIFOs 4 / 16 / 4 (**the committed defaults**) | 4 107 / 2 695 | +0.277 ns |
| DFI FIFOs 2 / 8 / 2 (knob; fails the two-clock component suite) | 4 086 / 2 687 | +0.074 ns (21 LUT under 4 / 16 / 4, a third of the slack) |
| committed text rebuilt as plain defaults (writes `fpga/reports`) | 4 107 / 2 695 | +0.277 ns, 0 / 97 293 |

Perf proxy against the TASK-054 defaults (board geometry, mismatched 0 everywhere):

| cell | no page-policy engine | DFI FIFOs 4 / 16 / 4 | DFI FIFOs 2 / 8 / 2 |
|---|---|---|---|
| 1 thread inc / row_major / col_ilv / col_major | 569.0 / 572.0, identical, **508.3 / 507.0 (+10 percent)**, **291.5 / 331.1 (-6 / -8 percent)** | identical | identical |
| 8 threads inc / row_major / col_ilv / col_major | **511.2 / 513.6, 511.1 / 513.1 (-8 percent), 512.0 / 513.6 (-4 / -6), 511.4 / 513.1 (+11 / +12)** | identical | identical |
| mixed, 8 threads | 97.9 (98.1) | identical | identical |

**The page-policy engine stays.** Without it the pick core's auto-precharge is
the close-on-drain term alone, and at eight threads that precharges rows
the next command would have hit: the streams lose 8 percent and only
col_major (a new row per access, where an early close is free) gains. The
engine's default on granite -- fixed_open with the idle timer off -- holds
rows open across the eight injectors' interleaving, which is what the
measured bandwidth was built on (TASK-048). 207 LUT and 192 FF on the board
are not worth 8 percent; the knob stays, default 1.

**The DFI FIFO depths shrink to 4 / 16 / 4.** Both 4 / 16 / 4 and 2 / 8 / 2
were cycle-identical on every cell, 1 and 8 threads and mixed, with the read
aligner's lost-beat assertion silent in the same-clock form (the ring is
always ready when a ticket is in flight, so the return FIFO never holds more
than one burst). 2 / 8 / 2 fails the component suite, whose dfi_clk runs at
twice aclk and whose async read FIFO therefore has to hold half a burst per
return cycle; the product default is 4 / 16 / 4, which passes both, and
2 / 8 / 2 stays a measured knob for a same-clock integration.

## Gates

Granite suite 6 / 1 xfailed with `HAS_PAGE_POLICY = 0`, with depths
4 / 16 / 4, and on the final defaults; at 2 / 8 / 2 the two granite_core
cells fail on the read aligner's sizing assertion (two test clocks, see
above), which is the reason that setting is not the default. Lint 0 errors
at every setting. Pumice is not touched (the knobs are granite_core's; the
scheduler plane's `HAS_PAGE_POLICY` generate and the DFI plane's depth
parameters already existed). Board md5 == working text for the final build.
