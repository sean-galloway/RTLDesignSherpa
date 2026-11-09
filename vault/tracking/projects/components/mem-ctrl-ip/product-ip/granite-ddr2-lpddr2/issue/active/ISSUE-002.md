# ISSUE-002: granite does not come up on the Nexys at 100 MHz (2026-11-09) -- every placement, the 2026-11-02 design included; 75 MHz and LiteDRAM at 100 MHz are fine

**Priority:** P1 -- the 100 MHz board point is the LiteDRAM comparison the owner asked for (memory-controllers MC-011 step 3 closed the timing; this blocks the measurement).
**Status:** active 2026-11-09 04:40 -- bracketed on the board (matrix below); cause not found.
**Owner:** TBD

## What happens

`make program` then `make run SEQUENCES="init write_read" RUN_ARGS="--controller granite"`
on any granite bitstream built for `GRANITE_SYS_100=1`: the host measures
`clk=100.00MHz`, a7ddrphy read leveling sweeps all 8 bitslips x 32 taps and
finds **no (bitslip, tap) eye** (every probe's write-pattern read-back
mismatches; ~300 s), `init` reports PASS with the leveling warning, and
`write_read` fails **512 / 512 beats mismatched**. Reads complete (0.5 s, no
hang); the data is wrong at every capture setting.

## The matrix (one board, Nexys A7-100T 210292BFA3EE, one hour, 2026-11-09 03:40-04:36)

| bitstream | design | host | result |
|---|---|---|---|
| `ddr2_char_granite_sku100_2026-11-09.bit` | HEAD + MC-011 step 3 RTL, FPGA SKU, 100 MHz, AltSpreadLogic_high (+0.147 under budget) | today | FAIL, no eye, 512/512 |
| flow's own Explore bitstream (+0.002) | same RTL, different placement | today | FAIL, same |
| `base_sys100.bit` from the kept 821b5c164 checkpoint | HEAD before the step-3 RTL, SKU, 100 MHz | today | FAIL, same |
| worktree build, HEAD `GRANITE_RESEARCH_CFG=1` (38,067 LUT, +0.023) | research configuration (combiner + narrow pack on) | today | FAIL, same |
| worktree build of **c38f80c9e** (35,743 LUT, +0.008) | the 2026-11-02 design that ran at 100 MHz on this board then (Ocelus board run) | today | FAIL, same |
| the same c38f80c9e bitstream | same | **the 2026-11-02 host** (worktree `env_python`, worktree regmaps) | FAIL, same |
| pumice sys75, current tree (build-perf, ExtraTimingOpt, +0.028) | pumice FPGA SKU at 75 MHz | today | **PASS** init + write_read |
| `ddr2_char_granite_sku75_2026-11-09.bit` | HEAD + step-3 RTL, SKU, **75 MHz** (+1.338) | today | **PASS** init + write_read |
| `litedram_char_100mhz_2026-10-31.bit` | LiteDRAM at **100 MHz** | its own host | **PASS**: `init_done=True`, quick `every` profile 708-760 MB/s incremental, no errors |

So: the board, the DRAM and the a7ddrphy work at 100 MHz (LiteDRAM); the
granite controller and harness work on the board (75 MHz); the granite
harness at 100 MHz fails for every design built today, including a
source-identical rebuild of the design that worked on 2026-11-02 under the
host of that day. Not the step-3 RTL, not the SKU parameters, not the false
paths or the budget (c38f80c9e has none of them), not the host.

## What is left

- **Placement / tool state.** The 2026-11-02 bitstream itself is gone (the
  flow overwrites `fpga/bitstream/ddr2_char.bit`; the dated copies in the
  sweep md were not kept). Five placements built today all fail, so a design
  that is marginal at 400 MT/s and happened to work on the 10-31 / 11-01 /
  11-02 placements is one explanation, but five of five is a lot of bad luck.
  The constraints are not the gap: in the kept 100 MHz report every PHY-facing
  path is timed inside `w_sys_i` (the OSERDES / ISERDES take CLKDIV = sys; the
  derived `w_sys2x_i`, `w_sys2x_dqs_i` {1.25, 3.75} and `w_idelay_i` clocks
  carry no flop endpoints), `check_timing` reports 0 no_clock and 0
  unconstrained endpoints, and the 75 MHz build that works has the identical
  clock structure. What differs between 75 and 100 is only the capture window
  at the DQS (5.0 ns vs 6.7 ns CK period).
- **Eye width.** The host's leveling logs its per-bitslip eye only when
  verbose; the 75 MHz runs printed none. pumice's `level_cache.json` (2026-11-08
  23:44, 75 MHz) shows bitslip 0, tap 8, window 0..16 -- a 17-tap eye. Run the
  granite init at 75 MHz verbose to read granite's eye; a narrow eye at 75
  says systematic margin (DRAM drive / ODT / OCD state from the harness init
  versus LiteDRAM's BIOS sequence), a wide one says the 100 MHz failure is
  specific to that point.
- **Write side vs read side.** "No eye" through the controller cannot tell a
  write that never lands from a read that never captures. The `telemetry`
  and `ocelus` sequences on the failing bitstream (ACT / WR / RD counts, DFI
  monitor RAM) split the two.
- **Temperature / supply.** The board has been running builds and tests for
  three days; LiteDRAM's margin at 100 MHz may simply be wider.
- The same Vivado (2025.1) built the 11-08 and 11-02 report sets.

## Where things are

- Logs: `scratchpad/g100fix/board_smoke.log`, `board_try_*.log`,
  `board_queue*.out`, `board_try_lite_*.log` (this session's scratchpad).
- Bitstreams kept beside them: `c_AltSpreadLogic_high.bit`, `c_Explore_flow.bit`,
  `base_sys100.bit`, `a_sys100.bit`, `b_sys100.bit`, `wt_c38f_default.bit`,
  `wt_head_research.bit`, `head_myrtl_sku75.bit`, `pumice_sys75_altspread.bit`
  (that one is the ExtraTimingOpt build).
- Worktrees `scratchpad/g100fix/wt_c38f` (c38f80c9e) and `wt_head`
  (821b5c164), detached; remove with `git worktree remove` when done.
- MC-011 (memory-controllers) has the timing side; the sweep md
  (`sweep_granite_vs_litedram_2026-10-29.md`, 2026-11-09 section) has the
  area comparison and the board status.
