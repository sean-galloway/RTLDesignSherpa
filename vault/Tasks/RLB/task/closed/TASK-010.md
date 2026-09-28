# TASK-010: RTC leftovers after the #56 fix

> Migrated 2026-09-27 from `vault/Tasks/RLB/closed.md` as **RLB-010** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-09-14

All three bullets are resolved. The entry had stayed open only to HOLD the
clock-mux constraint -- explicitly "rather than because anything is pending" --
and that constraint now lives in the RTL itself, worded per branch, so the
reason to keep it open is gone.

`apb4_rtc` was 60/60 at the full level after the #56 rewrite (ten review rounds
on the clock-domain crossing); nothing in this entry was ever a defect. The
durable lessons are in the handbook: [[cdc]] Rules 1-7 and
[[no-assertions-in-rtl]].

- ~~Two shared CDC primitives are not verilator -Wall clean.~~ FIXED
  2026-09-10 in `dc4ea9db7`: the handshake's timeout counter now lives inside
  the generate branch that uses it, so at TIMEOUT_CYCLES = 0 it does not exist
  rather than existing unused; `glitch_free_n_dff_arn`'s waveform-only
  flattened copy is waived where it is declared rather than deleted; and
  `reset_sync`'s four power-on initialisers carry a scoped PROCASSINIT waiver,
  because the initialiser is deliberate on a device with no reset before the
  first clock.

- ~~`selected_clk` is a combinational clock mux.~~ RESOLVED 2026-09-14 in
  `ae03c6b43`. The reasoning that kept it open was sound and still stands: a
  PORTABLE glitch-free mux is a break-before-make handshake needing BOTH clocks
  running, while the whole point of `clock_select` is running from pclk when
  the crystal may be absent -- so a portable version cannot switch away from a
  dead clock and would replace the documented constraint with a worse one. The
  entry named the real answer, a device-specific cell, and `rtc_clk_mux` is it:
  BUFGCTRL with IGNORE0/IGNORE1 on XILINX (the IGNOREs are the point -- they
  complete the switch without waiting for the departing clock's edge, which is
  the stopped-crystal case), ALTCLKCTRL on SYNTH_PRAGMA, and the original expression
  bit for bit everywhere else.

  The fallback is deliberately IDENTICAL rather than improved: one that quietly
  behaved differently from the cell would be worse than no fallback. So the
  rtc_enable-low constraint STILL APPLIES on the default branch, and all
  thirteen constraint statements now say which branch they apply to instead of
  claiming the hazard is gone. Seven of those thirteen were sites a narrower
  sweep had missed -- one wrapped across a line break, one in ch01_overview that
  named no mux at all, and two TB comments quoting the old inline expression.
  Enumerating every mention of the term found them; grepping the sites already
  known did not.

- ~~No formal area exists for retro_legacy_blocks.~~ CREATED 2026-09-14.
  `formal/retro_legacy_blocks/` exists on the rapids pattern (aggregator
  Makefile -> per-block Makefile -> sv2v flatten -> sby), with the
  `rtc_config_regs` proof wired into the top-level `formal:` goal in the same
  edit that added it.

  **PROVED: the RTC_STATUS W1C strobe.** `clear_alarm_flag`,
  `clear_second_tick` and `clear_commit_timeout` are each asserted for at most
  one cycle per W1C transaction. It matters because `peakrdl_to_cmdrsp` holds
  `regblk_req` for the accept cycle PLUS one, so a strobe derived from it is
  presented twice unless edge-detected -- the same two-cycle hold that produced
  defects in rapids (kick) and pm_acpi (`cfg_sys_reset`) the same week.
  MUTATION-CHECKED: removing `&& !r_status_sw_wr_d` makes the proof FAIL and
  restoring it makes it PASS; all three covers are reached at step 2; the named
  properties appear in `design_smt2.smt2` (the SMT model -- NOT
  `design_smt2.log`, which contains none of them; grepping the log is itself a
  false vacuity test).

  **STILL UNPROVED, and known to be unprovable here: the seconds-read latch
  alignment.** It is a property of `w_seconds_latch`, an internal signal, and
  internal visibility is unavailable for this block in this toolchain. Four
  routes were tried and all fail:
    1. `dut.<sig>` with the DUT read as flat Verilog and the harness as SV --
       "ERROR: Failed to resolve identifier".
    2. the same with `hierarchy`/`proc`/`flatten` before `prep` -- identical.
    3. the same with harness and DUT sv2v'd into ONE file -- identical.
    4. `bind` -- yosys drops the checker silently and the proof passes with no
       property cells; caught by MUTATION, not by reading the log. sv2v cannot
       parse `bind` at all ("unexpected token 'bind'").
  Reading the RTL as SystemVerilog instead (how `formal/apbx_xbar` gets
  internal visibility) is closed off: yosys cannot parse the generated package
  -- "rtc_regs_pkg.sv:10: ERROR: Only PACKED supported at this time". So it
  stays CHECK BY INSPECTION in the module header, which
  [[no-assertions-in-rtl]] sanctions as the accepted state. If the bridge's
  capture cycle ever changes, re-derive the alignment by hand.

Verified before closing: `make clean-all && make run-all-full-parallel` across
all nine blocks, **63 passed / 0 failed in 343.50s** (known-good baseline
343.60s), with all six RTC cells showing zero failure markers.

Design decisions to know before touching the block (all stated in
`rtc_core.sv`'s header and the MAS): the commit handshake is deliberately not
cancellable (a timeout reports and releases the register block, the transfer
lands late rather than never; a one-sided cancel was tried and is a trap); the
queued commit slot carries its own watchdog and two marks (expired per
occupant, reported per slot); `COMMIT_TIMEOUT_CYCLES=0` disables both watchdogs
and then a commit on a dead clock hangs busy unreported; the counter domain's
reset release needs pclk running.

---
