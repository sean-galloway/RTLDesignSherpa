// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rtc_core
// Purpose: Core logic for Real-Time Clock with alarm functionality
//
// Implements RTC functionality:
// - Time counting: seconds, minutes, hours, day, month, year
// - BCD and binary counting modes
// - 24-hour and 12-hour (AM/PM) modes, PM in bit 7 of the hours byte
// - Leap year handling (2000-2099)
// - Alarm comparison with field masking
// - Second tick and alarm interrupts
// - Clock source selection (32.768 kHz or system clock for testing)
//
//==============================================================================
// CLOCK DOMAINS (GitHub #56 H4/H7, round_2 items 4/5/6, round_3 items 1/2/3)
//==============================================================================
// This module spans TWO domains and every crossing between them is explicit.
//
//   COUNTER DOMAIN  - `selected_clk` (= rtc_clk, or pclk in clock_select=1 test
//                     mode), reset by `rtc_rst_n` through reset_sync (async
//                     assert, synchronous deassert on selected_clk). Holds the
//                     divider, the six time counters, the calendar arithmetic
//                     and the alarm comparator.
//   APB DOMAIN      - `clk` (pclk), reset by `rst_n`. Holds the shadow copy of
//                     the time that software reads, the sticky status flags,
//                     and the source side of the time-set commit.
//
// The four crossings, and the primitive each uses:
//
//   1. CONFIG / ALARM (pclk -> counter), quasi-static
//      `glitch_free_n_dff_arn` over one 34-bit bundle - the ten configuration
//      and alarm fields, the clock select, and the cfg_valid flag that
//      authorizes them - captured only when two consecutive samples agree, so
//      a torn word is never applied and the valid bit can never be seen ahead
//      of the fields it qualifies. These change
//      only while software is programming the block; they are not sampled
//      raw. Latency: SYNC_STAGES selected_clk cycles for the chain plus TWO
//      more for the filter (the delayed copy has to agree with the output
//      before the hold loads) - five at the default depth. The one bit that
//      is not held, time_set_mode, arrives in the chain's SYNC_STAGES.
//
//   2. TIME SET COMMIT (pclk -> counter), event + 48 bits of data
//      `cdc_4_phase_handshake`. Software raises RTC_CONFIG.time_set_mode,
//      writes the six time registers (which STAGE in the register block -
//      see rtc_config_regs.sv), then clears time_set_mode; that falling edge
//      is the commit. The six staged bytes cross as ONE closed-loop transfer
//      and load all six counters on a single counter-domain edge, so no field
//      can be lost or mixed with a previous batch. Closed loop, so it is
//      correct at ANY clock ratio - including the real 100 MHz : 32.768 kHz.
//      Latency: the load lands ~4-5 selected_clk cycles after the commit and
//      the full four-phase cycle completes in ~7 (~210 us on real silicon);
//      the register block keeps presenting the STAGED values until
//      `time_commit_busy` drops, so the readback never shows a stale time.
//
//      FOUR-phase, not two-phase, because the two domains reset
//      INDEPENDENTLY (`presetn` and `rtc_resetn` are separate pins and the
//      counter domain is meant to survive an APB reset). A two-phase
//      handshake stores its transfer state as toggle PARITY, which is
//      relative: reset one side alone and the other side's stale toggle
//      reads as a brand-new request. Measured both ways round on this block:
//      a presetn-only pulse fabricated a commit of the all-zero data the
//      same reset had just cleared (day/month loaded 0), and an
//      rtc_resetn-only pulse replayed the last committed time into the
//      freshly reset counters. In four-phase the request is a LEVEL and
//      `req = 0` IS idle, absolutely - a reset side observing req low
//      correctly concludes nothing is pending. See docs/markdown/rtl-cdc/
//      cdc.md "Reset Considerations", which states this as a design rule.
//
//      WATCHDOG, AND WHAT IT DOES NOT DO: if the counter clock is not
//      running the request can never be acknowledged.
//      COMMIT_TIMEOUT_CYCLES bounds the wait and the expiry is REPORTED -
//      RTC_STATUS.commit_timeout, sticky, W1C - but the transfer is NOT
//      cancelled. It stays pending with its data held, and lands unchanged
//      whenever the counter clock returns. So commit_timeout means exactly
//      "not acknowledged within the window; read the time back to find out
//      where it got to", and a timed-out commit MAY STILL LAND LATER,
//      carrying the time software asked for.
//
//      Cancelling was tried and is wrong: resetting the source side alone
//      drops the request level but leaves the DESTINATION's four-phase
//      state (its ack level, reset only by rtc_resetn) behind, so the next
//      request is satisfied by that stale ack in about one pclk cycle
//      instead of a real round trip - the protocol stops being a handshake.
//      Measured: req held high for 1 cycle where a genuine crossing needs
//      tens. Withdrawing a request needs BOTH sides to agree, which is
//      another handshake; not cancelling is simpler and strictly safer,
//      because the worst case is a correct time arriving late rather than
//      an unsynchronised link.
//
//      One commit may be queued behind an un-acknowledged one. It is only
//      handed to the handshake when the link is idle again, so a stalled
//      transfer can never be delivered twice, and the queued commit carries
//      the values captured at ITS OWN commit pulse - r_commit_data is loaded
//      from the staging registers when time_set_commit fires, not later when
//      the link finally accepts it, so what software wrote is what lands
//      however long the queue waits. `time_commit_busy` is cleared by the
//      timeout EVENT and never by its level, so a retry issued during a
//      stall keeps the staged registers visible until it lands or until its
//      own window expires, whichever comes first.
//
//      A QUEUED COMMIT HAS ITS OWN COMMIT_TIMEOUT_CYCLES WINDOW, counted in
//      pclk from its commit pulse. If it is not accepted within that window,
//      commit_timeout is reported again and busy is released while the
//      commit stays queued. A commit accepted within its window inherits
//      nothing and reports nothing - which is every commit in normal
//      operation, where the queue drains in about ten counter clocks. The
//      window exists because a queued commit that is never accepted cannot
//      be reported any other way: the in-flight watchdog is a level that
//      never dropped, so its edge detector can never fire a second time, and
//      busy would hang forever with the staged bytes pinned in the register
//      file and time_valid low. Expiry does NOT cancel anything -
//      r_commit_pend and r_commit_data are kept, the commit lands when the
//      clock returns, and the flag it raised retires by itself when the
//      commit that FINALLY LANDS FROM THAT SLOT completes. A THIRD commit
//      while one is queued replaces r_commit_data, re-raises busy and gives
//      itself a fresh window - the queue stays one deep and only the newest
//      word is ever delivered - but the report already standing for the slot
//      is not orphaned by the replacement: it retires when that newest word
//      lands.
//
//      RESETS AND THIS LINK. The source side is reset with the COUNTER
//      domain (rtc_resetn, synchronized into pclk), NOT with the bus:
//        - presetn alone: the link is untouched. An in-flight commit lands
//          intact. This is the whole point - resetting the source alone
//          zeroes r_src_data_hold while the request is already inside the
//          destination's synchronizer (the destination then loads zeros),
//          and it abandons the destination's ack level, which afterwards
//          satisfies the next request in about one pclk cycle instead of a
//          real round trip. Both were measured on this block.
//        - rtc_resetn alone (or both): BOTH ends reset together, so the link
//          is idle and an unacknowledged commit is DROPPED. Software must
//          re-issue it. Retiring a transfer without both ends agreeing is
//          not possible in any handshake, which is why this is the only
//          reset allowed to touch the source.
//
//   3. TIME READ (counter -> pclk), 49 bits, must be COHERENT
//      Two paths, both landing in the same pclk shadow registers:
//        (a) `sync_pulse` on the counter-domain update event, which captures
//            r_snap_* - a snapshot loaded atomically on the SAME edge the
//            counters change and stable for a whole second afterwards. This
//            is the fast path: the shadow is coherent ~3-4 pclk after a tick.
//        (b) `glitch_free_n_dff_arn` (3 flops) over {time_valid, six
//            counters}, captured only when two CONSECUTIVE synchronized
//            samples are identical. A counter change is instantaneous
//            relative to pclk, so at most ONE sample of the chain can be a
//            half-old/half-new mix; requiring the same word twice in a row
//            rejects that sample and can never latch a torn time. This path
//            needs no gating handshake, so it also picks up changes that
//            produce no event at all (a testbench forcing the counters, or a
//            publish that was never seen), which makes the shadow
//            self-healing rather than dependent on one pulse.
//      Read latency: one tick plus 3-4 pclk of synchronizer.
//
//      The pclk shadow is also seeded safely out of reset: the synchronizer
//      chain resets to zero and takes SYNC_STAGES cycles to fill with real
//      counter values, and "all zero" is a legal-looking but WRONG time
//      (day 0, month 0). The capture is gated until the chain has filled.
//
//   4. STATUS EVENTS (counter -> pclk)
//      r_second_tick and r_alarm_match are LEVELS one counter-clock wide
//      (~30.5 us on silicon). They are synchronized with
//      `glitch_free_n_dff_arn` and edge-detected in pclk, so each one becomes
//      a SINGLE-cycle set event. That is what stops a W1C from being undone:
//      the wide source level can no longer re-arm the flag one pclk after
//      software cleared it (round_3 item 2). The sticky flags themselves live
//      here in pclk. A set and a clear in the same cycle: SET WINS, so a tick
//      is never silently dropped.
//
//==============================================================================
// RESET TABLE - which flops reset on which reset
//==============================================================================
//   presetn only            NOTHING that keeps state across a bus reset.
//                           Specifically untouched: the counter domain
//                           (divider, counters, snapshot, alarm and the
//                           applied-configuration hold), the commit
//                           handshake in both directions, the pclk
//                           bookkeeping that tracks it (r_commit_pend /
//                           _busy / _snapped / _inflight / _timedout /
//                           _loaded / _timeout_d / _data, and the queued
//                           commit's watchdog r_pend_wdog / r_pend_wdog_arm
//                           / r_pend_expired / r_pend_reported), the
//                           DESTINATION sides of
//                           u_snap_pulse_sync, u_load_pulse_sync and
//                           u_event_sync with their edge detectors,
//                           r_commit_timeout_flag (the one status flag that
//                           follows the transfer it reports, not the register
//                           file), and r_clk_sel_held with its settle filter.
//                           Reset:
//                           the register file, the read shadow and its fill
//                           counter, the wrapper's snapshot/latch flops, the
//                           config-valid flag, and the alarm/tick status
//                           flags. The counter domain keeps the configuration
//                           it last applied (cfg_valid drops with the
//                           register file, and an unauthorized word is never
//                           loaded), EXCEPT time_set_mode, which is taken
//                           live so a bus reset during staging releases the
//                           pause instead of pinning the divider forever.
//                           A commit in flight or queued still lands - after
//                           a warm bus reset the time software asked for
//                           arrives, carrying r_commit_data.
//   rtc_resetn only         counter domain resets (async assert, release
//                           synchronized onto selected_clk), AND everything
//                           listed above as untouched by presetn, through
//                           u_rtc_rst_pclk_sync. Both ends idle: an
//                           unacknowledged commit is dropped, re-issue it. A
//                           commit staged entirely under this reset never
//                           sets busy and is never delivered on release.
//                           pclk status/shadow keep their flops but the
//                           shadow refills from the reset counters within a
//                           few pclk.
//                           RELEASE DEPENDS ON pclk. The clock-select settle
//                           one-shot runs on pclk and gates u_ctr_reset_sync,
//                           so the counter domain leaves reset roughly 7-9
//                           pclk edges after rtc_resetn rises - and with pclk
//                           stopped it never leaves reset at all. Recovery
//                           requires both clocks running, not just rtc_clk.
//   both                    everything, as at power-on.
//
//   The bookkeeping is on the handshake's reset and not on presetn because
//   they track the same object. Splitting them is a reset-domain crossing
//   with three teeth, all measured: a commit staged while rtc_resetn was low
//   set busy with no way to clear (the primitive holds src_ready low through
//   its own source reset, so nothing can complete OR time out); the timeout
//   edge detector, cleared by presetn while the watchdog level it samples
//   was not, manufactured an event at release; and the COMPLETION EVIDENCE -
//   the destination side of the snapshot pulse synchronizer - is parity, so
//   a bus reset over the load either destroyed the pulse (busy stuck, the
//   register file left presenting staged values) or fabricated one (the
//   pre-commit time published as the commit's answer), one per toggle
//   parity. The same argument covers u_event_sync: reset the synchronized
//   copy of a still-high counter-domain level and release looks like a fresh
//   0->1, manufacturing a status flag with no tick behind it.
//
//   The configuration hold is here for the mirror-image reason (cdc.md Rule
//   5): the register file's reset defaults are a COMMAND once they cross -
//   rtc_enable=0 stops the clock, clock_select=0 flips the mux - so the
//   counter domain applies the crossed bundle only while the crossed
//   cfg_valid flag says software has written RTC_CONFIG since the last bus
//   reset, and otherwise holds what it last applied.
//
//==============================================================================
// REQUIRED TIMING CONSTRAINTS (not optional - the crossings depend on them)
//==============================================================================
// Two of the crossings carry MULTI-BIT data whose bits must land in the same
// destination cycle as each other. A blanket `set_false_path` does NOT give
// that: it permits unbounded skew between bits, and skewed bits defeat both
// the two-identical-samples filter on the read bundle and the quasi-static
// argument for the config bundle. Constrain them as bounded datapaths:
//
//   # counter -> pclk: the 49-bit read bundle (u_read_sync's first stage)
//   set_max_delay -datapath_only \
//       -from [get_pins u_rtc_core/r_{seconds,minutes,hours,day,month,year}_reg[*]/C] \
//       -to   [get_pins u_rtc_core/u_read_sync/*r_q_array_reg[0][*]/D] <pclk_period>
//
//   # pclk -> counter: the config/alarm bundle (u_cfg_sync's first stage)
//   set_max_delay -datapath_only \
//       -from [get_pins u_config_regs/*/C] \
//       -to   [get_pins u_rtc_core/u_cfg_sync/*r_q_array_reg[0][*]/D] <rtc_clk_period>
//
//   # counter -> pclk: the snapshot registers, captured by the sync_pulse
//   #                  event; quasi-static between events but still bounded
//   set_max_delay -datapath_only \
//       -from [get_pins u_rtc_core/r_snap_*_reg[*]/C] \
//       -to   [get_pins u_rtc_core/r_shd_*_reg[*]/D] <pclk_period>
//
//   # single-bit toggles/levels (sync_pulse, the 4-phase req/ack) take the
//   # usual -datapath_only max_delay of one destination period.
//
// The four-phase handshake's own data bus is quasi-static: it is held by
// r_src_data_hold for the whole request and is only sampled after the
// request level has been through the destination synchronizer, so one
// destination period of max_delay is sufficient there too.
//
// TIMEKEEPING WHILE SOFTWARE IS SETTING THE TIME: the divider is held at
// zero while the counter domain sees time_set_mode and across the commit, so
// in the ordinary case there is no tick, no second interrupt, no alarm
// evaluation and no counter advance until the new time has been loaded. That
// pause is BEST EFFORT: time_set_mode crosses through a 3-flop synchronizer,
// and at the production ratio a software sequence short enough may never be
// sampled by the counter domain at all. The hard guarantee is separate and
// does not depend on it - the commit's dst_valid brackets the load and gates
// w_time_update, so a tick can never land adjacent to the load and the time
// that becomes readable after a commit is exactly the committed time. The hold releases ON the load edge -
// it is qualified with dst_valid alone, not with the one-cycle-longer
// w_commit_active used by the alarm gate - so the first second after a
// commit is EXACTLY one divider period (100 selected_clk edges in test mode,
// 32768 in production), not one period plus a hold cycle.
//
// CHECK BY INSPECTION (these were assertions; properties belong in external
// formal bindings, not inside the module):
//   - Counter updates are never back-to-back: a rollover and a commit load
//     cannot land on adjacent counter clocks, because the commit's dst_valid
//     gates w_time_update and the divider restarts from zero on the load.
//   - The snapshot registers are written from the same values on the same
//     edge as the counters, so r_snap_* is the counters or one update behind,
//     never a different time.
//   - A commit load restarts the divider (the hold branch zeroes it on that
//     edge), so the first second after a commit is a whole period.
//
// Deviations, stated rather than hidden:
//   - A commit that is still queued when a bus reset lands still lands, and
//     carries the bytes captured at its commit pulse rather than the register
//     file's reset values.
//   - commit_timeout does not tell you whether the commit landed. It says
//     the acknowledge did not come back in time AND has still not arrived:
//     it is a report of an OUTSTANDING stall, so it is retired when the
//     stalled commit finally completes, as well as by W1C. Software that
//     needs a latched record must read it while the stall persists.
//   - A commit that lands exactly on the alarm value does NOT fire the
//     alarm. Alarms are evaluated on a tick, and a commit is not a tick -
//     setting the clock to the alarm time arms the alarm for the next time
//     the counter REACHES that value, one full second later at the earliest.
//   - `selected_clk` is a plain combinational clock mux. Changing
//     RTC_CONFIG.clock_select while the RTC is enabled can produce a runt
//     clock pulse; software must change it with rtc_enable low. A glitchless
//     mux needs a cell (BUFGMUX/clock gate) that does not belong in portable
//     RTL. A runt pulse also has a second-order effect worth naming: a
//     commit in flight across a live clock_select switch can be stranded
//     (the destination side sees a corrupted or missing edge), in which case
//     it is the watchdog above that resolves it - the commit is abandoned
//     and reported in RTC_STATUS.commit_timeout rather than hanging.
//   - The alarm compare values, the mask and the mode bits cross as ONE
//     quasi-static bundle, sampled free-running. While software is part-way
//     through programming it the counter domain can observe an intermediate
//     combination for one counter clock (a new alarm second against an old
//     alarm minute). Program RTC_ALARM_* and the mask with the alarm
//     disabled, then enable it last; set the counting format before enabling
//     the RTC.
//   - RTC_ALARM_HOUR is compared against the WHOLE hours byte, bit 7
//     included. In 12-hour mode bit 7 is the PM flag, so 3 PM is 0x83 in
//     binary counting and 0x93 in BCD; an alarm hour with bit 7 clear can
//     only ever match an AM hour.
//   - Loading an out-of-range time (day 40, hours 90 in 12-hour mode) is
//     software's problem: the counters accept it and the arithmetic is still
//     defined (every comparison is >=, never ==), but the calendar only
//     becomes meaningful again after the field wraps. In BCD counting a
//     loaded value of 100 or more cannot be represented in two digits, so
//     the next tick CLAMPS it to 99 rather than truncating the tens digit
//     into a nonsense date.
//
// Follows PIC/PIT pattern: separate core logic from register interface

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rtc_core #(
    // Watchdog on the time-set commit handshake, in pclk cycles. FLOOR: the
    // commit needs about ten counter clocks end to end, so this must exceed
    // 10 * (pclk frequency / counter clock frequency) - at 100 MHz pclk
    // against a 32.768 kHz crystal that is ~30500 cycles. The default leaves
    // roughly 2x margin on that worst case and is ~655 us of real time, which
    // is far longer than any healthy commit and far shorter than a human
    // waiting to find out the clock is dead. 0 DISABLES both watchdogs (the
    // handshake primitive's and the queued-commit one); a stalled commit then
    // hangs busy with no report, which is only ever what a formal harness
    // wants.
    parameter int COMMIT_TIMEOUT_CYCLES = 65535
) (
    //========================================================================
    // Clocks and resets
    //========================================================================
    input  wire       clk,            // APB (pclk) domain clock
    input  wire       rst_n,          // APB domain reset, active low
    input  wire       rtc_clk,        // RTC clock (32.768 kHz)
    input  wire       rtc_rst_n,      // Counter domain reset, active low

    //========================================================================
    // Configuration from registers (pclk domain, quasi-static)
    //========================================================================
    input  wire       cfg_rtc_enable,
    input  wire       cfg_hour_mode_12,     // 0=24h, 1=12h
    input  wire       cfg_bcd_mode,         // 0=binary, 1=BCD
    input  wire       cfg_clock_select,     // 0=rtc_clk, 1=clk (for testing)
    input  wire       cfg_time_set_mode,    // 1=allow setting time (stops counter)
    input  wire       cfg_valid,            // 1=RTC_CONFIG has been written since presetn

    input  wire       cfg_alarm_enable,
    input  wire       cfg_alarm_int_enable,
    input  wire       cfg_second_int_enable,

    //========================================================================
    // Time set: staged values (pclk) + commit event
    //========================================================================
    input  wire [7:0] time_seconds_in,
    input  wire [7:0] time_minutes_in,
    input  wire [7:0] time_hours_in,
    input  wire [7:0] time_day_in,
    input  wire [7:0] time_month_in,
    input  wire [7:0] time_year_in,
    input  wire       time_set_commit,      // one pclk pulse: load the six above
    output wire       time_commit_busy,     // high until the load is visible here

    //========================================================================
    // Time read: coherent pclk shadow of the counters
    //========================================================================
    output wire [7:0] time_seconds_out,
    output wire [7:0] time_minutes_out,
    output wire [7:0] time_hours_out,
    output wire [7:0] time_day_out,
    output wire [7:0] time_month_out,
    output wire [7:0] time_year_out,

    //========================================================================
    // Alarm configuration (pclk domain, quasi-static)
    //========================================================================
    input  wire [7:0] alarm_seconds,
    input  wire [7:0] alarm_minutes,
    input  wire [7:0] alarm_hours,
    input  wire       alarm_sec_match_en,
    input  wire       alarm_min_match_en,
    input  wire       alarm_hour_match_en,

    //========================================================================
    // Status outputs (pclk domain)
    //========================================================================
    output wire       status_alarm_flag,
    output wire       status_second_tick,
    output wire       status_time_valid,
    output wire       status_pm_indicator,
    output wire       status_commit_timeout,

    //========================================================================
    // Status flag clears (pclk, one cycle, decoded from the W1C write)
    //========================================================================
    input  wire       clear_alarm_flag,
    input  wire       clear_second_tick,
    input  wire       clear_commit_timeout,

    //========================================================================
    // Interrupt outputs (pclk domain)
    //========================================================================
    output wire       rtc_alarm_irq,
    output wire       rtc_second_irq
);

    //========================================================================
    // Local Parameters
    //========================================================================

    // Divider targets. The counter rolls over when the divider REACHES the
    // target, so the period is TARGET+1 selected_clk cycles: 32768 for the
    // 32.768 kHz crystal (exactly one second) and 100 in clock_select=1 test
    // mode. dv/tbclasses/rtc/rtc_tb.py::force_divider_near_target depends on
    // these two numbers.
    localparam logic [15:0] DIV_TARGET_RTC = 16'd32767;
    localparam logic [15:0] DIV_TARGET_SYS = 16'd99;

    localparam int          SYNC_STAGES    = 3;    // synchronizer depth, both ways
    // Wide enough to count SYNC_STAGES, for any legal SYNC_STAGES (2-5) -
    // a fixed 2 bits silently stops counting at 3.
    localparam int          FILL_CNT_W     = $clog2(SYNC_STAGES + 1);
    localparam int          CFG_WIDTH      = 34;   // config/alarm bundle + valid
    // Everything in the bundle except cfg_valid (top) and time_set_mode
    // (bit 3), which is deliberately not held - see the pause below.
    localparam int          HOLD_WIDTH     = CFG_WIDTH - 2;
    // Width of the queued-commit watchdog, which counts the same window as
    // the handshake's own. COMMIT_TIMEOUT_CYCLES = 0 means "watchdog
    // disabled" (the handshake primitive documents and guards the same
    // value), and $clog2(1) is 0, which is not a legal width - so the width
    // is floored at 1 and the watchdog is gated off by PEND_WDOG_EN instead.
    localparam int          PEND_WDOG_W    =
        (COMMIT_TIMEOUT_CYCLES > 1) ? $clog2(COMMIT_TIMEOUT_CYCLES + 1) : 1;
    localparam bit          PEND_WDOG_EN   = (COMMIT_TIMEOUT_CYCLES != 0);
    localparam int          TIME_WIDTH     = 48;   // six time bytes
    localparam int          READ_WIDTH     = 49;   // time_valid + six time bytes
    // Reset-default encoding of the read bundle, used to seed the stability
    // filter so the post-reset transient can never publish day/month = 0.
    localparam logic [READ_WIDTH-1:0] READ_RESET =
        {1'b0, 8'h00, 8'h01, 8'h01, 8'h00, 8'h00, 8'h00};

    //========================================================================
    // Signals: clock select and counter-domain reset
    //========================================================================

    wire                    selected_clk;
    wire                    w_ctr_rst_n;

    //========================================================================
    // Signals: configuration crossing (pclk -> counter domain)
    //========================================================================

    wire [CFG_WIDTH-1:0]    w_cfg_bundle_pclk;
    wire  [CFG_WIDTH-1:0]   w_cfg_sync;
    logic [CFG_WIDTH-1:0]   r_cfg_sync_d;
    wire                    w_cfg_stable;
    wire                    w_cfg_sync_valid;
    logic [HOLD_WIDTH-1:0]  r_cfg_hold;
    wire  [HOLD_WIDTH-1:0]  w_cfg_holdable;
    wire  [HOLD_WIDTH-1:0]  w_cfg_applied;
    logic                   r_clk_sel_held;
    logic                   r_clk_sel_d;
    logic [SYNC_STAGES-1:0] r_sel_stable_pipe;
    logic                   r_sel_settled;
    wire                    w_ctr_rst_in_n;
    wire                    w_ctr_enable;
    wire                    w_ctr_hour12;
    wire                    w_ctr_bcd;
    wire                    w_ctr_time_set;
    wire                    w_ctr_clk_sel;
    wire                    w_ctr_alarm_en;
    wire                    w_ctr_sec_match_en;
    wire                    w_ctr_min_match_en;
    wire                    w_ctr_hour_match_en;
    wire [7:0]              w_ctr_alarm_sec;
    wire [7:0]              w_ctr_alarm_min;
    wire [7:0]              w_ctr_alarm_hour;

    //========================================================================
    // Signals: time-set commit handshake
    //========================================================================

    wire [TIME_WIDTH-1:0]   w_commit_stage_data;
    wire                    w_commit_src_valid;
    wire                    w_commit_src_ready;
    wire                    w_commit_src_rst_n;
    wire                    w_commit_bk_rst_n;
    wire                    w_rtc_rst_n_pclk;
    logic [TIME_WIDTH-1:0]  r_commit_data;
    logic                   r_commit_inflight;
    logic                   r_commit_timedout;
    logic [PEND_WDOG_W-1:0] r_pend_wdog;
    logic                   r_pend_wdog_arm;
    logic                   r_pend_expired;
    logic                   r_pend_reported;
    wire                    w_pend_timeout_evt;
    wire                    w_timeout_evt_any;
    logic                   r_commit_loaded;
    wire                    w_commit_load_pclk;
    wire                    w_commit_timeout_resolved;
    wire                    w_commit_accept;
    wire                    w_commit_complete;
    wire                    w_commit_retire;
    wire                    w_commit_idle_now;
    wire                    w_commit_visible;
    wire                    w_commit_timeout;
    logic                   r_commit_timeout_d;
    wire                    w_commit_timeout_evt;
    wire                    w_commit_dst_valid;
    wire [TIME_WIDTH-1:0]   w_commit_dst_data;
    wire                    w_commit_load;      // counter domain: load THIS edge
    wire                    w_commit_active;    // counter domain: load in flight
    logic                   r_commit_valid_d;   // counter domain
    logic                   r_commit_pend;      // pclk
    logic                   r_commit_busy;      // pclk
    logic                   r_commit_snapped;   // pclk
    wire                    w_commit_done;      // pclk

    //========================================================================
    // Signals: divider and tick (counter domain)
    //========================================================================

    logic [15:0]            r_clk_div_counter;
    logic                   r_second_tick;
    wire  [15:0]            w_clk_div_target;
    wire                    w_div_rollover;
    wire                    w_count_en;
    wire                    w_time_update;
    wire                    w_snap_pulse;

    //========================================================================
    // Signals: time counters and their coherent snapshot (counter domain)
    //========================================================================

    logic [7:0]             r_seconds;
    logic [7:0]             r_minutes;
    logic [7:0]             r_hours;
    logic [7:0]             r_day;
    logic [7:0]             r_month;
    logic [7:0]             r_year;
    logic                   r_time_valid;

    logic [7:0]             r_snap_seconds;
    logic [7:0]             r_snap_minutes;
    logic [7:0]             r_snap_hours;
    logic [7:0]             r_snap_day;
    logic [7:0]             r_snap_month;
    logic [7:0]             r_snap_year;
    logic                   r_snap_valid;

    //========================================================================
    // Signals: calendar arithmetic (counter domain, combinational)
    //========================================================================

    logic [7:0]             w_sec_bin;
    logic [7:0]             w_min_bin;
    logic [7:0]             w_hour_bin;
    logic [7:0]             w_day_bin;
    logic [7:0]             w_month_bin;
    logic [7:0]             w_year_bin;
    logic                   w_hour_pm;
    logic [7:0]             w_max_days;

    logic                   w_carry_min;
    logic                   w_carry_hour;
    logic                   w_carry_day;
    logic                   w_carry_month;
    logic                   w_carry_year;

    logic [7:0]             w_nxt_sec_bin;
    logic [7:0]             w_nxt_min_bin;
    logic [7:0]             w_nxt_hour_bin;
    logic [7:0]             w_nxt_day_bin;
    logic [7:0]             w_nxt_month_bin;
    logic [7:0]             w_nxt_year_bin;
    logic                   w_nxt_pm;
    logic [7:0]             w_nxt_hour_enc;

    logic [7:0]             w_next_seconds;
    logic [7:0]             w_next_minutes;
    logic [7:0]             w_next_hours;
    logic [7:0]             w_next_day;
    logic [7:0]             w_next_month;
    logic [7:0]             w_next_year;

    //========================================================================
    // Signals: alarm comparator (counter domain)
    //========================================================================

    wire                    w_alarm_eval;
    wire                    w_alarm_hit;
    logic                   r_alarm_match;

    //========================================================================
    // Signals: read crossing (counter -> pclk)
    //========================================================================

    wire [READ_WIDTH-1:0]   w_read_bundle_ctr;
    wire [READ_WIDTH-1:0]   w_read_bundle_pclk;
    logic [READ_WIDTH-1:0]  r_read_bundle_d;
    logic [FILL_CNT_W-1:0]  r_read_fill;
    wire                    w_read_filled;
    wire                    w_read_stable;
    wire                    w_snap_valid_pclk;

    logic [7:0]             r_shd_seconds;
    logic [7:0]             r_shd_minutes;
    logic [7:0]             r_shd_hours;
    logic [7:0]             r_shd_day;
    logic [7:0]             r_shd_month;
    logic [7:0]             r_shd_year;
    logic                   r_shd_valid;

    //========================================================================
    // Signals: status events and sticky flags (pclk)
    //========================================================================

    wire [1:0]              w_evt_sync;
    logic [1:0]             r_evt_sync_d;
    logic [1:0]             r_evt_sync_d2;
    wire                    w_tick_event;
    wire                    w_alarm_event;
    logic                   r_alarm_flag;
    logic                   r_second_tick_flag;
    logic                   r_commit_timeout_flag;

    //========================================================================
    // Encoding Helpers
    //========================================================================
    // Every calendar comparison below is done on BINARY values; BCD only ever
    // exists at the register boundary. That is deliberate: GitHub #56 H5 was a
    // BCD "conversion" that truncated {4'd0, days/10, days%10} (20 bits) into
    // an 8-bit result, leaving days%10 and rolling the month after day 2.

    function automatic logic [7:0] f_to_bin(input logic [7:0] val, input logic is_bcd);
        logic [7:0] tens_x10;
        tens_x10 = {4'd0, val[7:4]} * 8'd10;
        f_to_bin = is_bcd ? (tens_x10 + {4'd0, val[3:0]}) : val;
    endfunction

    function automatic logic [7:0] f_to_enc(input logic [7:0] val, input logic is_bcd);
        logic [7:0] clamped;
        logic [3:0] tens;
        logic [3:0] ones;
        // Two BCD digits cannot represent 100 or more. That only arises from
        // software loading an out-of-range value (or from bit 7 of a 12-hour
        // hours byte reaching here, which it cannot), and the honest answer
        // is to CLAMP: truncating the tens digit instead - which is what a
        // bare val/10 would do - turns 0xA5 into a plausible-looking wrong
        // date, and a wrong date that looks right is the worse failure.
        clamped  = (val > 8'd99) ? 8'd99 : val;
        tens     = 4'(clamped / 8'd10);
        ones     = 4'(clamped % 8'd10);
        f_to_enc = is_bcd ? {tens, ones} : val;
    endfunction

    // Days in month, in BINARY. Leap rule for 2000-2099: every year divisible
    // by 4 (2000 is divisible by 400, so there is no century exception in
    // range). Checked at a non-symmetric point: month 2 of year 24 must be 29
    // and month 2 of year 25 must be 28 - a rule that got both right by
    // accident would still have to get 4/6/9/11 -> 30 right.
    function automatic logic [7:0] f_days_in_month(input logic [7:0] month_bin,
                                                   input logic [7:0] year_bin);
        logic is_leap;
        is_leap = ((year_bin % 8'd4) == 8'd0);
        case (month_bin)
            8'd1, 8'd3, 8'd5, 8'd7, 8'd8, 8'd10, 8'd12: f_days_in_month = 8'd31;
            8'd4, 8'd6, 8'd9, 8'd11:                    f_days_in_month = 8'd30;
            8'd2:                                       f_days_in_month = is_leap ? 8'd29 : 8'd28;
            default:                                    f_days_in_month = 8'd31;
        endcase
    endfunction

    //========================================================================
    // Clock Selection and Counter-Domain Reset
    //========================================================================

    // The clock source is selected from a HELD copy, not from the register
    // field. The field resets to 0 on presetn like every other register, and
    // a bus reset must not re-clock a domain that is meant to keep counting
    // through it (cdc.md Rule 5). This flop tracks the field only while
    // cfg_valid says software has actually written RTC_CONFIG, and it is
    // reset with the far domain so presetn cannot touch it.
    //
    // It is a pclk flop rather than a counter-domain one because it feeds the
    // mux that makes the counter clock. The mux itself is still plain
    // combinational logic, so the "change clock_select only with rtc_enable
    // low" constraint below still applies to genuine software changes.
    assign selected_clk = r_clk_sel_held ? clk : rtc_clk;

    `ALWAYS_FF_RST(clk, w_rtc_rst_n_pclk,
        if (`RST_ASSERTED(w_rtc_rst_n_pclk)) begin
            r_clk_sel_held <= 1'b0;
        end else if (cfg_valid) begin
            r_clk_sel_held <= cfg_clock_select;
        end
    )

    // r_clk_sel_held moves the clock mux twice around an rtc_resetn pulse:
    // the async reset drops the select mid-pclk (selected_clk switches) and it
    // reloads one pclk after release (switches back). u_ctr_reset_sync is
    // clocked BY selected_clk, so without help it can be mid-deassertion when
    // the mux moves and let the counter domain out of reset on a runt edge.
    //
    // So the counter reset release is held until the select has been stable
    // for SYNC_STAGES pclk cycles after the far reset lifts. This is a
    // ONE-SHOT per rtc_resetn: cleared asynchronously by that reset, set once
    // after it, and sticky from then on. It must not re-arm on a later select
    // change, because a live software write of clock_select would then assert
    // the counter reset and wipe the time of day - and it would not even
    // help, since the mux has already moved by the time the flag could react.
    // A live change of clock_select stays the documented limitation: change it
    // only with rtc_enable low. Assertion is unaffected either way (it is
    // asynchronous, and a runt during assertion is harmless).
    `ALWAYS_FF_RST(clk, w_rtc_rst_n_pclk,
        if (`RST_ASSERTED(w_rtc_rst_n_pclk)) begin
            r_clk_sel_d       <= 1'b0;
            r_sel_stable_pipe <= '0;
            r_sel_settled     <= 1'b0;
        end else begin
            r_clk_sel_d       <= r_clk_sel_held;
            r_sel_stable_pipe <= {r_sel_stable_pipe[SYNC_STAGES-2:0],
                                  (r_clk_sel_held == r_clk_sel_d)};
            r_sel_settled     <= r_sel_settled || (&r_sel_stable_pipe);
        end
    )

    // ANDed into the async reset input: a registered term, and the only
    // direction it can glitch (settled falling) asserts reset, which is safe.
    assign w_ctr_rst_in_n = rtc_rst_n && r_sel_settled;

    // rtc_resetn is the counter domain's reset (GitHub #56 round_2 item 5: the
    // port used to be declared and wired to nothing). Async assert so the
    // counters reset even with no RTC clock; the release is synchronized to
    // selected_clk so it cannot violate recovery/removal.
    reset_sync #(
        .N                (SYNC_STAGES)
    ) u_ctr_reset_sync (
        .clk              (selected_clk),
        .rst_n            (w_ctr_rst_in_n),
        .sync_rst_n       (w_ctr_rst_n)
    );

    // The counter domain's reset, brought into pclk (async assert, sync
    // deassert) so the pclk-side of the commit handshake can be reset with
    // the far domain rather than with the bus. See the RESET TABLE in the
    // header for what this does and does not reset.
    reset_sync #(
        .N                (SYNC_STAGES)
    ) u_rtc_rst_pclk_sync (
        .clk              (clk),
        .rst_n            (rtc_rst_n),
        .sync_rst_n       (w_rtc_rst_n_pclk)
    );

    //========================================================================
    // Crossing 1: Configuration / Alarm (pclk -> counter domain)
    //========================================================================

    assign w_cfg_bundle_pclk = {cfg_valid,             // [33]
                                cfg_clock_select,      // [32]
                                alarm_hours,           // [31:24]
                                alarm_minutes,         // [23:16]
                                alarm_seconds,         // [15:8]
                                alarm_hour_match_en,   // [7]
                                alarm_min_match_en,    // [6]
                                alarm_sec_match_en,    // [5]
                                cfg_alarm_enable,      // [4]
                                cfg_time_set_mode,     // [3]
                                cfg_bcd_mode,          // [2]
                                cfg_hour_mode_12,      // [1]
                                cfg_rtc_enable};       // [0]

    // cfg_valid travels INSIDE this bundle, and the capture below only ever
    // takes a word that two consecutive samples agree on. That is what stops
    // the valid bit being observed ahead of the fields it qualifies: a
    // separately-crossed valid resolves independently of the data, and one
    // counter clock of valid=1 against pre-write data is enough to present
    // rtc_enable=0 and zero the divider mid-second. A torn word is rejected
    // whole, valid bit included, so the pair can never come apart.
    //
    // SYNC_STAGES deep, like the read and event crossings in this file. The
    // filter below sits ON TOP of the full chain, and that ordering is the
    // whole point: the two-identical-samples argument is only valid on a
    // settled output. Read a stage-1 output instead and a metastable bit can
    // resolve one way into the comparator and the other into the capture
    // register's D input in the same cycle, so "seen twice" stops meaning
    // "never in flight" - and the same bit would be feeding the divider
    // control directly.
    glitch_free_n_dff_arn #(
        .FLOP_COUNT       (SYNC_STAGES),
        .WIDTH            (CFG_WIDTH)
    ) u_cfg_sync (
        .clk              (selected_clk),
        .rst_n            (w_ctr_rst_n),
        .d                (w_cfg_bundle_pclk),
        .q                (w_cfg_sync)
    );

    // Both operands are the settled chain output, one cycle apart: an
    // asynchronous transition can be caught by at most ONE sample, so a word
    // the output has shown twice running is a word that was never in flight.
    assign w_cfg_stable     = (w_cfg_sync == r_cfg_sync_d);
    assign w_cfg_sync_valid = w_cfg_sync[CFG_WIDTH-1];

    // The counter domain OBEYS only what it has CAPTURED - never the live
    // crossing output, which can show a torn word for one cycle. A settled
    // word is loaded into the hold only when its own valid bit says software
    // authorized it, so the register file's reset defaults (which arrive with
    // valid=0) cannot stop the clock or switch its source (cdc.md Rule 5).
    // r_cfg_valid_ctr tracks the valid bit of the last settled word whether
    // or not it was authorized, which is what releases the staging pause
    // below when a bus reset clears cfg_valid.
    `ALWAYS_FF_RST(selected_clk, w_ctr_rst_n,
        if (`RST_ASSERTED(w_ctr_rst_n)) begin
            r_cfg_sync_d <= '0;
            r_cfg_hold   <= '0;
        end else begin
            r_cfg_sync_d <= w_cfg_sync;
            if (w_cfg_stable && w_cfg_sync_valid) begin
                r_cfg_hold <= w_cfg_holdable;
            end
        end
    )

    // The holdable fields are the quasi-static ones - everything except
    // cfg_valid, which authorizes them, and time_set_mode, which must never
    // be held (below). Bits 2:0 keep their bundle positions; the fields above
    // the removed time_set bit close up by one.
    assign w_cfg_holdable      = {w_cfg_sync[CFG_WIDTH-2:4], w_cfg_sync[2:0]};

    assign w_cfg_applied       = r_cfg_hold;

    //   hold bit  field                 hold bits  field
    //   0         rtc_enable            14:7       alarm_seconds
    //   1         hour_mode_12          22:15      alarm_minutes
    //   2         bcd_mode              30:23      alarm_hours
    //   3         alarm_enable          31         clock_select
    //   6:4       sec/min/hour match_en
    assign w_ctr_enable        = w_cfg_applied[0];
    assign w_ctr_hour12        = w_cfg_applied[1];
    assign w_ctr_bcd           = w_cfg_applied[2];
    // time_set_mode is a TRANSIENT control, not quasi-static configuration,
    // and it is the one bit in this bundle that must never be held. Held, it
    // outlives the software that would have cleared it: a bus reset during
    // staging clears the register file's copy but not the counter domain's,
    // the pause pins the divider at zero, and the clock stops for good.
    // Worse, a held copy re-arms - the first RTC_CONFIG write after such a
    // reset raises the crossed valid bit as the chain fills, two counter
    // clocks before the hold turns over, so a stale 1 would pause the divider
    // again for those cycles and silently drop up to a second.
    //
    // So the pause is the crossing output itself, never the hold. A single
    // bit through a 3-flop chain cannot read a spurious 0 in the middle of a
    // held 1 - a transition is mis-sampled at most once, at the transition -
    // so there is nothing for a held copy to protect against. It reaches the
    // counter domain in SYNC_STAGES counter clocks, two ahead of the hold.
    assign w_ctr_time_set      = w_cfg_sync[3];
    assign w_ctr_alarm_en      = w_cfg_applied[3];
    assign w_ctr_sec_match_en  = w_cfg_applied[4];
    assign w_ctr_min_match_en  = w_cfg_applied[5];
    assign w_ctr_hour_match_en = w_cfg_applied[6];
    assign w_ctr_alarm_sec     = w_cfg_applied[14:7];
    assign w_ctr_alarm_min     = w_cfg_applied[22:15];
    assign w_ctr_alarm_hour    = w_cfg_applied[30:23];
    // The divider TARGET takes the held copy - now that nothing is applied
    // live, this is simply true rather than aspirational - so it always
    // agrees with the clock the mux is actually on.
    assign w_ctr_clk_sel       = w_cfg_applied[31];

    //========================================================================
    // Crossing 2: Time Set Commit (pclk -> counter domain)
    //========================================================================

    assign w_commit_stage_data = {time_year_in, time_month_in, time_day_in,
                                  time_hours_in, time_minutes_in, time_seconds_in};

    // The source side is reset with the COUNTER domain, not with the bus.
    // presetn deliberately does not appear here: a bus-only reset must leave
    // an in-flight commit alone. Zeroing r_src_data_hold while the request is
    // already inside the destination's synchronizer makes the destination
    // load zeros, and resetting the source FSM while the destination's ack
    // level survives leaves that ack to satisfy the NEXT request in about one
    // pclk cycle instead of a real round trip. Both were measured.
    //
    // rtc_resetn DOES reset it, through the synchronizer above, because that
    // reset also resets the destination: both ends go idle together, which is
    // the only way to retire a transfer without an agreement protocol. An
    // unacknowledged commit is then simply dropped and software must re-issue
    // it.
    assign w_commit_src_rst_n = w_rtc_rst_n_pclk;

    // Every flop that TRACKS this handshake shares that reset. Two flops in
    // one clock domain under different resets is a reset-domain crossing, and
    // this one has two teeth: with the bookkeeping on presetn, a commit
    // staged while rtc_resetn was low set busy with no way to clear (the
    // primitive holds src_ready low through its own source reset, so nothing
    // can complete OR time out) and then delivered on release, undoing the
    // reset; and the timeout edge detector, reset to 0 by presetn while the
    // watchdog level it samples was not, manufactured an event at release.
    assign w_commit_bk_rst_n = w_commit_src_rst_n;

    // src_valid is asserted ONLY in a cycle the handshake can take it, which
    // keeps the primitive's "valid may not drop while ready is low" contract
    // vacuously true however r_commit_pend is reset. (r_commit_pend takes the
    // handshake's own reset - see w_commit_bk_rst_n above - so a queued
    // commit survives a bus reset and lands, carrying r_commit_data rather
    // than the register file's reset values.)
    assign w_commit_src_valid = r_commit_pend && w_commit_src_ready;

    cdc_4_phase_handshake #(
        .DATA_WIDTH       (TIME_WIDTH),
        .SYNC_STAGES      (SYNC_STAGES),
        .TIMEOUT_CYCLES   (COMMIT_TIMEOUT_CYCLES),
        .FAST_PATH        (1'b0)
    ) u_commit_cdc (
        .clk_src          (clk),
        .rst_src_n        (w_commit_src_rst_n),
        .src_valid        (w_commit_src_valid),
        .src_ready        (w_commit_src_ready),
        .src_data         (r_commit_data),
        .src_timeout      (w_commit_timeout),

        .clk_dst          (selected_clk),
        .rst_dst_n        (w_ctr_rst_n),
        .dst_valid        (w_commit_dst_valid),
        .dst_ready        (w_commit_load),
        .dst_data         (w_commit_dst_data)
    );

    // Accept one counter-domain cycle after dst_valid rises. The delay widens
    // w_commit_active into a three-cycle window that brackets the load, which
    // is what gates the alarm comparator off an unsettled counter (round_3
    // item 3) rather than only on the load edge itself.
    `ALWAYS_FF_RST(selected_clk, w_ctr_rst_n,
        if (`RST_ASSERTED(w_ctr_rst_n)) begin
            r_commit_valid_d <= 1'b0;
        end else begin
            r_commit_valid_d <= w_commit_dst_valid;
        end
    )

    assign w_commit_load   = w_commit_dst_valid && r_commit_valid_d;
    assign w_commit_active = w_commit_dst_valid || r_commit_valid_d;

    // The watchdog output is a LEVEL: it stays asserted for as long as the
    // handshake sits un-acknowledged, which with a stopped counter clock is
    // forever. It is edge-detected and qualified in the commit bookkeeping
    // below, where r_commit_timeout_d lives under the same reset as the
    // watchdog itself.

    //========================================================================
    // Clock Divider (counter domain)
    //========================================================================

    assign w_clk_div_target   = w_ctr_clk_sel ? DIV_TARGET_SYS : DIV_TARGET_RTC;
    assign w_div_rollover     = (r_clk_div_counter >= w_clk_div_target);
    assign w_count_en         = w_ctr_enable && !w_ctr_time_set;
    // The commit BRACKETS the tick: dst_valid is asserted the counter cycle
    // before the load and through it, so a rollover can never land on the
    // cycle adjacent to a commit load and the counters can never take two
    // updates on consecutive counter clocks. This is the hard guarantee. The
    // staging pause below it (w_ctr_time_set) is best effort - at the
    // production ratio a short time_set_mode may never be sampled by the
    // counter domain at all - so the "exactly the committed time" property
    // must not, and does not, depend on it.
    assign w_time_update      = w_div_rollover && w_count_en && !w_commit_dst_valid;
    assign w_snap_pulse       = w_time_update || w_commit_load;

    `ALWAYS_FF_RST(selected_clk, w_ctr_rst_n,
        if (`RST_ASSERTED(w_ctr_rst_n)) begin
            r_clk_div_counter <= 16'h0;
            r_second_tick     <= 1'b0;
        end else if (!w_ctr_enable || w_ctr_time_set || w_commit_dst_valid) begin
            // Held at zero for the whole of time_set_mode and across the
            // commit itself: no rollover, so no tick, no interrupt, no alarm
            // evaluation and no counter advance while software is staging a
            // time. The second that was in progress when staging began is
            // abandoned rather than carried over, so the first tick after a
            // commit is a WHOLE second after the load - which is the only
            // reading of "I just set the time to 12:00:00" that does not
            // produce a short first second.
            r_clk_div_counter <= 16'h0;
            r_second_tick     <= 1'b0;
        end else if (w_div_rollover) begin
            r_clk_div_counter <= 16'h0;
            r_second_tick     <= 1'b1;
        end else begin
            r_clk_div_counter <= r_clk_div_counter + 16'h1;
            r_second_tick     <= 1'b0;
        end
    )

    //========================================================================
    // Calendar Arithmetic (counter domain, combinational)
    //========================================================================
    //
    // 12-hour sequencing, stated as a table because GitHub #56 H6 got it
    // wrong by testing the wrong transition. The interesting (non-symmetric)
    // entries are the two 11->12 rows: they differ from each other and from
    // every 12->1 row.
    //
    //   hours  PM | next hours  next PM  day carry
    //   -------------------------------------------
    //     11    0 |     12         1         0      (11:59:59 AM -> 12:00 PM)
    //     11    1 |     12         0         1      (11:59:59 PM -> 12:00 AM, midnight)
    //     12    x |      1         x         0      (12:59:59    ->  1:00, no toggle)
    //      n    x |    n+1         x         0
    //
    // The day carries on the 11 PM -> 12 AM step ONLY. The old code toggled on
    // reaching 12 and carried the day at noon.

    always_comb begin
        w_sec_bin   = f_to_bin(r_seconds, w_ctr_bcd);
        w_min_bin   = f_to_bin(r_minutes, w_ctr_bcd);
        w_hour_pm   = w_ctr_hour12 && r_hours[7];
        w_hour_bin  = f_to_bin({1'b0, r_hours[6:0]}, w_ctr_bcd);
        w_day_bin   = f_to_bin(r_day,   w_ctr_bcd);
        w_month_bin = f_to_bin(r_month, w_ctr_bcd);
        w_year_bin  = f_to_bin(r_year,  w_ctr_bcd);
        w_max_days  = f_days_in_month(w_month_bin, w_year_bin);

        // Seconds
        w_carry_min   = (w_sec_bin >= 8'd59);
        w_nxt_sec_bin = w_carry_min ? 8'd0 : (w_sec_bin + 8'd1);

        // Minutes
        w_carry_hour  = w_carry_min && (w_min_bin >= 8'd59);
        if (!w_carry_min) begin
            w_nxt_min_bin = w_min_bin;
        end else begin
            w_nxt_min_bin = w_carry_hour ? 8'd0 : (w_min_bin + 8'd1);
        end

        // Hours + AM/PM + midnight day carry
        if (!w_carry_hour) begin
            w_nxt_hour_bin = w_hour_bin;
            w_nxt_pm       = w_hour_pm;
            w_carry_day    = 1'b0;
        end else if (w_ctr_hour12) begin
            if (w_hour_bin == 8'd11) begin
                w_nxt_hour_bin = 8'd12;
                w_nxt_pm       = ~w_hour_pm;
                w_carry_day    = w_hour_pm;      // 11 PM -> 12 AM is midnight
            end else if (w_hour_bin >= 8'd12) begin
                w_nxt_hour_bin = 8'd1;           // 12 (or out of range) -> 1
                w_nxt_pm       = w_hour_pm;
                w_carry_day    = 1'b0;
            end else begin
                w_nxt_hour_bin = w_hour_bin + 8'd1;
                w_nxt_pm       = w_hour_pm;
                w_carry_day    = 1'b0;
            end
        end else begin
            w_carry_day    = (w_hour_bin >= 8'd23);
            w_nxt_hour_bin = w_carry_day ? 8'd0 : (w_hour_bin + 8'd1);
            w_nxt_pm       = 1'b0;               // no PM flag in 24-hour mode
        end

        // Day
        w_carry_month = w_carry_day && (w_day_bin >= w_max_days);
        if (!w_carry_day) begin
            w_nxt_day_bin = w_day_bin;
        end else begin
            w_nxt_day_bin = w_carry_month ? 8'd1 : (w_day_bin + 8'd1);
        end

        // Month
        w_carry_year = w_carry_month && (w_month_bin >= 8'd12);
        if (!w_carry_month) begin
            w_nxt_month_bin = w_month_bin;
        end else begin
            w_nxt_month_bin = w_carry_year ? 8'd1 : (w_month_bin + 8'd1);
        end

        // Year (two digits, 2000-2099)
        if (!w_carry_year) begin
            w_nxt_year_bin = w_year_bin;
        end else begin
            w_nxt_year_bin = (w_year_bin >= 8'd99) ? 8'd0 : (w_year_bin + 8'd1);
        end

        // Re-encode
        w_nxt_hour_enc = f_to_enc(w_nxt_hour_bin, w_ctr_bcd);
        w_next_seconds = f_to_enc(w_nxt_sec_bin,   w_ctr_bcd);
        w_next_minutes = f_to_enc(w_nxt_min_bin,   w_ctr_bcd);
        // In 12-hour mode bit 7 carries PM and the hour occupies [6:0]; in
        // 24-hour mode the encoded value IS the whole byte (0-23 / 0x00-0x23,
        // so bit 7 is zero) and there is no PM flag to graft on.
        w_next_hours   = w_ctr_hour12 ? {w_nxt_pm, w_nxt_hour_enc[6:0]} : w_nxt_hour_enc;
        w_next_day     = f_to_enc(w_nxt_day_bin,   w_ctr_bcd);
        w_next_month   = f_to_enc(w_nxt_month_bin, w_ctr_bcd);
        w_next_year    = f_to_enc(w_nxt_year_bin,  w_ctr_bcd);
    end

    //========================================================================
    // Time Counters and Coherent Snapshot (counter domain)
    //========================================================================
    // r_snap_* is loaded from the SAME values on the SAME edge as the
    // counters, so it is always a coherent time, and it only moves when the
    // counters move - which means it is stable for a whole second either side
    // of the pulse that tells pclk to capture it.

    `ALWAYS_FF_RST(selected_clk, w_ctr_rst_n,
        if (`RST_ASSERTED(w_ctr_rst_n)) begin
            r_seconds      <= 8'h00;
            r_minutes      <= 8'h00;
            r_hours        <= 8'h00;
            r_day          <= 8'h01;
            r_month        <= 8'h01;
            r_year         <= 8'h00;
            r_time_valid   <= 1'b0;
            r_snap_seconds <= 8'h00;
            r_snap_minutes <= 8'h00;
            r_snap_hours   <= 8'h00;
            r_snap_day     <= 8'h01;
            r_snap_month   <= 8'h01;
            r_snap_year    <= 8'h00;
            r_snap_valid   <= 1'b0;
        end else if (w_commit_load) begin
            r_seconds      <= w_commit_dst_data[7:0];
            r_minutes      <= w_commit_dst_data[15:8];
            r_hours        <= w_commit_dst_data[23:16];
            r_day          <= w_commit_dst_data[31:24];
            r_month        <= w_commit_dst_data[39:32];
            r_year         <= w_commit_dst_data[47:40];
            r_time_valid   <= 1'b1;
            r_snap_seconds <= w_commit_dst_data[7:0];
            r_snap_minutes <= w_commit_dst_data[15:8];
            r_snap_hours   <= w_commit_dst_data[23:16];
            r_snap_day     <= w_commit_dst_data[31:24];
            r_snap_month   <= w_commit_dst_data[39:32];
            r_snap_year    <= w_commit_dst_data[47:40];
            r_snap_valid   <= 1'b1;
        end else if (w_time_update) begin
            r_seconds      <= w_next_seconds;
            r_minutes      <= w_next_minutes;
            r_hours        <= w_next_hours;
            r_day          <= w_next_day;
            r_month        <= w_next_month;
            r_year         <= w_next_year;
            r_time_valid   <= 1'b1;
            r_snap_seconds <= w_next_seconds;
            r_snap_minutes <= w_next_minutes;
            r_snap_hours   <= w_next_hours;
            r_snap_day     <= w_next_day;
            r_snap_month   <= w_next_month;
            r_snap_year    <= w_next_year;
            r_snap_valid   <= 1'b1;
        end
    )

    //========================================================================
    // Alarm Comparison (counter domain)
    //========================================================================
    // The comparison is against w_next_*: the time this tick is about to make
    // READABLE, not the one it is retiring. The tick that advances seconds
    // 29 -> 30 is the tick that both publishes 30 to the shadow and, with the
    // alarm set to 30, raises the flag - so software that sees the flag and
    // reads the clock sees the alarm value, not one second past it.
    // Comparing r_* instead (the pre-advance value) put the flag one tick
    // late, which reads as "the alarm fired at 31".
    //
    // The evaluation edge is unchanged: it is still the rollover, so the flag
    // is registered on the same edge that the counters advance and reaches
    // pclk with the same synchronizer latency as the new time.
    //
    // The hours comparison uses the WHOLE byte, bit 7 included, so in
    // 12-hour mode the alarm hour carries its own AM/PM: 3 PM is 0x83 binary
    // / 0x93 BCD. Gated by !time_set_mode (round_3 item 3 - a counter frozen
    // mid-programming sitting on the alarm value used to raise the flag) and
    // by !w_commit_active (the counters are mid-load and are not a settled
    // time).

    assign w_alarm_eval = w_ctr_alarm_en && w_div_rollover && w_count_en && !w_commit_active;
    assign w_alarm_hit  = (!w_ctr_sec_match_en  || (w_next_seconds == w_ctr_alarm_sec))  &&
                          (!w_ctr_min_match_en  || (w_next_minutes == w_ctr_alarm_min))  &&
                          (!w_ctr_hour_match_en || (w_next_hours   == w_ctr_alarm_hour));

    `ALWAYS_FF_RST(selected_clk, w_ctr_rst_n,
        if (`RST_ASSERTED(w_ctr_rst_n)) begin
            r_alarm_match <= 1'b0;
        end else if (w_alarm_eval) begin
            r_alarm_match <= w_alarm_hit;
        end else begin
            r_alarm_match <= 1'b0;
        end
    )

    //========================================================================
    // Crossing 3: Time Read (counter domain -> pclk)
    //========================================================================

    sync_pulse #(
        .SYNC_STAGES      (SYNC_STAGES)
    ) u_snap_pulse_sync (
        .i_src_clk        (selected_clk),
        .i_src_rst_n      (w_ctr_rst_n),
        .i_pulse          (w_snap_pulse),
        .i_dst_clk        (clk),
        // The destination side of this synchronizer is COMPLETION EVIDENCE
        // for the commit bookkeeping, so it takes the bookkeeping's reset
        // (cdc.md Rule 4, second half). A toggle synchronizer with one side
        // reset is parity: a bus reset covering the load either destroyed
        // the pulse - busy stuck, register file presenting reset defaults -
        // or fabricated one, publishing the pre-commit time as the commit's
        // answer. Both were measured, one per parity.
        .i_dst_rst_n      (w_commit_bk_rst_n),
        .o_pulse          (w_snap_valid_pclk)
    );

    // LOAD EVIDENCE. The snapshot pulse above fires for a TICK as well as a
    // commit load, so it cannot answer "did this commit land?" - a tick
    // between the accept and the load would answer it wrongly. This pulse
    // fires only on the commit load, and like the snapshot pulse its
    // destination side takes the bookkeeping's reset (cdc.md Rule 3/4).
    sync_pulse #(
        .SYNC_STAGES      (SYNC_STAGES)
    ) u_load_pulse_sync (
        .i_src_clk        (selected_clk),
        .i_src_rst_n      (w_ctr_rst_n),
        .i_pulse          (w_commit_load),
        .i_dst_clk        (clk),
        .i_dst_rst_n      (w_commit_bk_rst_n),
        .o_pulse          (w_commit_load_pclk)
    );

    assign w_read_bundle_ctr = {r_time_valid,
                                r_year, r_month, r_day, r_hours, r_minutes, r_seconds};

    glitch_free_n_dff_arn #(
        .FLOP_COUNT       (SYNC_STAGES),
        .WIDTH            (READ_WIDTH)
    ) u_read_sync (
        .clk              (clk),
        .rst_n            (rst_n),
        .d                (w_read_bundle_ctr),
        .q                (w_read_bundle_pclk)
    );

    // The synchronizer chain resets to zero and needs SYNC_STAGES cycles to
    // fill with real counter values. Zero is not a harmless intermediate
    // here - it is day 0 / month 0, a time that cannot exist - and two
    // consecutive zero samples would sail through the stability filter and be
    // published. So the filter is seeded with the reset-default encoding AND
    // held off until the chain has filled.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_read_bundle_d <= READ_RESET;
            r_read_fill     <= '0;
        end else begin
            r_read_bundle_d <= w_read_bundle_pclk;
            if (!w_read_filled) begin
                r_read_fill <= r_read_fill + FILL_CNT_W'(1);
            end
        end
    )

    assign w_read_filled = (r_read_fill == FILL_CNT_W'(SYNC_STAGES));
    assign w_read_stable = w_read_filled && (w_read_bundle_pclk == r_read_bundle_d);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_shd_seconds <= 8'h00;
            r_shd_minutes <= 8'h00;
            r_shd_hours   <= 8'h00;
            r_shd_day     <= 8'h01;
            r_shd_month   <= 8'h01;
            r_shd_year    <= 8'h00;
            r_shd_valid   <= 1'b0;
        end else if (w_snap_valid_pclk) begin
            // Fast path: the counter domain just changed and published a
            // snapshot that has been stable for SYNC_STAGES pclk cycles.
            r_shd_seconds <= r_snap_seconds;
            r_shd_minutes <= r_snap_minutes;
            r_shd_hours   <= r_snap_hours;
            r_shd_day     <= r_snap_day;
            r_shd_month   <= r_snap_month;
            r_shd_year    <= r_snap_year;
            r_shd_valid   <= r_snap_valid;
        end else if (w_read_stable) begin
            // Background path: synchronized counters, captured only when the
            // synchronized word has held still for two cycles.
            r_shd_seconds <= w_read_bundle_pclk[7:0];
            r_shd_minutes <= w_read_bundle_pclk[15:8];
            r_shd_hours   <= w_read_bundle_pclk[23:16];
            r_shd_day     <= w_read_bundle_pclk[31:24];
            r_shd_month   <= w_read_bundle_pclk[39:32];
            r_shd_year    <= w_read_bundle_pclk[47:40];
            r_shd_valid   <= w_read_bundle_pclk[48];
        end
    )

    //========================================================================
    // Commit Bookkeeping (pclk)
    //========================================================================
    // Four states, and the whole point of naming them is that "a transfer" is
    // a thing this wrapper can point at, so a watchdog event can be said to
    // belong to one:
    //
    //   r_commit_pend      software has committed and the handshake has not
    //                      taken it yet. Exactly one may be queued; a second
    //                      commit overwrites the queued data, it does not
    //                      make a second transfer.
    //   r_commit_data      the six bytes that commit will carry, captured at
    //                      the commit pulse rather than read live at
    //                      handover. That is what lets a queued commit
    //                      survive a bus reset that clears the register file
    //                      without delivering the file's reset values.
    //   r_commit_inflight  the handshake has taken it and has not returned to
    //                      idle. Set at handover, cleared at retire.
    //   r_commit_busy      the register block must keep showing the staged
    //                      values. Set at the commit pulse, cleared only when
    //                      nothing is queued or in flight AND the loaded time
    //                      is visible in the shadow - or by a watchdog event
    //                      for the transfer in flight with nothing queued
    //                      behind it.
    //
    // `w_commit_done` is deliberately a LEVEL, not a pulse on the retire
    // cycle: the shadow capture can arrive after the link goes idle, and a
    // pulse would have already passed by then, hanging busy forever.

    assign w_commit_accept   = r_commit_pend && w_commit_src_ready;
    // The link went idle without taking anything new, i.e. the transfer that
    // was in flight has completed.
    // The in-flight transfer has COMPLETED (the link went idle), whether or
    // not a queued commit is handed over in the same cycle...
    assign w_commit_complete = r_commit_inflight && w_commit_src_ready;
    // ...and RETIRED means completed with nothing new starting, which is what
    // clears the in-flight flag.
    assign w_commit_retire   = w_commit_complete && !w_commit_accept;
    assign w_commit_idle_now = !r_commit_inflight && !r_commit_pend;

    // Busy exists for exactly one reason: keep the staged values visible
    // until the readback would show the committed time. So the primary
    // release condition is that the shadow HAS the committed time - no
    // timing assumption, no dependence on which pulse arrived, and it
    // releases as soon as the answer is right rather than waiting for the
    // four-phase close-out three counter clocks later.
    //
    // The second term is the backstop for the case where the shadow can
    // never match (the counters were changed by something else after the
    // load): the transfer completed and a capture has happened since, so
    // holding the register file any longer serves nobody.
    assign w_commit_visible  = r_shd_valid &&
                               (r_shd_seconds == r_commit_data[7:0])   &&
                               (r_shd_minutes == r_commit_data[15:8])  &&
                               (r_shd_hours   == r_commit_data[23:16]) &&
                               (r_shd_day     == r_commit_data[31:24]) &&
                               (r_shd_month   == r_commit_data[39:32]) &&
                               (r_shd_year    == r_commit_data[47:40]);
    // Busy is released only on EVIDENCE THAT THIS COMMIT LANDED - a load
    // pulse observed since the handover - and only then does the data
    // comparison decide. Without the evidence term, re-committing the time
    // the shadow already shows released busy about three pclk after the
    // request was accepted, some forty before the load: the mirror resumed,
    // a tick advanced the readable time to T+1, and the stale-but-identical
    // commit then put it back to T. Busy said "done" through all of it.
    assign w_commit_done     = r_commit_busy && !r_commit_pend && r_commit_loaded &&
                               (w_commit_visible ||
                                (w_commit_idle_now &&
                                 (r_commit_snapped || w_snap_valid_pclk)));

    // A watchdog event belongs to the transfer IN FLIGHT, and a stall is
    // always reported - a retry queued behind it does not hide it, because
    // "your set-time is not getting through" is exactly what software needs
    // to know at that moment. The only qualification is that the transfer did
    // not just complete (`!w_commit_src_ready`): a timeout edge landing on
    // the retire cycle would otherwise report a stall for a transfer that
    // finished.
    //
    // What a QUEUED commit changes is not the report but the release: busy
    // stays set (see the clear term below) so the queued commit keeps its
    // staged values visible until it lands or overruns on its own account.
    assign w_commit_timeout_evt = w_commit_timeout && !r_commit_timeout_d &&
                                  r_commit_inflight && !w_commit_src_ready;

    // The report is about an OUTSTANDING stall, so it is retired when the
    // stalled transfer finally completes: commit_timeout means "not
    // acknowledged in time and still not through", and a clock that comes
    // back resolves it. Software that needs a latched record reads the bit
    // while the stall persists - busy is set for the same period. W1C works
    // at any time.
    // EVERY queued commit gets its own watchdog, counted from its own commit
    // pulse. Without it a queued commit can wait on a link that never moves:
    // src_ready stays low, so it is never accepted, so r_commit_pend never
    // clears, so neither branch of the busy release can fire - and the
    // in-flight watchdog is a LEVEL that never dropped, so its edge detector
    // can never fire again either. busy stayed high forever, the six
    // registers showed the staged bytes forever, time_valid stayed 0, and
    // only rtc_resetn recovered. Arming only when the link was ALREADY known
    // dead left the mirror image of that hang open: queue B inside A's own
    // window, let A time out, and B - unarmed - hangs busy just the same.
    //
    // So the rule has no exceptions: a queued commit has its own
    // COMMIT_TIMEOUT_CYCLES window counted from its commit pulse; if it is
    // not accepted within it, commit_timeout is reported again and busy is
    // released while the commit stays queued. A commit accepted within its
    // window has no window of its own to answer for and reports nothing -
    // which is every commit in normal operation, where the queue drains in
    // about ten counter clocks; if a report is already standing for the
    // slot it does inherit the duty to retire it (r_commit_timedout takes
    // r_pend_reported at accept).
    //
    // The queued slot carries TWO marks, and they are not the same thing:
    //   r_pend_expired  - "this occupant's window has run out". It gates the
    //                     counter and the event, and it is per-OCCUPANT: a
    //                     replacing commit pulse clears it, because the new
    //                     commit is entitled to a fresh window.
    //   r_pend_reported - "a report is standing for this SLOT". Set by the
    //                     expiry event, it SURVIVES a replacing commit pulse
    //                     and is cleared only at accept (where it transfers
    //                     into r_commit_timedout) or by the far reset. That
    //                     is what makes the report retire when whatever
    //                     finally lands from the slot completes, instead of
    //                     being orphaned by a third commit that replaced the
    //                     expired one.
    //
    // The event is qualified with !w_commit_accept, the mirror of the
    // in-flight path's !w_commit_src_ready above: a commit accepted on its
    // own expiry edge WAS accepted within its window, so it reports nothing,
    // keeps busy and takes no mark. Without that, the report was emitted, the
    // mark was then wiped by the accept in the same cycle, busy dropped with
    // the transfer in flight, and the flag could never retire.
    assign w_pend_timeout_evt = PEND_WDOG_EN && r_commit_pend && r_pend_wdog_arm &&
                                !r_pend_expired && !w_commit_accept &&
                                (r_pend_wdog == PEND_WDOG_W'(COMMIT_TIMEOUT_CYCLES));
    assign w_timeout_evt_any  = w_commit_timeout_evt || w_pend_timeout_evt;

    // A completion retires the flag only if it is the completion the flag is
    // waiting for. RULE: a completing transfer retires the report it carries
    // (r_commit_timedout) unless a report is standing for the QUEUED slot, in
    // which case the flag belongs to that later report and must survive until
    // the queued commit itself completes. Same-edge accept-and-complete is
    // consistent with this: r_commit_timedout read here is still the
    // COMPLETING transfer's mark (the queued slot's mark only takes its place
    // on this edge, for the next cycle), so the completing transfer resolves
    // against its own mark - and it is blocked precisely when the mark now
    // arriving says a second report is outstanding behind it.
    assign w_commit_timeout_resolved = w_commit_complete && r_commit_timedout &&
                                       !r_pend_reported;

    `ALWAYS_FF_RST(clk, w_commit_bk_rst_n,
        if (`RST_ASSERTED(w_commit_bk_rst_n)) begin
            r_commit_pend      <= 1'b0;
            r_commit_busy      <= 1'b0;
            r_commit_snapped   <= 1'b0;
            r_commit_inflight  <= 1'b0;
            r_commit_timedout  <= 1'b0;
            r_commit_loaded    <= 1'b0;
            r_pend_wdog        <= '0;
            r_pend_wdog_arm    <= 1'b0;
            r_pend_expired     <= 1'b0;
            r_pend_reported    <= 1'b0;
            r_commit_timeout_d <= 1'b0;
            r_commit_data      <= '0;
        end else begin
            r_commit_timeout_d <= w_commit_timeout;

            // Queue (set wins: a commit arriving in the cycle its predecessor
            // is handed over stays queued rather than being swallowed).
            if (time_set_commit) begin
                r_commit_pend   <= 1'b1;
                r_commit_busy   <= 1'b1;
                r_commit_data   <= w_commit_stage_data;
                // Arm unconditionally: this pulse leaves a commit pending, so
                // it owns a window starting here. A commit pulse while one is
                // already queued REPLACES its data and restarts both busy and
                // this watchdog; the queue is still one deep, so nothing is
                // delivered twice. r_pend_reported is deliberately NOT
                // cleared here - the report already made for this slot stands
                // until something from the slot lands.
                r_pend_wdog     <= '0;
                r_pend_expired  <= 1'b0;
                r_pend_wdog_arm <= 1'b1;
            end else if (w_commit_accept) begin
                r_commit_pend   <= 1'b0;
            end else if (r_commit_pend && r_pend_wdog_arm && !r_pend_expired &&
                         (r_pend_wdog != PEND_WDOG_W'(COMMIT_TIMEOUT_CYCLES))) begin
                // Saturating: holding at the target rather than wrapping means
                // an event suppressed for one cycle (by accept, or by a commit
                // pulse) is simply re-evaluated, never lost to a wrap.
                r_pend_wdog     <= r_pend_wdog + PEND_WDOG_W'(1);
            end

            // The window state is per-occupant and a commit pulse OWNS it: a
            // pulse landing on the expiry edge must leave the new commit with
            // a fresh window, so the expiry mark is qualified rather than
            // written after the pulse. Without the qualifier the pulse's
            // r_pend_expired <= 0 lost to this line, the count was dead
            // forever and busy stuck. The REPORT still stands (below and in
            // the sticky flag): the new commit gets its own window, and the
            // standing report retires when it lands.
            if (w_pend_timeout_evt && !time_set_commit) begin
                r_pend_expired  <= 1'b1;
            end
            if (w_pend_timeout_evt) begin
                r_pend_reported <= 1'b1;
            end

            // In-flight tracking, and whether THIS transfer overran its
            // window (which is what lets the report be retired when it
            // eventually completes).
            if (w_commit_load_pclk) begin
                r_commit_loaded <= 1'b1;
            end

            if (w_commit_accept) begin
                r_commit_inflight <= 1'b1;
                // The transfer leaving the queued slot carries the slot's
                // standing REPORT across the handover, so a report made for
                // that slot retires when whatever finally lands from it
                // completes - even if a third commit replaced the commit that
                // was expired when the report was made.
                r_commit_timedout <= r_pend_reported;
                r_pend_reported   <= 1'b0;
                r_pend_expired    <= 1'b0;
                // Accept and a fresh commit pulse can land on the same edge:
                // the old queued commit is handed over while a new one takes
                // its place. This block is written after the commit-pulse
                // block, so it owns the final value - it must not clear an
                // arm the pulse just set, or the newly queued commit would
                // never get the window it is entitled to.
                r_pend_wdog_arm   <= time_set_commit;
                r_commit_loaded   <= 1'b0;   // evidence is per-transfer
            end else if (w_commit_complete) begin
                r_commit_inflight <= !w_commit_retire;  // a queued commit takes over
                r_commit_timedout <= 1'b0;
            end else if (w_commit_timeout_evt) begin
                r_commit_timedout <= 1'b1;
            end

            // "The shadow has seen a capture since handover". The clear is
            // written last so a capture landing in the handover cycle - which
            // belongs to the PREVIOUS transfer - does not count for this one.
            if (w_snap_valid_pclk) begin
                r_commit_snapped <= 1'b1;
            end
            if (w_commit_accept) begin
                r_commit_snapped <= 1'b0;
            end

            // Busy is released by the done of the LAST accepted commit, or
            // by a watchdog event with nothing queued behind it. With a
            // commit queued, the stall is still reported but busy - and with
            // it the staged values the queued commit will carry - stays.
            if (!time_set_commit &&
                (w_commit_done ||
                 (r_commit_busy && w_commit_timeout_evt && !r_commit_pend) ||
                 (r_commit_busy && w_pend_timeout_evt))) begin
                r_commit_busy <= 1'b0;
            end
        end
    )

    assign time_commit_busy = r_commit_busy;

    //========================================================================
    // Crossing 4: Status Events and Sticky Flags (pclk)
    //========================================================================
    // The two sources are counter-domain LEVELS one counter clock wide. They
    // are synchronized and edge-detected HERE, so each becomes a single pclk
    // set event no matter how wide the source pulse is. Set beats a
    // simultaneous clear: a W1C that lands in the same cycle as a new tick
    // leaves the flag set, because dropping the event would lose an interrupt
    // and software will see the flag on the next read.

    // Same rule as the snapshot pulse: this synchronizer and the edge
    // detector after it are the EVIDENCE that a tick or a match happened, and
    // their sources are counter-domain levels that presetn does not touch.
    // Resetting the synchronized copy to 0 against a source still holding 1
    // makes release look like a fresh 0->1 - a flag manufactured by a reset,
    // with no tick behind it. The sticky flags themselves stay on presetn;
    // they are register-file-like, and clearing them on a bus reset is
    // correct. It is only their set EVIDENCE that must not be reset here.
    glitch_free_n_dff_arn #(
        .FLOP_COUNT       (SYNC_STAGES),
        .WIDTH            (2)
    ) u_event_sync (
        .clk              (clk),
        .rst_n            (w_commit_bk_rst_n),
        .d                ({r_alarm_match, r_second_tick}),
        .q                (w_evt_sync)
    );

    `ALWAYS_FF_RST(clk, w_commit_bk_rst_n,
        if (`RST_ASSERTED(w_commit_bk_rst_n)) begin
            r_evt_sync_d  <= 2'b00;
            r_evt_sync_d2 <= 2'b00;
        end else begin
            r_evt_sync_d  <= w_evt_sync;
            r_evt_sync_d2 <= r_evt_sync_d;
        end
    )

    // A rising edge that follows at least TWO idle cycles. The second idle
    // cycle is not decoration: both sources are low for a whole second
    // between events, so no real source can re-assert one cycle after
    // dropping - but a single-cycle dip in the synchronized level (a source
    // register being driven from two places, which is what a testbench force
    // looks like) would otherwise be counted as a second event and re-arm a
    // flag software had just cleared. Requiring the quiet window makes ONE
    // assertion of the source produce exactly ONE set event however long or
    // ragged the level is.
    assign w_tick_event  = w_evt_sync[0] && !r_evt_sync_d[0] && !r_evt_sync_d2[0];
    assign w_alarm_event = w_evt_sync[1] && !r_evt_sync_d[1] && !r_evt_sync_d2[1];

    // r_commit_timeout_flag is the one status flag that does NOT reset with
    // the register file. Its set evidence and its resolve evidence both live
    // under the commit bookkeeping's reset, and a flag on a different reset
    // from the thing it reports goes wrong in both directions: a presetn
    // pulse cleared it while the stall was still outstanding and no new edge
    // was ever coming, and an rtc_resetn - which drops the transfer - left it
    // set with nothing left to report. The W1C mask that clears it is still
    // decoded in the pclk register domain, which is correct: that is software
    // acknowledging, not a reset.
    `ALWAYS_FF_RST(clk, w_commit_bk_rst_n,
        if (`RST_ASSERTED(w_commit_bk_rst_n)) begin
            r_commit_timeout_flag <= 1'b0;
        end else begin
            if (w_timeout_evt_any) begin
                r_commit_timeout_flag <= 1'b1;
            end else if (clear_commit_timeout || w_commit_timeout_resolved) begin
                r_commit_timeout_flag <= 1'b0;
            end
        end
    )

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_alarm_flag          <= 1'b0;
            r_second_tick_flag    <= 1'b0;
        end else begin
            if (w_alarm_event) begin
                r_alarm_flag <= 1'b1;
            end else if (clear_alarm_flag) begin
                r_alarm_flag <= 1'b0;
            end

            if (w_tick_event) begin
                r_second_tick_flag <= 1'b1;
            end else if (clear_second_tick) begin
                r_second_tick_flag <= 1'b0;
            end

        end
    )

    //========================================================================
    // Output Assignments (all pclk domain)
    //========================================================================

    assign time_seconds_out    = r_shd_seconds;
    assign time_minutes_out    = r_shd_minutes;
    assign time_hours_out      = r_shd_hours;
    assign time_day_out        = r_shd_day;
    assign time_month_out      = r_shd_month;
    assign time_year_out       = r_shd_year;

    assign status_alarm_flag     = r_alarm_flag;
    assign status_second_tick    = r_second_tick_flag;
    assign status_commit_timeout = r_commit_timeout_flag;
    assign status_time_valid   = r_shd_valid;
    // Bit 7 of the hours byte is the PM flag in 12-hour mode, in BOTH binary
    // and BCD counting (H6: it used to be forced to 0 whenever !bcd_mode).
    assign status_pm_indicator = cfg_hour_mode_12 && r_shd_hours[7];

    assign rtc_alarm_irq       = r_alarm_flag && cfg_alarm_int_enable;
    assign rtc_second_irq      = r_second_tick_flag && cfg_second_int_enable;

endmodule
