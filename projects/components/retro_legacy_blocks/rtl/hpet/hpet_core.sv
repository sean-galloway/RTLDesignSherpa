// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hpet_core
// Purpose: Hpet Core module
//
// Documentation: projects/components/retro_legacy_blocks/rtl/hpet/README.md
// Subsystem: hpet
//
// Author: sean galloway
// Created: 2025-10-18
// Updated: 2026-09-09 - issue #46 review: periodic catch-up advance, re-arm
//                       restricted to comparator writes on a STOPPED timer
// Updated: 2026-09-09 - issue #46 review round_2: period-1 catch-up lattice,
//                       next-epoch hold bit, width-masked advance
// Updated: 2026-09-09 - issue #46 review round_3: epoch clear E2/E3 taken at
//                       the compare width

/**
 * ============================================================================
 * HPET Timer Core (High Speed Domain)
 * ============================================================================
 *
 * DESCRIPTION:
 *   Core HPET timer logic implementing main counter, timer comparators,
 *   and interrupt generation. Operates in high-speed clock domain for
 *   precise timing resolution.
 *
 * FEATURES:
 *   - 64-bit main counter, written as two INDEPENDENT 32-bit halves
 *   - Multiple independent timer comparators
 *   - One-shot and periodic timer modes
 *   - Individual timer interrupt generation
 *   - 32-bit and 64-bit comparison modes
 *
 * WRITE MODEL (issue #46 C3)
 *   Every software write into this core arrives as a one-cycle STROBE from
 *   hpet_config_regs with its data already settled, and each strobe names
 *   exactly one 32-bit half:
 *
 *     counter_write_lo    -> r_main_counter[31:0]  <= counter_wdata[31:0]
 *     counter_write_hi    -> r_main_counter[63:32] <= counter_wdata[63:32]
 *     timer_comp_write_lo -> r_timer_comparator[i][31:0]
 *     timer_comp_write_hi -> r_timer_comparator[i][63:32]
 *
 *   The halves are INDEPENDENT: a write to one half never disturbs the
 *   other. This matches the real HPET, whose 64-bit main counter is written
 *   as two 32-bit registers while the counter is halted; there is no
 *   64-bit-atomic write through a 32-bit register interface, and pretending
 *   otherwise is what made the previous "apply both halves on either strobe"
 *   scheme drop the second write.
 *
 * ----------------------------------------------------------------------------
 * THE RULE SET (issue #46 round_3 + review round_1 + review round_2)
 * ----------------------------------------------------------------------------
 *   COMPARE WIDTH. Everything below - the match, the advance, the carry that
 *   sets the epoch bit, the counter wrap that clears it - is evaluated at the
 *   COMPARE WIDTH selected by timer_size[i]: 32 bits when timer_size[i] = 0,
 *   64 bits when it is 1. A term evaluated at the wrong width is the class of
 *   defect this block keeps producing, so there is exactly one width mux
 *   (gen_timer_terms / gen_timer_advance) and every term goes through it.
 *
 *   MATCH
 *     w_timer_match_raw[i] = counter >= comparator      (at the compare width)
 *     w_timer_match[i]     = w_timer_match_raw[i] & ~r_comp_next_epoch[i]
 *     w_timer_fire[i]      = w_timer_match[i] & r_timer_armed[i]
 *                            & timer_enable[i] & hpet_enable
 *   The comparison is >= , never == : an equal-or-passed comparator is due,
 *   which is what makes a deficit (counter already past the target) fire
 *   rather than be missed. Every consumer below uses the EPOCH-GATED
 *   w_timer_match, so one bit suppresses the fire and the catch-up together.
 *
 *   ARMED LATCH  r_timer_armed[i] - "this timer still owes one interrupt for
 *   this comparator". Reset to 1. SET (which has priority over the clear)
 *   by any of:
 *     A1 NATURAL   !w_timer_match[i] - the counter is behind the comparator
 *                  again (an advance or a software write moved the target
 *                  forward, the counter was rewritten behind it, or the epoch
 *                  bit is holding the match at 0).
 *     A2 CATCH-UP  w_catchup_rearm[i] - a catch-up advance landed at or ahead
 *                  of the counter. This is the only re-arm path at period 1,
 *                  where the advance never pulls away from the counter and
 *                  the match therefore never falls on its own.
 *     A3 EXPLICIT  a comparator write strobe WHILE THE TIMER IS STOPPED
 *                  (timer_enable[i] = 0 or hpet_enable = 0).
 *   CLEARED by w_timer_fire[i] when no set condition holds.
 *
 *     CONTRACT (A3): a comparator write on a STOPPED timer ALWAYS re-arms,
 *     whatever value it writes. If the written value is at or below the
 *     counter the timer fires as soon as it is enabled - deliberately, and
 *     consistently with the >= match everywhere else. That is what lets
 *     software arm to an already-passed value: a zero comparator, or
 *     restarting a periodic phase after a counter reset. "Program it and it
 *     goes off immediately because it is already due" is the behaviour, not
 *     a defect; there is no wait-for-wrap.
 *
 *     A comparator write while the timer is RUNNING deliberately does NOT
 *     re-arm. The 64-bit comparator is written as two 32-bit halves, so
 *     between the two writes the register holds the torn value {old HI, new
 *     LO}; an unconditional re-arm on either half's strobe fires the timer on
 *     a value software never programmed. Loading the halves is always allowed
 *     - only the re-arm is withheld - so a running timer re-arms naturally,
 *     via A1, once the completed value is ahead of the counter.
 *
 *     CONTRACT (running reprogram): to reprogram a RUNNING timer's
 *     comparator, disable it first. Two consequences of NOT doing so are
 *     outside the contract and are not bugs: (1) a torn 64-bit value ABOVE
 *     the counter re-arms the timer through the natural path A1, and it then
 *     fires at the final value once that value is written - the tear is not
 *     what fires it, the completed value is; (2) a same-value rewrite on a
 *     running PERIODIC timer drags the comparator back from its
 *     auto-advanced position to the originally programmed value and can add
 *     one off-lattice fire.
 *
 *     The latch is what a plain rising-edge detect on the match cannot do. An
 *     edge detect that ignores the enables re-fires every expired one-shot
 *     the moment hpet_enable goes 0->1 (the original defect), while an edge
 *     detect on the raw match consumes the edge at the comparator WRITE,
 *     before the enables are on, and then never fires at all.
 *
 *   PERIODIC CATCH-UP
 *     w_timer_catchup[i] = timer_type[i] & ~r_timer_armed[i] & w_timer_match[i]
 *                          & ~w_timer_comp_write[i] & w_timer_period_nz[i]
 *                          & w_timer_running[i]
 *   A periodic timer that is RUNNING, has already fired on this match and is
 *   STILL at or behind the counter advances its comparator by one period per
 *   cycle WITHOUT firing, until the advance lands at or ahead of the counter.
 *   Missed periods are skipped, never burst: one interrupt per batch, and the
 *   next fire lands at the next boundary that is still in the future.
 *
 *   ADVANCE - one value, two callers (the fire advance of a periodic timer,
 *   and the catch-up advance), computed at the compare width:
 *
 *     period == 1 during CATCH-UP -> comparator <= counter + 1
 *     otherwise                   -> comparator <= comparator + period
 *
 *     WHY the period-1 case is different. At period 1 the comparator gains
 *     ZERO on the counter per cycle: both step by exactly 1, so the deficit
 *     between them is an INVARIANT and no compare operator can ever close it.
 *     Adding period forever is a non-terminating catch-up. But every integer
 *     is on the period-1 lattice, so counter+1 is a legal next boundary and
 *     landing there re-arms immediately. Cadence: period 1 delivers on every
 *     OTHER tick - the fastest the one-cycle fire/re-arm loop allows -
 *     regardless of how large the deficit is, and a live COUNTER write that
 *     opens a gap recovers on the next catch-up cycle.
 *
 *     TERMINATION is `advance >= counter`, not `>`. The advance is the value
 *     the comparator takes THIS cycle while the counter takes counter+1, so
 *     an advance that ties with the counter is one count behind it next
 *     cycle and is a legal, on-lattice boundary to fire at. `>` would skip it
 *     - and at period 1 (where the advance can only ever tie) `>` is exactly
 *     the bug that made a period-1 timer with a deficit go silent forever.
 *
 *     PERIOD 0 is treated as one-shot: a zero period can never get ahead, so
 *     the catch-up is suppressed (w_timer_period_nz) rather than rewriting
 *     the comparator with its own value forever. One fire, then quiescent.
 *
 *     WIDTH. In 32-bit mode the advance is masked to the compare width:
 *     comparator[63:32] is untouched, so carry out of bit 31 cannot corrupt
 *     a field the 32-bit comparison never reads.
 *
 *   EPOCH BIT  r_comp_next_epoch[i] - "the comparator has wrapped past the
 *   top of the compare width; it belongs to the counter's NEXT epoch". Reset
 *   0. CLEAR HAS PRIORITY OVER SET.
 *     SET   when an advance actually happens (fire or catch-up) and its sum
 *           CARRIES OUT of the compare width (bit 32 when timer_size = 0,
 *           bit 64 when it is 1 - {carry, sum} is computed at that width).
 *           The comparator keeps the wrapped low bits, the carry becomes this
 *           bit. While the bit is set the raw match is forced to 0, so there
 *           is no fire and no catch-up, and the armed latch simply re-sets
 *           through A1 (!match) and sits there - no churn, no rewrite loop.
 *     CLEAR on any of:
 *           E1 the COUNTER WRAPS at the compare width - its increment carries
 *              out (all-ones -> 0). The counter has now joined the epoch the
 *              comparator was waiting in, so the comparison is meaningful
 *              again. A software counter write is NOT a wrap.
 *           E2 software writes a COMPARATOR half THAT THE COMPARE WIDTH
 *              READS - a new target replaces the one that wrapped. In 64-bit
 *              mode either half; in 32-bit mode the LO half only.
 *           E3 software writes a COUNTER half THAT THE COMPARE WIDTH READS -
 *              a counter write RE-BASES the epoch. After it the ordinary
 *              counter >= comparator rule applies immediately, so a
 *              comparator that is now behind the counter fires promptly and
 *              catch-up follows from there. Again 64-bit mode: either half;
 *              32-bit mode: the LO half only.
 *
 *              E2 and E3 ARE EVALUATED AT THE COMPARE WIDTH because a write
 *              to a half the comparison never reads has not moved the
 *              comparison. In 32-bit mode a HI-half write changes no bit of
 *              counter[31:0] or comparator[31:0], so clearing the hold on it
 *              would restart a comparison whose operands are exactly what
 *              they were when the carry set the bit - the timer would fire a
 *              whole epoch early, for a write that did nothing. The 32-bit
 *              HI halves are storage the comparison does not consult.
 *
 *              Note the separation from the comparator-write suppression of
 *              the advance (w_comp_advance_en): that one is deliberately NOT
 *              width-taken. Software owns the register in a write cycle, so
 *              ANY half write beats the advance - the epoch question is
 *              "did the comparison move", the advance question is "who owns
 *              the register this cycle", and they have different answers.
 *           E4 timer_size[i] changes - the compare width itself moved, so the
 *              carry that set the bit was taken at a width that no longer
 *              applies. This is a cheap change-detect on the timer_size input
 *              (r_timer_size_d); hpet_config_regs exports no TIMER_CONFIG
 *              write strobe, and holding a stale epoch bit across a width
 *              change would silence the timer until a wrap at the new width.
 *     Clear beats set because they coincide exactly at the counter's own
 *     wrap: an advance to all-ones+1 carries in the same cycle the counter
 *     wraps, and taking the set there would hold the comparator for a WHOLE
 *     extra epoch instead of firing at the boundary that is now current.
 *
 *     CONTRACT (64-bit overflow hold): once a 64-bit-mode advance carries out
 *     of bit 63 the hold is cleared only by the counter wrapping at 64 bits
 *     (E1) or by software (E2/E3/E4). A 64-bit wrap is up to 2^64 = 1.8e19
 *     counts away - about 5800 years at 100 MHz, and even a quarter of an
 *     epoch is ~1460 years - so in practice such a timer fires once and never
 *     again until software reprograms it. That is register arithmetic doing
 *     what register arithmetic does at 64 bits, not a defect, and it is the
 *     reason the hold bit exists: without it the wrapped comparator would sit
 *     BELOW the counter and re-fire every cycle.
 *
 *   CONTRACT (catch-up latency): the catch-up is bounded but NOT constant. It
 *   performs at most one advance per cycle, and each advance closes
 *   (period - 1) counts of deficit - the comparator gains `period` while the
 *   counter gains 1 - so a deficit D takes about ceil(D / (period - 1))
 *   cycles at period >= 2, and exactly one cycle at period 1 (the lattice
 *   jump straight to counter+1). No interrupt is emitted for any of those
 *   cycles; one lands at the end.
 *
 *     The consequence at small periods is large. A counter HI write on a
 *     RUNNING period-2 timer can open a deficit of 2^52 counts, which closes
 *     at 1 count per cycle: ~4.5e15 cycles, about 520 days at 100 MHz, silent
 *     throughout. The timer is not hung and nothing is lost - it is doing
 *     exactly the arithmetic it was asked for - but this is precisely why the
 *     HPET specification requires the main counter to be HALTED before it is
 *     written. Halt, write both halves, reprogram the comparators, re-enable.
 *
 *   CONTRACT (timer_size): change timer_size[i] only while timer i is STOPPED,
 *   and REWRITE THE COMPARATOR (and hence the period) afterwards. E4 clears a
 *   stale epoch hold on the change, but that is all it can do: the old width's
 *   lattice is not the new width's. Switching 0 -> 1 live exposes
 *   comparator[63:32] and period[63:32] - bits the 32-bit comparison never
 *   read and never maintained - to a comparison that now does read them, so
 *   the comparator can land up to 2^32 counts behind the counter and catch up
 *   for ~2^32 cycles (~43 s at 100 MHz) before it fires again. Switching
 *   1 -> 0 live truncates the target to its low half, which usually makes an
 *   already-due comparator out of a future one.
 * ============================================================================
 */

`timescale 1ns / 1ps

`include "reset_defs.svh"

module hpet_core #(
    parameter int NUM_TIMERS = 3
)(
    // ========================================================================
    // Clock and Reset
    // ========================================================================
    input  logic                    clk,
    input  logic                    rst_n,

    // ========================================================================
    // Configuration Interface
    // ========================================================================
    input  logic                    hpet_enable,

    // Main Counter Interface (64-bit, written as two independent halves)
    input  logic                    counter_write_lo,
    input  logic                    counter_write_hi,
    input  logic [63:0]             counter_wdata,
    output logic [63:0]             counter_rdata,

    // Timer Configuration
    input  logic [NUM_TIMERS-1:0]   timer_enable,
    input  logic [NUM_TIMERS-1:0]   timer_int_enable,
    input  logic [NUM_TIMERS-1:0]   timer_type,
    input  logic [NUM_TIMERS-1:0]   timer_size,

    // Timer Comparators (64-bit, written as two independent halves)
    input  logic [NUM_TIMERS-1:0]   timer_comp_write_lo,
    input  logic [NUM_TIMERS-1:0]   timer_comp_write_hi,
    input  logic [63:0]             timer_comp_wdata [NUM_TIMERS],

    // Interrupt Interface
    output logic [NUM_TIMERS-1:0]   timer_int_status,
    input  logic [NUM_TIMERS-1:0]   timer_int_clear,
    output logic [NUM_TIMERS-1:0]   timer_irq
);

    // ========================================================================
    // Signal Declarations
    // ========================================================================
    logic [63:0]           r_main_counter;

    // FPGA Synthesis Attributes: Use distributed RAM for low latency
    // (typically 2-8 timers, small array)
`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif INTEL
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [63:0]           r_timer_comparator [NUM_TIMERS];

`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif INTEL
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [63:0]           r_timer_period [NUM_TIMERS];  // Period for periodic mode

    // Software write strobes and run state
    logic                  w_counter_sw_write;  // either counter half written
    logic                  w_counter_incr;      // the counter counts this cycle
    logic [NUM_TIMERS-1:0] w_counter_wrap;      // counter wraps at compare width
    logic [NUM_TIMERS-1:0] w_timer_comp_write;  // either half of timer i written
    logic [NUM_TIMERS-1:0] w_timer_running;     // timer_enable[i] & hpet_enable
    logic [NUM_TIMERS-1:0] w_comp_write_rearm;  // comp write on a STOPPED timer
    logic [NUM_TIMERS-1:0] w_timer_size_chg;    // compare width just moved

    // Compare-width terms
    logic [NUM_TIMERS-1:0] w_timer_match_raw;   // counter >= comparator
    logic [NUM_TIMERS-1:0] w_timer_match;       // raw match, held off by epoch
    logic [NUM_TIMERS-1:0] w_timer_period_nz;   // period can move the compare
    logic [NUM_TIMERS-1:0] w_timer_period_one;  // period == 1: unit lattice
    logic [NUM_TIMERS-1:0] w_epoch_clr_comp;    // comp write the compare reads
    logic [NUM_TIMERS-1:0] w_epoch_clr_ctr;     // ctr write the compare reads

    // Comparator advance (one value, two callers: fire and catch-up)
    logic [63:0]           w_adv_base [NUM_TIMERS];    // comparator, or counter
    logic [63:0]           w_adv_addend [NUM_TIMERS];  // period, or 1
    logic [64:0]           w_adv_sum_64 [NUM_TIMERS];  // {carry, sum} at 64 bits
    logic [32:0]           w_adv_sum_32 [NUM_TIMERS];  // {carry, sum} at 32 bits
    logic [63:0]           w_comp_advance [NUM_TIMERS];  // value written back
    logic [NUM_TIMERS-1:0] w_comp_adv_carry;    // advance left the compare width
    logic [NUM_TIMERS-1:0] w_comp_adv_ahead;    // advance >= counter (or carried)
    logic [NUM_TIMERS-1:0] w_comp_advance_en;   // an advance happens this cycle

    // Catch-up, epoch and fire
    logic [NUM_TIMERS-1:0] w_timer_catchup;     // advance a period, do NOT fire
    logic [NUM_TIMERS-1:0] w_catchup_rearm;     // catch-up finished this cycle
    logic [NUM_TIMERS-1:0] w_epoch_set;         // advance carried out
    logic [NUM_TIMERS-1:0] w_epoch_clr;         // wrap / writes / size change
    logic [NUM_TIMERS-1:0] w_timer_fire;        // one-cycle fire pulse

    logic [NUM_TIMERS-1:0] r_timer_armed;       // may this match still fire?
    logic [NUM_TIMERS-1:0] r_comp_next_epoch;   // comparator is an epoch ahead
    logic [NUM_TIMERS-1:0] r_timer_size_d;      // compare width, one cycle back
    logic [NUM_TIMERS-1:0] r_interrupt_status;
    logic [NUM_TIMERS-1:0] r_interrupt_output;

    genvar i;

    // ========================================================================
    // Main Counter (64-bit, two independently written halves)
    // ========================================================================
    // A write cycle does not increment: the half that software did not write
    // holds, so "write LO" cannot perturb HI by a count.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_main_counter <= '0;
        end else if (counter_write_lo || counter_write_hi) begin
            if (counter_write_lo) begin
                r_main_counter[31:0]  <= counter_wdata[31:0];
            end
            if (counter_write_hi) begin
                r_main_counter[63:32] <= counter_wdata[63:32];
            end
        end else if (hpet_enable) begin
            r_main_counter <= r_main_counter + 64'd1;
        end
    )

    assign counter_rdata = r_main_counter;

    // ========================================================================
    // Software Write Strobes, Run State and Counter Wrap
    // ========================================================================
    assign w_counter_sw_write = counter_write_lo | counter_write_hi;
    assign w_timer_comp_write = timer_comp_write_lo | timer_comp_write_hi;
    assign w_timer_running    = timer_enable & {NUM_TIMERS{hpet_enable}};
    assign w_comp_write_rearm = w_timer_comp_write & ~w_timer_running;

    // The counter counts exactly when it is enabled and software is not
    // loading it - the same condition the counter register above uses.
    assign w_counter_incr = hpet_enable & ~w_counter_sw_write;

    // Compare width, one cycle back: hpet_config_regs exports no TIMER_CONFIG
    // write strobe, so a change of timer_size is detected here (epoch clear
    // E4). r_timer_size_d resets to 0 with the epoch bits already clear, so
    // the reset-edge "change" is a no-op.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_timer_size_d <= '0;
        end else begin
            r_timer_size_d <= timer_size;
        end
    )

    assign w_timer_size_chg = timer_size ^ r_timer_size_d;

    // ========================================================================
    // Compare-Width Terms (match, period)
    // ========================================================================
    // Every term is evaluated at the SAME width as the match, because a
    // 32-bit-mode timer whose period is 0 in its low half cannot move its own
    // comparison no matter what the high half holds, and a counter that has
    // wrapped bit 31 is not "past" a comparator that has not.
    generate
        for (i = 0; i < NUM_TIMERS; i++) begin : gen_timer_terms
            always_comb begin
                if (timer_size[i]) begin
                    // 64-bit comparison mode
                    w_timer_match_raw[i]  = (r_main_counter >= r_timer_comparator[i]);
                    w_timer_period_nz[i]  = (r_timer_period[i] != 64'd0);
                    w_timer_period_one[i] = (r_timer_period[i] == 64'd1);
                    w_counter_wrap[i]     = w_counter_incr & (&r_main_counter);
                    // Both halves are inside a 64-bit compare, so either
                    // write moves a bit this comparison reads.
                    w_epoch_clr_comp[i]   = timer_comp_write_lo[i] | timer_comp_write_hi[i];
                    w_epoch_clr_ctr[i]    = counter_write_lo | counter_write_hi;
                end else begin
                    // 32-bit comparison mode
                    w_timer_match_raw[i]  = (r_main_counter[31:0] >= r_timer_comparator[i][31:0]);
                    w_timer_period_nz[i]  = (r_timer_period[i][31:0] != 32'd0);
                    w_timer_period_one[i] = (r_timer_period[i][31:0] == 32'd1);
                    w_counter_wrap[i]     = w_counter_incr & (&r_main_counter[31:0]);
                    // A HI-half write does NOT move any bit a 32-bit
                    // comparison reads, so it cannot re-base the epoch.
                    w_epoch_clr_comp[i]   = timer_comp_write_lo[i];
                    w_epoch_clr_ctr[i]    = counter_write_lo;
                end
            end
        end
    endgenerate

    // The epoch bit holds the match at 0 for as long as the comparator lives
    // in the counter's next epoch. Every consumer - fire, catch-up and the
    // natural re-arm - reads this gated match, so one bit stops the fire and
    // the advance together and re-arms the latch instead of churning.
    assign w_timer_match = w_timer_match_raw & ~r_comp_next_epoch;

    // ========================================================================
    // Periodic Catch-Up
    // ========================================================================
    // A periodic timer that is RUNNING, is NOT armed (it already fired on this
    // match) and whose comparator is STILL at or behind the counter steps its
    // comparator forward one boundary per cycle and does NOT fire, until the
    // advance lands at or ahead of the counter.
    //
    //   ~w_timer_comp_write : a software write owns the comparator this cycle
    //                         (see gen_timer_comparators), so no advance
    //                         happens and none may be claimed as finished.
    //   w_timer_period_nz   : period 0 can never get ahead - treat it as
    //                         one-shot rather than rewrite the same value
    //                         forever.
    //   w_timer_running     : state only changes while the timer is actually
    //                         counting, the same gate the fire uses.
    assign w_timer_catchup = timer_type & ~r_timer_armed & w_timer_match &
                             ~w_timer_comp_write & w_timer_period_nz &
                             w_timer_running;

    // ========================================================================
    // Comparator Advance
    // ========================================================================
    // ONE advanced value serves both callers - the fire advance of a periodic
    // timer and the catch-up advance - and the ahead-of-counter test reads the
    // same adder, so the value that gets written and the value that is tested
    // can never disagree.
    //
    // The base/addend pair is the whole period-1 story: at period 1 the
    // comparator gains 0 per cycle on the counter, so comparator+period can
    // never close a deficit. Every integer is on the period-1 lattice, so the
    // catch-up jumps straight to counter+1 - a legal boundary that is ahead by
    // construction, which terminates the catch-up in one cycle at any deficit.
    generate
        for (i = 0; i < NUM_TIMERS; i++) begin : gen_timer_advance
            assign w_adv_base[i]   = (w_timer_catchup[i] && w_timer_period_one[i]) ?
                                     r_main_counter : r_timer_comparator[i];
            assign w_adv_addend[i] = (w_timer_catchup[i] && w_timer_period_one[i]) ?
                                     64'd1 : r_timer_period[i];

            // {carry, sum} at each compare width. The carry is what the epoch
            // bit records; the sum is what the comparator takes.
            assign w_adv_sum_64[i] = {1'b0, w_adv_base[i]} + {1'b0, w_adv_addend[i]};
            assign w_adv_sum_32[i] = {1'b0, w_adv_base[i][31:0]} +
                                     {1'b0, w_adv_addend[i][31:0]};

            always_comb begin
                if (timer_size[i]) begin
                    w_comp_advance[i]   = w_adv_sum_64[i][63:0];
                    w_comp_adv_carry[i] = w_adv_sum_64[i][64];
                    w_comp_adv_ahead[i] = w_adv_sum_64[i][64] ||
                                          (w_adv_sum_64[i][63:0] >= r_main_counter);
                end else begin
                    // 32-bit mode: the advance NEVER disturbs bits [63:32] -
                    // a field this comparison does not read must not collect
                    // carry out of bit 31.
                    w_comp_advance[i]   = {r_timer_comparator[i][63:32],
                                           w_adv_sum_32[i][31:0]};
                    w_comp_adv_carry[i] = w_adv_sum_32[i][32];
                    w_comp_adv_ahead[i] = w_adv_sum_32[i][32] ||
                                          (w_adv_sum_32[i][31:0] >= r_main_counter[31:0]);
                end
            end
        end
    endgenerate

    // An advance happens on a periodic fire or on a catch-up step, and never
    // in a cycle software is writing the comparator (software wins - see
    // gen_timer_comparators). This is the single definition used by the
    // comparator register and by the epoch set term, so they cannot drift.
    assign w_comp_advance_en = ~w_timer_comp_write &
                               ((w_timer_fire & timer_type) | w_timer_catchup);

    // The catch-up is finished the cycle its advance lands AT OR AHEAD of the
    // counter (>=, not >: the comparator takes this value while the counter
    // takes counter+1, so a tie is a boundary one count ahead next cycle).
    // Re-arming HERE rather than waiting for the match to fall is what keeps
    // period 1 alive, where the advance can only ever tie.
    assign w_catchup_rearm = w_timer_catchup & w_comp_adv_ahead;

    // ========================================================================
    // Timer Comparators (64-bit, two independently written halves)
    // ========================================================================
    // r_timer_period mirrors whatever software last wrote, so periodic mode
    // advances by the programmed interval while r_timer_comparator walks
    // ahead of it. (The register block keeps showing the written value, not
    // the advanced one - that is the documented HPET behaviour.)
    generate
        for (i = 0; i < NUM_TIMERS; i++) begin : gen_timer_comparators
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_timer_comparator[i] <= '0;
                    r_timer_period[i]     <= '0;
                end else if (w_timer_comp_write[i]) begin
                    // SOFTWARE WINS. This branch has priority over the advance
                    // below, so a comparator write landing in the same cycle
                    // as a fire (or as a catch-up step) loads the software
                    // value and the advance is SKIPPED that cycle - the target
                    // software just programmed is never silently stepped past
                    // by hardware. The fire itself still happens (w_timer_fire
                    // is unaffected) and there is exactly one of it, because a
                    // write on a RUNNING timer does not re-arm.
                    if (timer_comp_write_lo[i]) begin
                        r_timer_comparator[i][31:0] <= timer_comp_wdata[i][31:0];
                        r_timer_period[i][31:0]     <= timer_comp_wdata[i][31:0];
                    end
                    if (timer_comp_write_hi[i]) begin
                        r_timer_comparator[i][63:32] <= timer_comp_wdata[i][63:32];
                        r_timer_period[i][63:32]     <= timer_comp_wdata[i][63:32];
                    end
                end else if (w_comp_advance_en[i]) begin
                    // Periodic mode: one period per interrupt on a fire, and
                    // one boundary per CYCLE while catching up - which skips
                    // whole missed periods without emitting an interrupt for
                    // any of them. The value is width-masked (32-bit mode
                    // keeps bits [63:32]) and its carry is taken by the epoch
                    // bit below.
                    r_timer_comparator[i] <= w_comp_advance[i];
                end
            )
        end
    endgenerate

    // ========================================================================
    // Next-Epoch Hold Bit
    // ========================================================================
    // Set when an advance carries out of the compare width: the comparator has
    // wrapped and now belongs to the counter's NEXT epoch, so the raw match is
    // meaningless until the counter joins it. Cleared by the counter's own
    // wrap (E1), by a software comparator write (E2), by a software counter
    // write (E3, which re-bases the epoch) or by a change of compare width
    // (E4).
    //
    // E2 and E3 are taken AT THE COMPARE WIDTH, like every other term in this
    // file. In 32-bit mode the comparison reads only bits [31:0], so only a
    // LO-half write can have moved anything it looks at; clearing the hold on
    // a HI-half write would resume a comparison against a target that did not
    // move, and the timer would fire an epoch early. In 64-bit mode either
    // half moves the compare, so either half clears.
    //
    // CLEAR BEATS SET. The two coincide exactly at the counter's own wrap - an
    // advance to all-ones+1 carries in the same cycle the counter wraps - and
    // taking the set there would hold the comparator for a whole extra epoch
    // instead of firing at the boundary that has just become current.
    assign w_epoch_set = w_comp_advance_en & w_comp_adv_carry;
    assign w_epoch_clr = w_counter_wrap | w_epoch_clr_comp | w_epoch_clr_ctr |
                         w_timer_size_chg;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_comp_next_epoch <= '0;
        end else begin
            for (int t = 0; t < NUM_TIMERS; t++) begin
                if (w_epoch_clr[t]) begin
                    r_comp_next_epoch[t] <= 1'b0;
                end else if (w_epoch_set[t]) begin
                    r_comp_next_epoch[t] <= 1'b1;
                end
            end
        end
    )

    // ========================================================================
    // Armed Latch and Fire Pulse
    // ========================================================================
    // Reset ARMED: out of reset counter == comparator == 0, so the raw match
    // is already 1; a timer enabled before anything is programmed is meant to
    // fire, and the enables gate it until then.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_timer_armed <= {NUM_TIMERS{1'b1}};
        end else begin
            for (int t = 0; t < NUM_TIMERS; t++) begin
                if (w_comp_write_rearm[t] || !w_timer_match[t] ||
                    w_catchup_rearm[t]) begin
                    // A3 explicit re-arm (software wrote the comparator while
                    // the timer was STOPPED - a write to a running timer loads
                    // the halves but must not re-arm, or a half-written 64-bit
                    // comparator fires on the torn {old HI, new LO} value),
                    // A1 natural re-arm (the counter is behind the comparator
                    // again, or the epoch bit is holding the match at 0), or
                    // A2 catch-up re-arm (the advance just landed at or ahead
                    // of the counter).
                    r_timer_armed[t] <= 1'b1;
                end else if (w_timer_fire[t]) begin
                    r_timer_armed[t] <= 1'b0;
                end
            end
        end
    )

    assign w_timer_fire = w_timer_match & r_timer_armed & timer_enable &
                          {NUM_TIMERS{hpet_enable}};

    // ========================================================================
    // Interrupt Status and Generation
    // ========================================================================
    // SAME-BIT RACE POLICY (issue #46 round_2): a fire and a software clear
    // landing on the same bit in the same cycle resolve with the FIRE
    // winning. A clear re-runs harmlessly (software can write the bit again)
    // but a lost fire is gone forever, so the new event takes priority.
    // hpet_config_regs narrows the multi-cycle register request to a
    // one-cycle clear pulse, so there is no trailing cycle that could undo a
    // fire this one just accepted.
    generate
        for (i = 0; i < NUM_TIMERS; i++) begin : gen_interrupt_logic
            // Interrupt status register (sticky, owned here)
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_interrupt_status[i] <= 1'b0;
                end else if (w_timer_fire[i]) begin
                    r_interrupt_status[i] <= 1'b1;
                end else if (timer_int_clear[i]) begin
                    r_interrupt_status[i] <= 1'b0;
                end
            )

            // Interrupt output generation
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_interrupt_output[i] <= 1'b0;
                end else if (w_timer_fire[i] && timer_int_enable[i]) begin
                    r_interrupt_output[i] <= 1'b1;
                end else if (timer_int_clear[i]) begin
                    r_interrupt_output[i] <= 1'b0;
                end else if (!r_interrupt_status[i]) begin
                    // Auto-clear when the status bit is not set
                    r_interrupt_output[i] <= 1'b0;
                end
            )
        end
    endgenerate

    // ========================================================================
    // Output Assignments
    // ========================================================================
    assign timer_int_status = r_interrupt_status;
    assign timer_irq        = r_interrupt_output;

    // ========================================================================
    // Simulation-time parameter validation
    // ========================================================================
`ifndef SYNTHESIS
    initial begin : param_check
        if (NUM_TIMERS < 1 || NUM_TIMERS > 8) begin
            $error("hpet_core: NUM_TIMERS=%0d out of range [1,8]", NUM_TIMERS);
        end
    end
`endif

endmodule : hpet_core
