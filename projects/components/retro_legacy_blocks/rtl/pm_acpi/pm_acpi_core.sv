// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pm_acpi_core
// Purpose: Core PM/ACPI power management logic
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pm_acpi/README.md
// Subsystem: pm_acpi
//
// Author: sean galloway
// Created: 2025-11-16
// Updated: 2026-09-09 - GitHub #54: sticky status ownership, GPE clear path,
//          PM1 per-source enables, level interrupt, latched wake, input
//          synchronizers, soft reset
// Updated: 2026-09-09 - GitHub #54 review follow-up: level pins edge-latched,
//          one-pulse request bits, unconditional event log, SCI_EN pin gate

/**
 * ============================================================================
 * PM_ACPI Core Logic
 * ============================================================================
 *
 * DESCRIPTION:
 *   Core power management logic implementing ACPI-compatible functionality:
 *   - 32-bit PM Timer with configurable divider
 *   - Power state FSM (S0/S1/S3)
 *   - General Purpose Event (GPE) handling
 *   - Clock gating control
 *   - Power domain sequencing
 *   - Wake event logic
 *   - Interrupt aggregation
 *
 * THIS BLOCK OWNS THE STICKY STATUS (issue #54 C2 / round_2 items 1-2)
 *   Every software-visible W1C status bit lives HERE, not in the generated
 *   register block. Each bit is
 *
 *       r_status <= (r_status & ~sw_clr) | w_set;
 *
 *   so a hardware event SETS, a software write-1-to-clear at the matching bit
 *   position CLEARS, a write of 0 does nothing, and a set that lands in the
 *   same cycle as a clear WINS (the event would otherwise be lost, and an
 *   event that is not recorded is an interrupt nobody can service).
 *   pm_acpi_config_regs decodes the per-bit clear mask from the write data and
 *   byte enables at the register's own address and presents it here for
 *   exactly one cycle per transaction; the register-block fields are live
 *   MIRRORS of these registers.
 *
 *   Before this change the register block held the state with `hwset` and an
 *   undriven `next`, which reloaded the field every cycle there was no write
 *   and no set: single-bit status could not hold at all, and a multi-bit
 *   hwset on GPE0_STATUS set all sixteen bits at once.
 *
 * EVERY STATUS BIT IS EDGE-SET (issue #54 follow-up F1)
 *   GPE, the two buttons, rtc_alarm and ext_wake_n all set their status bit on
 *   an ASSERTION EDGE, never on the level. Setting from a level re-armed the
 *   bit every cycle, so a W1C could not take effect while the pin was still
 *   asserted - software could see the event but never dismiss it, and with
 *   pm1_int behind it the interrupt could not be dropped either. The pin must
 *   deassert and reassert to record a second event.
 *
 *   The wake terms follow the same rule, so none of them is a raw pin level:
 *   see the wake-event section. The consequence is stated there rather than
 *   hidden - a source already asserted before the sleep request neither blocks
 *   sleep nor wakes the machine.
 *
 * INTERRUPT IS A LEVEL (round_3 item 3)
 *   pm_interrupt is the OR of ENABLED STICKY status bits, so it stays asserted
 *   until software clears every enabled source. It is never driven from a raw
 *   one-cycle hardware event. ACPI_INT_STATUS deliberately does NOT feed
 *   pm_interrupt: it is an unconditional per-source EVENT LOG of the same
 *   events - every bit sets whether its interrupt is enabled or not, and each
 *   is W1C independently - and feeding it back would mean software had to
 *   clear two registers to drop one interrupt.
 *
 * cfg_acpi_enable IS THE SCI_EN GATE (issue #54 follow-up F10)
 *   ACPI_CONTROL.acpi_enable gates GPE event CAPTURE and the pm_interrupt PIN.
 *   It does NOT gate PM1 or WAKE status recording: with ACPI disabled the
 *   block still keeps a history of what happened, it just does not interrupt
 *   anyone about it. That is the SCI_EN split - enabling ACPI later shows
 *   software what it missed rather than a blank slate.
 *
 * SELF-CLEARING REQUEST BITS ARE EDGE DETECTED (issue #54 follow-up F2)
 *   cfg_sleep_enable, cfg_soft_reset, cfg_sys_reset and cfg_periph_reset are
 *   `singlepulse` fields, but peakrdl_to_cmdrsp holds its request for the
 *   accept cycle plus CMD_WAIT_ACK, so each arrives here as a TWO-cycle level.
 *   All four are rising-edge detected, so one software write is exactly one
 *   core-clock pulse - including on sys_reset_req / periph_reset_req, which
 *   are a one-cycle contract at the pin.
 *
 *   The enable terms are:
 *     ACPI_STATUS bit N   gated by ACPI_INT_ENABLE bit N
 *     PM1_STATUS  bit N   gated by PM1_ENABLE bit N, then by ACPI_INT_ENABLE
 *                         .pm1_enable. PM1_STATUS.wak_sts has NO enable bit
 *                         (the RDL defines none, matching ACPI: a wake is
 *                         reported but is not an interrupt source), so it is
 *                         masked out of the PM1 term.
 *     GPE status  bit N   gated by GPE0_ENABLE bit N, then by ACPI_INT_ENABLE
 *                         .gpe_int_enable.
 *
 * WAKE IS LATCHED (issue #54 H5)
 *   power_button_press is one cycle wide. The old FSM left PWR_TRANSITION by
 *   re-reading cfg_sleep_type, which software has no reason to have rewritten,
 *   so a pulsed wake reached S0 for one cycle and fell straight back to sleep.
 *   r_wake_pending latches any enabled wake event while the machine is out of
 *   S0 and outranks sleep_type in PWR_TRANSITION. It is dropped on reaching S0
 *   and on a new sleep request. cfg_sleep_enable is a self-clearing one-shot
 *   in the register block and is rising-edge detected here, so returning to S0
 *   does not re-arm sleep and software need not unprogram sleep_type.
 *
 *   ONE-CYCLE CORNER, stated (issue #54 follow-up F8): a wake event landing in
 *   the EXACT cycle of the sleep request is not latched - w_sleep_req clears
 *   r_wake_pending in that cycle, and the machine is still in S0, where the
 *   latch is held clear anyway. The event is not lost: it is recorded in
 *   ACPI_STATUS.wake_status, PM1_STATUS.wak_sts and its WAKE_STATUS bit, and
 *   raises pm_interrupt if enabled. The machine sleeps and the NEXT wake
 *   returns it to S0. Widening the latch to cover that cycle would mean a wake
 *   arriving before software asked to sleep could block sleep entry, which is
 *   the failure the S0 clear exists to prevent.
 *
 * ASYNCHRONOUS INPUTS (round_2 item 6 / round_3 item 2)
 *   rtc_alarm, ext_wake_n and gpe_events_in are device pins and are
 *   asynchronous to this clock in both CDC_ENABLE settings, so each passes a
 *   SYNC_STAGES-deep synchronizer UNCONDITIONALLY. Gating the synchronizer on
 *   CDC_ENABLE would be asserting that a pin is synchronous to pclk, which
 *   nothing guarantees. power_button_n / sleep_button_n keep their existing
 *   3-flop chain, whose last two stages are the same filter and whose first
 *   two stages also supply the press edge detect.
 *
 *   Cost: SYNC_STAGES clocks of latency on those three inputs, and a pulse
 *   shorter than one clock period may not be seen at all. Drive them for at
 *   least two clock periods.
 *
 * PM TIMER:
 *   - 32-bit free-running counter
 *   - Configurable divider targeting the ACPI 3.579545 MHz rate
 *     (default /28 from 100 MHz = ~3.571 MHz, 0.23% low)
 *   - Rolls over ~1200 seconds at standard frequency
 *   - Generates overflow interrupt
 *
 * POWER STATES:
 *   - S0 (0): Working - Full power, all clocks active
 *   - S1 (1): Sleep   - Clock gating, context retained, quick wake
 *   - S3 (3): Deep    - Power domains off, context lost, wake from events
 *
 * PARAMETERS:
 *   - SYNC_STAGES: depth of the rtc_alarm / ext_wake_n / gpe_events_in
 *                  synchronizers. >= 2. Default 2.
 *
 * CHECK BY INSPECTION (this was a simulation-time parameter guard; contracts
 * belong in the header, properties in external formal bindings)
 *   - SYNC_STAGES must be >= 2. A single-stage "synchronizer" is not one; the
 *     design point is 2. Nothing in the RTL rejects a smaller value.
 *
 * ============================================================================
 */

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pm_acpi_core #(
    parameter int SYNC_STAGES = 2   // async input metastability filter depth, >= 2
) (
    // ========================================================================
    // Clock and Reset
    // ========================================================================
    input  logic        clk,
    input  logic        rst_n,

    // ========================================================================
    // Configuration Interface (from config_regs)
    // ========================================================================

    // Global control
    input  logic        cfg_acpi_enable,
    input  logic        cfg_pm_timer_enable,
    input  logic        cfg_gpe_enable,
    input  logic        cfg_soft_reset,        // ACPI_CONTROL.soft_reset, one-shot

    // PM1 control
    input  logic [2:0]  cfg_sleep_type,        // Target sleep state
    input  logic        cfg_sleep_enable,      // Sleep entry request, one-shot

    // PM1 per-source enables (PM1_ENABLE)
    input  logic        cfg_pm1_tmr_en,
    input  logic        cfg_pm1_pwrbtn_en,
    input  logic        cfg_pm1_slpbtn_en,
    input  logic        cfg_pm1_rtc_en,

    // PM Timer configuration
    input  logic [15:0] cfg_pm_timer_div,      // Clock divider
    input  logic [3:0]  cfg_timer_prescale,    // pre-divide by 2^this
    input  logic        cfg_timer_64bit,       // overflow from bit 63, not 31
    input  logic [31:0] cfg_timer_match,       // compare against the low word
    input  logic        pm_timer_value_read,   // read strobe for the low word

    // GPE enables
    input  logic [31:0] cfg_gpe_enables,

    // Clock gate control
    input  logic [31:0] cfg_clk_gate_ctrl,

    // Power domain control
    input  logic [7:0]  cfg_pwr_domain_ctrl,

    // Wake enables
    input  logic        cfg_gpe_wake_en,
    input  logic        cfg_pwrbtn_wake_en,
    input  logic        cfg_rtc_wake_en,
    input  logic        cfg_ext_wake_en,

    // Interrupt enables (top-level)
    input  logic        cfg_pme_enable,
    input  logic        cfg_wake_enable,
    input  logic        cfg_timer_ovf_enable,
    input  logic        cfg_timer_match_enable,
    input  logic        cfg_state_trans_enable,
    input  logic        cfg_pm1_enable,
    input  logic        cfg_gpe_int_enable,

    // Reset requests (RESET_CTRL), one-shot
    input  logic        cfg_sys_reset,
    input  logic        cfg_periph_reset,

    // ========================================================================
    // Software Write-1-to-Clear Masks (from config_regs, one cycle per write)
    // ========================================================================
    // Bit ordering is the register's own bit ordering - see the STATUS BIT MAP
    // localparams below, which are the single statement of the transform and
    // are mirrored by the decode in pm_acpi_config_regs (nothing in the RTL
    // cross-checks the two - see CHECK BY INSPECTION in that file's header).
    input  logic [4:0]  sw_clr_acpi_status,
    input  logic [6:0]  sw_clr_acpi_int_status,
    input  logic [4:0]  sw_clr_pm1_status,
    input  logic [3:0]  sw_clr_wake_status,
    input  logic [31:0] sw_clr_gpe_status,

    // ========================================================================
    // Status Interface (to config_regs) - sticky, W1C
    // ========================================================================
    output logic [1:0]  status_current_state,
    output logic [4:0]  status_acpi,          // ACPI_STATUS
    output logic [6:0]  status_acpi_int,      // ACPI_INT_STATUS
    output logic [4:0]  status_pm1,           // PM1_STATUS
    output logic [3:0]  status_wake_src,      // WAKE_STATUS
    output logic [31:0] status_gpe,           // GPE0_STATUS_HI:LO
    output logic [3:0]  status_reset_src,     // RESET_STATUS

    // Read-only mirrors
    output logic [31:0] status_pm_timer_value,
    output logic [31:0] status_pm_timer_value_hi,
    output logic [31:0] status_clk_gate_status,
    output logic [7:0]  status_pwr_domain_status,

    // ========================================================================
    // External Interfaces
    // ========================================================================

    // GPE event inputs (from system, asynchronous)
    input  logic [31:0] gpe_events_in,

    // Power button input (active low, asynchronous)
    input  logic        power_button_n,
    // Button timing, in core-clock cycles. A level must be stable for
    // cfg_debounce_cycles before an edge is reported; holding the
    // debounced power button for 2^cfg_long_press_shift asserts the
    // override. Zero disables either mechanism.
    input  logic [23:0] cfg_debounce_cycles,
    input  logic [4:0]  cfg_long_press_shift,
    input  logic        cfg_pwrbtn_ovr,

    // Sleep button input (active low, asynchronous)
    input  logic        sleep_button_n,

    // RTC alarm input (asynchronous)
    input  logic        rtc_alarm,

    // External wake input (active low, asynchronous)
    input  logic        ext_wake_n,
    // Reset-source inputs, active low, synchronized like the other board
    // pins. A pulse latches its RESET_STATUS bit until the next reset.
    input  logic        wdt_reset_n,
    input  logic        ext_reset_n,

    // Clock gate outputs (to clock gates)
    output logic [31:0] clock_gate_en,

    // Power domain outputs (to power switches)
    output logic [7:0]  power_domain_en,

    // System reset request (one-cycle pulse)
    output logic        sys_reset_req,

    // Peripheral reset request (one-cycle pulse)
    output logic        periph_reset_req,

    // PM interrupt output (aggregated level)
    output logic        pm_interrupt
);

    // ========================================================================
    // STATUS BIT MAP
    // ========================================================================
    // Each vector below is indexed by the SOFTWARE bit position in its
    // register, so status_acpi[2] is ACPI_STATUS bit 2 and nothing else. The
    // map is not symmetric - a transposition here would be invisible on an
    // all-bits-set stimulus - so every index is named once and used by name.
    localparam int ACPI_ST_PME    = 0;   // ACPI_STATUS.pme_status
    localparam int ACPI_ST_WAKE   = 1;   // ACPI_STATUS.wake_status
    localparam int ACPI_ST_TMROV  = 2;   // ACPI_STATUS.timer_overflow
    localparam int ACPI_ST_TRANS  = 3;   // ACPI_STATUS.state_transition
    localparam int ACPI_ST_TMATCH = 4;   // ACPI_STATUS.timer_match

    localparam int INT_ST_PME     = 0;   // ACPI_INT_STATUS.pme_int
    localparam int INT_ST_WAKE    = 1;   // ACPI_INT_STATUS.wake_int
    localparam int INT_ST_TMROV   = 2;   // ACPI_INT_STATUS.timer_ovf_int
    localparam int INT_ST_TRANS   = 3;   // ACPI_INT_STATUS.state_trans_int
    localparam int INT_ST_PM1     = 4;   // ACPI_INT_STATUS.pm1_int
    localparam int INT_ST_GPE     = 5;   // ACPI_INT_STATUS.gpe_int
    localparam int INT_ST_TMATCH  = 6;   // ACPI_INT_STATUS.timer_match_int

    localparam int PM1_ST_TMR     = 0;   // PM1_STATUS.tmr_sts
    localparam int PM1_ST_PWRBTN  = 1;   // PM1_STATUS.pwrbtn_sts
    localparam int PM1_ST_SLPBTN  = 2;   // PM1_STATUS.slpbtn_sts
    localparam int PM1_ST_RTC     = 3;   // PM1_STATUS.rtc_sts
    localparam int PM1_ST_WAK     = 4;   // PM1_STATUS.wak_sts (no enable bit)

    localparam int WK_ST_GPE      = 0;   // WAKE_STATUS.gpe_wake
    localparam int WK_ST_PWRBTN   = 1;   // WAKE_STATUS.pwrbtn_wake
    localparam int WK_ST_RTC      = 2;   // WAKE_STATUS.rtc_wake
    localparam int WK_ST_EXT      = 3;   // WAKE_STATUS.ext_wake

    localparam int RST_ST_POR     = 0;   // RESET_STATUS.por_reset
    localparam int RST_ST_WDT     = 1;   // RESET_STATUS.wdt_reset
    localparam int RST_ST_SW      = 2;   // RESET_STATUS.sw_reset
    localparam int RST_ST_EXT     = 3;   // RESET_STATUS.ext_reset

    // ========================================================================
    // Internal Registers and Signals
    // ========================================================================

    // PM Timer
    logic [63:0] r_pm_timer_count;
    logic [31:0] r_pm_timer_hi_shadow;
    logic [31:0] r_prescale_cnt;
    logic        w_prescale_tick;
    logic        r_timer_match_evt;
    logic [15:0] r_pm_timer_div_count;
    logic        r_pm_timer_tick;
    logic        r_pm_timer_ovf;

    // Power state FSM
    typedef enum logic [2:0] {
        PWR_S0_WORKING   = 3'b000,
        PWR_S1_SLEEP     = 3'b001,
        PWR_S3_SUSPEND   = 3'b011,
        PWR_S5_SOFF      = 3'b101,
        PWR_TRANSITION   = 3'b111
    } pwr_state_t;

    pwr_state_t r_pwr_state, w_next_pwr_state;
    logic       r_state_trans_done;
    logic       r_wake_pending;
    logic       r_sleep_enable_d;
    logic       w_sleep_req;

    // Self-clearing request bits, edge detected (issue #54 follow-up F2)
    logic       r_soft_reset_d;
    logic       r_sys_reset_d;
    logic       r_periph_reset_d;
    logic       w_soft_reset_req;
    logic       w_sys_reset_pulse;
    logic       w_periph_reset_pulse;

    // Asynchronous input synchronizers
    logic        r_rtc_alarm_sync  [SYNC_STAGES];
    logic        r_ext_wake_n_sync [SYNC_STAGES];
    logic        r_wdt_reset_n_sync [SYNC_STAGES];
    logic        r_ext_reset_n_sync [SYNC_STAGES];
    logic        r_wdt_reset_seen;
    logic        r_ext_reset_seen;
    logic [31:0] r_gpe_events_sync [SYNC_STAGES];
    logic        w_rtc_alarm;
    logic        w_ext_wake_n;
    logic        w_wdt_reset_n;
    logic        w_ext_reset_n;
    logic [31:0] w_gpe_events;

    // Assertion-edge detect on the two level pins (issue #54 follow-up F1)
    logic        r_rtc_alarm_d;
    logic        r_ext_wake_n_d;
    logic        w_rtc_alarm_edge;
    logic        w_ext_wake_edge;

    // GPE edge detection and sticky status
    logic [31:0] r_gpe_events_prev;
    logic [31:0] w_gpe_events_edge;
    logic [31:0] w_gpe_set;
    logic [31:0] r_gpe_status;

    // Button synchronization and edge detection
    logic [2:0] r_power_button_sync;
    logic [2:0] r_sleep_button_sync;
    logic       w_power_button_press;
    logic       w_sleep_button_press;

    // Wake event detection
    logic       w_any_wake_event;
    logic [3:0] w_wake_src_event;

    // Clock gating / power domain sequencing
    logic [31:0] w_clk_gate_target;
    logic [31:0] r_clk_gate_current;
    logic [7:0]  w_pwr_domain_target;
    logic [7:0]  r_pwr_domain_current;

    // Sticky status registers and their set terms
    logic [4:0]  r_acpi_status;
    logic [4:0]  w_acpi_status_set;
    logic [6:0]  r_acpi_int_status;
    logic [6:0]  w_acpi_int_status_set;
    logic [4:0]  r_pm1_status;
    logic [4:0]  w_pm1_status_set;
    logic [3:0]  r_wake_status;

    // Soft-reset-qualified copies of the set terms (see #54 F9 below)
    logic [4:0]  w_acpi_status_set_q;
    logic [6:0]  w_acpi_int_status_set_q;
    logic [4:0]  w_pm1_status_set_q;
    logic [3:0]  w_wake_src_event_q;
    logic [31:0] w_gpe_set_q;

    // Raw hardware events feeding the status bits
    logic       w_ev_pme;
    logic       w_ev_gpe_pending;

    // Reset source tracking
    logic       r_por_reset;
    logic       r_sw_reset;

    // Reset request outputs
    logic       r_sys_reset_req;
    logic [23:0] r_pwr_btn_cnt;
    logic [23:0] r_slp_btn_cnt;
    logic        r_pwr_btn_level;
    logic        r_slp_btn_level;
    logic        r_pwr_btn_level_d;
    logic        r_slp_btn_level_d;
    logic [31:0] r_pwr_hold_cnt;
    logic        r_long_press;
    logic        w_pwrbtn_override;
    logic       r_was_soff;
    logic       w_soff_exit;
    logic       r_periph_reset_req;

    // Interrupt aggregation
    logic [4:0] w_pm1_src_enable;
    logic       w_int_pme;
    logic       w_int_wake;
    logic       w_int_timer_ovf;
    logic       w_int_timer_match;
    logic       w_int_state_trans;
    logic       w_int_pm1;
    logic       w_int_gpe;

    // ========================================================================
    // Asynchronous Input Synchronizers
    // ========================================================================
    // Unconditional: these are device pins in both CDC_ENABLE settings.
    // ext_wake_n resets to its INACTIVE level (1) so a reset release cannot
    // fabricate a wake; the other two reset to 0 for the same reason.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int s = 0; s < SYNC_STAGES; s++) begin
                r_rtc_alarm_sync[s]  <= 1'b0;
                r_ext_wake_n_sync[s] <= 1'b1;
                r_wdt_reset_n_sync[s] <= 1'b1;
                r_ext_reset_n_sync[s] <= 1'b1;
                r_gpe_events_sync[s] <= '0;
            end
        end else begin
            r_rtc_alarm_sync[0]  <= rtc_alarm;
            r_ext_wake_n_sync[0] <= ext_wake_n;
            r_wdt_reset_n_sync[0] <= wdt_reset_n;
            r_ext_reset_n_sync[0] <= ext_reset_n;
            r_gpe_events_sync[0] <= gpe_events_in;
            for (int s = 1; s < SYNC_STAGES; s++) begin
                r_rtc_alarm_sync[s]  <= r_rtc_alarm_sync[s-1];
                r_ext_wake_n_sync[s] <= r_ext_wake_n_sync[s-1];
                r_wdt_reset_n_sync[s] <= r_wdt_reset_n_sync[s-1];
                r_ext_reset_n_sync[s] <= r_ext_reset_n_sync[s-1];
                r_gpe_events_sync[s] <= r_gpe_events_sync[s-1];
            end
        end
    )

    assign w_rtc_alarm  = r_rtc_alarm_sync[SYNC_STAGES-1];
    assign w_ext_wake_n = r_ext_wake_n_sync[SYNC_STAGES-1];
    assign w_gpe_events = r_gpe_events_sync[SYNC_STAGES-1];
    assign w_wdt_reset_n = r_wdt_reset_n_sync[SYNC_STAGES-1];
    assign w_ext_reset_n = r_ext_reset_n_sync[SYNC_STAGES-1];

    // A reset SOURCE is latched, not sampled: the pulse that caused the reset
    // is long gone by the time software reads RESET_STATUS, so the bit has to
    // survive until the next reset clears it.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wdt_reset_seen <= 1'b0;
            r_ext_reset_seen <= 1'b0;
        end else begin
            if (!w_wdt_reset_n) r_wdt_reset_seen <= 1'b1;
            if (!w_ext_reset_n) r_ext_reset_seen <= 1'b1;
        end
    )

    // ========================================================================
    // Assertion-Edge Detect on the Level Pins
    // ========================================================================
    // rtc_alarm and ext_wake_n are LEVELS on the pin, but the status bits they
    // set are software-clearable records of an EVENT. Setting them from the
    // level re-armed the bit every cycle, so a W1C could never take effect
    // while the pin was still asserted and the interrupt could not be
    // dismissed at all (issue #54 follow-up F1). They are now treated exactly
    // like GPE and the buttons: the ASSERTION EDGE sets, and the pin has to
    // deassert and reassert to set again.
    //
    // The reference flop is unconditional and its reset value matches the
    // synchronizer's, so a reset release cannot fabricate an edge.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rtc_alarm_d  <= 1'b0;
            r_ext_wake_n_d <= 1'b1;
        end else begin
            r_rtc_alarm_d  <= w_rtc_alarm;
            r_ext_wake_n_d <= w_ext_wake_n;
        end
    )

    // rtc_alarm is active high, ext_wake_n active low: both edges below are
    // the moment the source becomes ASSERTED.
    assign w_rtc_alarm_edge = w_rtc_alarm && !r_rtc_alarm_d;
    assign w_ext_wake_edge  = !w_ext_wake_n && r_ext_wake_n_d;

    // ========================================================================
    // PM Timer Logic
    // ========================================================================

    // PRESCALER, ahead of the divider. The divider is 16 bits, so on its own
    // it cannot reach the slow end of the range; pre-dividing by a power of
    // two extends it without widening the field software already uses. A
    // prescale of 0 passes every cycle through, which is the old behaviour.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n))                              r_prescale_cnt <= '0;
        else if (cfg_acpi_enable && cfg_pm_timer_enable)       r_prescale_cnt <= r_prescale_cnt + 32'd1;
        else                                                   r_prescale_cnt <= '0;
    )
    // A variable part-select is not legal, so mask instead: the low
    // cfg_timer_prescale bits must all be zero for the tick to pass.
    assign w_prescale_tick =
        ((r_prescale_cnt & ((32'd1 << cfg_timer_prescale) - 32'd1)) == 32'd0);

    // Timer divider counter
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pm_timer_div_count <= '0;
            r_pm_timer_tick <= 1'b0;
        end else if (cfg_acpi_enable && cfg_pm_timer_enable && w_prescale_tick) begin
            if (r_pm_timer_div_count >= cfg_pm_timer_div) begin
                r_pm_timer_div_count <= '0;
                r_pm_timer_tick <= 1'b1;
            end else begin
                r_pm_timer_div_count <= r_pm_timer_div_count + 1'b1;
                r_pm_timer_tick <= 1'b0;
            end
        end else if (cfg_acpi_enable && cfg_pm_timer_enable) begin
            r_pm_timer_tick <= 1'b0;   // between prescale ticks, hold
        end else begin
            r_pm_timer_div_count <= '0;
            r_pm_timer_tick <= 1'b0;
        end
    )

    // PM Timer counter (32-bit free-running). r_pm_timer_ovf is the raw
    // one-cycle carry-out; the software-visible overflow flags are the sticky
    // bits it sets.
    // The counter is always 64 bits; cfg_timer_64bit only chooses WHICH carry
    // counts as an overflow, so software can widen the timer without losing
    // the 32-bit overflow it may already be using.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pm_timer_count  <= '0;
            r_pm_timer_ovf    <= 1'b0;
            r_timer_match_evt <= 1'b0;
        end else if (cfg_acpi_enable && cfg_pm_timer_enable && r_pm_timer_tick) begin
            r_pm_timer_count <= r_pm_timer_count + 64'd1;
            r_pm_timer_ovf   <= cfg_timer_64bit
                              ? (r_pm_timer_count == 64'hFFFF_FFFF_FFFF_FFFF)
                              : (r_pm_timer_count[31:0] == 32'hFFFF_FFFF);
            // The match is on the value the counter is ABOUT to hold, so the
            // event and the readable value agree.
            r_timer_match_evt <= ((r_pm_timer_count[31:0] + 32'd1) == cfg_timer_match);
        end else begin
            r_pm_timer_ovf    <= 1'b0;
            r_timer_match_evt <= 1'b0;
        end
    )

    // COHERENT 64-BIT READ. Two 32-bit reads of a running counter can straddle
    // a carry and return a value the timer never held, so reading the low word
    // latches the high word and PM_TIMER_VALUE_HI returns that snapshot.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n))     r_pm_timer_hi_shadow <= '0;
        else if (pm_timer_value_read) r_pm_timer_hi_shadow <= r_pm_timer_count[63:32];
    )

    assign status_pm_timer_value    = r_pm_timer_count[31:0];
    assign status_pm_timer_value_hi = r_pm_timer_hi_shadow;

    // ========================================================================
    // Button Input Synchronization and Edge Detection
    // ========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_power_button_sync <= 3'b111;
            r_sleep_button_sync <= 3'b111;
        end else begin
            r_power_button_sync <= {r_power_button_sync[1:0], power_button_n};
            r_sleep_button_sync <= {r_sleep_button_sync[1:0], sleep_button_n};
        end
    )

    // DEBOUNCE. The synchronizer resolves metastability; it does nothing
    // about contact bounce, and a bouncing push button was recorded as
    // several presses (RLB-009). A candidate level has to hold for
    // cfg_debounce_cycles before it becomes the accepted level; any change
    // restarts the count. cfg_debounce_cycles = 0 accepts immediately, which
    // is the old behaviour.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pwr_btn_cnt   <= '0;
            r_slp_btn_cnt   <= '0;
            r_pwr_btn_level <= 1'b1;
            r_slp_btn_level <= 1'b1;
        end else begin
            if (r_power_button_sync[2] == r_pwr_btn_level) begin
                r_pwr_btn_cnt <= '0;
            end else if (r_pwr_btn_cnt >= cfg_debounce_cycles) begin
                r_pwr_btn_level <= r_power_button_sync[2];
                r_pwr_btn_cnt   <= '0;
            end else begin
                r_pwr_btn_cnt <= r_pwr_btn_cnt + 24'd1;
            end

            if (r_sleep_button_sync[2] == r_slp_btn_level) begin
                r_slp_btn_cnt <= '0;
            end else if (r_slp_btn_cnt >= cfg_debounce_cycles) begin
                r_slp_btn_level <= r_sleep_button_sync[2];
                r_slp_btn_cnt   <= '0;
            end else begin
                r_slp_btn_cnt <= r_slp_btn_cnt + 24'd1;
            end
        end
    )

    // Press = high-to-low transition of the DEBOUNCED level, one cycle wide.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pwr_btn_level_d <= 1'b1;
            r_slp_btn_level_d <= 1'b1;
        end else begin
            r_pwr_btn_level_d <= r_pwr_btn_level;
            r_slp_btn_level_d <= r_slp_btn_level;
        end
    )
    assign w_power_button_press = r_pwr_btn_level_d && !r_pwr_btn_level;
    assign w_sleep_button_press = r_slp_btn_level_d && !r_slp_btn_level;

    // LONG PRESS. Holding the debounced power button for 2^shift cycles is
    // ACPI's power-button override: the machine goes to soft off whatever it
    // was doing, which is the point - it is the escape hatch when software
    // has stopped responding. Software can force the same thing by writing
    // PM1_CONTROL.pwrbtn_ovr.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pwr_hold_cnt <= '0;
            r_long_press   <= 1'b0;
        end else if (r_pwr_btn_level) begin
            r_pwr_hold_cnt <= '0;
            r_long_press   <= 1'b0;
        end else if (cfg_long_press_shift != 5'd0) begin
            if (r_pwr_hold_cnt[cfg_long_press_shift]) r_long_press <= 1'b1;
            else                                      r_pwr_hold_cnt <= r_pwr_hold_cnt + 32'd1;
        end
    )
    // PM1_CONTROL.pwrbtn_ovr ENABLES the override rather than commanding it.
    // Commanding soft off from a control bit would mean any write that
    // happens to set the bit parks the machine in S5, which is not what a
    // register called "override" should do; as an enable it lets software
    // turn the four-second escape hatch off, and the hatch itself stays a
    // hardware property of holding the button.
    assign w_pwrbtn_override = r_long_press && cfg_pwrbtn_ovr;

    // ========================================================================
    // GPE Event Handling
    // ========================================================================

    // Edge reference tracks the synchronized input EVERY cycle. Freezing it
    // while GPE was disabled meant a level that changed during the disabled
    // window fabricated an edge the moment software re-enabled (round_3 item
    // 4); an input that never changed cannot produce an event.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_gpe_events_prev <= '0;
        end else begin
            r_gpe_events_prev <= w_gpe_events;
        end
    )

    assign w_gpe_events_edge = w_gpe_events & ~r_gpe_events_prev;

    // Recording an event is gated by the enables; CLEARING never is, so
    // software can always drain the register.
    assign w_gpe_set   = (cfg_acpi_enable && cfg_gpe_enable) ? w_gpe_events_edge : '0;
    assign w_gpe_set_q = cfg_soft_reset ? '0 : w_gpe_set;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_gpe_status <= '0;
        end else if (w_soft_reset_req) begin
            r_gpe_status <= '0;
        end else begin
            r_gpe_status <= (r_gpe_status & ~sw_clr_gpe_status) | w_gpe_set_q;
        end
    )

    assign status_gpe = r_gpe_status;

    // Any enabled GPE source is pending. This is the term behind both the GPE
    // interrupt and the GPE wake, and it now falls when software W1Cs the
    // status - which is what unblocks sleep entry (round_3 item 1).
    assign w_ev_gpe_pending = |(r_gpe_status & cfg_gpe_enables);

    // ========================================================================
    // Wake Event Detection
    // ========================================================================

    // No wake term is a raw pin level, so every one of them is something
    // software can eventually dismiss:
    //   GPE    - the ENABLED-and-PENDING level of the sticky GPE status, which
    //            W1C clears. An unacknowledged GPE therefore keeps the machine
    //            awake, which is the point of a wake source.
    //   pwrbtn - the press edge (two synchronized stages).
    //   rtc    - the alarm ASSERTION edge (#54 F1).
    //   ext    - the ext_wake_n ASSERTION edge (#54 F1).
    // Consequence, stated rather than hidden: a level source already asserted
    // BEFORE the sleep request does not block sleep entry and does not wake
    // the machine; it has to deassert and reassert. WAKE_STATUS records the
    // original assertion either way.
    assign w_wake_src_event[WK_ST_GPE]    = cfg_gpe_wake_en    && w_ev_gpe_pending;
    assign w_wake_src_event[WK_ST_PWRBTN] = cfg_pwrbtn_wake_en && w_power_button_press;
    assign w_wake_src_event[WK_ST_RTC]    = cfg_rtc_wake_en    && w_rtc_alarm_edge;
    assign w_wake_src_event[WK_ST_EXT]    = cfg_ext_wake_en    && w_ext_wake_edge;

    assign w_any_wake_event = |w_wake_src_event;

    // ========================================================================
    // Power State FSM
    // ========================================================================

    // cfg_sleep_enable is a self-clearing one-shot in the register block; the
    // bridge holds its request for two cycles, so edge-detect it here to get
    // exactly one sleep request per software write.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sleep_enable_d <= 1'b0;
        end else begin
            r_sleep_enable_d <= cfg_sleep_enable;
        end
    )

    assign w_sleep_req = cfg_sleep_enable && !r_sleep_enable_d;

    // The same correction for the other three self-clearing request bits.
    // peakrdl_to_cmdrsp HOLDS its request for the accept cycle plus
    // CMD_WAIT_ACK, so a `singlepulse` field presents as a TWO-cycle level
    // here. Edge detecting turns one software write into exactly one core
    // pulse, whatever the bridge does with the request width (#54 F2).
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_soft_reset_d   <= 1'b0;
            r_sys_reset_d    <= 1'b0;
            r_periph_reset_d <= 1'b0;
        end else begin
            r_soft_reset_d   <= cfg_soft_reset;
            r_sys_reset_d    <= cfg_sys_reset;
            r_periph_reset_d <= cfg_periph_reset;
        end
    )

    assign w_soft_reset_req     = cfg_soft_reset   && !r_soft_reset_d;
    assign w_sys_reset_pulse    = cfg_sys_reset    && !r_sys_reset_d;
    assign w_periph_reset_pulse = cfg_periph_reset && !r_periph_reset_d;

    // Latched wake request. Priority order matters: a new sleep request drops
    // a stale latch, being in S0 means there is nothing to wake from, and only
    // then does an event arm it. Without the S0 clear a wake taken while
    // awake would block the next sleep entry outright.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wake_pending <= 1'b0;
        end else if (!cfg_acpi_enable || cfg_soft_reset || w_sleep_req) begin
            r_wake_pending <= 1'b0;
        end else if (r_pwr_state == PWR_S0_WORKING) begin
            r_wake_pending <= 1'b0;
        end else if (w_any_wake_event) begin
            r_wake_pending <= 1'b1;
        end
    )

    // State register
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pwr_state <= PWR_S0_WORKING;
            r_state_trans_done <= 1'b0;
        end else begin
            r_pwr_state <= w_next_pwr_state;
            r_state_trans_done <= (r_pwr_state == PWR_TRANSITION) &&
                                  (w_next_pwr_state != PWR_TRANSITION);
        end
    )

    // Next state logic
    always_comb begin
        w_next_pwr_state = r_pwr_state;

        // The soft-reset LEVEL (not its edge) forces S0 for the whole request
        // window, so the machine cannot slip back into a sleep state between
        // the pulse and software observing S0.
        if (!cfg_acpi_enable || cfg_soft_reset) begin
            w_next_pwr_state = PWR_S0_WORKING;
        end else if (w_pwrbtn_override && (r_pwr_state != PWR_S5_SOFF)) begin
            // The override outranks everything except a reset: that is what
            // makes it an escape hatch rather than a request.
            w_next_pwr_state = PWR_S5_SOFF;
        end else begin
            case (r_pwr_state)
                PWR_S0_WORKING: begin
                    // Enter sleep on the one-shot request
                    if (w_sleep_req) begin
                        if (cfg_sleep_type == 3'h1 || cfg_sleep_type == 3'h3 ||
                            cfg_sleep_type == 3'h5) begin
                            w_next_pwr_state = PWR_TRANSITION;
                        end else begin
                            w_next_pwr_state = PWR_S0_WORKING;  // S0 or unsupported
                        end
                    end
                end

                PWR_S1_SLEEP: begin
                    if (w_any_wake_event) begin
                        w_next_pwr_state = PWR_TRANSITION;
                    end
                end

                PWR_S3_SUSPEND: begin
                    if (w_any_wake_event) begin
                        w_next_pwr_state = PWR_TRANSITION;
                    end
                end

                // S5 is SOFT OFF, not a deeper sleep: nothing is retained, so
                // leaving it is a boot rather than a resume. The wake sources
                // are the same ones - ACPI lets software choose which are
                // armed for soft off - but the exit pulses sys_reset_req, see
                // below, because there is no context to return to.
                PWR_S5_SOFF: begin
                    if (w_any_wake_event) begin
                        w_next_pwr_state = PWR_TRANSITION;
                    end
                end

                PWR_TRANSITION: begin
                    // A latched or live wake OUTRANKS the still-programmed
                    // sleep_type. Re-reading sleep_type here is what sent a
                    // pulsed wake straight back to sleep (#54 H5).
                    if (r_wake_pending || w_any_wake_event) begin
                        w_next_pwr_state = PWR_S0_WORKING;
                    end else if (cfg_sleep_type == 3'h1) begin
                        w_next_pwr_state = PWR_S1_SLEEP;
                    end else if (cfg_sleep_type == 3'h3) begin
                        w_next_pwr_state = PWR_S3_SUSPEND;
                    end else if (cfg_sleep_type == 3'h5) begin
                        w_next_pwr_state = PWR_S5_SOFF;
                    end else begin
                        w_next_pwr_state = PWR_S0_WORKING;
                    end
                end

                default: begin
                    w_next_pwr_state = PWR_S0_WORKING;
                end
            endcase
        end
    end

    // The status field is two bits, so it reports an ENCODING rather than the
    // ACPI number: 0 = S0, 1 = S1, 2 = S5, 3 = S3. Encoding 2 was the free one;
    // widening the field would have moved bits software already reads.
    assign status_current_state = (r_pwr_state == PWR_S1_SLEEP)   ? 2'b01 :
                                  (r_pwr_state == PWR_S3_SUSPEND) ? 2'b11 :
                                  (r_pwr_state == PWR_S5_SOFF)    ? 2'b10 : 2'b00;

    // ========================================================================
    // Clock Gating Control with Power State Awareness
    // ========================================================================

    always_comb begin
        case (r_pwr_state)
            PWR_S1_SLEEP: begin
                // S1: gate all clocks except the two essential ones
                w_clk_gate_target = cfg_clk_gate_ctrl & 32'h00000003;
            end
            PWR_S3_SUSPEND, PWR_S5_SOFF: begin
                // S3 and S5: gate every clock
                w_clk_gate_target = 32'h00000000;
            end
            default: begin
                // S0 and the transition state: configuration passes through
                w_clk_gate_target = cfg_clk_gate_ctrl;
            end
        endcase
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_clk_gate_current <= 32'hFFFFFFFF;  // All enabled at reset
        end else begin
            r_clk_gate_current <= w_clk_gate_target;
        end
    )

    assign clock_gate_en          = r_clk_gate_current;
    assign status_clk_gate_status = r_clk_gate_current;

    // ========================================================================
    // Power Domain Sequencing
    // ========================================================================

    always_comb begin
        case (r_pwr_state)
            PWR_S3_SUSPEND, PWR_S5_SOFF: begin
                // S3 and S5: power down all except domain 0 (always-on)
                w_pwr_domain_target = cfg_pwr_domain_ctrl & 8'h01;
            end
            default: begin
                // S0, S1 (context retention) and the transition state
                w_pwr_domain_target = cfg_pwr_domain_ctrl;
            end
        endcase
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pwr_domain_current <= 8'hFF;  // All powered at reset
        end else begin
            r_pwr_domain_current <= w_pwr_domain_target;
        end
    )

    assign power_domain_en          = r_pwr_domain_current;
    assign status_pwr_domain_status = r_pwr_domain_current;

    // ========================================================================
    // Sticky Status Registers
    // ========================================================================
    // One shape everywhere: (value & ~software_clear) | hardware_set.
    // A soft reset clears the lot.

    // PME: any power-management event worth telling software about.
    assign w_ev_pme = w_power_button_press || w_sleep_button_press ||
                      w_any_wake_event || r_state_trans_done;

    assign w_acpi_status_set[ACPI_ST_PME]   = w_ev_pme;
    assign w_acpi_status_set[ACPI_ST_WAKE]  = w_any_wake_event;
    assign w_acpi_status_set[ACPI_ST_TMROV] = r_pm_timer_ovf;
    assign w_acpi_status_set[ACPI_ST_TRANS] = r_state_trans_done;
    assign w_acpi_status_set[ACPI_ST_TMATCH] = r_timer_match_evt;

    assign w_pm1_status_set[PM1_ST_TMR]    = r_pm_timer_ovf;
    assign w_pm1_status_set[PM1_ST_PWRBTN] = w_power_button_press;
    assign w_pm1_status_set[PM1_ST_SLPBTN] = w_sleep_button_press;
    assign w_pm1_status_set[PM1_ST_RTC]    = w_rtc_alarm_edge;
    assign w_pm1_status_set[PM1_ST_WAK]    = w_any_wake_event;

    // ACPI_INT_STATUS is an UNCONDITIONAL per-source EVENT LOG. Every bit is
    // set by its event whether or not the corresponding interrupt is enabled,
    // and each is W1C independently. pm1_int is set from the same five sources
    // the pm1 interrupt term uses (round_2 item 7: it used to be set from
    // three of them), and gpe_int from the GPE EDGES rather than the pending
    // level, so it can be dismissed BEFORE GPE0_STATUS is drained instead of
    // re-arming itself until the last GPE bit is cleared (#54 F6).
    //
    // Deviation, stated: the gpe_int term is the CAPTURED edge - the same term
    // that sets GPE0_STATUS - so it follows GPE capture being enabled at all
    // (cfg_acpi_enable && cfg_gpe_enable). It is unconditional with respect to
    // every interrupt/enable MASK, which is what makes it a log; logging a GPE
    // this block was told not to watch would contradict GPE0_STATUS.
    assign w_acpi_int_status_set[INT_ST_PME]   = w_ev_pme;
    assign w_acpi_int_status_set[INT_ST_WAKE]  = w_any_wake_event;
    assign w_acpi_int_status_set[INT_ST_TMROV] = r_pm_timer_ovf;
    assign w_acpi_int_status_set[INT_ST_TRANS] = r_state_trans_done;
    assign w_acpi_int_status_set[INT_ST_TMATCH] = r_timer_match_evt;
    assign w_acpi_int_status_set[INT_ST_PM1]   = |w_pm1_status_set;
    assign w_acpi_int_status_set[INT_ST_GPE]   = |w_gpe_set;

    // Soft-reset qualification (#54 F9). The clear branch above fires on the
    // one-cycle w_soft_reset_req, but cfg_soft_reset is a two-cycle level
    // behind this bridge and could narrow to one in a different integration.
    // Suppressing the SET terms across the WHOLE level window means a soft
    // reset taken mid-transition cannot leave state_transition or pme set
    // however the request is shaped.
    assign w_acpi_status_set_q     = cfg_soft_reset ? 5'h0  : w_acpi_status_set;
    assign w_acpi_int_status_set_q = cfg_soft_reset ? 7'h0  : w_acpi_int_status_set;
    assign w_pm1_status_set_q      = cfg_soft_reset ? 5'h0  : w_pm1_status_set;
    assign w_wake_src_event_q      = cfg_soft_reset ? 4'h0  : w_wake_src_event;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_acpi_status     <= '0;
            r_acpi_int_status <= '0;
            r_pm1_status      <= '0;
            r_wake_status     <= '0;
        end else if (w_soft_reset_req) begin
            r_acpi_status     <= '0;
            r_acpi_int_status <= '0;
            r_pm1_status      <= '0;
            r_wake_status     <= '0;
        end else begin
            r_acpi_status     <= (r_acpi_status     & ~sw_clr_acpi_status)     |
                                 w_acpi_status_set_q;
            r_acpi_int_status <= (r_acpi_int_status & ~sw_clr_acpi_int_status) |
                                 w_acpi_int_status_set_q;
            r_pm1_status      <= (r_pm1_status      & ~sw_clr_pm1_status)      |
                                 w_pm1_status_set_q;
            r_wake_status     <= (r_wake_status     & ~sw_clr_wake_status)     |
                                 w_wake_src_event_q;
        end
    )

    assign status_acpi     = r_acpi_status;
    assign status_acpi_int = r_acpi_int_status;
    assign status_pm1      = r_pm1_status;
    assign status_wake_src = r_wake_status;

    // ========================================================================
    // Reset Source Tracking and Reset Requests
    // ========================================================================
    // por_reset is a sticky LEVEL, not the one-cycle pulse it used to be: no
    // APB read can ever land on a single cycle out of reset, so the old shape
    // reported nothing (round_2 item 7). A soft reset hands the title over.
    // wdt/ext have no input port on this module and read 0 - stated in the
    // RDL descriptions rather than left looking implemented.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_por_reset <= 1'b1;
            r_sw_reset  <= 1'b0;
        end else if (w_soft_reset_req) begin
            r_por_reset <= 1'b0;
            r_sw_reset  <= 1'b1;
        end
    )

    assign status_reset_src[RST_ST_POR] = r_por_reset;
    assign status_reset_src[RST_ST_WDT] = r_wdt_reset_seen;
    assign status_reset_src[RST_ST_SW]  = r_sw_reset;
    assign status_reset_src[RST_ST_EXT] = r_ext_reset_seen;

    // RESET_CTRL requests: registered so the output is a clean one-cycle
    // pulse in this clock domain regardless of how long the bridge holds the
    // write (#54 H6 - these outputs used to be hardwired to 0).
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sys_reset_req    <= 1'b0;
            r_periph_reset_req <= 1'b0;
        end else begin
            r_sys_reset_req    <= w_sys_reset_pulse || w_soff_exit;
            r_periph_reset_req <= w_periph_reset_pulse;
        end
    )

    // Leaving soft off is a BOOT, not a resume: S5 retains nothing, so the
    // system has to come up from reset rather than continue. One cycle, on
    // the S5 -> anything edge, ORed into the same request the RESET_CTRL
    // write drives.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) r_was_soff <= 1'b0;
        else                      r_was_soff <= (r_pwr_state == PWR_S5_SOFF);
    )
    assign w_soff_exit = r_was_soff && (r_pwr_state != PWR_S5_SOFF);

    assign sys_reset_req    = r_sys_reset_req;
    assign periph_reset_req = r_periph_reset_req;

    // ========================================================================
    // Interrupt Aggregation - a LEVEL over enabled sticky status
    // ========================================================================

    // PM1_STATUS.wak_sts has no enable bit in the RDL, so it is masked out of
    // the PM1 interrupt term rather than being treated as always-enabled.
    assign w_pm1_src_enable[PM1_ST_TMR]    = cfg_pm1_tmr_en;
    assign w_pm1_src_enable[PM1_ST_PWRBTN] = cfg_pm1_pwrbtn_en;
    assign w_pm1_src_enable[PM1_ST_SLPBTN] = cfg_pm1_slpbtn_en;
    assign w_pm1_src_enable[PM1_ST_RTC]    = cfg_pm1_rtc_en;
    assign w_pm1_src_enable[PM1_ST_WAK]    = 1'b0;

    assign w_int_pme         = r_acpi_status[ACPI_ST_PME]   && cfg_pme_enable;
    assign w_int_wake        = r_acpi_status[ACPI_ST_WAKE]  && cfg_wake_enable;
    assign w_int_timer_ovf   = r_acpi_status[ACPI_ST_TMROV] && cfg_timer_ovf_enable;
    assign w_int_state_trans = r_acpi_status[ACPI_ST_TRANS] && cfg_state_trans_enable;
    assign w_int_timer_match = r_acpi_status[ACPI_ST_TMATCH] && cfg_timer_match_enable;
    assign w_int_pm1         = (|(r_pm1_status & w_pm1_src_enable)) && cfg_pm1_enable;
    assign w_int_gpe         = w_ev_gpe_pending && cfg_gpe_int_enable;

    // cfg_acpi_enable is this block's SCI_EN: with ACPI disabled the pin is
    // held low even though the status registers keep recording events, so
    // software that has not enabled ACPI is never interrupted but loses no
    // history (#54 F10).
    assign pm_interrupt = cfg_acpi_enable &&
                          (w_int_pme || w_int_wake || w_int_timer_ovf ||
                           w_int_timer_match || w_int_state_trans ||
                           w_int_pm1 || w_int_gpe);


    // Elaboration-time parameter guard (sim only). Not an assertion in the
    // house sense: see vault/handbook/design/no-assertions-in-rtl.md.
`ifndef SYNTHESIS
    // Simulation-time parameter guard (same shape as the pit/hpet guards).
    initial begin : param_check
        if (SYNC_STAGES < 2) begin
            $error("pm_acpi_core: SYNC_STAGES=%0d but an input synchronizer needs >= 2",
                   SYNC_STAGES);
        end
    end
`endif

endmodule : pm_acpi_core
