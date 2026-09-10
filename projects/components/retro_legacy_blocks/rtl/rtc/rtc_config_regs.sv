// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rtc_config_regs
// Purpose: Configuration register wrapper for RTC - PeakRDL Wrapper
//
// This module wraps the PeakRDL-generated rtc_regs module and adds:
// - CMD/RSP to PeakRDL adapter (peakrdl_to_cmdrsp)
// - Strict address decode with PSLVERR on everything unmapped
// - The time-set staging/commit protocol
// - The read-coherency window for the six time registers
// - Status flag write-1-to-clear decode
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> decode --> rtc_regs (PeakRDL)
//               --> hwif --> mapping --> RTC core
//
//==============================================================================
// DECODE CONTRACT (GitHub #56 round_2 items 1 and 7)
//==============================================================================
// Exactly thirteen addresses are software visible: 0x000, 0x004, 0x008 and
// then 0x00C..0x030 on a 4-byte stride. EVERYTHING else in the 4 KB APB
// window - reserved slots inside the register file's own 6-bit space
// (0x034-0x03C) as much as anything above 0x03F - is dropped: the write is
// ignored, the read returns zero, and the access answers with PSLVERR.
//
// This closes two holes at once. The wrapper used to hand the register block
// `regblk_addr[5:0]` with no visibility check, so 0x864 aliased onto
// RTC_ALARM_SEC at 0x024 and could rewrite a live register through an address
// no map documents; and the generated block ties `cpuif_wr_err`/`readback_err`
// to zero, so even the genuinely reserved slots ack'd silently. The
// acknowledge for a dropped access is combinational on the held request -
// the same form the register block's own ack has - so a dropped access and a
// real one retire with identical adapter timing.
//
// The strobes below (time-register reads, the STATUS W1C) compare the SAME
// address bits the register block decodes and are qualified by `regblk_req`,
// which only asserts for a mapped address. That is round_2 item 7: the old
// range test `addr >= 0x00C && addr <= 0x020` fired on unimplemented offsets
// inside the range as well.
//
//==============================================================================
// TIME SET PROTOCOL (GitHub #56 H7, round_2 item 6, round_3 item 1)
//==============================================================================
//   1. Software sets RTC_CONFIG.time_set_mode. The counters stop and the six
//      time registers STOP mirroring the counter (hwif we is deasserted), so
//      they become staging registers.
//   2. Software writes RTC_SECONDS..RTC_YEAR in any order, at any speed. Each
//      write lands in its own register field. Nothing is sent to the counter
//      domain yet, so no field can be lost and no partial batch can be
//      loaded.
//   3. Software clears RTC_CONFIG.time_set_mode. That FALLING EDGE is the
//      commit: all six staged bytes cross to the counter domain as one
//      closed-loop cdc_4_phase_handshake transfer and load the counters on a
//      single edge (see rtc_core.sv crossing 2).
//   4. Until rtc_core reports the load is visible in its pclk shadow
//      (`time_commit_busy` low), the six registers keep presenting the STAGED
//      values, so a readback in that window shows the time software asked
//      for, never the pre-commit time. Reading busy low needs the timeout
//      bit to be read with it:
//        busy low, RTC_STATUS.commit_timeout CLEAR - the committed time has
//          LANDED in the counters and is visible in the shadow. That release
//          is driven by evidence of the load, not by the staged bytes
//          happening to match what the shadow already showed.
//        busy low, RTC_STATUS.commit_timeout SET - the commit's window
//          expired. It has NOT landed; it is still held and will land when
//          the counter clock returns. busy was released so the registers go
//          back to mirroring the counter, which is why they no longer show
//          the staged values.
//
//      One exception worth knowing: a presetn pulse while busy is set clears
//      the register file, so the six registers read their RESET DEFAULTS -
//      not the staged values - until busy clears and the mirror resumes with
//      the committed time. RTC_STATUS.time_valid reads 0 for that window and
//      is the signpost that what you are reading is not a time yet.
//
// The commit is a level's falling edge rather than a new "commit" register on
// purpose: it keeps the published register map unchanged.
//
//==============================================================================
// READING THE TIME: THE SECONDS READ IS THE SNAPSHOT POINT (GH#56 H4)
//==============================================================================
// rtc_core hands over a shadow that is always internally consistent, but a
// six-register read burst takes tens of pclk cycles and a tick can land in
// the middle of it - which is exactly the filed "seconds mismatch 0 vs 59"
// signature. The fix is one rule, with no window, no timer and no state to
// get stuck in:
//
//   RTC_SECONDS reads the LIVE shadow, and that read latches the other five
//   registers (plus pm_indicator and time_valid) at the same instant.
//
// So minutes/hours/day/month/year always report the time as of the last
// RTC_SECONDS read. Read the time as the burst SECONDS -> MINUTES -> HOURS
// -> DAY -> MONTH -> YEAR and every value in it belongs to one instant, no
// matter where the tick lands. Poll RTC_SECONDS alone and it tracks the
// clock, because it is never held. Read RTC_MINUTES without ever reading
// RTC_SECONDS and you get the last latch, which is the documented cost of
// having no hidden window.
//
// The alignment is exact, and it is worth stating why rather than trusting
// it. The bridge holds its request for TWO cycles but captures read data in
// the FIRST, so:
//   - the value returned for RTC_SECONDS is that field's storage during the
//     first request cycle, which the mirror loaded from the shadow one cycle
//     earlier;
//   - the latch strobe is that same first request cycle, edge-detected so
//     the second cycle cannot latch again;
//   - the five fields (and the two status bits) load from r_shd_d1_*, a
//     one-cycle-delayed copy of the shadow, so what they capture is the
//     shadow of that same earlier cycle.
// Both sides therefore come from ONE shadow cycle. A tick arriving during
// the bridge's second request cycle changes the live shadow and neither
// side.
//
//
// CHECK BY INSPECTION (these were assertions; properties belong in external
// formal bindings, not inside the module):
//   - Only a mapped address reaches the register block, and every mapped
//     address lives in the low 64 bytes, so the [5:0] slice into the regblock
//     cannot alias. Add a register above 0x03F and that stops being true.
//   - A dropped access asserts no internal strobe: every strobe is qualified
//     with regblk_req, which is gated off for an unmapped address.
//   - The RTC_SECONDS / RTC_YEAR / RTC_STATUS strobes compare the full 12-bit
//     address, so an address that merely shares the low six bits cannot fire
//     them.
//   - The snapshot latches exactly once per RTC_SECONDS read: the strobe is
//     edge-detected, so the bridge's second request cycle cannot latch again.
//   - The RTC_STATUS write decode is hand-written here and must keep matching
//     the generated block's own decode. Nothing in the RTL cross-checks that:
//     the guard is the DV suite's W1C tests (alarm, second_tick and
//     commit_timeout each cleared through a real APB write), which fail if a
//     regeneration moves the decode out from under this mirror.
//   - time_set_commit is one cycle wide, and the counter mirror never runs
//     while software is staging a time.
//
// Follows PIC/PIT pattern: separate generated registers from integration logic

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rtc_config_regs
    import rtc_regs_pkg::*;
(
    input wire clk,
    input wire rst_n,  // Active-low reset

    // Command/Response Interface (from apb4_slave)
    input  wire        cmd_valid,
    output wire        cmd_ready,
    input  wire        cmd_pwrite,
    input  wire [11:0] cmd_paddr,
    input  wire [31:0] cmd_pwdata,
    input  wire [3:0]  cmd_pstrb,

    output wire        rsp_valid,
    input  wire        rsp_ready,
    output wire [31:0] rsp_prdata,
    output wire        rsp_pslverr,

    // RTC Core Interface - Configuration
    output wire        cfg_rtc_enable,
    output wire        cfg_hour_mode_12,
    output wire        cfg_bcd_mode,
    output wire        cfg_clock_select,
    output wire        cfg_time_set_mode,
    output wire        cfg_valid,
    output wire        cfg_alarm_enable,
    output wire        cfg_alarm_int_enable,
    output wire        cfg_second_int_enable,

    // Time registers - staged values out, commit event out, busy in
    output wire [7:0]  time_seconds_out,
    output wire [7:0]  time_minutes_out,
    output wire [7:0]  time_hours_out,
    output wire [7:0]  time_day_out,
    output wire [7:0]  time_month_out,
    output wire [7:0]  time_year_out,
    output wire        time_set_commit,
    input  wire        time_commit_busy,

    // Time registers - coherent shadow in (from rtc_core, pclk domain)
    input  wire [7:0]  time_seconds_in,
    input  wire [7:0]  time_minutes_in,
    input  wire [7:0]  time_hours_in,
    input  wire [7:0]  time_day_in,
    input  wire [7:0]  time_month_in,
    input  wire [7:0]  time_year_in,

    // Alarm configuration
    output wire [7:0]  alarm_seconds,
    output wire [7:0]  alarm_minutes,
    output wire [7:0]  alarm_hours,
    output wire        alarm_sec_match_en,
    output wire        alarm_min_match_en,
    output wire        alarm_hour_match_en,

    // Status inputs (from rtc_core)
    input  wire        status_alarm_flag,
    input  wire        status_second_tick,
    input  wire        status_time_valid,
    input  wire        status_pm_indicator,
    input  wire        status_commit_timeout,

    // Status flag clears (one pclk cycle per W1C transaction)
    output wire        clear_alarm_flag,
    output wire        clear_second_tick,
    output wire        clear_commit_timeout
);

    //========================================================================
    // Local Parameters
    //========================================================================
    // The software-visible map. These MUST track rtc_regs.rdl; the guard is
    // the DV suite's W1C and decode tests (see CHECK BY INSPECTION above).

    localparam logic [11:0] ADDR_RTC_CONFIG     = 12'h000;
    localparam logic [11:0] ADDR_RTC_CONTROL    = 12'h004;
    localparam logic [11:0] ADDR_RTC_STATUS     = 12'h008;
    localparam logic [11:0] ADDR_RTC_SECONDS    = 12'h00C;
    localparam logic [11:0] ADDR_RTC_MINUTES    = 12'h010;
    localparam logic [11:0] ADDR_RTC_HOURS      = 12'h014;
    localparam logic [11:0] ADDR_RTC_DAY        = 12'h018;
    localparam logic [11:0] ADDR_RTC_MONTH      = 12'h01C;
    localparam logic [11:0] ADDR_RTC_YEAR       = 12'h020;
    localparam logic [11:0] ADDR_RTC_ALARM_SEC  = 12'h024;
    localparam logic [11:0] ADDR_RTC_ALARM_MIN  = 12'h028;
    localparam logic [11:0] ADDR_RTC_ALARM_HOUR = 12'h02C;
    localparam logic [11:0] ADDR_RTC_ALARM_MASK = 12'h030;


    //========================================================================
    // Internal Signals: adapter side
    //========================================================================

    logic                adapter_req;
    logic                adapter_req_is_wr;
    logic [11:0]         adapter_addr;
    logic [31:0]         adapter_wr_data;
    logic [31:0]         adapter_wr_biten;
    logic                adapter_req_stall_wr;
    logic                adapter_req_stall_rd;
    logic                adapter_rd_ack;
    logic                adapter_rd_err;
    logic [31:0]         adapter_rd_data;
    logic                adapter_wr_ack;
    logic                adapter_wr_err;

    //========================================================================
    // Internal Signals: register block side
    //========================================================================

    logic                regblk_req;
    logic                regblk_req_is_wr;
    logic [5:0]          regblk_addr;
    logic [31:0]         regblk_wr_data;
    logic [31:0]         regblk_wr_biten;
    logic                regblk_req_stall_wr;
    logic                regblk_req_stall_rd;
    logic                regblk_rd_ack;
    logic                regblk_rd_err;
    logic [31:0]         regblk_rd_data;
    logic                regblk_wr_ack;
    logic                regblk_wr_err;

    //========================================================================
    // Internal Signals: decode
    //========================================================================

    logic                w_addr_mapped;
    logic                w_drop;
    logic                w_drop_ack;

    //========================================================================
    // Internal Signals: time-set staging / commit
    //========================================================================

    logic                r_time_set_mode_d;
    logic                w_mirror_en;

    //========================================================================
    // Internal Signals: read coherency window
    //========================================================================

    logic                     w_seconds_rd_req;
    logic                     r_seconds_rd_d;
    logic                     w_seconds_latch;
    logic                     w_stage_hold;
    logic                     w_snapshot_load;
    logic                     w_staged_pm;
    logic [7:0]               r_shd_d1_minutes;
    logic [7:0]               r_shd_d1_hours;
    logic [7:0]               r_shd_d1_day;
    logic [7:0]               r_shd_d1_month;
    logic [7:0]               r_shd_d1_year;
    logic                     r_shd_d1_pm;
    logic                     r_shd_d1_valid;
    logic                     r_snap_pm;
    logic                     r_snap_time_valid;

    //========================================================================
    // Internal Signals: status write-1-to-clear
    //========================================================================

    logic                w_config_sw_wr;
    logic                r_cfg_valid;
    logic                w_status_sw_wr;
    logic                w_status_wr_event;
    logic                r_status_sw_wr_d;

    //========================================================================
    // PeakRDL Register Interface Structures
    //========================================================================

    rtc_regs__in_t  hwif_in;
    rtc_regs__out_t hwif_out;

    //========================================================================
    // Instantiate CMD/RSP to PeakRDL Adapter
    //========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        // CMD/RSP interface (external)
        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_pwrite         (cmd_pwrite),
        .cmd_paddr          (cmd_paddr),
        .cmd_pwdata         (cmd_pwdata),
        .cmd_pstrb          (cmd_pstrb),

        .rsp_valid          (rsp_valid),
        .rsp_ready          (rsp_ready),
        .rsp_prdata         (rsp_prdata),
        .rsp_pslverr        (rsp_pslverr),

        // PeakRDL passthrough interface (to the decode below)
        .regblk_req         (adapter_req),
        .regblk_req_is_wr   (adapter_req_is_wr),
        .regblk_addr        (adapter_addr),
        .regblk_wr_data     (adapter_wr_data),
        .regblk_wr_biten    (adapter_wr_biten),
        .regblk_req_stall_wr(adapter_req_stall_wr),
        .regblk_req_stall_rd(adapter_req_stall_rd),
        .regblk_rd_ack      (adapter_rd_ack),
        .regblk_rd_err      (adapter_rd_err),
        .regblk_rd_data     (adapter_rd_data),
        .regblk_wr_ack      (adapter_wr_ack),
        .regblk_wr_err      (adapter_wr_err)
    );

    //========================================================================
    // Address Decode
    //========================================================================
    // An equality against every mapped address, not a window test: an
    // in-window address that is not one of the thirteen is as invisible as one
    // above 0x03F, and answers the same way.

    always_comb begin
        case (adapter_addr)
            ADDR_RTC_CONFIG,
            ADDR_RTC_CONTROL,
            ADDR_RTC_STATUS,
            ADDR_RTC_SECONDS,
            ADDR_RTC_MINUTES,
            ADDR_RTC_HOURS,
            ADDR_RTC_DAY,
            ADDR_RTC_MONTH,
            ADDR_RTC_YEAR,
            ADDR_RTC_ALARM_SEC,
            ADDR_RTC_ALARM_MIN,
            ADDR_RTC_ALARM_HOUR,
            ADDR_RTC_ALARM_MASK: w_addr_mapped = 1'b1;
            default:             w_addr_mapped = 1'b0;
        endcase
    end

    assign w_drop     = !w_addr_mapped;
    assign w_drop_ack = adapter_req && w_drop;

    // Only a mapped address ever reaches the register block, so the [5:0]
    // slice below cannot alias: the upper six bits have already been proven
    // zero by the decode.
    assign regblk_req       = adapter_req && !w_drop;
    assign regblk_req_is_wr = adapter_req_is_wr;
    assign regblk_addr      = adapter_addr[5:0];
    assign regblk_wr_data   = adapter_wr_data;
    assign regblk_wr_biten  = adapter_wr_biten;

    // Response path: the register block's, or the local drop response. Every
    // drop is an error - unlike ioapic there is no "implemented but reserved"
    // selector class here.
    assign adapter_req_stall_wr = regblk_req_stall_wr;
    assign adapter_req_stall_rd = regblk_req_stall_rd;
    assign adapter_rd_ack       = regblk_rd_ack | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_err       = regblk_rd_err | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_data      = w_drop_ack ? 32'h0 : regblk_rd_data;
    assign adapter_wr_ack       = regblk_wr_ack | (w_drop_ack & adapter_req_is_wr);
    assign adapter_wr_err       = regblk_wr_err | (w_drop_ack & adapter_req_is_wr);

    //========================================================================
    // Time Set: commit on the falling edge of time_set_mode
    //========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_time_set_mode_d <= 1'b0;
        end else begin
            r_time_set_mode_d <= cfg_time_set_mode;
        end
    )

    assign time_set_commit = r_time_set_mode_d && !cfg_time_set_mode;

    //========================================================================
    // Seconds-Read Snapshot
    //========================================================================

    assign w_seconds_rd_req = regblk_req && !regblk_req_is_wr &&
                              (regblk_addr == ADDR_RTC_SECONDS[5:0]);

    // Edge-detected: the bridge holds its request for two cycles and this
    // must latch in the first of them, the one whose data the bridge
    // captures. Latching again in the second cycle would pair the seconds
    // value already captured with a shadow one cycle newer - the tear this
    // whole mechanism exists to prevent.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_seconds_rd_d <= 1'b0;
        end else begin
            r_seconds_rd_d <= w_seconds_rd_req;
        end
    )

    assign w_seconds_latch = w_seconds_rd_req && !r_seconds_rd_d;

    // One-cycle-delayed copy of the shadow. The register block loads its
    // fields one cycle behind hwif_in, so latching from this delayed copy is
    // what puts the five fields on the same shadow cycle as the seconds
    // value the bridge is capturing right now. Free-running: it is a delay
    // line, not a snapshot.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_shd_d1_minutes <= 8'h00;
            r_shd_d1_hours   <= 8'h00;
            r_shd_d1_day     <= 8'h01;
            r_shd_d1_month   <= 8'h01;
            r_shd_d1_year    <= 8'h00;
            r_shd_d1_pm      <= 1'b0;
            r_shd_d1_valid   <= 1'b0;
        end else begin
            r_shd_d1_minutes <= time_minutes_in;
            r_shd_d1_hours   <= time_hours_in;
            r_shd_d1_day     <= time_day_in;
            r_shd_d1_month   <= time_month_in;
            r_shd_d1_year    <= time_year_in;
            r_shd_d1_pm      <= status_pm_indicator;
            r_shd_d1_valid   <= status_time_valid;
        end
    )

    // Staging hold: while software is setting the time - and until the
    // commit is visible in the shadow - the six registers present the STAGED
    // values, so neither the seconds mirror nor the latch may run.
    //
    // `time_set_commit` is in that list for a reason that cost a debug cycle:
    // time_commit_busy cannot rise until the cycle AFTER the commit pulse, so
    // without this term there is exactly one cycle in which time_set_mode has
    // already fallen and busy has not yet risen - and the mirror wrote the
    // live shadow over all six staged values in it, so the handshake latched
    // the counter's time instead of the time software just wrote.
    assign w_stage_hold = cfg_time_set_mode || time_set_commit || time_commit_busy;

    // RTC_SECONDS mirrors the shadow every cycle (outside staging) - that is
    // what makes it live. The other five load only on the latch.
    assign w_mirror_en      = !w_stage_hold;
    assign w_snapshot_load  = w_seconds_latch && !w_stage_hold;

    //========================================================================
    // Held Status Bits (same snapshot as the five latched time registers)
    //========================================================================
    // pm_indicator and time_valid are read straight out of hwif_in by the
    // register block's readback mux, so they are latched HERE rather than by
    // a field write enable, from the same delayed shadow copy and on the same
    // strobe as the five - a status read taken anywhere in a burst then
    // belongs to the same instant as the burst.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_snap_pm         <= 1'b0;
            r_snap_time_valid <= 1'b0;
        end else if (w_snapshot_load) begin
            r_snap_pm         <= r_shd_d1_pm;
            r_snap_time_valid <= r_shd_d1_valid;
        end
    )

    // While the staged time is what software can read, the two status bits
    // have to describe THAT time, not the counter's. pm_indicator is bit 7 of
    // the staged hours byte; time_valid reads 0, because a staged time is
    // precisely one that is not yet in effect. Both revert to the latched
    // shadow values as soon as the commit is visible.
    assign w_staged_pm = cfg_hour_mode_12 && hwif_out.RTC_HOURS.hours.value[7];

    //========================================================================
    // Configuration Valid (GH#56 fifth review, cdc.md Rule 5)
    //========================================================================
    // The RTC keeps counting through a bus reset, but every configuration bit
    // it obeys lives in the register file and resets to zero there. Crossed
    // unconditionally, those reset defaults ARE a command: rtc_enable=0 stops
    // the clock and clock_select=0 flips the mux under a running domain, and
    // software never asked for either.
    //
    // So the configuration crosses together with this flag. Any write to
    // RTC_CONFIG sets it; presetn clears it; the counter domain applies the
    // crossed bundle only while it is set and otherwise holds its last
    // applied copy. After a bus reset the RTC therefore keeps running exactly
    // as it was, RTC_CONFIG reads its reset value, and software re-writes
    // RTC_CONFIG to re-establish (or change) the configuration.

    assign w_config_sw_wr = regblk_req && regblk_req_is_wr &&
                            (regblk_addr == ADDR_RTC_CONFIG[5:0]);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_cfg_valid <= 1'b0;
        end else if (w_config_sw_wr) begin
            r_cfg_valid <= 1'b1;
        end
    )

    assign cfg_valid = r_cfg_valid;

    //========================================================================
    // Status Flag Write-1-to-Clear Decode
    //========================================================================
    // Mirrors the register block's own decode for RTC_STATUS, narrowed to one
    // cycle per transaction (the adapter holds the request until it is acked,
    // and a two-cycle clear could undo a tick the core accepted in the first
    // of them). The clear reaches rtc_core in the SAME cycle the register
    // block commits the write, which is what removes the one-pclk readback
    // echo of round_2 item 7.

    assign w_status_sw_wr    = regblk_req && regblk_req_is_wr &&
                               (regblk_addr == ADDR_RTC_STATUS[5:0]);
    assign w_status_wr_event = w_status_sw_wr && !r_status_sw_wr_d;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_status_sw_wr_d <= 1'b0;
        end else begin
            r_status_sw_wr_d <= w_status_sw_wr;
        end
    )

    assign clear_alarm_flag     = w_status_wr_event && regblk_wr_data[0] && regblk_wr_biten[0];
    assign clear_second_tick    = w_status_wr_event && regblk_wr_data[1] && regblk_wr_biten[1];
    assign clear_commit_timeout = w_status_wr_event && regblk_wr_data[4] && regblk_wr_biten[4];

    //========================================================================
    // Hardware Interface Inputs (every member driven)
    //========================================================================

    // Seconds: live shadow, every cycle. The other five: the delayed shadow,
    // only when the seconds read says so.
    assign hwif_in.RTC_SECONDS.seconds.next = time_seconds_in;
    assign hwif_in.RTC_MINUTES.minutes.next = r_shd_d1_minutes;
    assign hwif_in.RTC_HOURS.hours.next     = r_shd_d1_hours;
    assign hwif_in.RTC_DAY.day.next         = r_shd_d1_day;
    assign hwif_in.RTC_MONTH.month.next     = r_shd_d1_month;
    assign hwif_in.RTC_YEAR.year.next       = r_shd_d1_year;

    assign hwif_in.RTC_SECONDS.seconds.we   = w_mirror_en;
    assign hwif_in.RTC_MINUTES.minutes.we   = w_snapshot_load;
    assign hwif_in.RTC_HOURS.hours.we       = w_snapshot_load;
    assign hwif_in.RTC_DAY.day.we           = w_snapshot_load;
    assign hwif_in.RTC_MONTH.month.we       = w_snapshot_load;
    assign hwif_in.RTC_YEAR.year.we         = w_snapshot_load;

    assign hwif_in.RTC_STATUS.alarm_flag.next     = status_alarm_flag;
    assign hwif_in.RTC_STATUS.second_tick.next    = status_second_tick;
    assign hwif_in.RTC_STATUS.commit_timeout.next = status_commit_timeout;
    assign hwif_in.RTC_STATUS.time_valid.next     = w_stage_hold ? 1'b0 : r_snap_time_valid;
    assign hwif_in.RTC_STATUS.pm_indicator.next   = w_stage_hold ? w_staged_pm : r_snap_pm;

    //========================================================================
    // PeakRDL Generated Register File
    //========================================================================

    // PeakRDL's regblock takes an ACTIVE-HIGH reset whatever the build
    // uses. Ask the macro whether reset is asserted rather than
    // inverting rst_n by hand: `~rst_n` is correct only while the
    // build is active-low, and under -DRESET_ACTIVE_HIGH it held the
    // whole register file in reset forever (RLB-012).
    rtc_regs u_rtc_regs (
        .clk                   (clk),
        .rst                   (`RST_ASSERTED(rst_n)),
        .s_cpuif_req           (regblk_req),
        .s_cpuif_req_is_wr     (regblk_req_is_wr),
        .s_cpuif_addr          (regblk_addr),
        .s_cpuif_wr_data       (regblk_wr_data),
        .s_cpuif_wr_biten      (regblk_wr_biten),
        .s_cpuif_req_stall_wr  (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd  (regblk_req_stall_rd),
        .s_cpuif_rd_ack        (regblk_rd_ack),
        .s_cpuif_rd_err        (regblk_rd_err),
        .s_cpuif_rd_data       (regblk_rd_data),
        .s_cpuif_wr_ack        (regblk_wr_ack),
        .s_cpuif_wr_err        (regblk_wr_err),
        .hwif_in               (hwif_in),
        .hwif_out              (hwif_out)
    );

    //========================================================================
    // Output Assignments to RTC Core
    //========================================================================

    // Configuration signals
    assign cfg_rtc_enable        = hwif_out.RTC_CONFIG.rtc_enable.value;
    assign cfg_hour_mode_12      = hwif_out.RTC_CONFIG.hour_mode_12.value;
    assign cfg_bcd_mode          = hwif_out.RTC_CONFIG.bcd_mode.value;
    assign cfg_clock_select      = hwif_out.RTC_CONFIG.clock_select.value;
    assign cfg_time_set_mode     = hwif_out.RTC_CONFIG.time_set_mode.value;

    // Control signals
    assign cfg_alarm_enable      = hwif_out.RTC_CONTROL.alarm_enable.value;
    assign cfg_alarm_int_enable  = hwif_out.RTC_CONTROL.alarm_int_enable.value;
    assign cfg_second_int_enable = hwif_out.RTC_CONTROL.second_int_enable.value;

    // Staged time values (only meaningful while the mirror is disabled)
    assign time_seconds_out = hwif_out.RTC_SECONDS.seconds.value;
    assign time_minutes_out = hwif_out.RTC_MINUTES.minutes.value;
    assign time_hours_out   = hwif_out.RTC_HOURS.hours.value;
    assign time_day_out     = hwif_out.RTC_DAY.day.value;
    assign time_month_out   = hwif_out.RTC_MONTH.month.value;
    assign time_year_out    = hwif_out.RTC_YEAR.year.value;

    // Alarm configuration
    assign alarm_seconds        = hwif_out.RTC_ALARM_SEC.alarm_seconds.value;
    assign alarm_minutes        = hwif_out.RTC_ALARM_MIN.alarm_minutes.value;
    assign alarm_hours          = hwif_out.RTC_ALARM_HOUR.alarm_hours.value;
    assign alarm_sec_match_en   = hwif_out.RTC_ALARM_MASK.sec_match_en.value;
    assign alarm_min_match_en   = hwif_out.RTC_ALARM_MASK.min_match_en.value;
    assign alarm_hour_match_en  = hwif_out.RTC_ALARM_MASK.hour_match_en.value;

endmodule
