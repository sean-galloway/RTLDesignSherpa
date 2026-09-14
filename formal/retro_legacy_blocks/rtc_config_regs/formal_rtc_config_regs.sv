// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for rtc_config_regs -- RLB-010's W1C strobe contract.
//
// WHAT IS PROVED (at the port boundary):
//   P1  clear_alarm_flag is never asserted two cycles running
//   P2  clear_second_tick likewise
//   P3  clear_commit_timeout likewise
// Together these are the contract the module header states as "Status flag
// clears (one pclk cycle per W1C transaction)". It matters because
// peakrdl_to_cmdrsp holds regblk_req for the accept cycle PLUS one
// (peakrdl_to_cmdrsp.sv:205), so a strobe derived from regblk_req is presented
// TWICE unless edge-detected -- the same two-cycle hold that produced defects
// in rapids (kick) and pm_acpi (cfg_sys_reset) the same week. The edge detect
// is w_status_wr_event = w_status_sw_wr && !r_status_sw_wr_d; remove it and
// these asserts fail (mutation-checked).
//
// WHAT IS NOT PROVED, AND WHY -- the seconds-read latch alignment.
// RLB-010 names it alongside the W1C strobe. It is NOT provable here: the
// contract is about w_seconds_latch, an internal signal, and internal
// visibility is unavailable for this block in this toolchain. Four routes were
// tried and all fail:
//   1. dut.<sig> with the DUT read as flat Verilog and the harness as SV:
//      "ERROR: Failed to resolve identifier \dut.w_status_wr_event".
//   2. the same with hierarchy/proc/flatten before prep: identical error.
//   3. the same with harness and DUT sv2v'd into ONE file: identical error.
//   4. bind: yosys silently drops the checker ("Removing unused module
//      $abstract\rtc_config_regs_fv") and the proof passes with zero property
//      cells -- caught by mutation, not by reading the log.
// Reading the RTL as SystemVerilog instead (which is how formal/apbx_xbar gets
// internal visibility) is closed off because yosys cannot parse the generated
// package: "rtc_regs_pkg.sv:10: ERROR: Only PACKED supported at this time".
// So that contract stays CHECK BY INSPECTION in the module header, which
// no-assertions-in-rtl.md explicitly sanctions as the accepted state.

module formal_rtc_config_regs (
    input logic clk,
    input logic rst_n
);

    (* anyseq *) reg         cmd_valid;
    (* anyseq *) reg         cmd_pwrite;
    (* anyseq *) reg [11:0]  cmd_paddr;
    (* anyseq *) reg [31:0]  cmd_pwdata;
    (* anyseq *) reg [3:0]   cmd_pstrb;
    (* anyseq *) reg         rsp_ready;
    (* anyseq *) reg         time_commit_busy;
    (* anyseq *) reg [7:0]   time_seconds_in, time_minutes_in, time_hours_in;
    (* anyseq *) reg [7:0]   time_day_in, time_month_in, time_year_in;
    (* anyseq *) reg         status_alarm_flag, status_second_tick;
    (* anyseq *) reg         status_time_valid, status_pm_indicator;
    (* anyseq *) reg         status_commit_timeout;

    wire        cmd_ready, rsp_valid, rsp_pslverr;
    wire [31:0] rsp_prdata;
    wire        cfg_rtc_enable, cfg_hour_mode_12, cfg_bcd_mode, cfg_clock_select;
    wire        cfg_time_set_mode, cfg_valid, cfg_alarm_enable;
    wire        cfg_alarm_int_enable, cfg_second_int_enable;
    wire [7:0]  time_seconds_out, time_minutes_out, time_hours_out;
    wire [7:0]  time_day_out, time_month_out, time_year_out;
    wire        time_set_commit;
    wire [7:0]  alarm_seconds, alarm_minutes, alarm_hours;
    wire        alarm_sec_match_en, alarm_min_match_en, alarm_hour_match_en;
    wire        clear_alarm_flag, clear_second_tick, clear_commit_timeout;

    rtc_config_regs dut (
        .clk (clk), .rst_n (rst_n),
        .cmd_valid (cmd_valid), .cmd_ready (cmd_ready), .cmd_pwrite (cmd_pwrite),
        .cmd_paddr (cmd_paddr), .cmd_pwdata (cmd_pwdata), .cmd_pstrb (cmd_pstrb),
        .rsp_valid (rsp_valid), .rsp_ready (rsp_ready),
        .rsp_prdata (rsp_prdata), .rsp_pslverr (rsp_pslverr),
        .cfg_rtc_enable (cfg_rtc_enable), .cfg_hour_mode_12 (cfg_hour_mode_12),
        .cfg_bcd_mode (cfg_bcd_mode), .cfg_clock_select (cfg_clock_select),
        .cfg_time_set_mode (cfg_time_set_mode), .cfg_valid (cfg_valid),
        .cfg_alarm_enable (cfg_alarm_enable),
        .cfg_alarm_int_enable (cfg_alarm_int_enable),
        .cfg_second_int_enable (cfg_second_int_enable),
        .time_seconds_out (time_seconds_out), .time_minutes_out (time_minutes_out),
        .time_hours_out (time_hours_out), .time_day_out (time_day_out),
        .time_month_out (time_month_out), .time_year_out (time_year_out),
        .time_set_commit (time_set_commit), .time_commit_busy (time_commit_busy),
        .time_seconds_in (time_seconds_in), .time_minutes_in (time_minutes_in),
        .time_hours_in (time_hours_in), .time_day_in (time_day_in),
        .time_month_in (time_month_in), .time_year_in (time_year_in),
        .alarm_seconds (alarm_seconds), .alarm_minutes (alarm_minutes),
        .alarm_hours (alarm_hours), .alarm_sec_match_en (alarm_sec_match_en),
        .alarm_min_match_en (alarm_min_match_en),
        .alarm_hour_match_en (alarm_hour_match_en),
        .status_alarm_flag (status_alarm_flag),
        .status_second_tick (status_second_tick),
        .status_time_valid (status_time_valid),
        .status_pm_indicator (status_pm_indicator),
        .status_commit_timeout (status_commit_timeout),
        .clear_alarm_flag (clear_alarm_flag),
        .clear_second_tick (clear_second_tick),
        .clear_commit_timeout (clear_commit_timeout)
    );

    reg f_past_valid = 1'b0;
    always @(posedge clk) f_past_valid <= 1'b1;

    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid) assume (rst_n);

    // A cmd/rsp master holds a request stable until it is accepted. Without
    // this the solver retracts requests mid-transaction and the proof debugs
    // the stimulus instead of the DUT.
    always @(posedge clk) begin
        if (rst_n && f_past_valid && $past(rst_n)) begin
            if ($past(cmd_valid) && !$past(cmd_ready)) begin
                assume (cmd_valid);
                assume (cmd_pwrite == $past(cmd_pwrite));
                assume (cmd_paddr  == $past(cmd_paddr));
                assume (cmd_pwdata == $past(cmd_pwdata));
                assume (cmd_pstrb  == $past(cmd_pstrb));
            end
        end
    end

    // P1-P3: one pclk cycle per W1C transaction.
    always @(posedge clk) begin
        if (rst_n && f_past_valid && $past(rst_n)) begin
            if ($past(clear_alarm_flag))
                ap_clear_alarm_single:   assert (!clear_alarm_flag);
            if ($past(clear_second_tick))
                ap_clear_tick_single:    assert (!clear_second_tick);
            if ($past(clear_commit_timeout))
                ap_clear_timeout_single: assert (!clear_commit_timeout);
        end
    end

    // Reachability. An assert whose antecedent is never reached proves
    // nothing, so each strobe must be COVERABLE.
    always @(posedge clk) begin
        if (rst_n && f_past_valid) begin
            cp_clear_alarm:   cover (clear_alarm_flag);
            cp_clear_tick:    cover (clear_second_tick);
            cp_clear_timeout: cover (clear_commit_timeout);
        end
    end

endmodule
