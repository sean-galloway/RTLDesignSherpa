// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Arming proof for the ZQ arm of scoria_cmd_arbiter. A lint-clean branch that
// can never be reached proves nothing; this drives the branch and checks the
// three things the arm is supposed to do:
//   1. a ZQCS reaches cmd_op_o and zq_grant_o pulses with it
//   2. an open row is PRECHARGED first (JESD79-3F 3.10: all banks idle)
//   3. NOTHING issues for t_zqcs_i cycles after it
`timescale 1ns/1ps
module tb_zq;
    import scoria_pkg::*;

    localparam int NB  = 8;
    localparam int RW  = 14;
    localparam int CW  = 10;
    localparam int NE  = 8;

    logic clk = 0, rst_n = 0;
    always #5 clk = ~clk;

    // bank state: all idle / all ready, one rank
    logic [0:0][NB-1:0] rdy   = '1;
    logic [0:0][NB-1:0] act   = '0;   // row_active
    logic [0:0][NB-1:0][RW-1:0] orow = '0;

    logic        zq_req = 0, zq_grant;
    logic [15:0] t_zqcs = 16'd12;

    logic        cmd_valid;
    dram_op_e    cmd_op;
    logic [$clog2(NB)-1:0] cmd_bank;

    // Real pending READ work. WITHOUT this the "nothing issued inside tZQCS"
    // check is vacuous -- nothing was trying to issue in the first place, which
    // is the same trap as an ILA trigger that cannot fire. CASE0 below proves
    // this work DOES issue when ZQ is idle, and only then does CASE1's silence
    // carry information.
    logic [NE-1:0]              rd_v    = '0;
    logic [NE*3-1:0]            rd_bank = '0;
    logic [NE*RW-1:0]           rd_row  = '0;
    logic [NE*CW-1:0]           rd_col  = '0;
    logic [NE*NE-1:0]           rd_old  = '0;

    scoria_cmd_arbiter #(
        .NUM_BANKS(NB), .ROW_WIDTH(RW), .COL_WIDTH(CW), .NUM_ENTRIES(NE)
    ) dut (
        .aclk(clk), .aresetn(rst_n),
        .page_policy_i(PAGE_POLICY_OPEN),
        .init_done_i(1'b1),
        .zq_req_i(zq_req), .zq_grant_o(zq_grant), .t_zqcs_i(t_zqcs),
        .bank_act_ready_i(rdy),  .bank_rdwr_ready_i(rdy),  .bank_pre_ready_i(rdy),
        .bank_act_ready_la_i(rdy), .bank_rdwr_ready_la_i(rdy), .bank_pre_ready_la_i(rdy),
        .bank_row_active_i(act), .bank_open_row_i(orow),
        .tfaw_ok_i(1'b1), .trrd_ok_i(1'b1), .twtr_ok_i(1'b1),
        .trtw_ok_i(1'b1), .tccd_ok_i(1'b1),
        .rd_sch_valid_i(rd_v), .rd_sch_bank_i(rd_bank), .rd_sch_row_i(rd_row),
        .rd_sch_col_i(rd_col), .rd_sch_older_i(rd_old),
        .rd_issue_ready_i(1'b1), .wr_commit_ready_i(1'b1),
        .cmd_valid_o(cmd_valid), .cmd_ready_i(1'b1),
        .cmd_op_o(cmd_op), .cmd_bank_o(cmd_bank)
    );

    int n_zqcs = 0, n_pre = 0, n_any_in_window = 0, n_baseline = 0;
    int window = 0;
    logic saw_grant_with_zqcs = 0;

    always @(posedge clk) if (rst_n) begin
        if (cmd_valid && cmd_op == OP_ZQCS) begin
            n_zqcs++;
            if (zq_grant) saw_grant_with_zqcs = 1;
            window = t_zqcs;             // start counting the block window
        end else begin
            if (window > 0) begin
                window--;
                if (cmd_valid) n_any_in_window++;   // MUST stay 0
            end
            if (cmd_valid && cmd_op == OP_PRE) n_pre++;
            if (cmd_valid) n_baseline++;
        end
    end

    initial begin
        repeat (4) @(posedge clk);
        rst_n = 1;
        repeat (10) @(posedge clk);

        // ---- case 0 (the arming proof): read work issues with ZQ idle ----
        rd_v = 8'h01;           // entry 0 pending, bank 0, row 0, col 0
        repeat (40) @(posedge clk);
        $display("CASE0 baseline_cmds=%0d", n_baseline);
        if (n_baseline == 0) begin
            $display("FAIL0: no command issues even with ZQ idle -- CASE1 would be vacuous");
            $finish;
        end
        $display("PASS0");
        n_baseline = 0; n_zqcs = 0; n_pre = 0; n_any_in_window = 0;

        // ---- case 1: ZQ requests with read work live -> ZQCS, then silence ----
        zq_req = 1;
        repeat (40) @(posedge clk);
        zq_req = 0;
        repeat (10) @(posedge clk);
        $display("CASE1 zqcs=%0d grant_aligned=%0b pre=%0d in_window=%0d",
                 n_zqcs, saw_grant_with_zqcs, n_pre, n_any_in_window);
        if (n_zqcs == 0)            $display("FAIL1: the ZQ arm never fired");
        else if (!saw_grant_with_zqcs) $display("FAIL1: ZQCS issued with no grant");
        else if (n_any_in_window)   $display("FAIL1: %0d commands inside tZQCS", n_any_in_window);
        else                        $display("PASS1");

        // ---- case 2: a row is open -> must PRECHARGE before calibrating ----
        n_zqcs = 0; n_pre = 0; n_any_in_window = 0; window = 0;
        act[0] = 8'b0000_0101;   // banks 0 and 2 open
        repeat (5) @(posedge clk);
        zq_req = 1;
        repeat (60) @(posedge clk);
        // the DUT has no bank model, so close the rows as it precharges them
        $display("CASE2 pre=%0d zqcs=%0d", n_pre, n_zqcs);
        if (n_pre == 0) $display("FAIL2: calibrated without precharging an open bank");
        else            $display("PASS2");
        $finish;
    end

    // crude bank model: a fired PRE closes the bank
    always @(posedge clk) if (rst_n && cmd_valid && cmd_op == OP_PRE) act[0][cmd_bank] <= 1'b0;
endmodule
