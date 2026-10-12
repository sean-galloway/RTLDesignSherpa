// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: delta_axis_flat_2x4_strb_amba5_th
// Purpose: Test harness -- pure wiring. Flattens the generated crossbar's
//          unpacked-array ports ([NUM_MASTERS] / [NUM_SLAVES]) into one
//          named port set per interface (s0_axis_*, m3_axis_*, ...) so the
//          RDS-DV AXIS5 BFMs bind to each one by prefix.
//
// DUT: projects/components/fabric-gen-ip/delta/rtl_test/delta_axis_flat_2x4_strb_amba5.sv
//      (module delta_axis_flat_2x4, generated with
//       --masters 2 --slaves 4 --data-width 32 --strb-width 4 --amba5).
//      If that generator command changes, this port list must follow it.
//
// Subsystem: delta (dv)
//
// Author: sean galloway
// Created: 2026-10-12

`timescale 1ns / 1ps

module delta_axis_flat_2x4_strb_amba5_th #(
    parameter int DATA_WIDTH  = 32,
    parameter int STRB_WIDTH  = 4,
    parameter int DEST_WIDTH  = 2,
    parameter int ID_WIDTH    = 1,
    parameter int USER_WIDTH  = 1,
    parameter int NUM_MASTERS = 2,
    parameter int NUM_SLAVES  = 4,
    parameter int TDATACHK_W  = DATA_WIDTH / 8,
    parameter int TSTRBCHK_W  = (STRB_WIDTH + 7) / 8,
    parameter int TIDCHK_W    = (ID_WIDTH + 7) / 8,
    parameter int TDESTCHK_W  = (DEST_WIDTH + 7) / 8,
    parameter int TUSERCHK_W  = (USER_WIDTH + 7) / 8
) (
    input  logic aclk,
    input  logic aresetn,
    input  logic [DATA_WIDTH-1:0]   s0_axis_tdata,
    input  logic [STRB_WIDTH-1:0]   s0_axis_tstrb,
    input  logic                    s0_axis_tlast,
    input  logic [ID_WIDTH-1:0]     s0_axis_tid,
    input  logic [DEST_WIDTH-1:0]   s0_axis_tdest,
    input  logic [USER_WIDTH-1:0]   s0_axis_tuser,
    input  logic                    s0_axis_twakeup,
    input  logic [TDATACHK_W-1:0]   s0_axis_tdatachk,
    input  logic [TSTRBCHK_W-1:0]   s0_axis_tstrbchk,
    input  logic                    s0_axis_tlastchk,
    input  logic [TIDCHK_W-1:0]     s0_axis_tidchk,
    input  logic [TDESTCHK_W-1:0]   s0_axis_tdestchk,
    input  logic [TUSERCHK_W-1:0]   s0_axis_tuserchk,
    input  logic                    s0_axis_tvalid,
    input  logic                    s0_axis_tvalidchk,
    input  logic                    s0_axis_twakeupchk,
    output logic                    s0_axis_tready,
    output logic                    s0_axis_treadychk,
    output logic                    s0_parity_error,
    input  logic [DATA_WIDTH-1:0]   s1_axis_tdata,
    input  logic [STRB_WIDTH-1:0]   s1_axis_tstrb,
    input  logic                    s1_axis_tlast,
    input  logic [ID_WIDTH-1:0]     s1_axis_tid,
    input  logic [DEST_WIDTH-1:0]   s1_axis_tdest,
    input  logic [USER_WIDTH-1:0]   s1_axis_tuser,
    input  logic                    s1_axis_twakeup,
    input  logic [TDATACHK_W-1:0]   s1_axis_tdatachk,
    input  logic [TSTRBCHK_W-1:0]   s1_axis_tstrbchk,
    input  logic                    s1_axis_tlastchk,
    input  logic [TIDCHK_W-1:0]     s1_axis_tidchk,
    input  logic [TDESTCHK_W-1:0]   s1_axis_tdestchk,
    input  logic [TUSERCHK_W-1:0]   s1_axis_tuserchk,
    input  logic                    s1_axis_tvalid,
    input  logic                    s1_axis_tvalidchk,
    input  logic                    s1_axis_twakeupchk,
    output logic                    s1_axis_tready,
    output logic                    s1_axis_treadychk,
    output logic                    s1_parity_error,
    output logic [DATA_WIDTH-1:0]   m0_axis_tdata,
    output logic [STRB_WIDTH-1:0]   m0_axis_tstrb,
    output logic                    m0_axis_tlast,
    output logic [ID_WIDTH-1:0]     m0_axis_tid,
    output logic [DEST_WIDTH-1:0]   m0_axis_tdest,
    output logic [USER_WIDTH-1:0]   m0_axis_tuser,
    output logic                    m0_axis_twakeup,
    output logic [TDATACHK_W-1:0]   m0_axis_tdatachk,
    output logic [TSTRBCHK_W-1:0]   m0_axis_tstrbchk,
    output logic                    m0_axis_tlastchk,
    output logic [TIDCHK_W-1:0]     m0_axis_tidchk,
    output logic [TDESTCHK_W-1:0]   m0_axis_tdestchk,
    output logic [TUSERCHK_W-1:0]   m0_axis_tuserchk,
    output logic                    m0_axis_tvalid,
    output logic                    m0_axis_tvalidchk,
    output logic                    m0_axis_twakeupchk,
    input  logic                    m0_axis_tready,
    input  logic                    m0_axis_treadychk,
    output logic                    m0_parity_error,
    output logic [DATA_WIDTH-1:0]   m1_axis_tdata,
    output logic [STRB_WIDTH-1:0]   m1_axis_tstrb,
    output logic                    m1_axis_tlast,
    output logic [ID_WIDTH-1:0]     m1_axis_tid,
    output logic [DEST_WIDTH-1:0]   m1_axis_tdest,
    output logic [USER_WIDTH-1:0]   m1_axis_tuser,
    output logic                    m1_axis_twakeup,
    output logic [TDATACHK_W-1:0]   m1_axis_tdatachk,
    output logic [TSTRBCHK_W-1:0]   m1_axis_tstrbchk,
    output logic                    m1_axis_tlastchk,
    output logic [TIDCHK_W-1:0]     m1_axis_tidchk,
    output logic [TDESTCHK_W-1:0]   m1_axis_tdestchk,
    output logic [TUSERCHK_W-1:0]   m1_axis_tuserchk,
    output logic                    m1_axis_tvalid,
    output logic                    m1_axis_tvalidchk,
    output logic                    m1_axis_twakeupchk,
    input  logic                    m1_axis_tready,
    input  logic                    m1_axis_treadychk,
    output logic                    m1_parity_error,
    output logic [DATA_WIDTH-1:0]   m2_axis_tdata,
    output logic [STRB_WIDTH-1:0]   m2_axis_tstrb,
    output logic                    m2_axis_tlast,
    output logic [ID_WIDTH-1:0]     m2_axis_tid,
    output logic [DEST_WIDTH-1:0]   m2_axis_tdest,
    output logic [USER_WIDTH-1:0]   m2_axis_tuser,
    output logic                    m2_axis_twakeup,
    output logic [TDATACHK_W-1:0]   m2_axis_tdatachk,
    output logic [TSTRBCHK_W-1:0]   m2_axis_tstrbchk,
    output logic                    m2_axis_tlastchk,
    output logic [TIDCHK_W-1:0]     m2_axis_tidchk,
    output logic [TDESTCHK_W-1:0]   m2_axis_tdestchk,
    output logic [TUSERCHK_W-1:0]   m2_axis_tuserchk,
    output logic                    m2_axis_tvalid,
    output logic                    m2_axis_tvalidchk,
    output logic                    m2_axis_twakeupchk,
    input  logic                    m2_axis_tready,
    input  logic                    m2_axis_treadychk,
    output logic                    m2_parity_error,
    output logic [DATA_WIDTH-1:0]   m3_axis_tdata,
    output logic [STRB_WIDTH-1:0]   m3_axis_tstrb,
    output logic                    m3_axis_tlast,
    output logic [ID_WIDTH-1:0]     m3_axis_tid,
    output logic [DEST_WIDTH-1:0]   m3_axis_tdest,
    output logic [USER_WIDTH-1:0]   m3_axis_tuser,
    output logic                    m3_axis_twakeup,
    output logic [TDATACHK_W-1:0]   m3_axis_tdatachk,
    output logic [TSTRBCHK_W-1:0]   m3_axis_tstrbchk,
    output logic                    m3_axis_tlastchk,
    output logic [TIDCHK_W-1:0]     m3_axis_tidchk,
    output logic [TDESTCHK_W-1:0]   m3_axis_tdestchk,
    output logic [TUSERCHK_W-1:0]   m3_axis_tuserchk,
    output logic                    m3_axis_tvalid,
    output logic                    m3_axis_tvalidchk,
    output logic                    m3_axis_twakeupchk,
    input  logic                    m3_axis_tready,
    input  logic                    m3_axis_treadychk,
    output logic                    m3_parity_error
);

    logic [DATA_WIDTH-1:0]   w_s_tdata [NUM_MASTERS];
    logic [DATA_WIDTH-1:0]   w_m_tdata [NUM_SLAVES];
    logic [STRB_WIDTH-1:0]   w_s_tstrb [NUM_MASTERS];
    logic [STRB_WIDTH-1:0]   w_m_tstrb [NUM_SLAVES];
    logic                    w_s_tlast [NUM_MASTERS];
    logic                    w_m_tlast [NUM_SLAVES];
    logic [ID_WIDTH-1:0]     w_s_tid [NUM_MASTERS];
    logic [ID_WIDTH-1:0]     w_m_tid [NUM_SLAVES];
    logic [DEST_WIDTH-1:0]   w_s_tdest [NUM_MASTERS];
    logic [DEST_WIDTH-1:0]   w_m_tdest [NUM_SLAVES];
    logic [USER_WIDTH-1:0]   w_s_tuser [NUM_MASTERS];
    logic [USER_WIDTH-1:0]   w_m_tuser [NUM_SLAVES];
    logic                    w_s_twakeup [NUM_MASTERS];
    logic                    w_m_twakeup [NUM_SLAVES];
    logic [TDATACHK_W-1:0]   w_s_tdatachk [NUM_MASTERS];
    logic [TDATACHK_W-1:0]   w_m_tdatachk [NUM_SLAVES];
    logic [TSTRBCHK_W-1:0]   w_s_tstrbchk [NUM_MASTERS];
    logic [TSTRBCHK_W-1:0]   w_m_tstrbchk [NUM_SLAVES];
    logic                    w_s_tlastchk [NUM_MASTERS];
    logic                    w_m_tlastchk [NUM_SLAVES];
    logic [TIDCHK_W-1:0]     w_s_tidchk [NUM_MASTERS];
    logic [TIDCHK_W-1:0]     w_m_tidchk [NUM_SLAVES];
    logic [TDESTCHK_W-1:0]   w_s_tdestchk [NUM_MASTERS];
    logic [TDESTCHK_W-1:0]   w_m_tdestchk [NUM_SLAVES];
    logic [TUSERCHK_W-1:0]   w_s_tuserchk [NUM_MASTERS];
    logic [TUSERCHK_W-1:0]   w_m_tuserchk [NUM_SLAVES];
    logic                    w_s_tvalid [NUM_MASTERS];
    logic                    w_m_tvalid [NUM_SLAVES];
    logic                    w_s_tvalidchk [NUM_MASTERS];
    logic                    w_m_tvalidchk [NUM_SLAVES];
    logic                    w_s_twakeupchk [NUM_MASTERS];
    logic                    w_m_twakeupchk [NUM_SLAVES];
    logic                    w_s_tready [NUM_MASTERS];
    logic                    w_m_tready [NUM_SLAVES];
    logic                    w_s_treadychk [NUM_MASTERS];
    logic                    w_m_treadychk [NUM_SLAVES];
    logic w_s_parity_error [NUM_MASTERS];
    logic w_m_parity_error [NUM_SLAVES];

    assign w_s_tdata[0] = s0_axis_tdata;
    assign w_s_tstrb[0] = s0_axis_tstrb;
    assign w_s_tlast[0] = s0_axis_tlast;
    assign w_s_tid[0] = s0_axis_tid;
    assign w_s_tdest[0] = s0_axis_tdest;
    assign w_s_tuser[0] = s0_axis_tuser;
    assign w_s_twakeup[0] = s0_axis_twakeup;
    assign w_s_tdatachk[0] = s0_axis_tdatachk;
    assign w_s_tstrbchk[0] = s0_axis_tstrbchk;
    assign w_s_tlastchk[0] = s0_axis_tlastchk;
    assign w_s_tidchk[0] = s0_axis_tidchk;
    assign w_s_tdestchk[0] = s0_axis_tdestchk;
    assign w_s_tuserchk[0] = s0_axis_tuserchk;
    assign w_s_tvalid[0] = s0_axis_tvalid;
    assign w_s_tvalidchk[0] = s0_axis_tvalidchk;
    assign w_s_twakeupchk[0] = s0_axis_twakeupchk;
    assign s0_axis_tready = w_s_tready[0];
    assign s0_axis_treadychk = w_s_treadychk[0];
    assign s0_parity_error = w_s_parity_error[0];
    assign w_s_tdata[1] = s1_axis_tdata;
    assign w_s_tstrb[1] = s1_axis_tstrb;
    assign w_s_tlast[1] = s1_axis_tlast;
    assign w_s_tid[1] = s1_axis_tid;
    assign w_s_tdest[1] = s1_axis_tdest;
    assign w_s_tuser[1] = s1_axis_tuser;
    assign w_s_twakeup[1] = s1_axis_twakeup;
    assign w_s_tdatachk[1] = s1_axis_tdatachk;
    assign w_s_tstrbchk[1] = s1_axis_tstrbchk;
    assign w_s_tlastchk[1] = s1_axis_tlastchk;
    assign w_s_tidchk[1] = s1_axis_tidchk;
    assign w_s_tdestchk[1] = s1_axis_tdestchk;
    assign w_s_tuserchk[1] = s1_axis_tuserchk;
    assign w_s_tvalid[1] = s1_axis_tvalid;
    assign w_s_tvalidchk[1] = s1_axis_tvalidchk;
    assign w_s_twakeupchk[1] = s1_axis_twakeupchk;
    assign s1_axis_tready = w_s_tready[1];
    assign s1_axis_treadychk = w_s_treadychk[1];
    assign s1_parity_error = w_s_parity_error[1];
    assign m0_axis_tdata = w_m_tdata[0];
    assign m0_axis_tstrb = w_m_tstrb[0];
    assign m0_axis_tlast = w_m_tlast[0];
    assign m0_axis_tid = w_m_tid[0];
    assign m0_axis_tdest = w_m_tdest[0];
    assign m0_axis_tuser = w_m_tuser[0];
    assign m0_axis_twakeup = w_m_twakeup[0];
    assign m0_axis_tdatachk = w_m_tdatachk[0];
    assign m0_axis_tstrbchk = w_m_tstrbchk[0];
    assign m0_axis_tlastchk = w_m_tlastchk[0];
    assign m0_axis_tidchk = w_m_tidchk[0];
    assign m0_axis_tdestchk = w_m_tdestchk[0];
    assign m0_axis_tuserchk = w_m_tuserchk[0];
    assign m0_axis_tvalid = w_m_tvalid[0];
    assign m0_axis_tvalidchk = w_m_tvalidchk[0];
    assign m0_axis_twakeupchk = w_m_twakeupchk[0];
    assign w_m_tready[0] = m0_axis_tready;
    assign w_m_treadychk[0] = m0_axis_treadychk;
    assign m0_parity_error = w_m_parity_error[0];
    assign m1_axis_tdata = w_m_tdata[1];
    assign m1_axis_tstrb = w_m_tstrb[1];
    assign m1_axis_tlast = w_m_tlast[1];
    assign m1_axis_tid = w_m_tid[1];
    assign m1_axis_tdest = w_m_tdest[1];
    assign m1_axis_tuser = w_m_tuser[1];
    assign m1_axis_twakeup = w_m_twakeup[1];
    assign m1_axis_tdatachk = w_m_tdatachk[1];
    assign m1_axis_tstrbchk = w_m_tstrbchk[1];
    assign m1_axis_tlastchk = w_m_tlastchk[1];
    assign m1_axis_tidchk = w_m_tidchk[1];
    assign m1_axis_tdestchk = w_m_tdestchk[1];
    assign m1_axis_tuserchk = w_m_tuserchk[1];
    assign m1_axis_tvalid = w_m_tvalid[1];
    assign m1_axis_tvalidchk = w_m_tvalidchk[1];
    assign m1_axis_twakeupchk = w_m_twakeupchk[1];
    assign w_m_tready[1] = m1_axis_tready;
    assign w_m_treadychk[1] = m1_axis_treadychk;
    assign m1_parity_error = w_m_parity_error[1];
    assign m2_axis_tdata = w_m_tdata[2];
    assign m2_axis_tstrb = w_m_tstrb[2];
    assign m2_axis_tlast = w_m_tlast[2];
    assign m2_axis_tid = w_m_tid[2];
    assign m2_axis_tdest = w_m_tdest[2];
    assign m2_axis_tuser = w_m_tuser[2];
    assign m2_axis_twakeup = w_m_twakeup[2];
    assign m2_axis_tdatachk = w_m_tdatachk[2];
    assign m2_axis_tstrbchk = w_m_tstrbchk[2];
    assign m2_axis_tlastchk = w_m_tlastchk[2];
    assign m2_axis_tidchk = w_m_tidchk[2];
    assign m2_axis_tdestchk = w_m_tdestchk[2];
    assign m2_axis_tuserchk = w_m_tuserchk[2];
    assign m2_axis_tvalid = w_m_tvalid[2];
    assign m2_axis_tvalidchk = w_m_tvalidchk[2];
    assign m2_axis_twakeupchk = w_m_twakeupchk[2];
    assign w_m_tready[2] = m2_axis_tready;
    assign w_m_treadychk[2] = m2_axis_treadychk;
    assign m2_parity_error = w_m_parity_error[2];
    assign m3_axis_tdata = w_m_tdata[3];
    assign m3_axis_tstrb = w_m_tstrb[3];
    assign m3_axis_tlast = w_m_tlast[3];
    assign m3_axis_tid = w_m_tid[3];
    assign m3_axis_tdest = w_m_tdest[3];
    assign m3_axis_tuser = w_m_tuser[3];
    assign m3_axis_twakeup = w_m_twakeup[3];
    assign m3_axis_tdatachk = w_m_tdatachk[3];
    assign m3_axis_tstrbchk = w_m_tstrbchk[3];
    assign m3_axis_tlastchk = w_m_tlastchk[3];
    assign m3_axis_tidchk = w_m_tidchk[3];
    assign m3_axis_tdestchk = w_m_tdestchk[3];
    assign m3_axis_tuserchk = w_m_tuserchk[3];
    assign m3_axis_tvalid = w_m_tvalid[3];
    assign m3_axis_tvalidchk = w_m_tvalidchk[3];
    assign m3_axis_twakeupchk = w_m_twakeupchk[3];
    assign w_m_tready[3] = m3_axis_tready;
    assign w_m_treadychk[3] = m3_axis_treadychk;
    assign m3_parity_error = w_m_parity_error[3];

    delta_axis_flat_2x4 #(
        .DATA_WIDTH(DATA_WIDTH), .DEST_WIDTH(DEST_WIDTH), .ID_WIDTH(ID_WIDTH),
        .USER_WIDTH(USER_WIDTH), .STRB_WIDTH(STRB_WIDTH),
        .NUM_MASTERS(NUM_MASTERS), .NUM_SLAVES(NUM_SLAVES)
    ) u_dut (
        .aclk(aclk), .aresetn(aresetn),
        .s_axis_tdata(w_s_tdata), .m_axis_tdata(w_m_tdata),
        .s_axis_tstrb(w_s_tstrb), .m_axis_tstrb(w_m_tstrb),
        .s_axis_tlast(w_s_tlast), .m_axis_tlast(w_m_tlast),
        .s_axis_tid(w_s_tid), .m_axis_tid(w_m_tid),
        .s_axis_tdest(w_s_tdest), .m_axis_tdest(w_m_tdest),
        .s_axis_tuser(w_s_tuser), .m_axis_tuser(w_m_tuser),
        .s_axis_twakeup(w_s_twakeup), .m_axis_twakeup(w_m_twakeup),
        .s_axis_tdatachk(w_s_tdatachk), .m_axis_tdatachk(w_m_tdatachk),
        .s_axis_tstrbchk(w_s_tstrbchk), .m_axis_tstrbchk(w_m_tstrbchk),
        .s_axis_tlastchk(w_s_tlastchk), .m_axis_tlastchk(w_m_tlastchk),
        .s_axis_tidchk(w_s_tidchk), .m_axis_tidchk(w_m_tidchk),
        .s_axis_tdestchk(w_s_tdestchk), .m_axis_tdestchk(w_m_tdestchk),
        .s_axis_tuserchk(w_s_tuserchk), .m_axis_tuserchk(w_m_tuserchk),
        .s_axis_tvalid(w_s_tvalid), .m_axis_tvalid(w_m_tvalid),
        .s_axis_tvalidchk(w_s_tvalidchk), .m_axis_tvalidchk(w_m_tvalidchk),
        .s_axis_twakeupchk(w_s_twakeupchk), .m_axis_twakeupchk(w_m_twakeupchk),
        .s_axis_tready(w_s_tready), .m_axis_tready(w_m_tready),
        .s_axis_treadychk(w_s_treadychk), .m_axis_treadychk(w_m_treadychk),
        .s_parity_error(w_s_parity_error), .m_parity_error(w_m_parity_error)
    );

endmodule : delta_axis_flat_2x4_strb_amba5_th
