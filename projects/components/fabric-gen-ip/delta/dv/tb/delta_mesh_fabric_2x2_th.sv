// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: delta_mesh_fabric_2x2_th
// Purpose: Test harness -- pure wiring. Flattens the generated 2x2x1 fabric's
//          boundary-local unpacked-array ports ([NUM_BOUNDARY]) into one named
//          port set per boundary cell (b0_..b3_) so the RDS-DV AXIS BFMs bind
//          to each one by prefix.
//
// DUT: delta_mesh_fabric_2x2x1, generated at run time by the test via
//      delta_generator.py --topology mesh --cells-x 2 --cells-y 2 --cells-z 1
//      --user-width 64 (sources passed in by the cocotb wrapper; nothing from
//      the checked-in rtl/ dir is bound here).
//      Boundary index -> coordinate map (x-major, then y, then z; see the
//      fabric's header comment -- with Z=1 both z faces are boundary so every
//      cell of a 2x2x1 mesh qualifies):
//        b0 = (0,0,0)  b1 = (1,0,0)  b2 = (0,1,0)  b3 = (1,1,0)
//      If that generator command changes, this port list must follow it.
//
// Credit sidebands: s_local_credit is tied to '1 (credits always available,
// matching the Task 2/3 cell tie-off); m_local_credit is exposed per boundary.
// b<i>_err are the per-cell malformed-dst drop counters (Task 5 o_err pass-
// through); suites may ignore them but the fabric port must exist.
//
// Subsystem: delta (dv)
//
// Author: sean galloway
// Created: 2026-10-14

`timescale 1ns / 1ps

module delta_mesh_fabric_2x2_th #(
    parameter int DATA_WIDTH   = 64,
    parameter int USER_WIDTH   = 64,
    parameter int COORD_W      = 1,
    parameter int NUM_VC       = 2,
    parameter int NUM_BOUNDARY = 4
) (
    input  logic aclk,
    input  logic aresetn,

    input  logic [DATA_WIDTH-1:0] b0_s_axis_tdata,
    input  logic                  b0_s_axis_tvalid,
    output logic                  b0_s_axis_tready,
    input  logic                  b0_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b0_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b0_m_axis_tdata,
    output logic                  b0_m_axis_tvalid,
    input  logic                  b0_m_axis_tready,
    output logic                  b0_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b0_m_axis_tuser,
    output logic [NUM_VC-1:0]     b0_m_credit,

    input  logic [DATA_WIDTH-1:0] b1_s_axis_tdata,
    input  logic                  b1_s_axis_tvalid,
    output logic                  b1_s_axis_tready,
    input  logic                  b1_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b1_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b1_m_axis_tdata,
    output logic                  b1_m_axis_tvalid,
    input  logic                  b1_m_axis_tready,
    output logic                  b1_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b1_m_axis_tuser,
    output logic [NUM_VC-1:0]     b1_m_credit,

    input  logic [DATA_WIDTH-1:0] b2_s_axis_tdata,
    input  logic                  b2_s_axis_tvalid,
    output logic                  b2_s_axis_tready,
    input  logic                  b2_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b2_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b2_m_axis_tdata,
    output logic                  b2_m_axis_tvalid,
    input  logic                  b2_m_axis_tready,
    output logic                  b2_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b2_m_axis_tuser,
    output logic [NUM_VC-1:0]     b2_m_credit,

    input  logic [DATA_WIDTH-1:0] b3_s_axis_tdata,
    input  logic                  b3_s_axis_tvalid,
    output logic                  b3_s_axis_tready,
    input  logic                  b3_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b3_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b3_m_axis_tdata,
    output logic                  b3_m_axis_tvalid,
    input  logic                  b3_m_axis_tready,
    output logic                  b3_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b3_m_axis_tuser,
    output logic [NUM_VC-1:0]     b3_m_credit,

    output logic [31:0]           b0_err,
    output logic [31:0]           b1_err,
    output logic [31:0]           b2_err,
    output logic [31:0]           b3_err
);

    // Fabric boundary index map (pinned by the generator, x-major then y
    // then z): 0 = (0,0,0), 1 = (1,0,0), 2 = (0,1,0), 3 = (1,1,0).

    logic [DATA_WIDTH-1:0] w_s_local_tdata  [NUM_BOUNDARY];
    logic                  w_s_local_tvalid [NUM_BOUNDARY];
    logic                  w_s_local_tready [NUM_BOUNDARY];
    logic                  w_s_local_tlast  [NUM_BOUNDARY];
    logic [USER_WIDTH-1:0] w_s_local_tuser  [NUM_BOUNDARY];
    logic [DATA_WIDTH-1:0] w_m_local_tdata  [NUM_BOUNDARY];
    logic                  w_m_local_tvalid [NUM_BOUNDARY];
    logic                  w_m_local_tready [NUM_BOUNDARY];
    logic                  w_m_local_tlast  [NUM_BOUNDARY];
    logic [USER_WIDTH-1:0] w_m_local_tuser  [NUM_BOUNDARY];
    logic [NUM_VC-1:0]     w_s_local_credit [NUM_BOUNDARY];
    logic [NUM_VC-1:0]     w_m_local_credit [NUM_BOUNDARY];

    assign w_s_local_tdata[0]  = b0_s_axis_tdata;
    assign w_s_local_tvalid[0] = b0_s_axis_tvalid;
    assign b0_s_axis_tready    = w_s_local_tready[0];
    assign w_s_local_tlast[0]  = b0_s_axis_tlast;
    assign w_s_local_tuser[0]  = b0_s_axis_tuser;
    assign b0_m_axis_tdata     = w_m_local_tdata[0];
    assign b0_m_axis_tvalid    = w_m_local_tvalid[0];
    assign w_m_local_tready[0] = b0_m_axis_tready;
    assign b0_m_axis_tlast     = w_m_local_tlast[0];
    assign b0_m_axis_tuser     = w_m_local_tuser[0];
    assign b0_m_credit         = w_m_local_credit[0];

    assign w_s_local_tdata[1]  = b1_s_axis_tdata;
    assign w_s_local_tvalid[1] = b1_s_axis_tvalid;
    assign b1_s_axis_tready    = w_s_local_tready[1];
    assign w_s_local_tlast[1]  = b1_s_axis_tlast;
    assign w_s_local_tuser[1]  = b1_s_axis_tuser;
    assign b1_m_axis_tdata     = w_m_local_tdata[1];
    assign b1_m_axis_tvalid    = w_m_local_tvalid[1];
    assign w_m_local_tready[1] = b1_m_axis_tready;
    assign b1_m_axis_tlast     = w_m_local_tlast[1];
    assign b1_m_axis_tuser     = w_m_local_tuser[1];
    assign b1_m_credit         = w_m_local_credit[1];

    assign w_s_local_tdata[2]  = b2_s_axis_tdata;
    assign w_s_local_tvalid[2] = b2_s_axis_tvalid;
    assign b2_s_axis_tready    = w_s_local_tready[2];
    assign w_s_local_tlast[2]  = b2_s_axis_tlast;
    assign w_s_local_tuser[2]  = b2_s_axis_tuser;
    assign b2_m_axis_tdata     = w_m_local_tdata[2];
    assign b2_m_axis_tvalid    = w_m_local_tvalid[2];
    assign w_m_local_tready[2] = b2_m_axis_tready;
    assign b2_m_axis_tlast     = w_m_local_tlast[2];
    assign b2_m_axis_tuser     = w_m_local_tuser[2];
    assign b2_m_credit         = w_m_local_credit[2];

    assign w_s_local_tdata[3]  = b3_s_axis_tdata;
    assign w_s_local_tvalid[3] = b3_s_axis_tvalid;
    assign b3_s_axis_tready    = w_s_local_tready[3];
    assign w_s_local_tlast[3]  = b3_s_axis_tlast;
    assign w_s_local_tuser[3]  = b3_s_axis_tuser;
    assign b3_m_axis_tdata     = w_m_local_tdata[3];
    assign b3_m_axis_tvalid    = w_m_local_tvalid[3];
    assign w_m_local_tready[3] = b3_m_axis_tready;
    assign b3_m_axis_tlast     = w_m_local_tlast[3];
    assign b3_m_axis_tuser     = w_m_local_tuser[3];
    assign b3_m_credit         = w_m_local_credit[3];

    // Task 2/3 credit tie-off: credits always available; the real credit
    // protocol lands in Task 4.
    for (genvar i = 0; i < NUM_BOUNDARY; i++) begin : gen_credit_tieoff
        assign w_s_local_credit[i] = {NUM_VC{1'b1}};
    end

    // Per-cell malformed-dst drop counters (Task 5): exposed per boundary
    // cell; the suites may ignore them but the fabric port must exist.
    logic [31:0] w_o_err [NUM_BOUNDARY];

    assign b0_err = w_o_err[0];
    assign b1_err = w_o_err[1];
    assign b2_err = w_o_err[2];
    assign b3_err = w_o_err[3];

    delta_mesh_fabric_2x2x1 #(
        .DATA_WIDTH(DATA_WIDTH),
        .USER_WIDTH(USER_WIDTH),
        .COORD_W(COORD_W),
        .NUM_VC(NUM_VC)
    ) u_dut (
        .aclk(aclk),
        .aresetn(aresetn),
        .s_local_tdata(w_s_local_tdata),
        .s_local_tvalid(w_s_local_tvalid),
        .s_local_tready(w_s_local_tready),
        .s_local_tlast(w_s_local_tlast),
        .s_local_tuser(w_s_local_tuser),
        .m_local_tdata(w_m_local_tdata),
        .m_local_tvalid(w_m_local_tvalid),
        .m_local_tready(w_m_local_tready),
        .m_local_tlast(w_m_local_tlast),
        .m_local_tuser(w_m_local_tuser),
        .s_local_credit(w_s_local_credit),
        .m_local_credit(w_m_local_credit),
        .o_err(w_o_err)
    );

endmodule : delta_mesh_fabric_2x2_th
