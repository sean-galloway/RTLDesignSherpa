// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: delta_mesh_fabric_4x1x1_th
// Purpose: Test harness -- pure wiring. Flattens the generated 4x1x1
//          fabric's boundary-local unpacked-array ports ([NUM_BOUNDARY])
//          into one named port set per boundary cell (b0_..b3_) so the
//          RDS-DV AXIS BFMs bind to each one by prefix.
//
// DUT: delta_mesh_fabric_4x1x1, generated at run time by the test via
//      delta_generator.py --topology mesh --cells-x 4 --cells-y 1
//      --cells-z 1 --torus-x --user-width 64 (sources passed in by the
//      cocotb wrapper; nothing from the checked-in rtl/ dir is bound here).
//      Boundary index -> coordinate map (x-major, then y, then z; see the
//      fabric's header comment -- with Y=1 and Z=1 every cell is on a
//      boundary face):
//        b0 = (0,0,0)  b1 = (1,0,0)  b2 = (2,0,0)  b3 = (3,0,0)
//
// Credit sidebands: s_local_credit is tied to '1; m_local_credit is
// exposed per boundary. b<i>_err / b<i>_mode_acks / b<i>_bulk_starved
// are the per-cell delta_mesh_cell pass-throughs. Suites may ignore them
// but the fabric ports must exist.
//
// Subsystem: delta (dv)
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

module delta_mesh_fabric_4x1x1_th #(
    parameter int DATA_WIDTH   = 64,
    parameter int USER_WIDTH   = 64,
    parameter int COORD_W      = 2,
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
    output logic [31:0]           b3_err,
    output logic [31:0]           b0_mode_acks,
    output logic [31:0]           b1_mode_acks,
    output logic [31:0]           b2_mode_acks,
    output logic [31:0]           b3_mode_acks,
    output logic [8:0]            b0_bulk_starved,
    output logic [8:0]            b1_bulk_starved,
    output logic [8:0]            b2_bulk_starved,
    output logic [8:0]            b3_bulk_starved,
    output logic                  b0_dft_active,
    output logic                  b1_dft_active,
    output logic                  b2_dft_active,
    output logic                  b3_dft_active
);

    // Fabric boundary index map (pinned by the generator, x-major then y
    // then z): b(x) = (x,0,0); all 4 cells of a 4x1x1 are boundary.

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

    for (genvar i = 0; i < NUM_BOUNDARY; i++) begin : gen_credit_tieoff
        assign w_s_local_credit[i] = {NUM_VC{1'b1}};
    end

    logic [31:0] w_o_err [NUM_BOUNDARY];
    assign b0_err = w_o_err[0];
    assign b1_err = w_o_err[1];
    assign b2_err = w_o_err[2];
    assign b3_err = w_o_err[3];

    logic [31:0] w_o_mode_acks [NUM_BOUNDARY];
    assign b0_mode_acks = w_o_mode_acks[0];
    assign b1_mode_acks = w_o_mode_acks[1];
    assign b2_mode_acks = w_o_mode_acks[2];
    assign b3_mode_acks = w_o_mode_acks[3];

    logic [8:0] w_o_bulk_starved [NUM_BOUNDARY];
    assign b0_bulk_starved = w_o_bulk_starved[0];
    assign b1_bulk_starved = w_o_bulk_starved[1];
    assign b2_bulk_starved = w_o_bulk_starved[2];
    assign b3_bulk_starved = w_o_bulk_starved[3];

    // Per-cell DFT-active flags (Task 10): exposed per boundary cell.
    logic w_o_dft_active [NUM_BOUNDARY];

    assign b0_dft_active = w_o_dft_active[0];
    assign b1_dft_active = w_o_dft_active[1];
    assign b2_dft_active = w_o_dft_active[2];
    assign b3_dft_active = w_o_dft_active[3];

    delta_mesh_fabric_4x1x1 #(
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
        .o_err(w_o_err),
        .o_mode_acks(w_o_mode_acks),
        .o_bulk_starved(w_o_bulk_starved),
        .o_dft_active(w_o_dft_active)
    );

endmodule : delta_mesh_fabric_4x1x1_th
