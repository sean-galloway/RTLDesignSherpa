// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: delta_mesh_fabric_4x4_th
// Purpose: Test harness -- pure wiring. Flattens the generated 4x4x1
//          fabric's boundary-local unpacked-array ports ([NUM_BOUNDARY])
//          into one named port set per boundary cell (b0_..b15_) so the
//          RDS-DV AXIS BFMs bind to each one by prefix.
//
// DUT: delta_mesh_fabric_4x4x1, generated at run time by the test via
//      delta_generator.py --topology mesh --cells-x 4 --cells-y 4
//      --cells-z 1 --user-width 64 (sources passed in by the cocotb
//      wrapper; nothing from the checked-in rtl/ dir is bound here).
//      Boundary index -> coordinate map (x-major, then y, then z; see the
//      fabric's header comment -- with Z=1 both z faces are boundary so
//      every cell of a 4x4x1 mesh qualifies):
//        b0  = (0,0,0)  b1  = (1,0,0)  b2  = (2,0,0)  b3  = (3,0,0)
//        b4  = (0,1,0)  b5  = (1,1,0)  b6  = (2,1,0)  b7  = (3,1,0)
//        b8  = (0,2,0)  b9  = (1,2,0)  b10 = (2,2,0)  b11 = (3,2,0)
//        b12 = (0,3,0)  b13 = (1,3,0)  b14 = (2,3,0)  b15 = (3,3,0)
//      If that generator command changes, this port list must follow it.
//
// Task 6c: the tile suite's harness -- a 4x4x1 fabric is ONE tile (2x2x1
// tetrads), the mode-10 K4-of-tetrads unit: the P_DIA2 diagonal-tetrad
// links wire (1,1,0)<->(2,2,0) and (1,2,0)<->(2,1,0); every boundary
// local below can source and sink tile-wide traffic.
//
// Credit sidebands: s_local_credit is tied to '1 (credits always
// available, matching the Task 2/3 cell tie-off); m_local_credit is
// exposed per boundary. b<i>_err are the per-cell malformed-dst drop
// counters (Task 5 o_err pass-through); b<i>_mode_acks are the per-cell
// mode-switch ack tallies (Task 6 o_mode_acks pass-through -- the tile
// suite's barrier expects 16); b<i>_bulk_starved are the per-cell bulk-
// reservation-due flag vectors (Task 7 o_bulk_starved[8:0] pass-through
// over the 9-port pin, Task 6c). Suites may ignore them but the fabric
// ports must exist.
//
// Subsystem: delta (dv)
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

module delta_mesh_fabric_4x4_th #(
    parameter int DATA_WIDTH   = 64,
    parameter int USER_WIDTH   = 64,
    parameter int COORD_W      = 2,
    parameter int NUM_VC       = 2,
    parameter int NUM_BOUNDARY = 16
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

    input  logic [DATA_WIDTH-1:0] b4_s_axis_tdata,
    input  logic                  b4_s_axis_tvalid,
    output logic                  b4_s_axis_tready,
    input  logic                  b4_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b4_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b4_m_axis_tdata,
    output logic                  b4_m_axis_tvalid,
    input  logic                  b4_m_axis_tready,
    output logic                  b4_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b4_m_axis_tuser,
    output logic [NUM_VC-1:0]     b4_m_credit,

    input  logic [DATA_WIDTH-1:0] b5_s_axis_tdata,
    input  logic                  b5_s_axis_tvalid,
    output logic                  b5_s_axis_tready,
    input  logic                  b5_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b5_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b5_m_axis_tdata,
    output logic                  b5_m_axis_tvalid,
    input  logic                  b5_m_axis_tready,
    output logic                  b5_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b5_m_axis_tuser,
    output logic [NUM_VC-1:0]     b5_m_credit,

    input  logic [DATA_WIDTH-1:0] b6_s_axis_tdata,
    input  logic                  b6_s_axis_tvalid,
    output logic                  b6_s_axis_tready,
    input  logic                  b6_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b6_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b6_m_axis_tdata,
    output logic                  b6_m_axis_tvalid,
    input  logic                  b6_m_axis_tready,
    output logic                  b6_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b6_m_axis_tuser,
    output logic [NUM_VC-1:0]     b6_m_credit,

    input  logic [DATA_WIDTH-1:0] b7_s_axis_tdata,
    input  logic                  b7_s_axis_tvalid,
    output logic                  b7_s_axis_tready,
    input  logic                  b7_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b7_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b7_m_axis_tdata,
    output logic                  b7_m_axis_tvalid,
    input  logic                  b7_m_axis_tready,
    output logic                  b7_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b7_m_axis_tuser,
    output logic [NUM_VC-1:0]     b7_m_credit,

    input  logic [DATA_WIDTH-1:0] b8_s_axis_tdata,
    input  logic                  b8_s_axis_tvalid,
    output logic                  b8_s_axis_tready,
    input  logic                  b8_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b8_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b8_m_axis_tdata,
    output logic                  b8_m_axis_tvalid,
    input  logic                  b8_m_axis_tready,
    output logic                  b8_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b8_m_axis_tuser,
    output logic [NUM_VC-1:0]     b8_m_credit,

    input  logic [DATA_WIDTH-1:0] b9_s_axis_tdata,
    input  logic                  b9_s_axis_tvalid,
    output logic                  b9_s_axis_tready,
    input  logic                  b9_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b9_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b9_m_axis_tdata,
    output logic                  b9_m_axis_tvalid,
    input  logic                  b9_m_axis_tready,
    output logic                  b9_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b9_m_axis_tuser,
    output logic [NUM_VC-1:0]     b9_m_credit,

    input  logic [DATA_WIDTH-1:0] b10_s_axis_tdata,
    input  logic                  b10_s_axis_tvalid,
    output logic                  b10_s_axis_tready,
    input  logic                  b10_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b10_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b10_m_axis_tdata,
    output logic                  b10_m_axis_tvalid,
    input  logic                  b10_m_axis_tready,
    output logic                  b10_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b10_m_axis_tuser,
    output logic [NUM_VC-1:0]     b10_m_credit,

    input  logic [DATA_WIDTH-1:0] b11_s_axis_tdata,
    input  logic                  b11_s_axis_tvalid,
    output logic                  b11_s_axis_tready,
    input  logic                  b11_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b11_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b11_m_axis_tdata,
    output logic                  b11_m_axis_tvalid,
    input  logic                  b11_m_axis_tready,
    output logic                  b11_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b11_m_axis_tuser,
    output logic [NUM_VC-1:0]     b11_m_credit,

    input  logic [DATA_WIDTH-1:0] b12_s_axis_tdata,
    input  logic                  b12_s_axis_tvalid,
    output logic                  b12_s_axis_tready,
    input  logic                  b12_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b12_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b12_m_axis_tdata,
    output logic                  b12_m_axis_tvalid,
    input  logic                  b12_m_axis_tready,
    output logic                  b12_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b12_m_axis_tuser,
    output logic [NUM_VC-1:0]     b12_m_credit,

    input  logic [DATA_WIDTH-1:0] b13_s_axis_tdata,
    input  logic                  b13_s_axis_tvalid,
    output logic                  b13_s_axis_tready,
    input  logic                  b13_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b13_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b13_m_axis_tdata,
    output logic                  b13_m_axis_tvalid,
    input  logic                  b13_m_axis_tready,
    output logic                  b13_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b13_m_axis_tuser,
    output logic [NUM_VC-1:0]     b13_m_credit,

    input  logic [DATA_WIDTH-1:0] b14_s_axis_tdata,
    input  logic                  b14_s_axis_tvalid,
    output logic                  b14_s_axis_tready,
    input  logic                  b14_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b14_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b14_m_axis_tdata,
    output logic                  b14_m_axis_tvalid,
    input  logic                  b14_m_axis_tready,
    output logic                  b14_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b14_m_axis_tuser,
    output logic [NUM_VC-1:0]     b14_m_credit,

    input  logic [DATA_WIDTH-1:0] b15_s_axis_tdata,
    input  logic                  b15_s_axis_tvalid,
    output logic                  b15_s_axis_tready,
    input  logic                  b15_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] b15_s_axis_tuser,
    output logic [DATA_WIDTH-1:0] b15_m_axis_tdata,
    output logic                  b15_m_axis_tvalid,
    input  logic                  b15_m_axis_tready,
    output logic                  b15_m_axis_tlast,
    output logic [USER_WIDTH-1:0] b15_m_axis_tuser,
    output logic [NUM_VC-1:0]     b15_m_credit,

    output logic [31:0]           b0_err,
    output logic [31:0]           b1_err,
    output logic [31:0]           b2_err,
    output logic [31:0]           b3_err,
    output logic [31:0]           b4_err,
    output logic [31:0]           b5_err,
    output logic [31:0]           b6_err,
    output logic [31:0]           b7_err,
    output logic [31:0]           b8_err,
    output logic [31:0]           b9_err,
    output logic [31:0]           b10_err,
    output logic [31:0]           b11_err,
    output logic [31:0]           b12_err,
    output logic [31:0]           b13_err,
    output logic [31:0]           b14_err,
    output logic [31:0]           b15_err,
    output logic [31:0]           b0_mode_acks,
    output logic [31:0]           b1_mode_acks,
    output logic [31:0]           b2_mode_acks,
    output logic [31:0]           b3_mode_acks,
    output logic [31:0]           b4_mode_acks,
    output logic [31:0]           b5_mode_acks,
    output logic [31:0]           b6_mode_acks,
    output logic [31:0]           b7_mode_acks,
    output logic [31:0]           b8_mode_acks,
    output logic [31:0]           b9_mode_acks,
    output logic [31:0]           b10_mode_acks,
    output logic [31:0]           b11_mode_acks,
    output logic [31:0]           b12_mode_acks,
    output logic [31:0]           b13_mode_acks,
    output logic [31:0]           b14_mode_acks,
    output logic [31:0]           b15_mode_acks,
    output logic [8:0]            b0_bulk_starved,
    output logic [8:0]            b1_bulk_starved,
    output logic [8:0]            b2_bulk_starved,
    output logic [8:0]            b3_bulk_starved,
    output logic [8:0]            b4_bulk_starved,
    output logic [8:0]            b5_bulk_starved,
    output logic [8:0]            b6_bulk_starved,
    output logic [8:0]            b7_bulk_starved,
    output logic [8:0]            b8_bulk_starved,
    output logic [8:0]            b9_bulk_starved,
    output logic [8:0]            b10_bulk_starved,
    output logic [8:0]            b11_bulk_starved,
    output logic [8:0]            b12_bulk_starved,
    output logic [8:0]            b13_bulk_starved,
    output logic [8:0]            b14_bulk_starved,
    output logic [8:0]            b15_bulk_starved,
    output logic                  b0_dft_active,
    output logic                  b1_dft_active,
    output logic                  b2_dft_active,
    output logic                  b3_dft_active,
    output logic                  b4_dft_active,
    output logic                  b5_dft_active,
    output logic                  b6_dft_active,
    output logic                  b7_dft_active,
    output logic                  b8_dft_active,
    output logic                  b9_dft_active,
    output logic                  b10_dft_active,
    output logic                  b11_dft_active,
    output logic                  b12_dft_active,
    output logic                  b13_dft_active,
    output logic                  b14_dft_active,
    output logic                  b15_dft_active
);

    // Fabric boundary index map (pinned by the generator, x-major then y
    // then z): b(y*4+x) = (x,y,0); all 16 cells of a 4x4x1 are boundary
    // (Z == 1 puts every cell on both z faces).

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

    assign w_s_local_tdata[4]  = b4_s_axis_tdata;
    assign w_s_local_tvalid[4] = b4_s_axis_tvalid;
    assign b4_s_axis_tready    = w_s_local_tready[4];
    assign w_s_local_tlast[4]  = b4_s_axis_tlast;
    assign w_s_local_tuser[4]  = b4_s_axis_tuser;
    assign b4_m_axis_tdata     = w_m_local_tdata[4];
    assign b4_m_axis_tvalid    = w_m_local_tvalid[4];
    assign w_m_local_tready[4] = b4_m_axis_tready;
    assign b4_m_axis_tlast     = w_m_local_tlast[4];
    assign b4_m_axis_tuser     = w_m_local_tuser[4];
    assign b4_m_credit         = w_m_local_credit[4];

    assign w_s_local_tdata[5]  = b5_s_axis_tdata;
    assign w_s_local_tvalid[5] = b5_s_axis_tvalid;
    assign b5_s_axis_tready    = w_s_local_tready[5];
    assign w_s_local_tlast[5]  = b5_s_axis_tlast;
    assign w_s_local_tuser[5]  = b5_s_axis_tuser;
    assign b5_m_axis_tdata     = w_m_local_tdata[5];
    assign b5_m_axis_tvalid    = w_m_local_tvalid[5];
    assign w_m_local_tready[5] = b5_m_axis_tready;
    assign b5_m_axis_tlast     = w_m_local_tlast[5];
    assign b5_m_axis_tuser     = w_m_local_tuser[5];
    assign b5_m_credit         = w_m_local_credit[5];

    assign w_s_local_tdata[6]  = b6_s_axis_tdata;
    assign w_s_local_tvalid[6] = b6_s_axis_tvalid;
    assign b6_s_axis_tready    = w_s_local_tready[6];
    assign w_s_local_tlast[6]  = b6_s_axis_tlast;
    assign w_s_local_tuser[6]  = b6_s_axis_tuser;
    assign b6_m_axis_tdata     = w_m_local_tdata[6];
    assign b6_m_axis_tvalid    = w_m_local_tvalid[6];
    assign w_m_local_tready[6] = b6_m_axis_tready;
    assign b6_m_axis_tlast     = w_m_local_tlast[6];
    assign b6_m_axis_tuser     = w_m_local_tuser[6];
    assign b6_m_credit         = w_m_local_credit[6];

    assign w_s_local_tdata[7]  = b7_s_axis_tdata;
    assign w_s_local_tvalid[7] = b7_s_axis_tvalid;
    assign b7_s_axis_tready    = w_s_local_tready[7];
    assign w_s_local_tlast[7]  = b7_s_axis_tlast;
    assign w_s_local_tuser[7]  = b7_s_axis_tuser;
    assign b7_m_axis_tdata     = w_m_local_tdata[7];
    assign b7_m_axis_tvalid    = w_m_local_tvalid[7];
    assign w_m_local_tready[7] = b7_m_axis_tready;
    assign b7_m_axis_tlast     = w_m_local_tlast[7];
    assign b7_m_axis_tuser     = w_m_local_tuser[7];
    assign b7_m_credit         = w_m_local_credit[7];

    assign w_s_local_tdata[8]  = b8_s_axis_tdata;
    assign w_s_local_tvalid[8] = b8_s_axis_tvalid;
    assign b8_s_axis_tready    = w_s_local_tready[8];
    assign w_s_local_tlast[8]  = b8_s_axis_tlast;
    assign w_s_local_tuser[8]  = b8_s_axis_tuser;
    assign b8_m_axis_tdata     = w_m_local_tdata[8];
    assign b8_m_axis_tvalid    = w_m_local_tvalid[8];
    assign w_m_local_tready[8] = b8_m_axis_tready;
    assign b8_m_axis_tlast     = w_m_local_tlast[8];
    assign b8_m_axis_tuser     = w_m_local_tuser[8];
    assign b8_m_credit         = w_m_local_credit[8];

    assign w_s_local_tdata[9]  = b9_s_axis_tdata;
    assign w_s_local_tvalid[9] = b9_s_axis_tvalid;
    assign b9_s_axis_tready    = w_s_local_tready[9];
    assign w_s_local_tlast[9]  = b9_s_axis_tlast;
    assign w_s_local_tuser[9]  = b9_s_axis_tuser;
    assign b9_m_axis_tdata     = w_m_local_tdata[9];
    assign b9_m_axis_tvalid    = w_m_local_tvalid[9];
    assign w_m_local_tready[9] = b9_m_axis_tready;
    assign b9_m_axis_tlast     = w_m_local_tlast[9];
    assign b9_m_axis_tuser     = w_m_local_tuser[9];
    assign b9_m_credit         = w_m_local_credit[9];

    assign w_s_local_tdata[10]  = b10_s_axis_tdata;
    assign w_s_local_tvalid[10] = b10_s_axis_tvalid;
    assign b10_s_axis_tready    = w_s_local_tready[10];
    assign w_s_local_tlast[10]  = b10_s_axis_tlast;
    assign w_s_local_tuser[10]  = b10_s_axis_tuser;
    assign b10_m_axis_tdata     = w_m_local_tdata[10];
    assign b10_m_axis_tvalid    = w_m_local_tvalid[10];
    assign w_m_local_tready[10] = b10_m_axis_tready;
    assign b10_m_axis_tlast     = w_m_local_tlast[10];
    assign b10_m_axis_tuser     = w_m_local_tuser[10];
    assign b10_m_credit         = w_m_local_credit[10];

    assign w_s_local_tdata[11]  = b11_s_axis_tdata;
    assign w_s_local_tvalid[11] = b11_s_axis_tvalid;
    assign b11_s_axis_tready    = w_s_local_tready[11];
    assign w_s_local_tlast[11]  = b11_s_axis_tlast;
    assign w_s_local_tuser[11]  = b11_s_axis_tuser;
    assign b11_m_axis_tdata     = w_m_local_tdata[11];
    assign b11_m_axis_tvalid    = w_m_local_tvalid[11];
    assign w_m_local_tready[11] = b11_m_axis_tready;
    assign b11_m_axis_tlast     = w_m_local_tlast[11];
    assign b11_m_axis_tuser     = w_m_local_tuser[11];
    assign b11_m_credit         = w_m_local_credit[11];

    assign w_s_local_tdata[12]  = b12_s_axis_tdata;
    assign w_s_local_tvalid[12] = b12_s_axis_tvalid;
    assign b12_s_axis_tready    = w_s_local_tready[12];
    assign w_s_local_tlast[12]  = b12_s_axis_tlast;
    assign w_s_local_tuser[12]  = b12_s_axis_tuser;
    assign b12_m_axis_tdata     = w_m_local_tdata[12];
    assign b12_m_axis_tvalid    = w_m_local_tvalid[12];
    assign w_m_local_tready[12] = b12_m_axis_tready;
    assign b12_m_axis_tlast     = w_m_local_tlast[12];
    assign b12_m_axis_tuser     = w_m_local_tuser[12];
    assign b12_m_credit         = w_m_local_credit[12];

    assign w_s_local_tdata[13]  = b13_s_axis_tdata;
    assign w_s_local_tvalid[13] = b13_s_axis_tvalid;
    assign b13_s_axis_tready    = w_s_local_tready[13];
    assign w_s_local_tlast[13]  = b13_s_axis_tlast;
    assign w_s_local_tuser[13]  = b13_s_axis_tuser;
    assign b13_m_axis_tdata     = w_m_local_tdata[13];
    assign b13_m_axis_tvalid    = w_m_local_tvalid[13];
    assign w_m_local_tready[13] = b13_m_axis_tready;
    assign b13_m_axis_tlast     = w_m_local_tlast[13];
    assign b13_m_axis_tuser     = w_m_local_tuser[13];
    assign b13_m_credit         = w_m_local_credit[13];

    assign w_s_local_tdata[14]  = b14_s_axis_tdata;
    assign w_s_local_tvalid[14] = b14_s_axis_tvalid;
    assign b14_s_axis_tready    = w_s_local_tready[14];
    assign w_s_local_tlast[14]  = b14_s_axis_tlast;
    assign w_s_local_tuser[14]  = b14_s_axis_tuser;
    assign b14_m_axis_tdata     = w_m_local_tdata[14];
    assign b14_m_axis_tvalid    = w_m_local_tvalid[14];
    assign w_m_local_tready[14] = b14_m_axis_tready;
    assign b14_m_axis_tlast     = w_m_local_tlast[14];
    assign b14_m_axis_tuser     = w_m_local_tuser[14];
    assign b14_m_credit         = w_m_local_credit[14];

    assign w_s_local_tdata[15]  = b15_s_axis_tdata;
    assign w_s_local_tvalid[15] = b15_s_axis_tvalid;
    assign b15_s_axis_tready    = w_s_local_tready[15];
    assign w_s_local_tlast[15]  = b15_s_axis_tlast;
    assign w_s_local_tuser[15]  = b15_s_axis_tuser;
    assign b15_m_axis_tdata     = w_m_local_tdata[15];
    assign b15_m_axis_tvalid    = w_m_local_tvalid[15];
    assign w_m_local_tready[15] = b15_m_axis_tready;
    assign b15_m_axis_tlast     = w_m_local_tlast[15];
    assign b15_m_axis_tuser     = w_m_local_tuser[15];
    assign b15_m_credit         = w_m_local_credit[15];

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
    assign b4_err = w_o_err[4];
    assign b5_err = w_o_err[5];
    assign b6_err = w_o_err[6];
    assign b7_err = w_o_err[7];
    assign b8_err = w_o_err[8];
    assign b9_err = w_o_err[9];
    assign b10_err = w_o_err[10];
    assign b11_err = w_o_err[11];
    assign b12_err = w_o_err[12];
    assign b13_err = w_o_err[13];
    assign b14_err = w_o_err[14];
    assign b15_err = w_o_err[15];

    // Per-cell mode-switch ack tallies (Task 6): exposed per boundary
    // cell; only the origin's entry feeds the tile suite's barrier.
    logic [31:0] w_o_mode_acks [NUM_BOUNDARY];

    assign b0_mode_acks = w_o_mode_acks[0];
    assign b1_mode_acks = w_o_mode_acks[1];
    assign b2_mode_acks = w_o_mode_acks[2];
    assign b3_mode_acks = w_o_mode_acks[3];
    assign b4_mode_acks = w_o_mode_acks[4];
    assign b5_mode_acks = w_o_mode_acks[5];
    assign b6_mode_acks = w_o_mode_acks[6];
    assign b7_mode_acks = w_o_mode_acks[7];
    assign b8_mode_acks = w_o_mode_acks[8];
    assign b9_mode_acks = w_o_mode_acks[9];
    assign b10_mode_acks = w_o_mode_acks[10];
    assign b11_mode_acks = w_o_mode_acks[11];
    assign b12_mode_acks = w_o_mode_acks[12];
    assign b13_mode_acks = w_o_mode_acks[13];
    assign b14_mode_acks = w_o_mode_acks[14];
    assign b15_mode_acks = w_o_mode_acks[15];

    // Per-cell bulk-reservation-due flags (Task 7): bit p of each
    // entry = that cell's output port p reservation is due. Exposed
    // per boundary cell; suites may ignore them but the fabric port
    // must exist. Width follows the 9-port pin (Task 6c).
    logic [8:0] w_o_bulk_starved [NUM_BOUNDARY];

    assign b0_bulk_starved = w_o_bulk_starved[0];
    assign b1_bulk_starved = w_o_bulk_starved[1];
    assign b2_bulk_starved = w_o_bulk_starved[2];
    assign b3_bulk_starved = w_o_bulk_starved[3];
    assign b4_bulk_starved = w_o_bulk_starved[4];
    assign b5_bulk_starved = w_o_bulk_starved[5];
    assign b6_bulk_starved = w_o_bulk_starved[6];
    assign b7_bulk_starved = w_o_bulk_starved[7];
    assign b8_bulk_starved = w_o_bulk_starved[8];
    assign b9_bulk_starved = w_o_bulk_starved[9];
    assign b10_bulk_starved = w_o_bulk_starved[10];
    assign b11_bulk_starved = w_o_bulk_starved[11];
    assign b12_bulk_starved = w_o_bulk_starved[12];
    assign b13_bulk_starved = w_o_bulk_starved[13];
    assign b14_bulk_starved = w_o_bulk_starved[14];
    assign b15_bulk_starved = w_o_bulk_starved[15];

    // Per-cell DFT-active flags (Task 10): exposed per boundary cell.
    logic w_o_dft_active [NUM_BOUNDARY];

    assign b0_dft_active  = w_o_dft_active[0];
    assign b1_dft_active  = w_o_dft_active[1];
    assign b2_dft_active  = w_o_dft_active[2];
    assign b3_dft_active  = w_o_dft_active[3];
    assign b4_dft_active  = w_o_dft_active[4];
    assign b5_dft_active  = w_o_dft_active[5];
    assign b6_dft_active  = w_o_dft_active[6];
    assign b7_dft_active  = w_o_dft_active[7];
    assign b8_dft_active  = w_o_dft_active[8];
    assign b9_dft_active  = w_o_dft_active[9];
    assign b10_dft_active = w_o_dft_active[10];
    assign b11_dft_active = w_o_dft_active[11];
    assign b12_dft_active = w_o_dft_active[12];
    assign b13_dft_active = w_o_dft_active[13];
    assign b14_dft_active = w_o_dft_active[14];
    assign b15_dft_active = w_o_dft_active[15];

    delta_mesh_fabric_4x4x1 #(
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

endmodule : delta_mesh_fabric_4x4_th
