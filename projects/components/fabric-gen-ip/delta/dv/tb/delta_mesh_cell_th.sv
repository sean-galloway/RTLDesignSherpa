// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: delta_mesh_cell_th
// Purpose: Test harness -- pure wiring. Flattens the generated cell's
//          unpacked-array ports ([9]) into one named port set per mesh port
//          (xneg_, xpos_, yneg_, ypos_, zneg_, zpos_, dia_, dia2_, local_)
//          so the RDS-DV AXIS BFMs bind to each one by prefix.
//
// DUT: projects/components/fabric-gen-ip/delta/rtl/delta_mesh_cell.sv
//      (module delta_mesh_cell, generated with
//       --topology mesh --cells-x 4 --cells-y 4 --cells-z 1 --user-width 64,
//       instantiated here at POS (1,1,0) of the 4x4x1 grid).
//      If that generator command changes, this port list must follow it.
//
// Port index map (pinned in delta_mesh_cell; Task 6c added P_DIA2 at 7 and
// MOVED P_LOCAL from 7 to 8):
//   0 = P_X_NEG, 1 = P_X_POS, 2 = P_Y_NEG, 3 = P_Y_POS,
//   4 = P_Z_NEG, 5 = P_Z_POS, 6 = P_DIA (tetrad diagonal), 7 = P_DIA2
//   (inter-tetrad diagonal), 8 = P_LOCAL
//
// Credit sidebands: s_credit is driven per port per VC by the test (modeling
// the downstream neighbor's advertised credits); m_credit is the credit
// count this cell advertises for its own input buffers (Task 4 protocol).
// err_drop_cnt is the cell's malformed-dst drop tally (Task 5), exposed for
// the tables/drop suites; mode_acks is the mode-switch ack tally (Task 6,
// the modes suite's barrier), exposed the same way; bulk_starved is the
// per-output bulk-reservation-due flag vector (Task 7 o_bulk_starved[8:0]
// pass-through -- the qos suite's starve observability), exposed the same
// way. GRID_* defaults match the checked-in 4x4x1 cell. The dia_ port is
// the tetrad diagonal link (Task 6b); the dia2_ port is the inter-tetrad
// diagonal link (Task 6c); both are driven here like any neighbor port
// (s_credit all-ones default in the TB).
//
// Subsystem: delta (dv)
//
// Author: sean galloway
// Created: 2026-10-14

`timescale 1ns / 1ps

module delta_mesh_cell_th #(
    parameter int DATA_WIDTH = 64,
    parameter int USER_WIDTH = 64,
    parameter int COORD_W    = 2,
    parameter int POS_X      = 1,
    parameter int POS_Y      = 1,
    parameter int POS_Z      = 0,
    parameter int GRID_X     = 4,
    parameter int GRID_Y     = 4,
    parameter int GRID_Z     = 1,
    parameter int NUM_VC     = 2,
    parameter int AGING_LIMIT = 64,
    parameter int BULK_MIN_CREDITS = 1
) (
    input  logic aclk,
    input  logic aresetn,

    input  logic [DATA_WIDTH-1:0] xneg_s_axis_tdata,
    input  logic                  xneg_s_axis_tvalid,
    output logic                  xneg_s_axis_tready,
    input  logic                  xneg_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] xneg_s_axis_tuser,
    input  logic [NUM_VC-1:0]     xneg_s_credit,
    output logic [DATA_WIDTH-1:0] xneg_m_axis_tdata,
    output logic                  xneg_m_axis_tvalid,
    input  logic                  xneg_m_axis_tready,
    output logic                  xneg_m_axis_tlast,
    output logic [USER_WIDTH-1:0] xneg_m_axis_tuser,
    output logic [NUM_VC-1:0]     xneg_m_credit,

    input  logic [DATA_WIDTH-1:0] xpos_s_axis_tdata,
    input  logic                  xpos_s_axis_tvalid,
    output logic                  xpos_s_axis_tready,
    input  logic                  xpos_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] xpos_s_axis_tuser,
    input  logic [NUM_VC-1:0]     xpos_s_credit,
    output logic [DATA_WIDTH-1:0] xpos_m_axis_tdata,
    output logic                  xpos_m_axis_tvalid,
    input  logic                  xpos_m_axis_tready,
    output logic                  xpos_m_axis_tlast,
    output logic [USER_WIDTH-1:0] xpos_m_axis_tuser,
    output logic [NUM_VC-1:0]     xpos_m_credit,

    input  logic [DATA_WIDTH-1:0] yneg_s_axis_tdata,
    input  logic                  yneg_s_axis_tvalid,
    output logic                  yneg_s_axis_tready,
    input  logic                  yneg_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] yneg_s_axis_tuser,
    input  logic [NUM_VC-1:0]     yneg_s_credit,
    output logic [DATA_WIDTH-1:0] yneg_m_axis_tdata,
    output logic                  yneg_m_axis_tvalid,
    input  logic                  yneg_m_axis_tready,
    output logic                  yneg_m_axis_tlast,
    output logic [USER_WIDTH-1:0] yneg_m_axis_tuser,
    output logic [NUM_VC-1:0]     yneg_m_credit,

    input  logic [DATA_WIDTH-1:0] ypos_s_axis_tdata,
    input  logic                  ypos_s_axis_tvalid,
    output logic                  ypos_s_axis_tready,
    input  logic                  ypos_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] ypos_s_axis_tuser,
    input  logic [NUM_VC-1:0]     ypos_s_credit,
    output logic [DATA_WIDTH-1:0] ypos_m_axis_tdata,
    output logic                  ypos_m_axis_tvalid,
    input  logic                  ypos_m_axis_tready,
    output logic                  ypos_m_axis_tlast,
    output logic [USER_WIDTH-1:0] ypos_m_axis_tuser,
    output logic [NUM_VC-1:0]     ypos_m_credit,

    input  logic [DATA_WIDTH-1:0] zneg_s_axis_tdata,
    input  logic                  zneg_s_axis_tvalid,
    output logic                  zneg_s_axis_tready,
    input  logic                  zneg_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] zneg_s_axis_tuser,
    input  logic [NUM_VC-1:0]     zneg_s_credit,
    output logic [DATA_WIDTH-1:0] zneg_m_axis_tdata,
    output logic                  zneg_m_axis_tvalid,
    input  logic                  zneg_m_axis_tready,
    output logic                  zneg_m_axis_tlast,
    output logic [USER_WIDTH-1:0] zneg_m_axis_tuser,
    output logic [NUM_VC-1:0]     zneg_m_credit,

    input  logic [DATA_WIDTH-1:0] zpos_s_axis_tdata,
    input  logic                  zpos_s_axis_tvalid,
    output logic                  zpos_s_axis_tready,
    input  logic                  zpos_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] zpos_s_axis_tuser,
    input  logic [NUM_VC-1:0]     zpos_s_credit,
    output logic [DATA_WIDTH-1:0] zpos_m_axis_tdata,
    output logic                  zpos_m_axis_tvalid,
    input  logic                  zpos_m_axis_tready,
    output logic                  zpos_m_axis_tlast,
    output logic [USER_WIDTH-1:0] zpos_m_axis_tuser,
    output logic [NUM_VC-1:0]     zpos_m_credit,

    input  logic [DATA_WIDTH-1:0] dia_s_axis_tdata,
    input  logic                  dia_s_axis_tvalid,
    output logic                  dia_s_axis_tready,
    input  logic                  dia_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] dia_s_axis_tuser,
    input  logic [NUM_VC-1:0]     dia_s_credit,
    output logic [DATA_WIDTH-1:0] dia_m_axis_tdata,
    output logic                  dia_m_axis_tvalid,
    input  logic                  dia_m_axis_tready,
    output logic                  dia_m_axis_tlast,
    output logic [USER_WIDTH-1:0] dia_m_axis_tuser,
    output logic [NUM_VC-1:0]     dia_m_credit,

    input  logic [DATA_WIDTH-1:0] dia2_s_axis_tdata,
    input  logic                  dia2_s_axis_tvalid,
    output logic                  dia2_s_axis_tready,
    input  logic                  dia2_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] dia2_s_axis_tuser,
    input  logic [NUM_VC-1:0]     dia2_s_credit,
    output logic [DATA_WIDTH-1:0] dia2_m_axis_tdata,
    output logic                  dia2_m_axis_tvalid,
    input  logic                  dia2_m_axis_tready,
    output logic                  dia2_m_axis_tlast,
    output logic [USER_WIDTH-1:0] dia2_m_axis_tuser,
    output logic [NUM_VC-1:0]     dia2_m_credit,

    input  logic [DATA_WIDTH-1:0] local_s_axis_tdata,
    input  logic                  local_s_axis_tvalid,
    output logic                  local_s_axis_tready,
    input  logic                  local_s_axis_tlast,
    input  logic [USER_WIDTH-1:0] local_s_axis_tuser,
    input  logic [NUM_VC-1:0]     local_s_credit,
    output logic [DATA_WIDTH-1:0] local_m_axis_tdata,
    output logic                  local_m_axis_tvalid,
    input  logic                  local_m_axis_tready,
    output logic                  local_m_axis_tlast,
    output logic [USER_WIDTH-1:0] local_m_axis_tuser,
    output logic [NUM_VC-1:0]     local_m_credit,

    output logic [31:0]           err_drop_cnt,
    output logic [31:0]           mode_acks,
    output logic [8:0]            bulk_starved,
    output logic [31:0]           spec_active,
    output logic                  dft_active,

    input  logic [8:0]            wrap_mask
);

    // DUT port index map (pinned localparams in delta_mesh_cell, Task 6c):
    //   0 = P_X_NEG, 1 = P_X_POS, 2 = P_Y_NEG, 3 = P_Y_POS,
    //   4 = P_Z_NEG, 5 = P_Z_POS, 6 = P_DIA, 7 = P_DIA2, 8 = P_LOCAL
    localparam int NUM_PORTS = 9;

    logic [DATA_WIDTH-1:0] w_s_tdata  [NUM_PORTS];
    logic                  w_s_tvalid [NUM_PORTS];
    logic                  w_s_tready [NUM_PORTS];
    logic                  w_s_tlast  [NUM_PORTS];
    logic [USER_WIDTH-1:0] w_s_tuser  [NUM_PORTS];
    logic [DATA_WIDTH-1:0] w_m_tdata  [NUM_PORTS];
    logic                  w_m_tvalid [NUM_PORTS];
    logic                  w_m_tready [NUM_PORTS];
    logic                  w_m_tlast  [NUM_PORTS];
    logic [USER_WIDTH-1:0] w_m_tuser  [NUM_PORTS];
    logic [NUM_VC-1:0]     w_s_credit [NUM_PORTS];
    logic [NUM_VC-1:0]     w_m_credit [NUM_PORTS];

    assign w_s_tdata[0]  = xneg_s_axis_tdata;
    assign w_s_tvalid[0] = xneg_s_axis_tvalid;
    assign xneg_s_axis_tready = w_s_tready[0];
    assign w_s_tlast[0]  = xneg_s_axis_tlast;
    assign w_s_tuser[0]  = xneg_s_axis_tuser;
    assign w_s_credit[0] = xneg_s_credit;
    assign xneg_m_axis_tdata  = w_m_tdata[0];
    assign xneg_m_axis_tvalid = w_m_tvalid[0];
    assign w_m_tready[0] = xneg_m_axis_tready;
    assign xneg_m_axis_tlast = w_m_tlast[0];
    assign xneg_m_axis_tuser = w_m_tuser[0];
    assign xneg_m_credit = w_m_credit[0];

    assign w_s_tdata[1]  = xpos_s_axis_tdata;
    assign w_s_tvalid[1] = xpos_s_axis_tvalid;
    assign xpos_s_axis_tready = w_s_tready[1];
    assign w_s_tlast[1]  = xpos_s_axis_tlast;
    assign w_s_tuser[1]  = xpos_s_axis_tuser;
    assign w_s_credit[1] = xpos_s_credit;
    assign xpos_m_axis_tdata  = w_m_tdata[1];
    assign xpos_m_axis_tvalid = w_m_tvalid[1];
    assign w_m_tready[1] = xpos_m_axis_tready;
    assign xpos_m_axis_tlast = w_m_tlast[1];
    assign xpos_m_axis_tuser = w_m_tuser[1];
    assign xpos_m_credit = w_m_credit[1];

    assign w_s_tdata[2]  = yneg_s_axis_tdata;
    assign w_s_tvalid[2] = yneg_s_axis_tvalid;
    assign yneg_s_axis_tready = w_s_tready[2];
    assign w_s_tlast[2]  = yneg_s_axis_tlast;
    assign w_s_tuser[2]  = yneg_s_axis_tuser;
    assign w_s_credit[2] = yneg_s_credit;
    assign yneg_m_axis_tdata  = w_m_tdata[2];
    assign yneg_m_axis_tvalid = w_m_tvalid[2];
    assign w_m_tready[2] = yneg_m_axis_tready;
    assign yneg_m_axis_tlast = w_m_tlast[2];
    assign yneg_m_axis_tuser = w_m_tuser[2];
    assign yneg_m_credit = w_m_credit[2];

    assign w_s_tdata[3]  = ypos_s_axis_tdata;
    assign w_s_tvalid[3] = ypos_s_axis_tvalid;
    assign ypos_s_axis_tready = w_s_tready[3];
    assign w_s_tlast[3]  = ypos_s_axis_tlast;
    assign w_s_tuser[3]  = ypos_s_axis_tuser;
    assign w_s_credit[3] = ypos_s_credit;
    assign ypos_m_axis_tdata  = w_m_tdata[3];
    assign ypos_m_axis_tvalid = w_m_tvalid[3];
    assign w_m_tready[3] = ypos_m_axis_tready;
    assign ypos_m_axis_tlast = w_m_tlast[3];
    assign ypos_m_axis_tuser = w_m_tuser[3];
    assign ypos_m_credit = w_m_credit[3];

    assign w_s_tdata[4]  = zneg_s_axis_tdata;
    assign w_s_tvalid[4] = zneg_s_axis_tvalid;
    assign zneg_s_axis_tready = w_s_tready[4];
    assign w_s_tlast[4]  = zneg_s_axis_tlast;
    assign w_s_tuser[4]  = zneg_s_axis_tuser;
    assign w_s_credit[4] = zneg_s_credit;
    assign zneg_m_axis_tdata  = w_m_tdata[4];
    assign zneg_m_axis_tvalid = w_m_tvalid[4];
    assign w_m_tready[4] = zneg_m_axis_tready;
    assign zneg_m_axis_tlast = w_m_tlast[4];
    assign zneg_m_axis_tuser = w_m_tuser[4];
    assign zneg_m_credit = w_m_credit[4];

    assign w_s_tdata[5]  = zpos_s_axis_tdata;
    assign w_s_tvalid[5] = zpos_s_axis_tvalid;
    assign zpos_s_axis_tready = w_s_tready[5];
    assign w_s_tlast[5]  = zpos_s_axis_tlast;
    assign w_s_tuser[5]  = zpos_s_axis_tuser;
    assign w_s_credit[5] = zpos_s_credit;
    assign zpos_m_axis_tdata  = w_m_tdata[5];
    assign zpos_m_axis_tvalid = w_m_tvalid[5];
    assign w_m_tready[5] = zpos_m_axis_tready;
    assign zpos_m_axis_tlast = w_m_tlast[5];
    assign zpos_m_axis_tuser = w_m_tuser[5];
    assign zpos_m_credit = w_m_credit[5];

    assign w_s_tdata[6]  = dia_s_axis_tdata;
    assign w_s_tvalid[6] = dia_s_axis_tvalid;
    assign dia_s_axis_tready = w_s_tready[6];
    assign w_s_tlast[6]  = dia_s_axis_tlast;
    assign w_s_tuser[6]  = dia_s_axis_tuser;
    assign w_s_credit[6] = dia_s_credit;
    assign dia_m_axis_tdata  = w_m_tdata[6];
    assign dia_m_axis_tvalid = w_m_tvalid[6];
    assign w_m_tready[6] = dia_m_axis_tready;
    assign dia_m_axis_tlast = w_m_tlast[6];
    assign dia_m_axis_tuser = w_m_tuser[6];
    assign dia_m_credit = w_m_credit[6];

    assign w_s_tdata[7]  = dia2_s_axis_tdata;
    assign w_s_tvalid[7] = dia2_s_axis_tvalid;
    assign dia2_s_axis_tready = w_s_tready[7];
    assign w_s_tlast[7]  = dia2_s_axis_tlast;
    assign w_s_tuser[7]  = dia2_s_axis_tuser;
    assign w_s_credit[7] = dia2_s_credit;
    assign dia2_m_axis_tdata  = w_m_tdata[7];
    assign dia2_m_axis_tvalid = w_m_tvalid[7];
    assign w_m_tready[7] = dia2_m_axis_tready;
    assign dia2_m_axis_tlast = w_m_tlast[7];
    assign dia2_m_axis_tuser = w_m_tuser[7];
    assign dia2_m_credit = w_m_credit[7];

    assign w_s_tdata[8]  = local_s_axis_tdata;
    assign w_s_tvalid[8] = local_s_axis_tvalid;
    assign local_s_axis_tready = w_s_tready[8];
    assign w_s_tlast[8]  = local_s_axis_tlast;
    assign w_s_tuser[8]  = local_s_axis_tuser;
    assign w_s_credit[8] = local_s_credit;
    assign local_m_axis_tdata  = w_m_tdata[8];
    assign local_m_axis_tvalid = w_m_tvalid[8];
    assign w_m_tready[8] = local_m_axis_tready;
    assign local_m_axis_tlast = w_m_tlast[8];
    assign local_m_axis_tuser = w_m_tuser[8];
    assign local_m_credit = w_m_credit[8];

    // Credit sidebands: driven per port per VC by the test bench (s_credit
    // models the downstream neighbor's advertised credit levels).
    delta_mesh_cell #(
        .DATA_WIDTH(DATA_WIDTH),
        .USER_WIDTH(USER_WIDTH),
        .COORD_W(COORD_W),
        .POS_X(POS_X),
        .POS_Y(POS_Y),
        .POS_Z(POS_Z),
        .GRID_X(GRID_X),
        .GRID_Y(GRID_Y),
        .GRID_Z(GRID_Z),
        .NUM_VC(NUM_VC),
        .AGING_LIMIT(AGING_LIMIT),
        .BULK_MIN_CREDITS(BULK_MIN_CREDITS)
    ) u_dut (
        .aclk(aclk),
        .aresetn(aresetn),
        .s_axis_tdata(w_s_tdata),
        .s_axis_tvalid(w_s_tvalid),
        .s_axis_tready(w_s_tready),
        .s_axis_tlast(w_s_tlast),
        .s_axis_tuser(w_s_tuser),
        .m_axis_tdata(w_m_tdata),
        .m_axis_tvalid(w_m_tvalid),
        .m_axis_tready(w_m_tready),
        .m_axis_tlast(w_m_tlast),
        .m_axis_tuser(w_m_tuser),
        .s_credit(w_s_credit),
        .m_credit(w_m_credit),
        .wrap_mask(wrap_mask),
        .o_err_drop_cnt(err_drop_cnt),
        .o_mode_acks(mode_acks),
        .o_bulk_starved(bulk_starved),
        .o_spec_active(spec_active),
        .o_dft_active(dft_active)
    );

endmodule : delta_mesh_cell_th
