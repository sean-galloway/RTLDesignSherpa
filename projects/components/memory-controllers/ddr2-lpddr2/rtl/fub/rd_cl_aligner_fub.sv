// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: rd_cl_aligner_fub
// Purpose: SKELETON — tags issued RD ops with their CL countdown,
//          asserts dfi_rddata_en at the right cycle, accepts dfi_rddata
//          + dfi_rddata_valid, routes the beats into the axi_frontend's
//          rd_inject port keyed by the rd CAM slot's AXI ID.
//
// Status:  Port-list only. Drives rd_inject idle.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module rd_cl_aligner_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int RD_CAM_DEPTH    = 16,
    parameter int AXI_ID_WIDTH    = 4,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DFI_DATA_WIDTH  = 64,
    parameter int DFI_VALID_WIDTH = 1,
    parameter int DFI_EN_WIDTH    = 1,

    parameter int RSL = $clog2(RD_CAM_DEPTH),
    parameter int IW  = AXI_ID_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH
) (
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,

    input  logic [3:0]                    cl_i,           // from mode_register
    input  logic [3:0]                    al_i,

    // ----- read-op handshake from scheduler -----
    input  logic                          op_valid_i,
    output logic                          op_ready_o,
    input  logic [RSL-1:0]                op_slot_i,
    input  logic [IW-1:0]                 op_id_i,
    input  logic [BLW-1:0]                op_len_i,

    // ----- DFI read data interface -----
    output logic [DFI_EN_WIDTH-1:0]       dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]     dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0]    dfi_rddata_valid_i,

    // ----- rd_inject into axi_frontend -----
    output logic                          rd_inject_valid_o,
    input  logic                          rd_inject_ready_i,
    output logic [IW-1:0]                 rd_inject_id_o,
    output logic [DFI_DATA_WIDTH-1:0]     rd_inject_data_o,
    output logic                          rd_inject_last_o,

    // ----- per-beat strobe to rd CAM (beat retire) -----
    output logic                          rd_beat_we_o,
    output logic [RSL-1:0]                rd_beat_slot_o
);

    // -- TODO: implementation --
    assign op_ready_o        = 1'b1;
    assign dfi_rddata_en_o   = '0;
    assign rd_inject_valid_o = 1'b0;
    assign rd_inject_id_o    = '0;
    assign rd_inject_data_o  = '0;
    assign rd_inject_last_o  = 1'b0;
    assign rd_beat_we_o      = 1'b0;
    assign rd_beat_slot_o    = '0;

    wire unused = |{ mc_clk, mc_rst_n, cl_i, al_i,
                     op_valid_i, op_slot_i, op_id_i, op_len_i,
                     dfi_rddata_i, dfi_rddata_valid_i,
                     rd_inject_ready_i };

endmodule : rd_cl_aligner_fub
