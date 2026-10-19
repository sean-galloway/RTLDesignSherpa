// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: tb_tile_cell_loop
// Purpose: Unit-test top for the tile harness's cell model (rapids TASK-032):
//          two tile_cell_tx cells merged by tid onto one stream the cocotb
//          side plays RAPIDS for, and tile_credit_rx taking that side's
//          credit packets back to the cells. Test only; not in the harness.
//
// Author: sean galloway
// Created: 2026-10-19

`timescale 1ns / 1ps

module tb_tile_cell_loop #(
    parameter int DW         = 512,
    parameter int LAND_FLITS = 16,
    parameter int SW         = DW / 8
) (
    input  logic            aclk,
    input  logic            aresetn,

    input  logic            cfg_start,
    input  logic [31:0]     cfg_seed,
    input  logic [31:0]     cfg_num_beats,
    input  logic [31:0]     cfg_beats_per_pkt,
    input  logic            cfg_hold,

    // cell A: channel 2, slot 0; cell B: channel 5, slot 6
    output logic            a_axis_tvalid,
    input  logic            a_axis_tready,
    output logic [DW-1:0]   a_axis_tdata,
    output logic [SW-1:0]   a_axis_tstrb,
    output logic            a_axis_tlast,
    output logic [7:0]      a_axis_tid,
    output logic [3:0]      a_axis_tdest,
    output logic [0:0]      a_axis_tuser,
    output logic            b_axis_tvalid,
    input  logic            b_axis_tready,
    output logic [DW-1:0]   b_axis_tdata,
    output logic [SW-1:0]   b_axis_tstrb,
    output logic            b_axis_tlast,
    output logic [7:0]      b_axis_tid,
    output logic [3:0]      b_axis_tdest,
    output logic [0:0]      b_axis_tuser,

    // RAPIDS's credit-return port, as RAPIDS drives it
    input  logic            crd_valid,
    output logic            crd_ready,
    input  logic [127:0]    crd_packet,

    output logic            a_busy, b_busy,
    output logic [31:0]     a_crc, b_crc,
    output logic [31:0]     a_sent, a_returned, b_sent, b_returned,
    output logic [4:0]      a_free, b_free,
    output logic            a_err_over, a_err_big, b_err_over, b_err_big,
    output logic [31:0]     crd_pkts, crd_sets, crd_errs,
    output logic            crd_err
);

    assign a_axis_tdest = '0;
    assign a_axis_tuser = '0;
    assign b_axis_tdest = '0;
    assign b_axis_tuser = '0;

    localparam logic [14:0] A_COORD = rapids_pkg::tile_ext_coord(5'd0, 4'd0);
    localparam logic [14:0] B_COORD = rapids_pkg::tile_ext_coord(5'd6, 4'd0);

    logic [19:0] w_ret_valid;
    logic        w_ret_set;
    logic [31:0] w_ret_count;

    tile_credit_rx u_crd (
        .clk(aclk), .rst_n(aresetn), .cfg_hold(cfg_hold),
        .s_valid(crd_valid), .s_ready(crd_ready), .s_data(crd_packet),
        .ret_valid(w_ret_valid), .ret_set(w_ret_set), .ret_count(w_ret_count),
        .pkt_count(crd_pkts), .set_count(crd_sets), .err_count(crd_errs), .err_any(crd_err)
    );

    tile_cell_tx #(.DW(DW), .LAND_FLITS(LAND_FLITS)) u_a (
        .clk(aclk), .rst_n(aresetn),
        .cfg_start(cfg_start), .cfg_seed(cfg_seed), .cfg_channel(4'd2), .cfg_coord(A_COORD),
        .cfg_num_beats(cfg_num_beats), .cfg_beats_per_pkt(cfg_beats_per_pkt),
        .busy(a_busy), .done(),
        .ret_valid(w_ret_valid[0]), .ret_set(w_ret_set), .ret_count(w_ret_count),
        .m_valid(a_axis_tvalid), .m_ready(a_axis_tready), .m_data(a_axis_tdata),
        .m_strb(a_axis_tstrb), .m_last(a_axis_tlast), .m_tid(a_axis_tid),
        .expected_crc(a_crc), .strap_free(a_free), .sent_flits(a_sent),
        .returned_flits(a_returned), .sent_pkts(),
        .err_over_return(a_err_over), .err_pkt_too_big(a_err_big)
    );

    tile_cell_tx #(.DW(DW), .LAND_FLITS(LAND_FLITS)) u_b (
        .clk(aclk), .rst_n(aresetn),
        .cfg_start(cfg_start), .cfg_seed(cfg_seed), .cfg_channel(4'd5), .cfg_coord(B_COORD),
        .cfg_num_beats(cfg_num_beats), .cfg_beats_per_pkt(cfg_beats_per_pkt),
        .busy(b_busy), .done(),
        .ret_valid(w_ret_valid[6]), .ret_set(w_ret_set), .ret_count(w_ret_count),
        .m_valid(b_axis_tvalid), .m_ready(b_axis_tready), .m_data(b_axis_tdata),
        .m_strb(b_axis_tstrb), .m_last(b_axis_tlast), .m_tid(b_axis_tid),
        .expected_crc(b_crc), .strap_free(b_free), .sent_flits(b_sent),
        .returned_flits(b_returned), .sent_pkts(),
        .err_over_return(b_err_over), .err_pkt_too_big(b_err_big)
    );

endmodule : tb_tile_cell_loop
