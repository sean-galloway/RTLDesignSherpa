// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: tile_credit_rx
// Purpose: The cells' and cores' side of RAPIDS's credit-return port
//          (m_tile_credit_*, TILE_SPEC 11.9-11.10): decode each return and
//          hand it to the sender it names (rapids TASK-032)
//
// Description:
//   Every packet on the port is one 128-bit tile header: ptype credit, op add
//   (0) or set (1), the count in length, the class in target[1:0], the
//   destination the sender's coordinate. The destination's external slot
//   (rapids_pkg::tile_ext_slot) picks the sender: slots 0-15 are cells and
//   must carry class 0 (landing-space flits), slots 16-19 control cores and
//   class 1 (intake entries). One return goes out per packet, the cycle it is
//   taken, as ret_valid[slot] with ret_set / ret_count.
//
//   Anything else is an error, counted and flagged sticky, and not passed on:
//   a ptype other than credit, a source other than RAPIDS, a destination with
//   no external slot or a spare one, a class that does not match the slot.
//
//   cfg_hold deasserts ready, so a test can hold returns back and see RAPIDS
//   coalesce them.
//
// Subsystem: fpga-systems/Genesys2/rapids tile harness
//
// Author: sean galloway
// Created: 2026-10-19

`timescale 1ns / 1ps

`include "reset_defs.svh"

module tile_credit_rx #(
    parameter logic [rapids_pkg::TILE_COORD_W-1:0] RAPIDS_COORD =
        {1'b0, rapids_pkg::TILE_LEVEL_IO, 12'h000},
    parameter int NS = rapids_pkg::TILE_CORE_SLOT0 + rapids_pkg::TILE_NUM_CORES   // 20 senders
) (
    input  logic            clk,
    input  logic            rst_n,

    input  logic            cfg_hold,

    // RAPIDS m_tile_credit_*
    input  logic            s_valid,
    output logic            s_ready,
    input  logic [127:0]    s_data,

    // One return per packet, to the sender it names
    output logic [NS-1:0]   ret_valid,
    output logic            ret_set,
    output logic [31:0]     ret_count,

    // Status
    output logic [31:0]     pkt_count,
    output logic [31:0]     set_count,
    output logic [31:0]     err_count,
    output logic            err_any      // sticky
);

    localparam int CRW = rapids_pkg::TILE_COORD_W;

    logic [CRW-1:0] w_dst, w_src;
    logic [2:0]     w_ptype;
    logic           w_op;
    logic [31:0]    w_len;
    logic [1:0]     w_cls;
    assign w_dst   = s_data[rapids_pkg::TILE_HDR_DST_LO   +: CRW];
    assign w_src   = s_data[rapids_pkg::TILE_HDR_SRC_LO   +: CRW];
    assign w_ptype = s_data[rapids_pkg::TILE_HDR_PTYPE_LO +: 3];
    assign w_op    = s_data[rapids_pkg::TILE_HDR_OP];
    assign w_len   = s_data[rapids_pkg::TILE_HDR_LEN_LO   +: 32];
    assign w_cls   = s_data[rapids_pkg::TILE_HDR_TGT_LO   +: 2];

    logic [rapids_pkg::TILE_EXT_W:0] w_slot_ok;
    logic [rapids_pkg::TILE_EXT_W-1:0] w_slot;
    logic w_is_cell, w_is_core, w_good;
    assign w_slot_ok = rapids_pkg::tile_ext_slot(w_dst);
    assign w_slot    = w_slot_ok[rapids_pkg::TILE_EXT_W-1:0];
    assign w_is_cell = w_slot_ok[rapids_pkg::TILE_EXT_W] && (w_slot < 5'(rapids_pkg::TILE_NUM_CELLS));
    assign w_is_core = w_slot_ok[rapids_pkg::TILE_EXT_W] && (w_slot >= 5'(rapids_pkg::TILE_CORE_SLOT0))
                       && (w_slot < 5'(NS));
    assign w_good    = (w_ptype == rapids_pkg::TILE_PTYPE_CREDIT) && (w_src == RAPIDS_COORD)
                       && ((w_is_cell && (w_cls == rapids_pkg::TILE_CLASS_SPACE))
                           || (w_is_core && (w_cls == rapids_pkg::TILE_CLASS_DESC)));

    assign s_ready = !cfg_hold;

    logic w_take;
    assign w_take = s_valid && s_ready;

    always_comb begin
        ret_valid = '0;
        if (w_take && w_good) ret_valid[w_slot] = 1'b1;
    end
    assign ret_set   = w_op;
    assign ret_count = w_len;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            pkt_count <= '0;
            set_count <= '0;
            err_count <= '0;
            err_any   <= 1'b0;
        end else if (w_take) begin
            pkt_count <= pkt_count + 1'b1;
            if (w_good && w_op) set_count <= set_count + 1'b1;
            if (!w_good) begin
                err_count <= err_count + 1'b1;
                err_any   <= 1'b1;
            end
        end
    )

endmodule : tile_credit_rx
