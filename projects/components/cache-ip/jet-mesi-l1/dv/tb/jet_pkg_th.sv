// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_pkg_th
// Purpose:
//   Compile-only harness for jet_pkg. Exposes the package parameters and
//   enum encodings as output ports so the cocotb test can assert the J1/J5
//   defaults and the widths of the jet-specific types.
//
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

module jet_pkg_th
    import jet_pkg::*;
#(
    parameter int MSHR_COUNT   = jet_pkg::MSHR_COUNT,
    parameter int VICTIM_DEPTH = jet_pkg::VICTIM_DEPTH,
    parameter int RSP_DEPTH    = jet_pkg::RSP_DEPTH,
    localparam int SEQ_W       = $clog2(RSP_DEPTH),
    localparam int MW          = $clog2(MSHR_COUNT)
)(
    output logic [31:0] mshr_count_o,
    output logic [31:0] victim_depth_o,
    output logic [31:0] rsp_depth_o,
    output logic [31:0] seq_w_o,
    output logic [31:0] mw_o,
    output logic [1:0]  fill_class_rnsd_o,
    output logic [1:0]  fill_class_ru_o,
    output logic [1:0]  pend_none_o,
    output logic [1:0]  pend_downgrade_s_o,
    output logic [1:0]  pend_invalidate_i_o
);

    assign mshr_count_o        = MSHR_COUNT;
    assign victim_depth_o      = VICTIM_DEPTH;
    assign rsp_depth_o         = RSP_DEPTH;
    assign seq_w_o             = SEQ_W;
    assign mw_o                = MW;
    assign fill_class_rnsd_o   = JET_CLS_RNSD;
    assign fill_class_ru_o     = JET_CLS_RU;
    assign pend_none_o         = JET_PEND_NONE;
    assign pend_downgrade_s_o  = JET_PEND_DOWNGRADE_S;
    assign pend_invalidate_i_o = JET_PEND_INVALIDATE_I;

endmodule : jet_pkg_th
