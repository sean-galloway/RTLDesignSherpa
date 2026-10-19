// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_tile_desc_intake
// Purpose: Intake queue for core-issued descriptors (TILE_SPEC 11.11, rapids TASK-027)
//
// Description:
//   A tetrad's control core sends `desc` packets only against its strap of
//   intake entries (credit class 1). This FIFO is that reserved space: as
//   deep as the entries handed out (DEPTH = cores x DESC_PER_CORE). The sink
//   port's header decode pushes each descriptor in as a pulse, with the
//   channel it names and its sender's slot; the queue hands them, in order,
//   to the put side of the descriptor queue (descriptor_engine_shared inj_*),
//   which takes one when that channel's injection slot is free. A descriptor
//   for a busy channel at the head waits there; the scheduler's 2-deep
//   descriptor skid keeps that wait short.
//
//   When an entry leaves for the descriptor queue its credit goes back to its
//   sender (ret_valid, class 1). A push into a full queue (a core over its
//   strap) is dropped, sets sts_overrun and still returns its credit, so no
//   path consumes a descriptor silently.
//
// Documentation: projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md (Section 11)
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2026-10-19

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_tile_desc_intake #(
    parameter int NUM_CHANNELS = 8,
    parameter int DEPTH        = 8,
    parameter int NC  = NUM_CHANNELS,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1,
    parameter int XW  = rapids_pkg::TILE_EXT_W
) (
    input  logic                clk,
    input  logic                rst_n,

    // From rapids_tile_hdr_rx (pulse, no backpressure)
    input  logic                in_valid,
    input  logic [CIW-1:0]      in_ch,
    input  logic [255:0]        in_data,
    input  logic [XW:0]         in_slot,     // {ok, sender slot}

    // To descriptor_engine_shared
    output logic                out_valid,
    input  logic                out_ready,
    output logic [CIW-1:0]      out_ch,
    output logic [255:0]        out_data,

    // One entry back to its sender (registered pulse)
    output logic                ret_valid,
    output logic [XW-1:0]       ret_slot,
    output logic                drop_ret_valid,   // ...for a push dropped on overrun
    output logic [XW-1:0]       drop_ret_slot,

    output logic                sts_overrun   // sticky until reset
);

    localparam int EW = CIW + 256 + XW + 1;

    logic          w_wr_ready;
    logic [EW-1:0] w_rd_data;
    logic [XW:0]   w_out_slot;

    assign {w_out_slot, out_ch, out_data} = w_rd_data;

    gaxi_fifo_sync #(
        .DATA_WIDTH (EW),
        .DEPTH      (DEPTH)
    ) u_intake (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (in_valid),
        .wr_ready    (w_wr_ready),
        .wr_data     ({in_slot, in_ch, in_data}),
        .rd_ready    (out_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (out_valid),
        .rd_data     (w_rd_data)
    );

    // Pops and overrun drops return on separate pulses (both can happen in
    // one cycle).
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            ret_valid      <= 1'b0;
            ret_slot       <= '0;
            drop_ret_valid <= 1'b0;
            drop_ret_slot  <= '0;
            sts_overrun    <= 1'b0;
        end else begin
            ret_valid      <= out_valid && out_ready && w_out_slot[XW];
            ret_slot       <= w_out_slot[XW-1:0];
            drop_ret_valid <= in_valid && !w_wr_ready && in_slot[XW];
            drop_ret_slot  <= in_slot[XW-1:0];
            if (in_valid && !w_wr_ready) sts_overrun <= 1'b1;
        end
    )

endmodule : rapids_tile_desc_intake
