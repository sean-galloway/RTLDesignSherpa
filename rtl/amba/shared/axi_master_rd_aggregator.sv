// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_master_rd_aggregator
// Purpose: Return-path companion to axi_master_rd_splitter. When a read burst is
//          split into N sub-bursts, the sub-bursts each carry their own RLAST;
//          a master that issued ONE burst must see ONE RLAST (on the original
//          final beat). This aggregator reassembles the R channel: it passes all
//          data beats through unchanged and regenerates RLAST once per ORIGINAL
//          transaction. Symmetric with the WR splitter's B-response
//          consolidation (which the WR side will move into an axi_master_wr
//          aggregator for the same separation of concerns).
//
//          Mechanism: snoop the original AR stream and capture its `arlen` the
//          cycle the transaction is first presented (before any R can return, so
//          it never misses a sub-burst), then count returned R beats and assert
//          fub_rlast on the (arlen+1)-th beat. Total sub-burst beats always equal
//          the original beat count, so this is exact for any split shape and
//          robust to response timing. In-order reassembly (the splitter emits a
//          transaction's sub-bursts, and successive transactions, in order).
//
// Documentation: rtl/amba/shared/axi_master_rd_splitter.sv
`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_master_rd_aggregator #(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_DATA_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1,
    // Outstanding original-transaction budget (arlen tracking FIFO depth).
    parameter int TRACK_DEPTH    = 16,
    parameter int IW = AXI_ID_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH
) (
    input  logic                aclk,
    input  logic                aresetn,

    // ---- AR snoop: the ORIGINAL transaction stream (read-only) -------------
    input  logic                s_arvalid,
    input  logic                s_arready,
    input  logic [7:0]          s_arlen,

    // ---- R in: sub-burst responses (from the splitter's fub_r) -------------
    input  logic                m_rvalid,
    output logic                m_rready,
    input  logic [IW-1:0]       m_rid,
    input  logic [DW-1:0]       m_rdata,
    input  logic [1:0]          m_rresp,
    input  logic                m_rlast,
    input  logic [UW-1:0]       m_ruser,

    // ---- R out: reassembled response (to the master) -----------------------
    output logic                fub_rvalid,
    input  logic                fub_rready,
    output logic [IW-1:0]       fub_rid,
    output logic [DW-1:0]       fub_rdata,
    output logic [1:0]          fub_rresp,
    output logic                fub_rlast,
    output logic [UW-1:0]       fub_ruser
);

    // ---- AR snoop: capture original arlen once per transaction, EARLY -------
    // Capture on the first cycle a new AR is presented (not on accept, which the
    // splitter defers until the final sub-AR — potentially after the first R).
    logic r_cap_pending;
    logic w_ar_accept, w_ar_capture;
    assign w_ar_accept  = s_arvalid && s_arready;
    assign w_ar_capture = s_arvalid && !r_cap_pending;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cap_pending <= 1'b0;
        end else begin
            if (w_ar_accept)        r_cap_pending <= 1'b0;   // ready for next txn
            else if (w_ar_capture)  r_cap_pending <= 1'b1;   // this txn captured
        end
    )

    // ---- arlen tracking FIFO -----------------------------------------------
    logic [7:0] w_arlen_head;
    logic       w_track_valid;
    logic       w_track_pop;

    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (8),
        .DEPTH      (TRACK_DEPTH)
    ) u_arlen_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_ar_capture),
        .wr_data     (s_arlen),
        .rd_ready    (w_track_pop),
        .rd_valid    (w_track_valid),
        .rd_data     (w_arlen_head),
        /* verilator lint_off PINCONNECTEMPTY */
        .wr_ready    (),
        .count       ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ---- R channel: pass data, regenerate RLAST per original burst ---------
    logic [7:0] r_beat;             // beats returned for the AR draining now
    logic       w_beat_acc, w_orig_last;
    assign w_beat_acc  = m_rvalid && fub_rready;
    assign w_orig_last = w_track_valid && (r_beat == w_arlen_head);

    assign fub_rvalid = m_rvalid;
    assign m_rready   = fub_rready;
    assign fub_rid    = m_rid;
    assign fub_rdata  = m_rdata;
    assign fub_rresp  = m_rresp;
    assign fub_ruser  = m_ruser;
    // consolidated RLAST on the original last beat; empty tracker => pass through
    assign fub_rlast  = w_track_valid ? w_orig_last : m_rlast;

    assign w_track_pop = w_beat_acc && w_orig_last;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_beat <= 8'd0;
        end else if (w_beat_acc) begin
            r_beat <= w_orig_last ? 8'd0 : (r_beat + 8'd1);
        end
    )

    // synthesis translate_off
    always_ff @(posedge aclk) begin
        if (aresetn && w_ar_capture) begin
            assert (u_arlen_fifo.wr_ready) else
                $error("axi_master_rd_aggregator: arlen FIFO overflow (increase TRACK_DEPTH)");
        end
    end
    // synthesis translate_on

endmodule : axi_master_rd_aggregator
