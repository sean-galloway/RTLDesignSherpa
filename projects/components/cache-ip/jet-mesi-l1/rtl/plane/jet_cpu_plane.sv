// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_cpu_plane
// Purpose:
//   CPU plane for the jet lockup-free MESI L1 (cache-ip plane
//   restructure, Task 4): the CPU-side protocol-generation boundary.
//   Closes the GAXI CPU slave (l1_cpu_frontend), the D-6 request skid
//   (gaxi_fifo_sync) that adapts the frontend's pulse-style req_valid to
//   jet's hold-until-accepted lookup contract, and the J4 response
//   sequencer (jet_rsp_seq, in-issue-order release). Extracted from
//   jet_top.sv by move-don't-edit; the response-staging-room tap stays
//   internal to this plane.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch01_overview/02_port_list.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_cpu_plane
//==============================================================================
// Description:
//   The CPU-side protocol-generation plane (the jet variant of the CPU
//   seam; every CPU-generation variant owns its CPU plane).  Unlike
//   amber's pulse-style boundary, jet's lookup stage holds a request
//   presented until lkup_ready -- the D-6 request skid sits between the
//   frontend and the coherence core: the frontend handshakes into the
//   skid (wr_ready = ctrl_req_ready, the pulse lands once), the skid
//   holds the request presented until lkup_ready.  The skid is BYPASSED
//   while it is empty (TASK-003 step 2): the arriving request stands at
//   the lookup in its own handshake cycle, so the tag read overlaps the
//   cycle the skid used to cost every request, and it enters the skid only
//   when the lookup does not take it in that cycle -- from then on the
//   skid presents it, same fields, until lkup_ready (the hold-until-
//   accepted contract is unchanged; the request reaches the lookup a cycle
//   sooner).  The frontend's ready
//   is gated with the synchronized reset (without the gate the empty
//   skid's wr_ready is high through the reset-sync tail, and a request
//   handshaked there would be dropped by the FIFO's own reset) and with
//   the coherence core's sticky CTRL_ERROR (a dead cache admits no
//   work).
//
//   On the response side jet releases are level-held (jet_rsp_seq):
//   rsp_ready_i is the frontend staging FIFO's room (the read-only
//   u_frontend.stage_wr_ready tap, the sanctioned l1_core pattern) and
//   the FIFO write is the same qualifier, so a backed-up CPU response
//   channel backpressures the release pointer instead of overflowing the
//   depth-2 staging queue.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per l1_pkg defaults
//     Type: int
//   MSHR_COUNT:
//     Description: response-sequencer depth follows the J1 file
//                  (RSP_DEPTH = MSHR_COUNT + 2)
//     Type: int
//
//------------------------------------------------------------------------------
// Notes:
//   - Single clock / active-low reset (aclk / aresetn). The plane is
//     reset-synchronized by its top (jet_top / jet_ace_top), so this
//     module consumes the synchronized reset.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: jet_top, jet_ace_top
//   - Instantiates: l1_cpu_frontend, gaxi_fifo_sync (request skid),
//     jet_rsp_seq
//   - Package: jet_pkg, l1_pkg
//
//==============================================================================

module jet_cpu_plane
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int SETS           = AMBER_SETS,
    parameter int WAYS           = AMBER_WAYS,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int MSHR_COUNT     = jet_pkg::MSHR_COUNT,
    localparam int STRB_W      = BUS_WIDTH / 8,
    localparam int CPU_REQ_W   = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W   = BUS_WIDTH,
    localparam int RSP_DEPTH   = MSHR_COUNT + 2,
    localparam int SEQ_W       = $clog2(RSP_DEPTH)
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    // ------------------------------------------------------------------
    // CPU GAXI slave (MAS ch03/01)
    // ------------------------------------------------------------------
    input  logic                        cpu_req_wr_valid,
    output logic                        cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu_req_wr_data,
    output logic                        cpu_rsp_rd_valid,
    input  logic                        cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu_rsp_rd_data,

    // ------------------------------------------------------------------
    // Lookup seam to the coherence core plane (the D-6 skid's held
    // request; the unpack matches jet_control's lkup_* pin order)
    // ------------------------------------------------------------------
    output logic                        lkup_valid,
    output logic [ADDR_WIDTH-1:0]       lkup_addr,
    output logic                        lkup_we,
    output logic [STRB_W-1:0]           lkup_be,
    output logic [BUS_WIDTH-1:0]        lkup_wdata,
    input  logic                        lkup_ready,

    // CTRL_ERROR dead-stop from the coherence core plane (gates the
    // frontend's request ready)
    input  logic                        ctrl_error,

    // ------------------------------------------------------------------
    // Response-sequencer seam to the coherence core plane (J4:
    // in-issue-order release; the tag is granted at the lookup accept)
    // ------------------------------------------------------------------
    input  logic                        ctrl_tag_req,
    output logic                        rsp_tag_gnt,
    output logic [SEQ_W-1:0]            rsp_tag,
    input  logic                        ctrl_cpl_valid,
    input  logic [SEQ_W-1:0]            ctrl_cpl_tag,
    input  logic [BUS_WIDTH-1:0]        ctrl_cpl_data
);

    // ------------------------------------------------------------------
    // frontend <-> control request/response contract, with the D-6
    // request skid between (see the header: the frontend's pulse-style
    // req_valid cannot drive jet's hold-until-accepted lookup directly)
    // ------------------------------------------------------------------
    logic                     fe_req_valid;
    logic [ADDR_WIDTH-1:0]    fe_req_addr;
    logic                     fe_req_we;
    logic [STRB_W-1:0]        fe_req_be;
    logic [BUS_WIDTH-1:0]     fe_req_wdata;
    logic                     ctrl_req_ready;
    logic                     rsp_valid;
    logic [BUS_WIDTH-1:0]     rsp_data;
    logic                     rsp_room;     // frontend staging FIFO room

    // request skid: the frontend's one-cycle pulse lands here; the skid
    // holds the request presented to the lookup stage until lkup_ready.
    // The frontend's ready is gated with the synchronized reset: without
    // the gate the empty skid's wr_ready is high through the reset-sync
    // tail, and a request handshaked there would be dropped by the FIFO's
    // own reset (the pair-rig fabric may present a request the cycle the
    // port aresetn releases).  And with CTRL_ERROR latched the boundary
    // dead-stops (amber's contract: a dead cache admits no work).
    logic                     skid_rd_valid;
    logic [CPU_REQ_W-1:0]     skid_rd_data;
    logic                     skid_wr_ready;
    logic                     w_skid_bypass;   // the arriving request is presented to the lookup this cycle
    logic [CPU_REQ_W-1:0]     w_fe_req_data;
    logic [CPU_REQ_W-1:0]     w_lkup_data;

    assign ctrl_req_ready = skid_wr_ready & aresetn & ~ctrl_error;

    // Skid bypass (TASK-003 step 2, 2026-11-10): an empty skid is
    // transparent.  The arriving request stands at the lookup in its own
    // handshake cycle (the tag read on port A happens in this cycle, so the
    // classify follows the handshake by one cycle, not two); it enters the
    // skid only when the lookup does not capture it here, and the skid then
    // presents the same fields until lkup_ready.  A non-empty skid is never
    // bypassed (issue order = skid order), and the frontend's ready stays
    // the skid's room, so the write below never meets a full skid.
    assign w_fe_req_data = {fe_req_addr, fe_req_we, fe_req_be, fe_req_wdata};
    assign w_skid_bypass = fe_req_valid & ~skid_rd_valid;

    gaxi_fifo_sync #(
        .DATA_WIDTH (CPU_REQ_W),
        .DEPTH      (2)
    ) u_req_skid (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (fe_req_valid & ~(w_skid_bypass & lkup_ready)),
        .wr_ready    (skid_wr_ready),
        .wr_data     (w_fe_req_data),
        .rd_ready    (lkup_ready),
        .count       (),
        .rd_valid    (skid_rd_valid),
        .rd_data     (skid_rd_data)
    );

    l1_cpu_frontend #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_frontend (
        .clk               (aclk),
        .rst_n             (aresetn),
        .cpu_req_wr_valid  (cpu_req_wr_valid),
        .cpu_req_wr_ready  (cpu_req_wr_ready),
        .cpu_req_wr_data   (cpu_req_wr_data),
        .cpu_rsp_rd_valid  (cpu_rsp_rd_valid),
        .cpu_rsp_rd_ready  (cpu_rsp_rd_ready),
        .cpu_rsp_rd_data   (cpu_rsp_rd_data),
        .req_valid         (fe_req_valid),
        .req_addr          (fe_req_addr),
        .req_we            (fe_req_we),
        .req_be            (fe_req_be),
        .req_wdata         (fe_req_wdata),
        .ctrl_req_ready    (ctrl_req_ready),
        .ctrl_rsp_valid    (rsp_valid & rsp_room),
        .ctrl_rsp_data     (rsp_data)
    );

    // response staging room (the read-only tap; the FIFO write and the
    // rsp_seq release are the same qualifier, so the depth-2 staging
    // queue can never overflow)
    assign rsp_room = u_frontend.stage_wr_ready;

    // the request at the lookup window: the skid's head, or the arriving
    // request while the skid is empty (bypass)
    assign w_lkup_data = skid_rd_valid ? skid_rd_data : w_fe_req_data;
    assign lkup_valid  = skid_rd_valid | w_skid_bypass;
    assign lkup_addr   = w_lkup_data[CPU_REQ_W-1 -: ADDR_WIDTH];
    assign lkup_we     = w_lkup_data[BUS_WIDTH + STRB_W];
    assign lkup_be     = w_lkup_data[BUS_WIDTH + STRB_W - 1 -: STRB_W];
    assign lkup_wdata  = w_lkup_data[BUS_WIDTH-1:0];

    // ------------------------------------------------------------------
    // Response sequencer (J4: in-issue-order release); the frontend's
    // response staging always accepts (same contract as amber's core).
    // ------------------------------------------------------------------
    jet_rsp_seq #(
        .RSP_DEPTH (RSP_DEPTH),
        .BUS_WIDTH (BUS_WIDTH),
        .SEQ_W     (SEQ_W)
    ) u_rsp (
        .clk         (aclk),
        .rst_n       (aresetn),
        .tag_req_i   (ctrl_tag_req),
        .tag_gnt_o   (rsp_tag_gnt),
        .tag_o       (rsp_tag),
        .cpl_i       (ctrl_cpl_valid),
        .cpl_tag_i   (ctrl_cpl_tag),
        .cpl_data_i  (ctrl_cpl_data),
        .rsp_valid_o (rsp_valid),
        .rsp_data_o  (rsp_data),
        .rsp_ready_i (rsp_room)
    );

endmodule : jet_cpu_plane
