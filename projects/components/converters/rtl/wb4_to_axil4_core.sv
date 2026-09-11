// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_to_axil4_core
// Purpose: Wishbone command/response queues (the FUB side of wb4_slave) to
//          the five AXI4-Lite channels of an axil4 master pair.
//
// Documentation: projects/components/converters/docs/converter_mas/ch03_protocol_blocks/11_wb4_to_axil4.md
// Subsystem: converters
//
// Author: sean galloway
// Created: 2026-09-10
//
//==============================================================================
// Description:
//   The mirror of axil4_to_wb4_core, and the harder direction. Going the
//   other way, AXI4-Lite's two response channels have to be merged into
//   Wishbone's single in-order termination stream.
//
//   B4 terminates in ISSUE ORDER. AXI4-Lite's B and R channels are
//   independent and a slave may answer them in any order, so a read issued
//   after a write can complete before it. This block therefore records the
//   direction of every command it issues in an in-order side queue and only
//   releases the response at the head: a completed out-of-order response
//   waits in its channel's skid until its predecessors have retired. That
//   is what makes the Wishbone side legal, and it is the whole reason this
//   direction needs more than wires.
//
//   Ordering cost: a slow write sitting at the head holds back a read that
//   finished behind it. OUTSTANDING = 1 avoids the question entirely and is
//   the default; raise it only when the AXI slave answers roughly in order,
//   or the head-of-line wait eats the benefit.
//
//   No width conversion. Both sides share ADDR_WIDTH and DATA_WIDTH; put a
//   width converter in front when they differ.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH, DATA_WIDTH - shared by both sides
//   OUTSTANDING            - commands issued and not yet answered; also the
//                            direction queue depth. 1 = strictly serialised
//   AXIL_PROT              - the ARPROT/AWPROT value driven on every command
//                            (Wishbone carries no protection bits)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - wb4_to_axil4.sv (wrapper: wb4_slave + this + the axil4 masters)
//   - axil4_to_wb4_core.sv (the opposite direction, which is simpler)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/converters/dv/tests/test_wb4_to_axil4.py
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wb4_to_axil4_core
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int OUTSTANDING = 1,
    parameter logic [2:0] AXIL_PROT = 3'b000,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW/8,
    parameter int STW = WB4_STATUS_WIDTH
)
(
    input  logic              aclk,
    input  logic              aresetn,

    // Wishbone command / response queues (the wb4_slave FUB side)
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_we,
    input  logic [AW-1:0]     cmd_adr,
    input  logic [DW-1:0]     cmd_dat,
    input  logic [SW-1:0]     cmd_sel,

    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [STW-1:0]    rsp_status,
    output logic [DW-1:0]     rsp_dat,

    // AXI4-Lite master channels (the fub_* side of the axil4 masters)
    output logic [AW-1:0]     fub_awaddr,
    output logic [2:0]        fub_awprot,
    output logic              fub_awvalid,
    input  logic              fub_awready,
    output logic [DW-1:0]     fub_wdata,
    output logic [SW-1:0]     fub_wstrb,
    output logic              fub_wvalid,
    input  logic              fub_wready,
    input  logic [1:0]        fub_bresp,
    input  logic              fub_bvalid,
    output logic              fub_bready,

    output logic [AW-1:0]     fub_araddr,
    output logic [2:0]        fub_arprot,
    output logic              fub_arvalid,
    input  logic              fub_arready,
    input  logic [DW-1:0]     fub_rdata,
    input  logic [1:0]        fub_rresp,
    input  logic              fub_rvalid,
    output logic              fub_rready
);

    localparam int CW = $clog2(OUTSTANDING + 1);

    // ------------------------------------------------------------------------
    // Issue: one command becomes either AW+W or AR.
    //
    // A write is only launched when BOTH address and data channels can take
    // it in the same clock. Splitting them would let AW go while W stalled,
    // and the count that bounds OUTSTANDING would then describe a half-issued
    // transfer.
    // ------------------------------------------------------------------------
    logic w_room, w_issue, w_wr_go, w_rd_go;
    logic w_side_wr_ready, w_side_rd_valid, w_side_head_we, w_side_rd_ready;

    assign w_room  = w_side_wr_ready;
    assign w_wr_go = cmd_valid &&  cmd_we && w_room && fub_awready && fub_wready;
    assign w_rd_go = cmd_valid && !cmd_we && w_room && fub_arready;

    assign fub_awvalid = cmd_valid &&  cmd_we && w_room && fub_wready;
    assign fub_wvalid  = cmd_valid &&  cmd_we && w_room && fub_awready;
    assign fub_arvalid = cmd_valid && !cmd_we && w_room;

    assign fub_awaddr  = cmd_adr;
    assign fub_araddr  = cmd_adr;
    assign fub_awprot  = AXIL_PROT;
    assign fub_arprot  = AXIL_PROT;
    assign fub_wdata   = cmd_dat;
    assign fub_wstrb   = cmd_sel;

    assign w_issue   = w_wr_go || w_rd_go;
    assign cmd_ready = w_issue;

    // Direction of each issued command, in order. Mux read: the head is
    // valid in the clock of its handshake, which is when the response below
    // is formed.
    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (1),
        .DEPTH      (OUTSTANDING < 2 ? 2 : OUTSTANDING)
    ) side_queue (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_issue),
        .wr_ready    (w_side_wr_ready),
        .wr_data     (cmd_we),
        .rd_ready    (w_side_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_side_rd_valid),
        .rd_data     (w_side_head_we)
    );

    // Outstanding bound. The side queue's depth alone would not do it: its
    // floor is 2 so OUTSTANDING=1 still needs an explicit count.
    logic [CW-1:0] r_open;
    logic          w_retire;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_open <= '0;
        else                        r_open <= r_open + CW'(w_issue) - CW'(w_retire);
    )

    // ------------------------------------------------------------------------
    // Retire: only the head's channel may complete, so Wishbone sees its
    // terminations in issue order however AXI answered.
    // ------------------------------------------------------------------------
    logic w_head_is_wr, w_head_ready;
    assign w_head_is_wr = w_side_rd_valid && w_side_head_we;
    assign w_head_ready = w_side_rd_valid && (w_head_is_wr ? fub_bvalid : fub_rvalid);

    assign rsp_valid  = w_head_ready;
    assign rsp_status = (w_head_is_wr ? fub_bresp : fub_rresp) == 2'b00
                        ? STW'(WB4_RSP_ACK) : STW'(WB4_RSP_ERR);
    assign rsp_dat    = fub_rdata;

    assign w_retire         = rsp_valid && rsp_ready;
    assign w_side_rd_ready  = w_retire;
    assign fub_bready       = w_retire &&  w_head_is_wr;
    assign fub_rready       = w_retire && !w_head_is_wr;

    // SLVERR and DECERR both become a Wishbone ERR: B4 has one error
    // termination and no way to say which kind. RTY is never produced -- an
    // AXI slave has no way to ask for a retry.
    /* verilator lint_off UNUSEDSIGNAL */
    logic w_unused;
    assign w_unused = ^{r_open};
    /* verilator lint_on UNUSEDSIGNAL */

`ifdef FORMAL
    logic f_past_valid;
    initial f_past_valid = 1'b0;
    always_ff @(posedge aclk) f_past_valid <= 1'b1;
    always_ff @(posedge aclk) if (f_past_valid && aresetn && $past(aresetn)) begin
        // A write takes both channels together, never one alone.
        assert (!(fub_awvalid && fub_awready) || (fub_wvalid && fub_wready));
        assert (!(fub_wvalid && fub_wready) || (fub_awvalid && fub_awready));
        // Never a write and a read issue in the same clock.
        assert (!(w_wr_go && w_rd_go));
        // Only the head's channel is consumed.
        assert (!(fub_bready && fub_rready));
        assert (!fub_bready || w_head_is_wr);
        assert (!fub_rready || (w_side_rd_valid && !w_side_head_we));
        // The outstanding bound holds.
        assert (32'(r_open) <= OUTSTANDING);
    end
`endif

endmodule : wb4_to_axil4_core
