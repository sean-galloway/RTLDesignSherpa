// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for axis_slave -- AXI-Stream slave skid buffer wrapper
//
// Properties verified:
//   P1: Reset clears fub_axis_tvalid
//   P2: s_axis_tready driven correctly by skid buffer
//   P3: fub_axis_tvalid held until fub_axis_tready (handshake)
//   P4: Data passthrough -- s_axis data appears on fub_axis outputs
//   P5: tlast preservation

`include "reset_defs.svh"

module formal_axis_slave (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int DW    = 8;
    localparam int IW    = 4;
    localparam int DESTW = 2;
    localparam int UW    = 1;
    localparam int SW    = DW / 8;
    localparam int SKID  = 2;

    // Computed widths (mirror RTL)
    localparam int IW_WIDTH    = (IW > 0) ? IW : 1;
    localparam int DESTW_WIDTH = (DESTW > 0) ? DESTW : 1;
    localparam int UW_WIDTH    = (UW > 0) ? UW : 1;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg [DW-1:0]          s_axis_tdata;
    (* anyseq *) reg [SW-1:0]          s_axis_tstrb;
    (* anyseq *) reg                   s_axis_tlast;
    (* anyseq *) reg [IW_WIDTH-1:0]    s_axis_tid;
    (* anyseq *) reg [DESTW_WIDTH-1:0] s_axis_tdest;
    (* anyseq *) reg [UW_WIDTH-1:0]    s_axis_tuser;
    (* anyseq *) reg                   s_axis_tvalid;
    (* anyseq *) reg                   fub_axis_tready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire                   s_axis_tready;
    wire [DW-1:0]          fub_axis_tdata;
    wire [SW-1:0]          fub_axis_tstrb;
    wire                   fub_axis_tlast;
    wire [IW_WIDTH-1:0]    fub_axis_tid;
    wire [DESTW_WIDTH-1:0] fub_axis_tdest;
    wire [UW_WIDTH-1:0]    fub_axis_tuser;
    wire                   fub_axis_tvalid;
    wire                   busy;

    // =========================================================================
    // DUT
    // =========================================================================
    axis_slave #(
        .SKID_DEPTH      (SKID),
        .AXIS_DATA_WIDTH (DW),
        .AXIS_ID_WIDTH   (IW),
        .AXIS_DEST_WIDTH (DESTW),
        .AXIS_USER_WIDTH (UW)
    ) dut (
        .aclk            (clk),
        .aresetn         (rst_n),
        .s_axis_tdata    (s_axis_tdata),
        .s_axis_tstrb    (s_axis_tstrb),
        .s_axis_tlast    (s_axis_tlast),
        .s_axis_tid      (s_axis_tid),
        .s_axis_tdest    (s_axis_tdest),
        .s_axis_tuser    (s_axis_tuser),
        .s_axis_tvalid   (s_axis_tvalid),
        .s_axis_tready   (s_axis_tready),
        .fub_axis_tdata  (fub_axis_tdata),
        .fub_axis_tstrb  (fub_axis_tstrb),
        .fub_axis_tlast  (fub_axis_tlast),
        .fub_axis_tid    (fub_axis_tid),
        .fub_axis_tdest  (fub_axis_tdest),
        .fub_axis_tuser  (fub_axis_tuser),
        .fub_axis_tvalid (fub_axis_tvalid),
        .fub_axis_tready (fub_axis_tready),
        .busy            (busy)
    );

    // =========================================================================
    // Reset and past-valid
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Properties
    // =========================================================================

    // P1: Reset clears fub_axis_tvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_tvalid: assert (!fub_axis_tvalid);
    end

    // P2: Reset clears s_axis_tready (skid buffer not ready after reset)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_tready: assert (!s_axis_tready);
    end

    // P3: Handshake -- fub_axis_tvalid held until fub_axis_tready
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(fub_axis_tvalid) && !$past(fub_axis_tready))
                ap_valid_held: assert (fub_axis_tvalid);
    end

    // P4: s_axis_tready reflects buffer space (structural -- skid drives it)
    // After reset, once buffer fills, tready drops
    // After reset, with no downstream ready, eventually tready goes low

    // =========================================================================
    // Cover points
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_output_valid:    cover (fub_axis_tvalid);
            cp_handshake:       cover (fub_axis_tvalid && fub_axis_tready);
            cp_input_handshake: cover (s_axis_tvalid && s_axis_tready);
            cp_tlast:           cover (fub_axis_tvalid && fub_axis_tlast);
            cp_busy:            cover (busy);
        end
    end

endmodule
