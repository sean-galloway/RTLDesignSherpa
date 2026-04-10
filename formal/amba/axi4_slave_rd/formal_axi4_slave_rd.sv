// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for axi4_slave_rd -- AXI4 read slave skid buffer wrapper
//
// Thin passthrough wrapper with two gaxi_skid_buffer instances (AR, R).
// Input side: s_axi_* (slave). Output side: fub_axi_* (memory/backend).
//
// Properties verified:
//   P1: Reset clears fub_axi_arvalid
//   P2: Reset clears s_axi_rvalid
//   P3: AR/R handshake stability
//   P4: busy at reset depends only on external valids

`include "reset_defs.svh"

module formal_axi4_slave_rd (
    input logic clk,
    input logic rst_n
);

    localparam int IW   = 2;
    localparam int AW   = 8;
    localparam int DW   = 8;
    localparam int UW   = 1;
    localparam int SKID_AR = 2;
    localparam int SKID_R  = 2;

    (* anyseq *) reg [IW-1:0]       s_axi_arid;
    (* anyseq *) reg [AW-1:0]       s_axi_araddr;
    (* anyseq *) reg [7:0]          s_axi_arlen;
    (* anyseq *) reg [2:0]          s_axi_arsize;
    (* anyseq *) reg [1:0]          s_axi_arburst;
    (* anyseq *) reg                s_axi_arlock;
    (* anyseq *) reg [3:0]          s_axi_arcache;
    (* anyseq *) reg [2:0]          s_axi_arprot;
    (* anyseq *) reg [3:0]          s_axi_arqos;
    (* anyseq *) reg [3:0]          s_axi_arregion;
    (* anyseq *) reg [UW-1:0]       s_axi_aruser;
    (* anyseq *) reg                s_axi_arvalid;
    (* anyseq *) reg                s_axi_rready;
    (* anyseq *) reg                fub_axi_arready;
    (* anyseq *) reg [IW-1:0]       fub_axi_rid;
    (* anyseq *) reg [DW-1:0]       fub_axi_rdata;
    (* anyseq *) reg [1:0]          fub_axi_rresp;
    (* anyseq *) reg                fub_axi_rlast;
    (* anyseq *) reg [UW-1:0]       fub_axi_ruser;
    (* anyseq *) reg                fub_axi_rvalid;

    wire                s_axi_arready;
    wire [IW-1:0]       s_axi_rid;
    wire [DW-1:0]       s_axi_rdata;
    wire [1:0]          s_axi_rresp;
    wire                s_axi_rlast;
    wire [UW-1:0]       s_axi_ruser;
    wire                s_axi_rvalid;
    wire [IW-1:0]       fub_axi_arid;
    wire [AW-1:0]       fub_axi_araddr;
    wire [7:0]          fub_axi_arlen;
    wire [2:0]          fub_axi_arsize;
    wire [1:0]          fub_axi_arburst;
    wire                fub_axi_arlock;
    wire [3:0]          fub_axi_arcache;
    wire [2:0]          fub_axi_arprot;
    wire [3:0]          fub_axi_arqos;
    wire [3:0]          fub_axi_arregion;
    wire [UW-1:0]       fub_axi_aruser;
    wire                fub_axi_arvalid;
    wire                fub_axi_rready;
    wire                busy;

    axi4_slave_rd #(
        .SKID_DEPTH_AR  (SKID_AR),
        .SKID_DEPTH_R   (SKID_R),
        .AXI_ID_WIDTH   (IW),
        .AXI_ADDR_WIDTH (AW),
        .AXI_DATA_WIDTH (DW),
        .AXI_USER_WIDTH (UW)
    ) dut (
        .aclk            (clk),
        .aresetn         (rst_n),
        .s_axi_arid      (s_axi_arid),
        .s_axi_araddr    (s_axi_araddr),
        .s_axi_arlen     (s_axi_arlen),
        .s_axi_arsize    (s_axi_arsize),
        .s_axi_arburst   (s_axi_arburst),
        .s_axi_arlock    (s_axi_arlock),
        .s_axi_arcache   (s_axi_arcache),
        .s_axi_arprot    (s_axi_arprot),
        .s_axi_arqos     (s_axi_arqos),
        .s_axi_arregion  (s_axi_arregion),
        .s_axi_aruser    (s_axi_aruser),
        .s_axi_arvalid   (s_axi_arvalid),
        .s_axi_arready   (s_axi_arready),
        .s_axi_rid       (s_axi_rid),
        .s_axi_rdata     (s_axi_rdata),
        .s_axi_rresp     (s_axi_rresp),
        .s_axi_rlast     (s_axi_rlast),
        .s_axi_ruser     (s_axi_ruser),
        .s_axi_rvalid    (s_axi_rvalid),
        .s_axi_rready    (s_axi_rready),
        .fub_axi_arid    (fub_axi_arid),
        .fub_axi_araddr  (fub_axi_araddr),
        .fub_axi_arlen   (fub_axi_arlen),
        .fub_axi_arsize  (fub_axi_arsize),
        .fub_axi_arburst (fub_axi_arburst),
        .fub_axi_arlock  (fub_axi_arlock),
        .fub_axi_arcache (fub_axi_arcache),
        .fub_axi_arprot  (fub_axi_arprot),
        .fub_axi_arqos   (fub_axi_arqos),
        .fub_axi_arregion(fub_axi_arregion),
        .fub_axi_aruser  (fub_axi_aruser),
        .fub_axi_arvalid (fub_axi_arvalid),
        .fub_axi_arready (fub_axi_arready),
        .fub_axi_rid     (fub_axi_rid),
        .fub_axi_rdata   (fub_axi_rdata),
        .fub_axi_rresp   (fub_axi_rresp),
        .fub_axi_rlast   (fub_axi_rlast),
        .fub_axi_ruser   (fub_axi_ruser),
        .fub_axi_rvalid  (fub_axi_rvalid),
        .fub_axi_rready  (fub_axi_rready),
        .busy            (busy)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // P1: Reset clears fub_axi_arvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_fub_arvalid: assert (!fub_axi_arvalid);
    end

    // P2: Reset clears s_axi_rvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_s_rvalid: assert (!s_axi_rvalid);
    end

    // P3a: fub AR handshake stability
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(fub_axi_arvalid) && !$past(fub_axi_arready))
                ap_fub_arvalid_held: assert (fub_axi_arvalid);
    end

    // P3b: s R handshake stability
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(s_axi_rvalid) && !$past(s_axi_rready))
                ap_s_rvalid_held: assert (s_axi_rvalid);
    end

    // P4: busy at reset depends only on external valids
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_busy:
                assert (busy == (s_axi_arvalid || fub_axi_rvalid));
    end

    // Covers
    always @(posedge clk) begin
        if (rst_n) begin
            cp_fub_ar_hs: cover (fub_axi_arvalid && fub_axi_arready);
            cp_s_r_hs:    cover (s_axi_rvalid && s_axi_rready);
            cp_busy:      cover (busy);
        end
    end

endmodule
