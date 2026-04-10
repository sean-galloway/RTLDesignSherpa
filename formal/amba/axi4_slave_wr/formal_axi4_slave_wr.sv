// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for axi4_slave_wr -- AXI4 write slave skid buffer wrapper
//
// Thin passthrough wrapper with three gaxi_skid_buffer instances (AW/W/B).
// Input side: s_axi_* (from master). Output side: fub_axi_* (to memory).
//
// Properties verified:
//   P1: Reset clears fub_axi_awvalid
//   P2: Reset clears fub_axi_wvalid
//   P3: Reset clears s_axi_bvalid
//   P4: AW/W/B handshake stability
//   P5: busy at reset depends only on external valids

`include "reset_defs.svh"

module formal_axi4_slave_wr (
    input logic clk,
    input logic rst_n
);

    localparam int IW = 2;
    localparam int AW = 8;
    localparam int DW = 8;
    localparam int UW = 1;
    localparam int SW = DW / 8;
    localparam int SKID_AW = 2;
    localparam int SKID_W  = 2;
    localparam int SKID_B  = 2;

    (* anyseq *) reg [IW-1:0]   s_axi_awid;
    (* anyseq *) reg [AW-1:0]   s_axi_awaddr;
    (* anyseq *) reg [7:0]      s_axi_awlen;
    (* anyseq *) reg [2:0]      s_axi_awsize;
    (* anyseq *) reg [1:0]      s_axi_awburst;
    (* anyseq *) reg            s_axi_awlock;
    (* anyseq *) reg [3:0]      s_axi_awcache;
    (* anyseq *) reg [2:0]      s_axi_awprot;
    (* anyseq *) reg [3:0]      s_axi_awqos;
    (* anyseq *) reg [3:0]      s_axi_awregion;
    (* anyseq *) reg [UW-1:0]   s_axi_awuser;
    (* anyseq *) reg            s_axi_awvalid;
    (* anyseq *) reg [DW-1:0]   s_axi_wdata;
    (* anyseq *) reg [SW-1:0]   s_axi_wstrb;
    (* anyseq *) reg            s_axi_wlast;
    (* anyseq *) reg [UW-1:0]   s_axi_wuser;
    (* anyseq *) reg            s_axi_wvalid;
    (* anyseq *) reg            s_axi_bready;
    (* anyseq *) reg            fub_axi_awready;
    (* anyseq *) reg            fub_axi_wready;
    (* anyseq *) reg [IW-1:0]   fub_axi_bid;
    (* anyseq *) reg [1:0]      fub_axi_bresp;
    (* anyseq *) reg [UW-1:0]   fub_axi_buser;
    (* anyseq *) reg            fub_axi_bvalid;

    wire            s_axi_awready;
    wire            s_axi_wready;
    wire [IW-1:0]   s_axi_bid;
    wire [1:0]      s_axi_bresp;
    wire [UW-1:0]   s_axi_buser;
    wire            s_axi_bvalid;
    wire [IW-1:0]   fub_axi_awid;
    wire [AW-1:0]   fub_axi_awaddr;
    wire [7:0]      fub_axi_awlen;
    wire [2:0]      fub_axi_awsize;
    wire [1:0]      fub_axi_awburst;
    wire            fub_axi_awlock;
    wire [3:0]      fub_axi_awcache;
    wire [2:0]      fub_axi_awprot;
    wire [3:0]      fub_axi_awqos;
    wire [3:0]      fub_axi_awregion;
    wire [UW-1:0]   fub_axi_awuser;
    wire            fub_axi_awvalid;
    wire [DW-1:0]   fub_axi_wdata;
    wire [SW-1:0]   fub_axi_wstrb;
    wire            fub_axi_wlast;
    wire [UW-1:0]   fub_axi_wuser;
    wire            fub_axi_wvalid;
    wire            fub_axi_bready;
    wire            busy;

    axi4_slave_wr #(
        .SKID_DEPTH_AW  (SKID_AW),
        .SKID_DEPTH_W   (SKID_W),
        .SKID_DEPTH_B   (SKID_B),
        .AXI_ID_WIDTH   (IW),
        .AXI_ADDR_WIDTH (AW),
        .AXI_DATA_WIDTH (DW),
        .AXI_USER_WIDTH (UW)
    ) dut (
        .aclk            (clk),
        .aresetn         (rst_n),
        .s_axi_awid      (s_axi_awid),
        .s_axi_awaddr    (s_axi_awaddr),
        .s_axi_awlen     (s_axi_awlen),
        .s_axi_awsize    (s_axi_awsize),
        .s_axi_awburst   (s_axi_awburst),
        .s_axi_awlock    (s_axi_awlock),
        .s_axi_awcache   (s_axi_awcache),
        .s_axi_awprot    (s_axi_awprot),
        .s_axi_awqos     (s_axi_awqos),
        .s_axi_awregion  (s_axi_awregion),
        .s_axi_awuser    (s_axi_awuser),
        .s_axi_awvalid   (s_axi_awvalid),
        .s_axi_awready   (s_axi_awready),
        .s_axi_wdata     (s_axi_wdata),
        .s_axi_wstrb     (s_axi_wstrb),
        .s_axi_wlast     (s_axi_wlast),
        .s_axi_wuser     (s_axi_wuser),
        .s_axi_wvalid    (s_axi_wvalid),
        .s_axi_wready    (s_axi_wready),
        .s_axi_bid       (s_axi_bid),
        .s_axi_bresp     (s_axi_bresp),
        .s_axi_buser     (s_axi_buser),
        .s_axi_bvalid    (s_axi_bvalid),
        .s_axi_bready    (s_axi_bready),
        .fub_axi_awid    (fub_axi_awid),
        .fub_axi_awaddr  (fub_axi_awaddr),
        .fub_axi_awlen   (fub_axi_awlen),
        .fub_axi_awsize  (fub_axi_awsize),
        .fub_axi_awburst (fub_axi_awburst),
        .fub_axi_awlock  (fub_axi_awlock),
        .fub_axi_awcache (fub_axi_awcache),
        .fub_axi_awprot  (fub_axi_awprot),
        .fub_axi_awqos   (fub_axi_awqos),
        .fub_axi_awregion(fub_axi_awregion),
        .fub_axi_awuser  (fub_axi_awuser),
        .fub_axi_awvalid (fub_axi_awvalid),
        .fub_axi_awready (fub_axi_awready),
        .fub_axi_wdata   (fub_axi_wdata),
        .fub_axi_wstrb   (fub_axi_wstrb),
        .fub_axi_wlast   (fub_axi_wlast),
        .fub_axi_wuser   (fub_axi_wuser),
        .fub_axi_wvalid  (fub_axi_wvalid),
        .fub_axi_wready  (fub_axi_wready),
        .fub_axi_bid     (fub_axi_bid),
        .fub_axi_bresp   (fub_axi_bresp),
        .fub_axi_buser   (fub_axi_buser),
        .fub_axi_bvalid  (fub_axi_bvalid),
        .fub_axi_bready  (fub_axi_bready),
        .busy            (busy)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // P1: Reset clears fub_axi_awvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_fub_awvalid: assert (!fub_axi_awvalid);
    end

    // P2: Reset clears fub_axi_wvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_fub_wvalid: assert (!fub_axi_wvalid);
    end

    // P3: Reset clears s_axi_bvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_s_bvalid: assert (!s_axi_bvalid);
    end

    // P4a: fub AW handshake stability
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(fub_axi_awvalid) && !$past(fub_axi_awready))
                ap_fub_awvalid_held: assert (fub_axi_awvalid);
    end

    // P4b: fub W handshake stability
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(fub_axi_wvalid) && !$past(fub_axi_wready))
                ap_fub_wvalid_held: assert (fub_axi_wvalid);
    end

    // P4c: s B handshake stability
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(s_axi_bvalid) && !$past(s_axi_bready))
                ap_s_bvalid_held: assert (s_axi_bvalid);
    end

    // P5: busy at reset depends only on external valids
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_busy:
                assert (busy == (s_axi_awvalid || s_axi_wvalid || fub_axi_bvalid));
    end

    always @(posedge clk) begin
        if (rst_n) begin
            cp_aw_hs: cover (fub_axi_awvalid && fub_axi_awready);
            cp_w_hs:  cover (fub_axi_wvalid && fub_axi_wready);
            cp_b_hs:  cover (s_axi_bvalid && s_axi_bready);
            cp_busy:  cover (busy);
        end
    end

endmodule
