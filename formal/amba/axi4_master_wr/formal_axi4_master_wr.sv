// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for axi4_master_wr -- AXI4 write master skid buffer wrapper
//
// Thin passthrough wrapper with three gaxi_skid_buffer instances (AW/W/B).
//
// Properties verified:
//   P1: Reset clears m_axi_awvalid
//   P2: Reset clears m_axi_wvalid
//   P3: Reset clears fub_axi_bvalid
//   P4: AW/W/B handshake stability (valid held until ready)
//   P5: busy at reset depends only on unconstrained external valids

`include "reset_defs.svh"

module formal_axi4_master_wr (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam int IW   = 2;
    localparam int AW   = 8;
    localparam int DW   = 8;
    localparam int UW   = 1;
    localparam int SW   = DW / 8;
    localparam int SKID_AW = 2;
    localparam int SKID_W  = 2;
    localparam int SKID_B  = 2;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg [IW-1:0]   fub_axi_awid;
    (* anyseq *) reg [AW-1:0]   fub_axi_awaddr;
    (* anyseq *) reg [7:0]      fub_axi_awlen;
    (* anyseq *) reg [2:0]      fub_axi_awsize;
    (* anyseq *) reg [1:0]      fub_axi_awburst;
    (* anyseq *) reg            fub_axi_awlock;
    (* anyseq *) reg [3:0]      fub_axi_awcache;
    (* anyseq *) reg [2:0]      fub_axi_awprot;
    (* anyseq *) reg [3:0]      fub_axi_awqos;
    (* anyseq *) reg [3:0]      fub_axi_awregion;
    (* anyseq *) reg [UW-1:0]   fub_axi_awuser;
    (* anyseq *) reg            fub_axi_awvalid;
    (* anyseq *) reg [DW-1:0]   fub_axi_wdata;
    (* anyseq *) reg [SW-1:0]   fub_axi_wstrb;
    (* anyseq *) reg            fub_axi_wlast;
    (* anyseq *) reg [UW-1:0]   fub_axi_wuser;
    (* anyseq *) reg            fub_axi_wvalid;
    (* anyseq *) reg            fub_axi_bready;
    (* anyseq *) reg            m_axi_awready;
    (* anyseq *) reg            m_axi_wready;
    (* anyseq *) reg [IW-1:0]   m_axi_bid;
    (* anyseq *) reg [1:0]      m_axi_bresp;
    (* anyseq *) reg [UW-1:0]   m_axi_buser;
    (* anyseq *) reg            m_axi_bvalid;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire            fub_axi_awready;
    wire            fub_axi_wready;
    wire [IW-1:0]   fub_axi_bid;
    wire [1:0]      fub_axi_bresp;
    wire [UW-1:0]   fub_axi_buser;
    wire            fub_axi_bvalid;
    wire [IW-1:0]   m_axi_awid;
    wire [AW-1:0]   m_axi_awaddr;
    wire [7:0]      m_axi_awlen;
    wire [2:0]      m_axi_awsize;
    wire [1:0]      m_axi_awburst;
    wire            m_axi_awlock;
    wire [3:0]      m_axi_awcache;
    wire [2:0]      m_axi_awprot;
    wire [3:0]      m_axi_awqos;
    wire [3:0]      m_axi_awregion;
    wire [UW-1:0]   m_axi_awuser;
    wire            m_axi_awvalid;
    wire [DW-1:0]   m_axi_wdata;
    wire [SW-1:0]   m_axi_wstrb;
    wire            m_axi_wlast;
    wire [UW-1:0]   m_axi_wuser;
    wire            m_axi_wvalid;
    wire            m_axi_bready;
    wire            busy;

    // =========================================================================
    // DUT
    // =========================================================================
    axi4_master_wr #(
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
        .m_axi_awid      (m_axi_awid),
        .m_axi_awaddr    (m_axi_awaddr),
        .m_axi_awlen     (m_axi_awlen),
        .m_axi_awsize    (m_axi_awsize),
        .m_axi_awburst   (m_axi_awburst),
        .m_axi_awlock    (m_axi_awlock),
        .m_axi_awcache   (m_axi_awcache),
        .m_axi_awprot    (m_axi_awprot),
        .m_axi_awqos     (m_axi_awqos),
        .m_axi_awregion  (m_axi_awregion),
        .m_axi_awuser    (m_axi_awuser),
        .m_axi_awvalid   (m_axi_awvalid),
        .m_axi_awready   (m_axi_awready),
        .m_axi_wdata     (m_axi_wdata),
        .m_axi_wstrb     (m_axi_wstrb),
        .m_axi_wlast     (m_axi_wlast),
        .m_axi_wuser     (m_axi_wuser),
        .m_axi_wvalid    (m_axi_wvalid),
        .m_axi_wready    (m_axi_wready),
        .m_axi_bid       (m_axi_bid),
        .m_axi_bresp     (m_axi_bresp),
        .m_axi_buser     (m_axi_buser),
        .m_axi_bvalid    (m_axi_bvalid),
        .m_axi_bready    (m_axi_bready),
        .busy            (busy)
    );

    // =========================================================================
    // Reset / past-valid
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Properties
    // =========================================================================

    // P1: Reset clears m_axi_awvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_m_awvalid: assert (!m_axi_awvalid);
    end

    // P2: Reset clears m_axi_wvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_m_wvalid: assert (!m_axi_wvalid);
    end

    // P3: Reset clears fub_axi_bvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_fub_bvalid: assert (!fub_axi_bvalid);
    end

    // P4a: AW handshake stability
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_axi_awvalid) && !$past(m_axi_awready))
                ap_m_awvalid_held: assert (m_axi_awvalid);
    end

    // P4b: W handshake stability
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_axi_wvalid) && !$past(m_axi_wready))
                ap_m_wvalid_held: assert (m_axi_wvalid);
    end

    // P4c: B handshake stability (fub side -- output of b skid buffer)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(fub_axi_bvalid) && !$past(fub_axi_bready))
                ap_fub_bvalid_held: assert (fub_axi_bvalid);
    end

    // P5: busy at reset depends only on external valids (all counts are 0)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_busy:
                assert (busy == (fub_axi_awvalid || fub_axi_wvalid || m_axi_bvalid));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_aw_handshake: cover (m_axi_awvalid && m_axi_awready);
            cp_w_handshake:  cover (m_axi_wvalid && m_axi_wready);
            cp_b_handshake:  cover (fub_axi_bvalid && fub_axi_bready);
            cp_busy:         cover (busy);
        end
    end

endmodule
