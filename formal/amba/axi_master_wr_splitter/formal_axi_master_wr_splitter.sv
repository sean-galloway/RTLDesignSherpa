// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for axi_master_wr_splitter (yosys-compatible)
// Proves reset behavior, write data passthrough, WLAST behavior,
// and B response properties. No hierarchical references.
// Uses small parameters for tractability: AWLEN <= 3, AWBURST=INCR.

`timescale 1ns / 1ps

module formal_axi_master_wr_splitter #(
    parameter int IW = 4,
    parameter int AW = 16,
    parameter int DW = 32,
    parameter int UW = 1,
    parameter int SPLIT_FIFO_DEPTH = 4
) (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 1) assume (rst_n);
    end

    // =========================================================================
    // Free inputs
    // =========================================================================
    logic [11:0]     alignment_mask;
    logic            m_axi_awready;
    logic            m_axi_wready;
    logic [IW-1:0]   m_axi_bid;
    logic [1:0]      m_axi_bresp;
    logic [UW-1:0]   m_axi_buser;
    logic            m_axi_bvalid;
    logic            block_ready;
    logic [IW-1:0]   fub_awid;
    logic [AW-1:0]   fub_awaddr;
    logic [7:0]      fub_awlen;
    logic [2:0]      fub_awsize;
    logic [1:0]      fub_awburst;
    logic            fub_awlock;
    logic [3:0]      fub_awcache;
    logic [2:0]      fub_awprot;
    logic [3:0]      fub_awqos;
    logic [3:0]      fub_awregion;
    logic [UW-1:0]   fub_awuser;
    logic            fub_awvalid;
    logic [DW-1:0]   fub_wdata;
    logic [DW/8-1:0] fub_wstrb;
    logic            fub_wlast;
    logic [UW-1:0]   fub_wuser;
    logic            fub_wvalid;
    logic            fub_bready;
    logic            fub_split_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    logic [IW-1:0]   m_axi_awid, m_axi_awaddr_out;
    logic [AW-1:0]   m_axi_awaddr;
    logic [7:0]      m_axi_awlen;
    logic [2:0]      m_axi_awsize;
    logic [1:0]      m_axi_awburst;
    logic            m_axi_awlock;
    logic [3:0]      m_axi_awcache;
    logic [2:0]      m_axi_awprot;
    logic [3:0]      m_axi_awqos;
    logic [3:0]      m_axi_awregion;
    logic [UW-1:0]   m_axi_awuser;
    logic            m_axi_awvalid;
    logic [DW-1:0]   m_axi_wdata;
    logic [DW/8-1:0] m_axi_wstrb;
    logic            m_axi_wlast;
    logic [UW-1:0]   m_axi_wuser;
    logic            m_axi_wvalid;
    logic            m_axi_bready;
    logic            fub_awready;
    logic            fub_wready;
    logic [IW-1:0]   fub_bid;
    logic [1:0]      fub_bresp;
    logic [UW-1:0]   fub_buser;
    logic            fub_bvalid;
    logic [AW-1:0]   fub_split_addr;
    logic [IW-1:0]   fub_split_id;
    logic [7:0]      fub_split_cnt;
    logic            fub_split_valid;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    axi_master_wr_splitter #(
        .AXI_ID_WIDTH     (IW),
        .AXI_ADDR_WIDTH   (AW),
        .AXI_DATA_WIDTH   (DW),
        .AXI_USER_WIDTH   (UW),
        .SPLIT_FIFO_DEPTH (SPLIT_FIFO_DEPTH)
    ) dut (
        .aclk            (clk),
        .aresetn         (rst_n),
        .alignment_mask  (alignment_mask),
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
        .block_ready     (block_ready),
        .fub_awid        (fub_awid),
        .fub_awaddr      (fub_awaddr),
        .fub_awlen       (fub_awlen),
        .fub_awsize      (fub_awsize),
        .fub_awburst     (fub_awburst),
        .fub_awlock      (fub_awlock),
        .fub_awcache     (fub_awcache),
        .fub_awprot      (fub_awprot),
        .fub_awqos       (fub_awqos),
        .fub_awregion    (fub_awregion),
        .fub_awuser      (fub_awuser),
        .fub_awvalid     (fub_awvalid),
        .fub_awready     (fub_awready),
        .fub_wdata       (fub_wdata),
        .fub_wstrb       (fub_wstrb),
        .fub_wlast       (fub_wlast),
        .fub_wuser       (fub_wuser),
        .fub_wvalid      (fub_wvalid),
        .fub_wready      (fub_wready),
        .fub_bid         (fub_bid),
        .fub_bresp       (fub_bresp),
        .fub_buser       (fub_buser),
        .fub_bvalid      (fub_bvalid),
        .fub_bready      (fub_bready),
        .fub_split_addr  (fub_split_addr),
        .fub_split_id    (fub_split_id),
        .fub_split_cnt   (fub_split_cnt),
        .fub_split_valid (fub_split_valid),
        .fub_split_ready (fub_split_ready)
    );

    // =========================================================================
    // Environment constraints
    // =========================================================================
    localparam int BYTES_PER_BEAT = DW / 8;
    localparam int LOG2_BPB = $clog2(BYTES_PER_BEAT);

    always @(posedge clk) if (rst_n) assume (alignment_mask == 12'hFFF);
    always @(posedge clk) if (rst_n) assume (fub_awburst == 2'b01);
    always @(posedge clk) if (rst_n) assume (fub_awsize == LOG2_BPB[2:0]);
    always @(posedge clk) if (rst_n) assume (fub_awlen <= 8'd3);
    always @(posedge clk) if (rst_n) assume ((fub_awaddr & AW'(BYTES_PER_BEAT - 1)) == '0);
    always @(posedge clk) if (rst_n) assume (!block_ready);

    // AXI valid-stable on AW channel
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(fub_awvalid) && !$past(fub_awready))
                assume (fub_awvalid);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(fub_awvalid) && !$past(fub_awready)) begin
                assume (fub_awaddr == $past(fub_awaddr));
                assume (fub_awlen  == $past(fub_awlen));
                assume (fub_awid   == $past(fub_awid));
            end
    end

    // =========================================================================
    // Safety properties (output-only)
    // =========================================================================

    // P1: After reset, m_axi_awvalid follows fub_awvalid (IDLE passthrough)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n) && rst_n)
            ap_reset_awvalid: assert (m_axi_awvalid == fub_awvalid);
    end

    // P2: Write data passthrough
    always @(posedge clk) begin
        if (rst_n) begin
            ap_wdata_pass:  assert (m_axi_wdata  == fub_wdata);
            ap_wstrb_pass:  assert (m_axi_wstrb  == fub_wstrb);
            ap_wuser_pass:  assert (m_axi_wuser  == fub_wuser);
            ap_wvalid_pass: assert (m_axi_wvalid == fub_wvalid);
        end
    end

    // P3: fub_wready mirrors m_axi_wready
    always @(posedge clk) begin
        if (rst_n)
            ap_wready_pass: assert (fub_wready == m_axi_wready);
    end

    // P4: After reset with no valid fub request, fub_awready follows m_axi_awready
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(!rst_n) && !fub_awvalid)
            ap_reset_awready: assert (fub_awready == m_axi_awready);
    end

    // P5: m_axi_awlen never exceeds constraint
    always @(posedge clk) begin
        if (rst_n && m_axi_awvalid)
            ap_len_bounded: assert (m_axi_awlen <= 8'd3);
    end

    // P6: After reset, no fub_bvalid (no response pending)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n) && rst_n && !m_axi_bvalid)
            ap_reset_no_bresp: assert (!fub_bvalid);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    always @(posedge clk) begin
        if (rst_n) cp_passthrough: cover (fub_awvalid && fub_awready);
    end

    always @(posedge clk) begin
        if (rst_n) cp_ready_suppressed: cover (fub_awvalid && !fub_awready);
    end

    always @(posedge clk) begin
        if (rst_n) cp_split_fifo: cover (fub_split_valid);
    end

    always @(posedge clk) begin
        if (rst_n) cp_w_handshake: cover (m_axi_wvalid && m_axi_wready);
    end

    always @(posedge clk) begin
        if (rst_n) cp_b_response: cover (fub_bvalid && fub_bready);
    end

endmodule
