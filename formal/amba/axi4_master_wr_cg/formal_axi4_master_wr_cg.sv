// SPDX-License-Identifier: MIT
// Formal wrapper for axi4_master_wr_cg
//
// Verifies the clock-gated wrapper around axi4_master_wr. Uses a
// pass-through formal stub for amba_clock_gate_ctrl and a bound checker
// module to verify the wake aggregation covers every AMBA valid.

`include "reset_defs.svh"

module formal_axi4_master_wr_cg (
    input logic clk,
    input logic rst_n
);

    localparam int IW = 2;
    localparam int AW = 8;
    localparam int DW = 8;
    localparam int UW = 1;
    localparam int SW = DW/8;
    localparam int CG_ICW = 4;

    // Free inputs
    (* anyseq *) reg                  cfg_cg_enable;
    (* anyseq *) reg [CG_ICW-1:0]     cfg_cg_idle_count;

    (* anyseq *) reg [IW-1:0]         fub_axi_awid;
    (* anyseq *) reg [AW-1:0]         fub_axi_awaddr;
    (* anyseq *) reg [7:0]            fub_axi_awlen;
    (* anyseq *) reg [2:0]            fub_axi_awsize;
    (* anyseq *) reg [1:0]            fub_axi_awburst;
    (* anyseq *) reg                  fub_axi_awlock;
    (* anyseq *) reg [3:0]            fub_axi_awcache;
    (* anyseq *) reg [2:0]            fub_axi_awprot;
    (* anyseq *) reg [3:0]            fub_axi_awqos;
    (* anyseq *) reg [3:0]            fub_axi_awregion;
    (* anyseq *) reg [UW-1:0]         fub_axi_awuser;
    (* anyseq *) reg                  fub_axi_awvalid;

    (* anyseq *) reg [DW-1:0]         fub_axi_wdata;
    (* anyseq *) reg [SW-1:0]         fub_axi_wstrb;
    (* anyseq *) reg                  fub_axi_wlast;
    (* anyseq *) reg [UW-1:0]         fub_axi_wuser;
    (* anyseq *) reg                  fub_axi_wvalid;

    (* anyseq *) reg                  fub_axi_bready;

    (* anyseq *) reg                  m_axi_awready;
    (* anyseq *) reg                  m_axi_wready;
    (* anyseq *) reg [IW-1:0]         m_axi_bid;
    (* anyseq *) reg [1:0]            m_axi_bresp;
    (* anyseq *) reg [UW-1:0]         m_axi_buser;
    (* anyseq *) reg                  m_axi_bvalid;

    // DUT outputs
    wire                  fub_axi_awready;
    wire                  fub_axi_wready;
    wire [IW-1:0]         fub_axi_bid;
    wire [1:0]            fub_axi_bresp;
    wire [UW-1:0]         fub_axi_buser;
    wire                  fub_axi_bvalid;

    wire [IW-1:0]         m_axi_awid;
    wire [AW-1:0]         m_axi_awaddr;
    wire [7:0]            m_axi_awlen;
    wire [2:0]            m_axi_awsize;
    wire [1:0]            m_axi_awburst;
    wire                  m_axi_awlock;
    wire [3:0]            m_axi_awcache;
    wire [2:0]            m_axi_awprot;
    wire [3:0]            m_axi_awqos;
    wire [3:0]            m_axi_awregion;
    wire [UW-1:0]         m_axi_awuser;
    wire                  m_axi_awvalid;

    wire [DW-1:0]         m_axi_wdata;
    wire [SW-1:0]         m_axi_wstrb;
    wire                  m_axi_wlast;
    wire [UW-1:0]         m_axi_wuser;
    wire                  m_axi_wvalid;

    wire                  m_axi_bready;

    wire                  cg_gating;
    wire                  cg_idle;

    axi4_master_wr_cg #(
        .SKID_DEPTH_AW    (2),
        .SKID_DEPTH_W     (2),
        .SKID_DEPTH_B     (2),
        .AXI_ID_WIDTH     (IW),
        .AXI_ADDR_WIDTH   (AW),
        .AXI_DATA_WIDTH   (DW),
        .AXI_USER_WIDTH   (UW),
        .CG_IDLE_COUNT_WIDTH(CG_ICW)
    ) dut (
        .aclk             (clk),
        .aresetn          (rst_n),
        .cfg_cg_enable    (cfg_cg_enable),
        .cfg_cg_idle_count(cfg_cg_idle_count),

        .fub_axi_awid     (fub_axi_awid),
        .fub_axi_awaddr   (fub_axi_awaddr),
        .fub_axi_awlen    (fub_axi_awlen),
        .fub_axi_awsize   (fub_axi_awsize),
        .fub_axi_awburst  (fub_axi_awburst),
        .fub_axi_awlock   (fub_axi_awlock),
        .fub_axi_awcache  (fub_axi_awcache),
        .fub_axi_awprot   (fub_axi_awprot),
        .fub_axi_awqos    (fub_axi_awqos),
        .fub_axi_awregion (fub_axi_awregion),
        .fub_axi_awuser   (fub_axi_awuser),
        .fub_axi_awvalid  (fub_axi_awvalid),
        .fub_axi_awready  (fub_axi_awready),

        .fub_axi_wdata    (fub_axi_wdata),
        .fub_axi_wstrb    (fub_axi_wstrb),
        .fub_axi_wlast    (fub_axi_wlast),
        .fub_axi_wuser    (fub_axi_wuser),
        .fub_axi_wvalid   (fub_axi_wvalid),
        .fub_axi_wready   (fub_axi_wready),

        .fub_axi_bid      (fub_axi_bid),
        .fub_axi_bresp    (fub_axi_bresp),
        .fub_axi_buser    (fub_axi_buser),
        .fub_axi_bvalid   (fub_axi_bvalid),
        .fub_axi_bready   (fub_axi_bready),

        .m_axi_awid       (m_axi_awid),
        .m_axi_awaddr     (m_axi_awaddr),
        .m_axi_awlen      (m_axi_awlen),
        .m_axi_awsize     (m_axi_awsize),
        .m_axi_awburst    (m_axi_awburst),
        .m_axi_awlock     (m_axi_awlock),
        .m_axi_awcache    (m_axi_awcache),
        .m_axi_awprot     (m_axi_awprot),
        .m_axi_awqos      (m_axi_awqos),
        .m_axi_awregion   (m_axi_awregion),
        .m_axi_awuser     (m_axi_awuser),
        .m_axi_awvalid    (m_axi_awvalid),
        .m_axi_awready    (m_axi_awready),

        .m_axi_wdata      (m_axi_wdata),
        .m_axi_wstrb      (m_axi_wstrb),
        .m_axi_wlast      (m_axi_wlast),
        .m_axi_wuser      (m_axi_wuser),
        .m_axi_wvalid     (m_axi_wvalid),
        .m_axi_wready     (m_axi_wready),

        .m_axi_bid        (m_axi_bid),
        .m_axi_bresp      (m_axi_bresp),
        .m_axi_buser      (m_axi_buser),
        .m_axi_bvalid     (m_axi_bvalid),
        .m_axi_bready     (m_axi_bready),

        .cg_gating        (cg_gating),
        .cg_idle          (cg_idle)
    );

    // Reset / past-valid
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // P1: reset clears m_axi_awvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_m_awvalid: assert (!m_axi_awvalid);
    end
    // P1b: reset clears m_axi_wvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_m_wvalid: assert (!m_axi_wvalid);
    end
    // P2: reset clears fub_axi_bvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_fub_bvalid: assert (!fub_axi_bvalid);
    end

    // P3: gated => user-side readies forced to 0
    always @(*) if (rst_n && cg_gating) begin
        ap_gated_fub_awready_zero: assert (fub_axi_awready == 1'b0);
        ap_gated_fub_wready_zero:  assert (fub_axi_wready  == 1'b0);
        ap_gated_m_bready_zero:    assert (m_axi_bready    == 1'b0);
    end

    // P5: handshake stability on AXI-side output valids
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(m_axi_awvalid) && !$past(m_axi_awready))
            ap_m_awvalid_held: assert (m_axi_awvalid);
        if ($past(m_axi_wvalid) && !$past(m_axi_wready))
            ap_m_wvalid_held: assert (m_axi_wvalid);
        if ($past(fub_axi_bvalid) && !$past(fub_axi_bready))
            ap_fub_bvalid_held: assert (fub_axi_bvalid);
    end

    // Cover properties
    always @(posedge clk) if (rst_n) begin
        cp_aw_handshake:   cover (m_axi_awvalid && m_axi_awready);
        cp_w_handshake:    cover (m_axi_wvalid  && m_axi_wready);
        cp_fub_b_handshake:cover (fub_axi_bvalid && fub_axi_bready);
        cp_gated:          cover (cg_gating);
    end

endmodule

// ======================================================================
// Bound wake-coverage checker (P7/P8): every AMBA valid that should
// keep the clock running must be OR-ed into user_valid|axi_valid.
// ======================================================================
module axi4_master_wr_cg_wake_checker (
    input logic aclk,
    input logic aresetn,
    input logic fub_axi_awvalid,
    input logic fub_axi_wvalid,
    input logic fub_axi_bvalid,
    input logic fub_axi_bready,
    input logic m_axi_awvalid,
    input logic m_axi_wvalid,
    input logic m_axi_bvalid,
    input logic user_valid,
    input logic axi_valid
);
    wire wake = user_valid || axi_valid;
    always @(*) if (aresetn) begin
        ap_wake_covers_fub_awvalid: assert (!fub_axi_awvalid || wake);
        ap_wake_covers_fub_wvalid:  assert (!fub_axi_wvalid  || wake);
        ap_wake_covers_fub_bvalid:  assert (!fub_axi_bvalid  || wake);
        ap_wake_covers_fub_bready:  assert (!fub_axi_bready  || wake);
        ap_wake_covers_m_awvalid:   assert (!m_axi_awvalid   || wake);
        ap_wake_covers_m_wvalid:    assert (!m_axi_wvalid    || wake);
        ap_wake_covers_m_bvalid:    assert (!m_axi_bvalid    || wake);
    end
endmodule

bind axi4_master_wr_cg axi4_master_wr_cg_wake_checker u_wake_check (
    .aclk            (aclk),
    .aresetn         (aresetn),
    .fub_axi_awvalid (fub_axi_awvalid),
    .fub_axi_wvalid  (fub_axi_wvalid),
    .fub_axi_bvalid  (fub_axi_bvalid),
    .fub_axi_bready  (fub_axi_bready),
    .m_axi_awvalid   (m_axi_awvalid),
    .m_axi_wvalid    (m_axi_wvalid),
    .m_axi_bvalid    (m_axi_bvalid),
    .user_valid      (user_valid),
    .axi_valid       (axi_valid)
);
