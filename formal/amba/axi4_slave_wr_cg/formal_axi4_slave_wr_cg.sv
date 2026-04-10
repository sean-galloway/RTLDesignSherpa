// SPDX-License-Identifier: MIT
// Formal wrapper for axi4_slave_wr_cg

`include "reset_defs.svh"

module formal_axi4_slave_wr_cg (
    input logic clk,
    input logic rst_n
);

    localparam int IW = 2;
    localparam int AW = 8;
    localparam int DW = 8;
    localparam int UW = 1;
    localparam int SW = DW/8;
    localparam int CG_ICW = 4;

    (* anyseq *) reg                  cfg_cg_enable;
    (* anyseq *) reg [CG_ICW-1:0]     cfg_cg_idle_count;

    (* anyseq *) reg [IW-1:0]         s_axi_awid;
    (* anyseq *) reg [AW-1:0]         s_axi_awaddr;
    (* anyseq *) reg [7:0]            s_axi_awlen;
    (* anyseq *) reg [2:0]            s_axi_awsize;
    (* anyseq *) reg [1:0]            s_axi_awburst;
    (* anyseq *) reg                  s_axi_awlock;
    (* anyseq *) reg [3:0]            s_axi_awcache;
    (* anyseq *) reg [2:0]            s_axi_awprot;
    (* anyseq *) reg [3:0]            s_axi_awqos;
    (* anyseq *) reg [3:0]            s_axi_awregion;
    (* anyseq *) reg [UW-1:0]         s_axi_awuser;
    (* anyseq *) reg                  s_axi_awvalid;

    (* anyseq *) reg [DW-1:0]         s_axi_wdata;
    (* anyseq *) reg [SW-1:0]         s_axi_wstrb;
    (* anyseq *) reg                  s_axi_wlast;
    (* anyseq *) reg [UW-1:0]         s_axi_wuser;
    (* anyseq *) reg                  s_axi_wvalid;

    (* anyseq *) reg                  s_axi_bready;

    (* anyseq *) reg                  fub_axi_awready;
    (* anyseq *) reg                  fub_axi_wready;
    (* anyseq *) reg [IW-1:0]         fub_axi_bid;
    (* anyseq *) reg [1:0]            fub_axi_bresp;
    (* anyseq *) reg [UW-1:0]         fub_axi_buser;
    (* anyseq *) reg                  fub_axi_bvalid;

    wire                  s_axi_awready;
    wire                  s_axi_wready;
    wire [IW-1:0]         s_axi_bid;
    wire [1:0]            s_axi_bresp;
    wire [UW-1:0]         s_axi_buser;
    wire                  s_axi_bvalid;

    wire [IW-1:0]         fub_axi_awid;
    wire [AW-1:0]         fub_axi_awaddr;
    wire [7:0]            fub_axi_awlen;
    wire [2:0]            fub_axi_awsize;
    wire [1:0]            fub_axi_awburst;
    wire                  fub_axi_awlock;
    wire [3:0]            fub_axi_awcache;
    wire [2:0]            fub_axi_awprot;
    wire [3:0]            fub_axi_awqos;
    wire [3:0]            fub_axi_awregion;
    wire [UW-1:0]         fub_axi_awuser;
    wire                  fub_axi_awvalid;

    wire [DW-1:0]         fub_axi_wdata;
    wire [SW-1:0]         fub_axi_wstrb;
    wire                  fub_axi_wlast;
    wire [UW-1:0]         fub_axi_wuser;
    wire                  fub_axi_wvalid;

    wire                  fub_axi_bready;

    wire                  cg_gating;
    wire                  cg_idle;

    axi4_slave_wr_cg #(
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

        .s_axi_awid       (s_axi_awid),
        .s_axi_awaddr     (s_axi_awaddr),
        .s_axi_awlen      (s_axi_awlen),
        .s_axi_awsize     (s_axi_awsize),
        .s_axi_awburst    (s_axi_awburst),
        .s_axi_awlock     (s_axi_awlock),
        .s_axi_awcache    (s_axi_awcache),
        .s_axi_awprot     (s_axi_awprot),
        .s_axi_awqos      (s_axi_awqos),
        .s_axi_awregion   (s_axi_awregion),
        .s_axi_awuser     (s_axi_awuser),
        .s_axi_awvalid    (s_axi_awvalid),
        .s_axi_awready    (s_axi_awready),

        .s_axi_wdata      (s_axi_wdata),
        .s_axi_wstrb      (s_axi_wstrb),
        .s_axi_wlast      (s_axi_wlast),
        .s_axi_wuser      (s_axi_wuser),
        .s_axi_wvalid     (s_axi_wvalid),
        .s_axi_wready     (s_axi_wready),

        .s_axi_bid        (s_axi_bid),
        .s_axi_bresp      (s_axi_bresp),
        .s_axi_buser      (s_axi_buser),
        .s_axi_bvalid     (s_axi_bvalid),
        .s_axi_bready     (s_axi_bready),

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

        .cg_gating        (cg_gating),
        .cg_idle          (cg_idle)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    always @(posedge clk) if (f_past_valid > 0 && $past(!rst_n)) begin
        ap_reset_fub_awvalid: assert (!fub_axi_awvalid);
        ap_reset_fub_wvalid:  assert (!fub_axi_wvalid);
        ap_reset_s_bvalid:    assert (!s_axi_bvalid);
    end

    always @(*) if (rst_n && cg_gating) begin
        ap_gated_s_awready_zero:  assert (s_axi_awready  == 1'b0);
        ap_gated_s_wready_zero:   assert (s_axi_wready   == 1'b0);
        ap_gated_fub_bready_zero: assert (fub_axi_bready == 1'b0);
    end

    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(fub_axi_awvalid) && !$past(fub_axi_awready))
            ap_fub_awvalid_held: assert (fub_axi_awvalid);
        if ($past(fub_axi_wvalid) && !$past(fub_axi_wready))
            ap_fub_wvalid_held: assert (fub_axi_wvalid);
        if ($past(s_axi_bvalid) && !$past(s_axi_bready))
            ap_s_bvalid_held: assert (s_axi_bvalid);
    end

    always @(posedge clk) if (rst_n) begin
        cp_fub_aw_handshake: cover (fub_axi_awvalid && fub_axi_awready);
        cp_fub_w_handshake:  cover (fub_axi_wvalid  && fub_axi_wready);
        cp_s_b_handshake:    cover (s_axi_bvalid   && s_axi_bready);
        cp_gated:            cover (cg_gating);
    end

endmodule

// ======================================================================
// Bound wake-coverage checker for axi4_slave_wr_cg
// ======================================================================
module axi4_slave_wr_cg_wake_checker (
    input logic aclk,
    input logic aresetn,
    input logic s_axi_awvalid,
    input logic s_axi_wvalid,
    input logic s_axi_bvalid,
    input logic s_axi_bready,
    input logic fub_axi_awvalid,
    input logic fub_axi_wvalid,
    input logic fub_axi_bvalid,
    input logic user_valid,
    input logic axi_valid
);
    wire wake = user_valid || axi_valid;
    always @(*) if (aresetn) begin
        ap_wake_covers_s_awvalid:   assert (!s_axi_awvalid   || wake);
        ap_wake_covers_s_wvalid:    assert (!s_axi_wvalid    || wake);
        ap_wake_covers_s_bvalid:    assert (!s_axi_bvalid    || wake);
        ap_wake_covers_s_bready:    assert (!s_axi_bready    || wake);
        ap_wake_covers_fub_awvalid: assert (!fub_axi_awvalid || wake);
        ap_wake_covers_fub_wvalid:  assert (!fub_axi_wvalid  || wake);
        ap_wake_covers_fub_bvalid:  assert (!fub_axi_bvalid  || wake);
    end
endmodule

bind axi4_slave_wr_cg axi4_slave_wr_cg_wake_checker u_wake_check (
    .aclk            (aclk),
    .aresetn         (aresetn),
    .s_axi_awvalid   (s_axi_awvalid),
    .s_axi_wvalid    (s_axi_wvalid),
    .s_axi_bvalid    (s_axi_bvalid),
    .s_axi_bready    (s_axi_bready),
    .fub_axi_awvalid (fub_axi_awvalid),
    .fub_axi_wvalid  (fub_axi_wvalid),
    .fub_axi_bvalid  (fub_axi_bvalid),
    .user_valid      (user_valid),
    .axi_valid       (axi_valid)
);
