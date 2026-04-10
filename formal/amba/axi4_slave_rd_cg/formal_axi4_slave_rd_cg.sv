// SPDX-License-Identifier: MIT
// Formal wrapper for axi4_slave_rd_cg

`include "reset_defs.svh"

module formal_axi4_slave_rd_cg (
    input logic clk,
    input logic rst_n
);

    localparam int IW = 2;
    localparam int AW = 8;
    localparam int DW = 8;
    localparam int UW = 1;
    localparam int CG_ICW = 4;

    (* anyseq *) reg                  cfg_cg_enable;
    (* anyseq *) reg [CG_ICW-1:0]     cfg_cg_idle_count;

    (* anyseq *) reg [IW-1:0]         s_axi_arid;
    (* anyseq *) reg [AW-1:0]         s_axi_araddr;
    (* anyseq *) reg [7:0]            s_axi_arlen;
    (* anyseq *) reg [2:0]            s_axi_arsize;
    (* anyseq *) reg [1:0]            s_axi_arburst;
    (* anyseq *) reg                  s_axi_arlock;
    (* anyseq *) reg [3:0]            s_axi_arcache;
    (* anyseq *) reg [2:0]            s_axi_arprot;
    (* anyseq *) reg [3:0]            s_axi_arqos;
    (* anyseq *) reg [3:0]            s_axi_arregion;
    (* anyseq *) reg [UW-1:0]         s_axi_aruser;
    (* anyseq *) reg                  s_axi_arvalid;
    (* anyseq *) reg                  s_axi_rready;

    (* anyseq *) reg                  fub_axi_arready;
    (* anyseq *) reg [IW-1:0]         fub_axi_rid;
    (* anyseq *) reg [DW-1:0]         fub_axi_rdata;
    (* anyseq *) reg [1:0]            fub_axi_rresp;
    (* anyseq *) reg                  fub_axi_rlast;
    (* anyseq *) reg [UW-1:0]         fub_axi_ruser;
    (* anyseq *) reg                  fub_axi_rvalid;

    wire                  s_axi_arready;
    wire [IW-1:0]         s_axi_rid;
    wire [DW-1:0]         s_axi_rdata;
    wire [1:0]            s_axi_rresp;
    wire                  s_axi_rlast;
    wire [UW-1:0]         s_axi_ruser;
    wire                  s_axi_rvalid;

    wire [IW-1:0]         fub_axi_arid;
    wire [AW-1:0]         fub_axi_araddr;
    wire [7:0]            fub_axi_arlen;
    wire [2:0]            fub_axi_arsize;
    wire [1:0]            fub_axi_arburst;
    wire                  fub_axi_arlock;
    wire [3:0]            fub_axi_arcache;
    wire [2:0]            fub_axi_arprot;
    wire [3:0]            fub_axi_arqos;
    wire [3:0]            fub_axi_arregion;
    wire [UW-1:0]         fub_axi_aruser;
    wire                  fub_axi_arvalid;
    wire                  fub_axi_rready;

    wire                  cg_gating;
    wire                  cg_idle;

    axi4_slave_rd_cg #(
        .SKID_DEPTH_AR    (2),
        .SKID_DEPTH_R     (2),
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

        .s_axi_arid       (s_axi_arid),
        .s_axi_araddr     (s_axi_araddr),
        .s_axi_arlen      (s_axi_arlen),
        .s_axi_arsize     (s_axi_arsize),
        .s_axi_arburst    (s_axi_arburst),
        .s_axi_arlock     (s_axi_arlock),
        .s_axi_arcache    (s_axi_arcache),
        .s_axi_arprot     (s_axi_arprot),
        .s_axi_arqos      (s_axi_arqos),
        .s_axi_arregion   (s_axi_arregion),
        .s_axi_aruser     (s_axi_aruser),
        .s_axi_arvalid    (s_axi_arvalid),
        .s_axi_arready    (s_axi_arready),

        .s_axi_rid        (s_axi_rid),
        .s_axi_rdata      (s_axi_rdata),
        .s_axi_rresp      (s_axi_rresp),
        .s_axi_rlast      (s_axi_rlast),
        .s_axi_ruser      (s_axi_ruser),
        .s_axi_rvalid     (s_axi_rvalid),
        .s_axi_rready     (s_axi_rready),

        .fub_axi_arid     (fub_axi_arid),
        .fub_axi_araddr   (fub_axi_araddr),
        .fub_axi_arlen    (fub_axi_arlen),
        .fub_axi_arsize   (fub_axi_arsize),
        .fub_axi_arburst  (fub_axi_arburst),
        .fub_axi_arlock   (fub_axi_arlock),
        .fub_axi_arcache  (fub_axi_arcache),
        .fub_axi_arprot   (fub_axi_arprot),
        .fub_axi_arqos    (fub_axi_arqos),
        .fub_axi_arregion (fub_axi_arregion),
        .fub_axi_aruser   (fub_axi_aruser),
        .fub_axi_arvalid  (fub_axi_arvalid),
        .fub_axi_arready  (fub_axi_arready),

        .fub_axi_rid      (fub_axi_rid),
        .fub_axi_rdata    (fub_axi_rdata),
        .fub_axi_rresp    (fub_axi_rresp),
        .fub_axi_rlast    (fub_axi_rlast),
        .fub_axi_ruser    (fub_axi_ruser),
        .fub_axi_rvalid   (fub_axi_rvalid),
        .fub_axi_rready   (fub_axi_rready),

        .cg_gating        (cg_gating),
        .cg_idle          (cg_idle)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    always @(posedge clk) if (f_past_valid > 0 && $past(!rst_n)) begin
        ap_reset_fub_arvalid: assert (!fub_axi_arvalid);
        ap_reset_s_rvalid:    assert (!s_axi_rvalid);
    end

    always @(*) if (rst_n && cg_gating) begin
        ap_gated_s_arready_zero:   assert (s_axi_arready  == 1'b0);
        ap_gated_fub_rready_zero:  assert (fub_axi_rready == 1'b0);
    end

    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(fub_axi_arvalid) && !$past(fub_axi_arready))
            ap_fub_arvalid_held: assert (fub_axi_arvalid);
        if ($past(s_axi_rvalid) && !$past(s_axi_rready))
            ap_s_rvalid_held: assert (s_axi_rvalid);
    end

    always @(posedge clk) if (rst_n) begin
        cp_fub_ar_handshake: cover (fub_axi_arvalid && fub_axi_arready);
        cp_s_r_handshake:    cover (s_axi_rvalid && s_axi_rready);
        cp_gated:            cover (cg_gating);
    end

endmodule

// ======================================================================
// Bound wake-coverage checker for axi4_slave_rd_cg
// ======================================================================
module axi4_slave_rd_cg_wake_checker (
    input logic aclk,
    input logic aresetn,
    input logic s_axi_arvalid,
    input logic s_axi_rvalid,
    input logic s_axi_rready,
    input logic fub_axi_arvalid,
    input logic fub_axi_rvalid,
    input logic user_valid,
    input logic axi_valid
);
    wire wake = user_valid || axi_valid;
    always @(*) if (aresetn) begin
        ap_wake_covers_s_arvalid:  assert (!s_axi_arvalid  || wake);
        ap_wake_covers_s_rvalid:   assert (!s_axi_rvalid   || wake);
        ap_wake_covers_s_rready:   assert (!s_axi_rready   || wake);
        ap_wake_covers_fub_arvalid:assert (!fub_axi_arvalid || wake);
        ap_wake_covers_fub_rvalid: assert (!fub_axi_rvalid || wake);
    end
endmodule

bind axi4_slave_rd_cg axi4_slave_rd_cg_wake_checker u_wake_check (
    .aclk            (aclk),
    .aresetn         (aresetn),
    .s_axi_arvalid   (s_axi_arvalid),
    .s_axi_rvalid    (s_axi_rvalid),
    .s_axi_rready    (s_axi_rready),
    .fub_axi_arvalid (fub_axi_arvalid),
    .fub_axi_rvalid  (fub_axi_rvalid),
    .user_valid      (user_valid),
    .axi_valid       (axi_valid)
);
