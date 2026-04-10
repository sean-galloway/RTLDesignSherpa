// SPDX-License-Identifier: MIT
// Formal wrapper for axis_master_cg

`include "reset_defs.svh"

module formal_axis_master_cg (
    input logic clk,
    input logic rst_n
);

    localparam int DW    = 8;
    localparam int IW    = 2;
    localparam int DESTW = 2;
    localparam int UW    = 1;
    localparam int SW    = DW/8;
    localparam int CG_ICW = 4;

    (* anyseq *) reg                  cfg_cg_enable;
    (* anyseq *) reg [CG_ICW-1:0]     cfg_cg_idle_count;

    (* anyseq *) reg [DW-1:0]         fub_axis_tdata;
    (* anyseq *) reg [SW-1:0]         fub_axis_tstrb;
    (* anyseq *) reg                  fub_axis_tlast;
    (* anyseq *) reg [IW-1:0]         fub_axis_tid;
    (* anyseq *) reg [DESTW-1:0]      fub_axis_tdest;
    (* anyseq *) reg [UW-1:0]         fub_axis_tuser;
    (* anyseq *) reg                  fub_axis_tvalid;

    (* anyseq *) reg                  m_axis_tready;

    wire                  fub_axis_tready;
    wire [DW-1:0]         m_axis_tdata;
    wire [SW-1:0]         m_axis_tstrb;
    wire                  m_axis_tlast;
    wire [IW-1:0]         m_axis_tid;
    wire [DESTW-1:0]      m_axis_tdest;
    wire [UW-1:0]         m_axis_tuser;
    wire                  m_axis_tvalid;

    wire                  cg_gating;
    wire                  cg_idle;

    axis_master_cg #(
        .SKID_DEPTH          (2),
        .AXIS_DATA_WIDTH     (DW),
        .AXIS_ID_WIDTH       (IW),
        .AXIS_DEST_WIDTH     (DESTW),
        .AXIS_USER_WIDTH     (UW),
        .CG_IDLE_COUNT_WIDTH (CG_ICW)
    ) dut (
        .aclk             (clk),
        .aresetn          (rst_n),
        .cfg_cg_enable    (cfg_cg_enable),
        .cfg_cg_idle_count(cfg_cg_idle_count),
        .fub_axis_tdata   (fub_axis_tdata),
        .fub_axis_tstrb   (fub_axis_tstrb),
        .fub_axis_tlast   (fub_axis_tlast),
        .fub_axis_tid     (fub_axis_tid),
        .fub_axis_tdest   (fub_axis_tdest),
        .fub_axis_tuser   (fub_axis_tuser),
        .fub_axis_tvalid  (fub_axis_tvalid),
        .fub_axis_tready  (fub_axis_tready),
        .m_axis_tdata     (m_axis_tdata),
        .m_axis_tstrb     (m_axis_tstrb),
        .m_axis_tlast     (m_axis_tlast),
        .m_axis_tid       (m_axis_tid),
        .m_axis_tdest     (m_axis_tdest),
        .m_axis_tuser     (m_axis_tuser),
        .m_axis_tvalid    (m_axis_tvalid),
        .m_axis_tready    (m_axis_tready),
        .cg_gating        (cg_gating),
        .cg_idle          (cg_idle)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    always @(posedge clk) if (f_past_valid > 0 && $past(!rst_n))
        ap_reset_m_tvalid: assert (!m_axis_tvalid);

    always @(*) if (rst_n && cg_gating)
        ap_gated_fub_tready_zero: assert (fub_axis_tready == 1'b0);

    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n))
        if ($past(m_axis_tvalid) && !$past(m_axis_tready))
            ap_m_tvalid_held: assert (m_axis_tvalid);

    always @(posedge clk) if (rst_n) begin
        cp_m_t_handshake: cover (m_axis_tvalid && m_axis_tready);
        cp_gated:         cover (cg_gating);
    end

endmodule

// ======================================================================
// Bound wake-coverage checker for axis_master_cg
// ======================================================================
module axis_master_cg_wake_checker (
    input logic aclk,
    input logic aresetn,
    input logic fub_axis_tvalid,
    input logic m_axis_tvalid,
    input logic m_axis_tready,
    input logic user_valid,
    input logic axi_valid
);
    wire wake = user_valid || axi_valid;
    always @(*) if (aresetn) begin
        ap_wake_covers_fub_tvalid: assert (!fub_axis_tvalid || wake);
        ap_wake_covers_m_tvalid:   assert (!m_axis_tvalid   || wake);
        ap_wake_covers_m_tready:   assert (!m_axis_tready   || wake);
    end
endmodule

bind axis_master_cg axis_master_cg_wake_checker u_wake_check (
    .aclk            (aclk),
    .aresetn         (aresetn),
    .fub_axis_tvalid (fub_axis_tvalid),
    .m_axis_tvalid   (m_axis_tvalid),
    .m_axis_tready   (m_axis_tready),
    .user_valid      (user_valid),
    .axi_valid       (axi_valid)
);
