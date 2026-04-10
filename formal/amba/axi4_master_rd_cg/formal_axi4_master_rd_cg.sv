// SPDX-License-Identifier: MIT
// Formal wrapper for axi4_master_rd_cg
//
// Verifies the clock-gated wrapper around axi4_master_rd. The ICG/clock
// gate controller is replaced by a pass-through formal stub
// (amba_clock_gate_ctrl_fv.sv) so the inner module always sees a running
// clock while formal freely exercises the "gating" status line.
//
// Properties verified:
//   P1: Reset clears m_axi_arvalid (output AR from the core skid buffer)
//   P2: Reset clears fub_axi_rvalid (output R to the user side)
//   P3: When gating is asserted, fub_axi_arready must be 0
//   P4: When gating is asserted, m_axi_rready must be 0
//   P5: m_axi_arvalid held stable until m_axi_arready (AXI handshake)
//   P6: fub_axi_rvalid held stable until fub_axi_rready (AXI handshake)
//   P7: user_valid OR-covers ALL user-side activity (the critical CG bug
//       hunt property): any user-side valid/ready that needs the clock
//       running must result in the wakeup condition being true
//   P8: axi_valid OR-covers all AXI-side valids that need the clock
//
// The "aggregation" properties P7/P8 drive the core bug hunt: if a required
// valid signal is missing from the wake-up OR, the assertion fails.

`include "reset_defs.svh"

module formal_axi4_master_rd_cg (
    input logic clk,
    input logic rst_n
);

    // ------------------------------------------------------------------
    // Small parameters for tractability
    // ------------------------------------------------------------------
    localparam int IW = 2;
    localparam int AW = 8;
    localparam int DW = 8;
    localparam int UW = 1;
    localparam int SKID_AR = 2;
    localparam int SKID_R  = 2;
    localparam int CG_ICW  = 4;

    // ------------------------------------------------------------------
    // Free inputs
    // ------------------------------------------------------------------
    (* anyseq *) reg                  cfg_cg_enable;
    (* anyseq *) reg [CG_ICW-1:0]     cfg_cg_idle_count;

    (* anyseq *) reg [IW-1:0]         fub_axi_arid;
    (* anyseq *) reg [AW-1:0]         fub_axi_araddr;
    (* anyseq *) reg [7:0]            fub_axi_arlen;
    (* anyseq *) reg [2:0]            fub_axi_arsize;
    (* anyseq *) reg [1:0]            fub_axi_arburst;
    (* anyseq *) reg                  fub_axi_arlock;
    (* anyseq *) reg [3:0]            fub_axi_arcache;
    (* anyseq *) reg [2:0]            fub_axi_arprot;
    (* anyseq *) reg [3:0]            fub_axi_arqos;
    (* anyseq *) reg [3:0]            fub_axi_arregion;
    (* anyseq *) reg [UW-1:0]         fub_axi_aruser;
    (* anyseq *) reg                  fub_axi_arvalid;
    (* anyseq *) reg                  fub_axi_rready;

    (* anyseq *) reg                  m_axi_arready;
    (* anyseq *) reg [IW-1:0]         m_axi_rid;
    (* anyseq *) reg [DW-1:0]         m_axi_rdata;
    (* anyseq *) reg [1:0]            m_axi_rresp;
    (* anyseq *) reg                  m_axi_rlast;
    (* anyseq *) reg [UW-1:0]         m_axi_ruser;
    (* anyseq *) reg                  m_axi_rvalid;

    // ------------------------------------------------------------------
    // DUT outputs
    // ------------------------------------------------------------------
    wire                  fub_axi_arready;
    wire [IW-1:0]         fub_axi_rid;
    wire [DW-1:0]         fub_axi_rdata;
    wire [1:0]            fub_axi_rresp;
    wire                  fub_axi_rlast;
    wire [UW-1:0]         fub_axi_ruser;
    wire                  fub_axi_rvalid;

    wire [IW-1:0]         m_axi_arid;
    wire [AW-1:0]         m_axi_araddr;
    wire [7:0]            m_axi_arlen;
    wire [2:0]            m_axi_arsize;
    wire [1:0]            m_axi_arburst;
    wire                  m_axi_arlock;
    wire [3:0]            m_axi_arcache;
    wire [2:0]            m_axi_arprot;
    wire [3:0]            m_axi_arqos;
    wire [3:0]            m_axi_arregion;
    wire [UW-1:0]         m_axi_aruser;
    wire                  m_axi_arvalid;
    wire                  m_axi_rready;

    wire                  cg_gating;
    wire                  cg_idle;

    // ------------------------------------------------------------------
    // DUT instantiation
    // ------------------------------------------------------------------
    axi4_master_rd_cg #(
        .SKID_DEPTH_AR    (SKID_AR),
        .SKID_DEPTH_R     (SKID_R),
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

        .m_axi_arid       (m_axi_arid),
        .m_axi_araddr     (m_axi_araddr),
        .m_axi_arlen      (m_axi_arlen),
        .m_axi_arsize     (m_axi_arsize),
        .m_axi_arburst    (m_axi_arburst),
        .m_axi_arlock     (m_axi_arlock),
        .m_axi_arcache    (m_axi_arcache),
        .m_axi_arprot     (m_axi_arprot),
        .m_axi_arqos      (m_axi_arqos),
        .m_axi_arregion   (m_axi_arregion),
        .m_axi_aruser     (m_axi_aruser),
        .m_axi_arvalid    (m_axi_arvalid),
        .m_axi_arready    (m_axi_arready),

        .m_axi_rid        (m_axi_rid),
        .m_axi_rdata      (m_axi_rdata),
        .m_axi_rresp      (m_axi_rresp),
        .m_axi_rlast      (m_axi_rlast),
        .m_axi_ruser      (m_axi_ruser),
        .m_axi_rvalid     (m_axi_rvalid),
        .m_axi_rready     (m_axi_rready),

        .cg_gating        (cg_gating),
        .cg_idle          (cg_idle)
    );

    // ------------------------------------------------------------------
    // Reset / past-valid
    // ------------------------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // ------------------------------------------------------------------
    // Properties
    // ------------------------------------------------------------------

    // P1: Reset clears m_axi_arvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_m_arvalid: assert (!m_axi_arvalid);
    end

    // P2: Reset clears fub_axi_rvalid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_fub_rvalid: assert (!fub_axi_rvalid);
    end

    // P3: When gating active, fub_axi_arready must be 0 (user-side)
    always @(*) begin
        if (rst_n && cg_gating)
            ap_gated_fub_arready_zero: assert (fub_axi_arready == 1'b0);
    end

    // P4: When gating active, m_axi_rready must be 0 (AXI-side)
    always @(*) begin
        if (rst_n && cg_gating)
            ap_gated_m_rready_zero: assert (m_axi_rready == 1'b0);
    end

    // P5: m_axi_arvalid stability until m_axi_arready
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(m_axi_arvalid) && !$past(m_axi_arready))
                ap_m_arvalid_held: assert (m_axi_arvalid);
    end

    // P6: fub_axi_rvalid stability until fub_axi_rready
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            if ($past(fub_axi_rvalid) && !$past(fub_axi_rready))
                ap_fub_rvalid_held: assert (fub_axi_rvalid);
    end

    // ------------------------------------------------------------------
    // P7/P8: CG enable coverage (the bug-hunt properties)
    // ------------------------------------------------------------------
    // These properties verify that the wrapper's aggregated user_valid /
    // axi_valid signals (which feed the clock-gate wakeup OR) together
    // cover ALL AMBA valids that must keep the clock running. They are
    // implemented inside a `bind`-instantiated checker module
    // `axi4_master_rd_cg_wake_checker` (see below this module) which has
    // direct scope access to the DUT's `user_valid` / `axi_valid` wires.

    // ------------------------------------------------------------------
    // Cover properties
    // ------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            cp_ar_handshake:    cover (m_axi_arvalid && m_axi_arready);
            cp_fub_r_handshake: cover (fub_axi_rvalid && fub_axi_rready);
            cp_gated:           cover (cg_gating);
        end
    end

endmodule

// ======================================================================
// Bound wake-coverage checker
// ======================================================================
// Bound into axi4_master_rd_cg so it has direct scope access to the
// internal `user_valid` and `axi_valid` wires. Verifies every AMBA valid
// that must keep the clock running is OR-ed into the wake expression.
// ======================================================================
module axi4_master_rd_cg_wake_checker (
    input logic aclk,
    input logic aresetn,
    input logic fub_axi_arvalid,
    input logic fub_axi_rvalid,
    input logic fub_axi_rready,
    input logic m_axi_arvalid,
    input logic m_axi_rvalid,
    input logic user_valid,
    input logic axi_valid
);
    wire wake = user_valid || axi_valid;

    always @(*) begin
        if (aresetn) begin
            ap_wake_covers_fub_arvalid:
                assert (!fub_axi_arvalid || wake);
            ap_wake_covers_fub_rvalid:
                assert (!fub_axi_rvalid  || wake);
            ap_wake_covers_fub_rready:
                assert (!fub_axi_rready  || wake);
            ap_wake_covers_m_arvalid:
                assert (!m_axi_arvalid   || wake);
            ap_wake_covers_m_rvalid:
                assert (!m_axi_rvalid    || wake);
        end
    end
endmodule

// Bind the checker into the DUT instance
bind axi4_master_rd_cg axi4_master_rd_cg_wake_checker u_wake_check (
    .aclk            (aclk),
    .aresetn         (aresetn),
    .fub_axi_arvalid (fub_axi_arvalid),
    .fub_axi_rvalid  (fub_axi_rvalid),
    .fub_axi_rready  (fub_axi_rready),
    .m_axi_arvalid   (m_axi_arvalid),
    .m_axi_rvalid    (m_axi_rvalid),
    .user_valid      (user_valid),
    .axi_valid       (axi_valid)
);
