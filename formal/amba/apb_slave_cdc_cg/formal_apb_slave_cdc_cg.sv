// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for apb_slave_cdc_cg -- single clock model (pclk=aclk)
//
// See KNOWN_BUG.md in this directory for suspected issues:
//   - s_apb_PREADY is forced to 0 during pclk_cg_gating (line 115)
//   - aclk_axi_valid uses s_apb_PSEL directly from pclk domain (CDC hazard,
//     invisible in single-clock model)
//
// Properties verified:
//   P1: Reset clears s_apb_PREADY and both gating signals
//   P2: cfg_cg_enable=0 implies no gating
//   P3: Cover -- valid transactions can complete

`include "reset_defs.svh"

module formal_apb_slave_cdc_cg (
    input logic clk,
    input logic rst_n
);

    localparam int AW  = 12;
    localparam int DW  = 32;
    localparam int SW  = DW / 8;
    localparam int PW  = 3;
    localparam int ICW = 3;

    (* anyseq *) reg             cfg_cg_enable;
    (* anyseq *) reg [ICW-1:0]   cfg_cg_idle_count;
    (* anyseq *) reg              s_apb_PSEL;
    (* anyseq *) reg              s_apb_PENABLE;
    (* anyseq *) reg [AW-1:0]     s_apb_PADDR;
    (* anyseq *) reg              s_apb_PWRITE;
    (* anyseq *) reg [DW-1:0]     s_apb_PWDATA;
    (* anyseq *) reg [SW-1:0]     s_apb_PSTRB;
    (* anyseq *) reg [PW-1:0]     s_apb_PPROT;
    (* anyseq *) reg              cmd_ready;
    (* anyseq *) reg              rsp_valid;
    (* anyseq *) reg [DW-1:0]     rsp_prdata;
    (* anyseq *) reg              rsp_pslverr;

    wire             s_apb_PREADY;
    wire [DW-1:0]    s_apb_PRDATA;
    wire             s_apb_PSLVERR;
    wire             cmd_valid;
    wire             cmd_pwrite;
    wire [AW-1:0]    cmd_paddr;
    wire [DW-1:0]    cmd_pwdata;
    wire [SW-1:0]    cmd_pstrb;
    wire [PW-1:0]    cmd_pprot;
    wire             rsp_ready;
    wire             pclk_cg_gating, pclk_cg_idle;
    wire             aclk_cg_gating, aclk_cg_idle;

    apb_slave_cdc_cg #(
        .ADDR_WIDTH(AW),
        .DATA_WIDTH(DW),
        .STRB_WIDTH(SW),
        .PROT_WIDTH(PW),
        .DEPTH(2),
        .CG_IDLE_COUNT_WIDTH(ICW)
    ) dut (
        .pclk              (clk),
        .presetn           (rst_n),
        .aclk              (clk),
        .aresetn           (rst_n),
        .cfg_cg_enable     (cfg_cg_enable),
        .cfg_cg_idle_count (cfg_cg_idle_count),
        .s_apb_PSEL        (s_apb_PSEL),
        .s_apb_PENABLE     (s_apb_PENABLE),
        .s_apb_PREADY      (s_apb_PREADY),
        .s_apb_PADDR       (s_apb_PADDR),
        .s_apb_PWRITE      (s_apb_PWRITE),
        .s_apb_PWDATA      (s_apb_PWDATA),
        .s_apb_PSTRB       (s_apb_PSTRB),
        .s_apb_PPROT       (s_apb_PPROT),
        .s_apb_PRDATA      (s_apb_PRDATA),
        .s_apb_PSLVERR     (s_apb_PSLVERR),
        .cmd_valid         (cmd_valid),
        .cmd_ready         (cmd_ready),
        .cmd_pwrite        (cmd_pwrite),
        .cmd_paddr         (cmd_paddr),
        .cmd_pwdata        (cmd_pwdata),
        .cmd_pstrb         (cmd_pstrb),
        .cmd_pprot         (cmd_pprot),
        .rsp_valid         (rsp_valid),
        .rsp_ready         (rsp_ready),
        .rsp_prdata        (rsp_prdata),
        .rsp_pslverr       (rsp_pslverr),
        .pclk_cg_gating    (pclk_cg_gating),
        .pclk_cg_idle      (pclk_cg_idle),
        .aclk_cg_gating    (aclk_cg_gating),
        .aclk_cg_idle      (aclk_cg_idle)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid < 3) assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 3) assume (rst_n);

    // P1: Reset clears outputs
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_pready:     assert (!s_apb_PREADY);
            ap_reset_pclk_gate:  assert (!pclk_cg_gating);
            ap_reset_aclk_gate:  assert (!aclk_cg_gating);
        end
    end

    // P2: cfg_cg_enable=0 implies no gating in either domain
    always @(posedge clk) begin
        if (rst_n && !cfg_cg_enable) begin
            ap_disabled_no_pclk_gate: assert (!pclk_cg_gating);
            ap_disabled_no_aclk_gate: assert (!aclk_cg_gating);
        end
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_pclk_gating:  cover (pclk_cg_gating);
            cp_aclk_gating:  cover (aclk_cg_gating);
            cp_pready:       cover (s_apb_PREADY);
            cp_cmd:          cover (cmd_valid);
            cp_rsp:          cover (rsp_valid && rsp_ready);
        end
    end

endmodule
