// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_to_peakrdl
// Purpose: One-stop APB slave -> PeakRDL passthrough ("cpuif") adapter.
//          Stitches the two existing converters:
//
//            APB (pclk) --apb4_slave_cdc--> CMD/RSP (aclk) --peakrdl_to_cmdrsp--> cpuif
//
//          so a design that exposes a PeakRDL passthrough register interface
//          (regblk_* / s_cpuif_*) can be driven from a plain APB slave port.
//          The CDC lets the APB bus and the register/core clock differ; tie
//          pclk==aclk for a single-clock system (the CDC then adds a couple of
//          synchronizer cycles but is otherwise transparent).
//
//          This is the exact stack the (retired) pumice_csr_slave documented
//          and that stream_top_ch8 wires inline; factored out here so board
//          harnesses can adapt a bridge APB config window onto a rearchitected
//          controller's cpuif without re-plumbing the converters each time.
//
// Documentation: projects/components/converters/rtl/peakrdl_to_cmdrsp.sv
//                rtl/amba/apb4/apb4_slave_cdc.sv
`timescale 1ns / 1ps

module apb4_to_peakrdl #(
    parameter int ADDR_WIDTH = 12,   // APB + cpuif byte address width
    parameter int DATA_WIDTH = 32,   // Must match PeakRDL generation (32)
    parameter int PROT_WIDTH = 3,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    // CDC command/response FIFO depth (>=2)
    parameter int CDC_DEPTH  = 2,
    // Async-FIFO pointer encoding, forwarded to the CDC block below:
    // 0 = Gray (power-of-2 depth only), 1 = Johnson (any depth, DEPTH-bit
    // pointers). Gray by default -- Johnson is opt-in.
    parameter int USE_JOHNSON = 0,
    parameter bit USE_2_PHASE_CDC = 1'b1
) (
    // Register/core clock domain (drives the cpuif master)
    input  logic                    aclk,
    input  logic                    aresetn,
    // APB clock domain
    input  logic                    pclk,
    input  logic                    presetn,

    // ---- APB slave port ----
    input  logic                    s_apb_PSEL,
    input  logic                    s_apb_PENABLE,
    output logic                    s_apb_PREADY,
    input  logic [ADDR_WIDTH-1:0]   s_apb_PADDR,
    input  logic                    s_apb_PWRITE,
    input  logic [DATA_WIDTH-1:0]   s_apb_PWDATA,
    input  logic [STRB_WIDTH-1:0]   s_apb_PSTRB,
    input  logic [PROT_WIDTH-1:0]   s_apb_PPROT,
    output logic [DATA_WIDTH-1:0]   s_apb_PRDATA,
    output logic                    s_apb_PSLVERR,

    // ---- PeakRDL passthrough (cpuif) master ----
    output logic                    cpuif_req,
    output logic                    cpuif_req_is_wr,
    output logic [ADDR_WIDTH-1:0]   cpuif_addr,
    output logic [DATA_WIDTH-1:0]   cpuif_wr_data,
    output logic [DATA_WIDTH-1:0]   cpuif_wr_biten,
    input  logic                    cpuif_req_stall_wr,
    input  logic                    cpuif_req_stall_rd,
    input  logic                    cpuif_rd_ack,
    input  logic                    cpuif_rd_err,
    input  logic [DATA_WIDTH-1:0]   cpuif_rd_data,
    input  logic                    cpuif_wr_ack,
    input  logic                    cpuif_wr_err
);

    // ---- CMD/RSP link between the two stages ----
    logic                    cmd_valid, cmd_ready, cmd_pwrite;
    logic [ADDR_WIDTH-1:0]   cmd_paddr;
    logic [DATA_WIDTH-1:0]   cmd_pwdata;
    logic [STRB_WIDTH-1:0]   cmd_pstrb;
    logic [PROT_WIDTH-1:0]   cmd_pprot;
    logic                    rsp_valid, rsp_ready, rsp_pslverr;
    logic [DATA_WIDTH-1:0]   rsp_prdata;

    // Stage 1: APB (pclk) -> CMD/RSP (aclk)
    apb4_slave_cdc #(
        .ADDR_WIDTH      (ADDR_WIDTH),
        .DATA_WIDTH      (DATA_WIDTH),
        .STRB_WIDTH      (STRB_WIDTH),
        .PROT_WIDTH      (PROT_WIDTH),
        .DEPTH           (CDC_DEPTH),
        .USE_2_PHASE_CDC (USE_2_PHASE_CDC),
        .USE_JOHNSON     (USE_JOHNSON)
    ) u_apb_cdc (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .pclk        (pclk),
        .presetn     (presetn),
        .s_apb_PSEL  (s_apb_PSEL),
        .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY(s_apb_PREADY),
        .s_apb_PADDR (s_apb_PADDR),
        .s_apb_PWRITE(s_apb_PWRITE),
        .s_apb_PWDATA(s_apb_PWDATA),
        .s_apb_PSTRB (s_apb_PSTRB),
        .s_apb_PPROT (s_apb_PPROT),
        .s_apb_PRDATA(s_apb_PRDATA),
        .s_apb_PSLVERR(s_apb_PSLVERR),
        .cmd_valid   (cmd_valid),
        .cmd_ready   (cmd_ready),
        .cmd_pwrite  (cmd_pwrite),
        .cmd_paddr   (cmd_paddr),
        .cmd_pwdata  (cmd_pwdata),
        .cmd_pstrb   (cmd_pstrb),
        .cmd_pprot   (cmd_pprot),
        .rsp_valid   (rsp_valid),
        .rsp_ready   (rsp_ready),
        .rsp_prdata  (rsp_prdata),
        .rsp_pslverr (rsp_pslverr)
    );

    // Stage 2: CMD/RSP (aclk) -> PeakRDL passthrough (cpuif)
    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH)
    ) u_cpuif (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .cmd_valid        (cmd_valid),
        .cmd_ready        (cmd_ready),
        .cmd_pwrite       (cmd_pwrite),
        .cmd_paddr        (cmd_paddr),
        .cmd_pwdata       (cmd_pwdata),
        .cmd_pstrb        (cmd_pstrb),
        .rsp_valid        (rsp_valid),
        .rsp_ready        (rsp_ready),
        .rsp_prdata       (rsp_prdata),
        .rsp_pslverr      (rsp_pslverr),
        .regblk_req       (cpuif_req),
        .regblk_req_is_wr (cpuif_req_is_wr),
        .regblk_addr      (cpuif_addr),
        .regblk_wr_data   (cpuif_wr_data),
        .regblk_wr_biten  (cpuif_wr_biten),
        .regblk_req_stall_wr(cpuif_req_stall_wr),
        .regblk_req_stall_rd(cpuif_req_stall_rd),
        .regblk_rd_ack    (cpuif_rd_ack),
        .regblk_rd_err    (cpuif_rd_err),
        .regblk_rd_data   (cpuif_rd_data),
        .regblk_wr_ack    (cpuif_wr_ack),
        .regblk_wr_err    (cpuif_wr_err)
    );

endmodule : apb4_to_peakrdl
