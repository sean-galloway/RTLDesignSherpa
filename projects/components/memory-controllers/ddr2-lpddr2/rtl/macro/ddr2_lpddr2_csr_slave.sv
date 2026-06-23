// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: ddr2_lpddr2_csr_slave
// Purpose: APB CSR slave for the DDR2/LPDDR2 memory controller. Mirrors
//          the stream component's CSR methodology: APB → CDC → CMD/RSP
//          → PeakRDL passthrough → generated register block. The hwif_*
//          struct is forwarded to ddr2_lpddr2_config_block.sv for
//          projection into mc_clk-domain config / status signals.
//
// Three-block stack:
//   1. apb_slave_cdc        — APB (pclk) → CMD/RSP (aclk) crossing
//   2. peakrdl_to_cmdrsp    — CMD/RSP → PeakRDL passthrough adapter
//   3. ddr2_lpddr2_csr      — PeakRDL-generated register block
//
// CSR map: docs/ddr2_lpddr2_has/ch06_integration/03_csr_map.md
// RDL src: rtl/macro/ddr2_lpddr2_csr.rdl
// Layout : docs/csr_obs_layout.md (obs_words readback at 0x1C0+)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module ddr2_lpddr2_csr_slave
    import ddr2_lpddr2_csr_pkg::*;
#(
    parameter int APB_ADDR_WIDTH = 12,
    parameter int APB_DATA_WIDTH = 32,
    parameter int APB_STRB_WIDTH = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH = 3
) (
    // mc_clk-domain (controller core) reset + clock
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,

    // APB-domain clock + reset
    input  logic                          pclk,
    input  logic                          presetn,

    // APB slave port
    input  logic                          s_apb_PSEL,
    input  logic                          s_apb_PENABLE,
    output logic                          s_apb_PREADY,
    input  logic [APB_ADDR_WIDTH-1:0]     s_apb_PADDR,
    input  logic                          s_apb_PWRITE,
    input  logic [APB_DATA_WIDTH-1:0]     s_apb_PWDATA,
    input  logic [APB_STRB_WIDTH-1:0]     s_apb_PSTRB,
    input  logic [APB_PROT_WIDTH-1:0]     s_apb_PPROT,
    output logic [APB_DATA_WIDTH-1:0]     s_apb_PRDATA,
    output logic                          s_apb_PSLVERR,

    // Register hwif (consumed by ddr2_lpddr2_config_block)
    output ddr2_lpddr2_csr__out_t         hwif_out,
    input  ddr2_lpddr2_csr__in_t          hwif_in
);

    //=========================================================================
    // 1. APB → CMD/RSP with CDC (pclk → mc_clk)
    //=========================================================================
    logic                          cmd_valid;
    logic                          cmd_ready;
    logic                          cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]     cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]     cmd_pwdata;
    logic [APB_STRB_WIDTH-1:0]     cmd_pstrb;
    logic [APB_PROT_WIDTH-1:0]     cmd_pprot;

    logic                          rsp_valid;
    logic                          rsp_ready;
    logic [APB_DATA_WIDTH-1:0]     rsp_prdata;
    logic                          rsp_pslverr;

    apb_slave_cdc #(
        .ADDR_WIDTH      (APB_ADDR_WIDTH),
        .DATA_WIDTH      (APB_DATA_WIDTH),
        .STRB_WIDTH      (APB_STRB_WIDTH),
        .PROT_WIDTH      (APB_PROT_WIDTH),
        .USE_2_PHASE_CDC (1'b1)
    ) u_apb_slave_cdc (
        .aclk             (mc_clk),
        .aresetn          (mc_rst_n),
        .pclk             (pclk),
        .presetn          (presetn),
        .s_apb_PSEL       (s_apb_PSEL),
        .s_apb_PENABLE    (s_apb_PENABLE),
        .s_apb_PREADY     (s_apb_PREADY),
        .s_apb_PADDR      (s_apb_PADDR),
        .s_apb_PWRITE     (s_apb_PWRITE),
        .s_apb_PWDATA     (s_apb_PWDATA),
        .s_apb_PSTRB      (s_apb_PSTRB),
        .s_apb_PPROT      (s_apb_PPROT),
        .s_apb_PRDATA     (s_apb_PRDATA),
        .s_apb_PSLVERR    (s_apb_PSLVERR),
        .cmd_valid        (cmd_valid),
        .cmd_ready        (cmd_ready),
        .cmd_pwrite       (cmd_pwrite),
        .cmd_paddr        (cmd_paddr),
        .cmd_pwdata       (cmd_pwdata),
        .cmd_pstrb        (cmd_pstrb),
        .cmd_pprot        (cmd_pprot),
        .rsp_valid        (rsp_valid),
        .rsp_ready        (rsp_ready),
        .rsp_prdata       (rsp_prdata),
        .rsp_pslverr      (rsp_pslverr)
    );

    //=========================================================================
    // 2. CMD/RSP → PeakRDL passthrough adapter
    //=========================================================================
    logic                          regblk_req;
    logic                          regblk_req_is_wr;
    logic [APB_ADDR_WIDTH-1:0]     regblk_addr;
    logic [APB_DATA_WIDTH-1:0]     regblk_wr_data;
    logic [APB_DATA_WIDTH-1:0]     regblk_wr_biten;
    logic                          regblk_req_stall_wr;
    logic                          regblk_req_stall_rd;
    logic                          regblk_rd_ack;
    logic                          regblk_rd_err;
    logic [APB_DATA_WIDTH-1:0]     regblk_rd_data;
    logic                          regblk_wr_ack;
    logic                          regblk_wr_err;

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_peakrdl_adapter (
        .aclk                 (mc_clk),
        .aresetn              (mc_rst_n),
        .cmd_valid            (cmd_valid),
        .cmd_ready            (cmd_ready),
        .cmd_pwrite           (cmd_pwrite),
        .cmd_paddr            (cmd_paddr),
        .cmd_pwdata           (cmd_pwdata),
        .cmd_pstrb            (cmd_pstrb),
        .rsp_valid            (rsp_valid),
        .rsp_ready            (rsp_ready),
        .rsp_prdata           (rsp_prdata),
        .rsp_pslverr          (rsp_pslverr),
        .regblk_req           (regblk_req),
        .regblk_req_is_wr     (regblk_req_is_wr),
        .regblk_addr          (regblk_addr),
        .regblk_wr_data       (regblk_wr_data),
        .regblk_wr_biten      (regblk_wr_biten),
        .regblk_req_stall_wr  (regblk_req_stall_wr),
        .regblk_req_stall_rd  (regblk_req_stall_rd),
        .regblk_rd_ack        (regblk_rd_ack),
        .regblk_rd_err        (regblk_rd_err),
        .regblk_rd_data       (regblk_rd_data),
        .regblk_wr_ack        (regblk_wr_ack),
        .regblk_wr_err        (regblk_wr_err)
    );

    //=========================================================================
    // 3. PeakRDL register block
    //=========================================================================
    ddr2_lpddr2_csr u_regs (
        .clk                  (mc_clk),
        .rst                  (~mc_rst_n),
        .s_cpuif_req          (regblk_req),
        .s_cpuif_req_is_wr    (regblk_req_is_wr),
        .s_cpuif_addr         (regblk_addr),
        .s_cpuif_wr_data      (regblk_wr_data),
        .s_cpuif_wr_biten     (regblk_wr_biten),
        .s_cpuif_req_stall_wr (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd (regblk_req_stall_rd),
        .s_cpuif_rd_ack       (regblk_rd_ack),
        .s_cpuif_rd_err       (regblk_rd_err),
        .s_cpuif_rd_data      (regblk_rd_data),
        .s_cpuif_wr_ack       (regblk_wr_ack),
        .s_cpuif_wr_err       (regblk_wr_err),
        .hwif_in              (hwif_in),
        .hwif_out             (hwif_out)
    );

    // PSTRB and PPROT not consumed by the regblock — silence lint.
    wire unused_cmd = |{ cmd_pstrb, cmd_pprot };

endmodule : ddr2_lpddr2_csr_slave
