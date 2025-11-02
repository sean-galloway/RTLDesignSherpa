// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hpet_regs_wrapper
// Purpose: Hpet Regs Wrapper module
//
// Documentation: projects/components/peakrdl/PRD.md
// Subsystem: peakrdl
//
// Author: sean galloway
// Created: 2025-10-18

module hpet_regs_wrapper #(
    parameter int VENDOR_ID = 1,
    parameter int REVISION_ID = 1,
    parameter int NUM_TIMERS = 2
) (
    // Clock and Reset
    input  logic                    aclk,
    input  logic                    aresetn,

    // Command Interface (rtldesignsherpa standard)
    input  logic                    cmd_valid,
    output logic                    cmd_ready,
    input  logic                    cmd_pwrite,
    input  logic [11:0]             cmd_paddr,
    input  logic [31:0]             cmd_pwdata,
    input  logic [3:0]              cmd_pstrb,

    // Response Interface (rtldesignsherpa standard)
    output logic                    rsp_valid,
    input  logic                    rsp_ready,
    output logic [31:0]             rsp_prdata,
    output logic                    rsp_pslverr,

    // Hardware Interface (connect to HPET core)
    input  hpet_regs_pkg::hpet_regs__in_t  hwif_in,
    output hpet_regs_pkg::hpet_regs__out_t hwif_out
);

    // =========================================================================
    // PeakRDL Passthrough Register Block Interface Signals
    // =========================================================================
    logic        regblk_req;
    logic        regblk_req_is_wr;
    logic [11:0] regblk_addr;          // 12-bit address (adapter handles width)
    logic [31:0] regblk_wr_data;
    logic [31:0] regblk_wr_biten;
    logic        regblk_req_stall_wr;
    logic        regblk_req_stall_rd;
    logic        regblk_rd_ack;
    logic        regblk_rd_err;
    logic [31:0] regblk_rd_data;
    logic        regblk_wr_ack;
    logic        regblk_wr_err;

    // =========================================================================
    // Instantiate Generic PeakRDL to CMD/RSP Adapter
    // =========================================================================
    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk                   (aclk),
        .aresetn                (aresetn),

        // CMD/RSP interface (to HPET)
        .cmd_valid              (cmd_valid),
        .cmd_ready              (cmd_ready),
        .cmd_pwrite             (cmd_pwrite),
        .cmd_paddr              (cmd_paddr),
        .cmd_pwdata             (cmd_pwdata),
        .cmd_pstrb              (cmd_pstrb),

        .rsp_valid              (rsp_valid),
        .rsp_ready              (rsp_ready),
        .rsp_prdata             (rsp_prdata),
        .rsp_pslverr            (rsp_pslverr),

        // PeakRDL passthrough interface
        .regblk_req             (regblk_req),
        .regblk_req_is_wr       (regblk_req_is_wr),
        .regblk_addr            (regblk_addr),
        .regblk_wr_data         (regblk_wr_data),
        .regblk_wr_biten        (regblk_wr_biten),
        .regblk_req_stall_wr    (regblk_req_stall_wr),
        .regblk_req_stall_rd    (regblk_req_stall_rd),
        .regblk_rd_ack          (regblk_rd_ack),
        .regblk_rd_err          (regblk_rd_err),
        .regblk_rd_data         (regblk_rd_data),
        .regblk_wr_ack          (regblk_wr_ack),
        .regblk_wr_err          (regblk_wr_err)
    );

    // =========================================================================
    // Instantiate PeakRDL-generated Register Block
    // =========================================================================
    hpet_regs u_hpet_regs (
        .clk                    (aclk),
        .rst                    (~aresetn),  // PeakRDL uses active-high reset

        // CPU Interface (passthrough) - lower 9 bits of address used
        .s_cpuif_req            (regblk_req),
        .s_cpuif_req_is_wr      (regblk_req_is_wr),
        .s_cpuif_addr           (regblk_addr[8:0]),  // PeakRDL uses 9-bit address
        .s_cpuif_wr_data        (regblk_wr_data),
        .s_cpuif_wr_biten       (regblk_wr_biten),
        .s_cpuif_req_stall_wr   (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd   (regblk_req_stall_rd),
        .s_cpuif_rd_ack         (regblk_rd_ack),
        .s_cpuif_rd_err         (regblk_rd_err),
        .s_cpuif_rd_data        (regblk_rd_data),
        .s_cpuif_wr_ack         (regblk_wr_ack),
        .s_cpuif_wr_err         (regblk_wr_err),

        // Hardware Interface
        .hwif_in                (hwif_in),
        .hwif_out               (hwif_out)
    );

endmodule

