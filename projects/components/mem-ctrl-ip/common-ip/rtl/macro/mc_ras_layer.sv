// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_ras_layer
// Purpose: Reliability/Availability/Serviceability (RAS) transform layer on the
//          two memory data seams: write-data forward and read-return backward.
//          Skeleton only: at HAS_ECC=ECC_OFF the layer elaborates to straight
//          wiring. ECC encode/detect/correct and scrubber are reserved for a
//          future enabling customer.
//
// Documentation: common-ip/docs/mc_ras_layer_knobs.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_ras_layer #(
    parameter int DATA_WIDTH     = 64,
    parameter int STRB_WIDTH     = DATA_WIDTH / 8,
    // HAS_ECC enum: 0=OFF (default), 1=DETECT, 2=CORRECT
    parameter int HAS_ECC        = 0,
    // ECC_MODE / ECC_CODE_WIDTH are reserved knobs (documented, not yet wired).
    parameter int ECC_MODE       = 0,
    parameter int ECC_CODE_WIDTH = 8
) (
    input logic clk,
    input logic rst_n,

    //=========================================================================
    // Write-data forward seam (upstream -> downstream)
    //=========================================================================
    input  logic                wdata_valid_i,
    output logic                wdata_ready_o,
    input  logic [DATA_WIDTH-1:0] wdata_data_i,
    input  logic [STRB_WIDTH-1:0] wdata_strb_i,
    input  logic                wdata_last_i,

    output logic                wdata_valid_o,
    input  logic                wdata_ready_i,
    output logic [DATA_WIDTH-1:0] wdata_data_o,
    output logic [STRB_WIDTH-1:0] wdata_strb_o,
    output logic                wdata_last_o,

    //=========================================================================
    // Read-return backward seam (downstream -> upstream)
    //=========================================================================
    input  logic                rdata_valid_i,
    output logic                rdata_ready_o,
    input  logic [DATA_WIDTH-1:0] rdata_data_i,
    input  logic [1:0]          rdata_resp_i,
    input  logic                rdata_last_i,

    output logic                rdata_valid_o,
    input  logic                rdata_ready_i,
    output logic [DATA_WIDTH-1:0] rdata_data_o,
    output logic [1:0]          rdata_resp_o,
    output logic                rdata_last_o,

    //=========================================================================
    // Reserved CSR surface (reads 0 when HAS_ECC = OFF)
    //=========================================================================
    input  logic                csr_ecc_en_i,
    input  logic [1:0]          csr_ecc_mode_i,
    output logic [31:0]         csr_ecc_stat_o,

    output logic                busy_o
);

    if (HAS_ECC == 0) begin : gen_ecc_off
        // Zero-cost passthrough. Verilator lint of this branch shows no
        // combinational logic beyond the assigns themselves.
        assign wdata_valid_o = wdata_valid_i;
        assign wdata_ready_o = wdata_ready_i;
        assign wdata_data_o  = wdata_data_i;
        assign wdata_strb_o  = wdata_strb_i;
        assign wdata_last_o  = wdata_last_i;

        assign rdata_valid_o = rdata_valid_i;
        assign rdata_ready_o = rdata_ready_i;
        assign rdata_data_o  = rdata_data_i;
        assign rdata_resp_o  = rdata_resp_i;
        assign rdata_last_o  = rdata_last_i;

        assign csr_ecc_stat_o = '0;
        assign busy_o         = 1'b0;
    end else begin : gen_ecc_reserved
        // Reserved for ECC DETECT/CORRECT implementation. Until then the seam
        // remains a bit-identical passthrough so integration/lint can proceed.
        assign wdata_valid_o = wdata_valid_i;
        assign wdata_ready_o = wdata_ready_i;
        assign wdata_data_o  = wdata_data_i;
        assign wdata_strb_o  = wdata_strb_i;
        assign wdata_last_o  = wdata_last_i;

        assign rdata_valid_o = rdata_valid_i;
        assign rdata_ready_o = rdata_ready_i;
        assign rdata_data_o  = rdata_data_i;
        assign rdata_resp_o  = rdata_resp_i;
        assign rdata_last_o  = rdata_last_i;

        assign csr_ecc_stat_o = '0;
        assign busy_o         = 1'b0;
    end

endmodule : mc_ras_layer
