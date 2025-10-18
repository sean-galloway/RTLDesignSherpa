// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_slave_rd
// Purpose: Axi Slave Rd module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi_slave_rd
#(
    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Channel parameter
    parameter int CHANNELS          = 16,    // Number of channels to monitor (typically <= 2^AXI_ID_WIDTH)

    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // FIFO parameters
    parameter int ERROR_FIFO_DEPTH  = 2,
    parameter int ADDR_FIFO_DEPTH   = 4,     // Depth of address tracking FIFO

    // Timeout parameters (in clock cycles)
    parameter int TIMEOUT_AR        = 1000,  // Read address channel timeout
    parameter int TIMEOUT_R         = 1000,  // Read data channel timeout

    // Derived parameters
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Master AXI Interface (Input Side)
    // Read address channel (AR)
    output logic [AXI_ID_WIDTH-1:0]      fub_arid,
    output logic [AXI_ADDR_WIDTH-1:0]    fub_araddr,
    output logic [7:0]                   fub_arlen,
    output logic [2:0]                   fub_arsize,
    output logic [1:0]                   fub_arburst,
    output logic                         fub_arlock,
    output logic [3:0]                   fub_arcache,
    output logic [2:0]                   fub_arprot,
    output logic [3:0]                   fub_arqos,
    output logic [3:0]                   fub_arregion,
    output logic [AXI_USER_WIDTH-1:0]    fub_aruser,
    output logic                         fub_arvalid,
    input  logic                         fub_arready,

    // Read data channel (R)
    input  logic [AXI_ID_WIDTH-1:0]      fub_rid,
    input  logic [AXI_DATA_WIDTH-1:0]    fub_rdata,
    input  logic [1:0]                   fub_rresp,
    input  logic                         fub_rlast,
    input  logic [AXI_USER_WIDTH-1:0]    fub_ruser,
    input  logic                         fub_rvalid,
    output logic                         fub_rready,

    // Slave AXI Interface (Output Side to memory or backend)
    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]      s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]    s_axi_araddr,
    input  logic [7:0]                   s_axi_arlen,
    input  logic [2:0]                   s_axi_arsize,
    input  logic [1:0]                   s_axi_arburst,
    input  logic                         s_axi_arlock,
    input  logic [3:0]                   s_axi_arcache,
    input  logic [2:0]                   s_axi_arprot,
    input  logic [3:0]                   s_axi_arqos,
    input  logic [3:0]                   s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]    s_axi_aruser,
    input  logic                         s_axi_arvalid,
    output logic                         s_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]      s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]    s_axi_rdata,
    output logic [1:0]                   s_axi_rresp,
    output logic                         s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]    s_axi_ruser,
    output logic                         s_axi_rvalid,
    input  logic                         s_axi_rready,

    // Error outputs with FIFO interface
    output logic [3:0]                 fub_error_type,
    output logic [AXI_ADDR_WIDTH-1:0]  fub_error_addr,
    output logic [AXI_ID_WIDTH-1:0]    fub_error_id,
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready
);

    // Internal connections between error monitor and skid buffer
    logic                       int_arready;

    // SKID buffer connections
    logic [3:0]                int_ar_count;

    logic [3:0]                int_r_count;

    // Flow control signal (not used in this case)
    logic                      int_block_ready;

    // block the arready signal when the error monitor is full
    assign s_axi_arready = int_arready && !int_block_ready;

    // Instantiate base error monitor module directly
    axi_errmon_base #(
        .CHANNELS(CHANNELS),
        .ADDR_WIDTH(AXI_ADDR_WIDTH),
        .ID_WIDTH(AXI_ID_WIDTH),
        .TIMEOUT_ADDR(TIMEOUT_AR),
        .TIMEOUT_DATA(TIMEOUT_R),
        .TIMEOUT_RESP(0),         // Not used for read
        .ERROR_FIFO_DEPTH(ERROR_FIFO_DEPTH),
        .ADDR_FIFO_DEPTH(ADDR_FIFO_DEPTH),
        .IS_READ(1),              // This is a read monitor
        .IS_AXI(1)                // Full AXI (not AXI-Lite)
    ) i_axi_errmon_base (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Address channel signals (slave interface)
        .i_addr               (fub_araddr),
        .i_id                 (fub_arid),
        .i_valid              (fub_arvalid),
        .i_ready              (fub_arready),

        // Data channel signals (slave interface)
        .i_data_id            (fub_rid),
        .i_data_valid         (fub_rvalid),
        .i_data_ready         (fub_rready),
        .i_data_last          (fub_rlast),

        // Response channel signals (unused for read)
        .i_resp_id            ('0),
        .i_resp               (fub_rresp),
        .i_resp_valid         (1'b0),
        .i_resp_ready         (1'b0),

        // Error outputs
        .o_error_valid        (fub_error_valid),
        .i_error_ready        (fub_error_ready),
        .o_error_type         (fub_error_type),
        .o_error_addr         (fub_error_addr),
        .o_error_id           (fub_error_id),

        // Flow control
        .o_block_ready        (int_block_ready)
    );


    // Instantiate AR Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize)
    ) i_ar_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (s_axi_arvalid),
        .o_wr_ready               (int_arready),
        .i_wr_data                ({s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize,
                                    s_axi_arburst, s_axi_arlock, s_axi_arcache, s_axi_arprot,
                                    s_axi_arqos, s_axi_arregion, s_axi_aruser}),
        .o_rd_valid               (fub_arvalid),
        .i_rd_ready               (fub_arready),
        .o_rd_count               (int_ar_count),
        .o_rd_data                ({fub_arid, fub_araddr, fub_arlen, fub_arsize,
        fub_arburst, fub_arlock, fub_arcache, fub_arprot,
        fub_arqos, fub_arregion, fub_aruser})
    );


    // Instantiate R channel for read data from memory back to the master
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize)
    ) i_r_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (fub_rvalid),
        .o_wr_ready               (fub_rready),
        .i_wr_data                ({fub_rid, fub_rdata, fub_rresp, fub_rlast, fub_ruser}),
        .o_rd_valid               (s_axi_rvalid),
        .i_rd_ready               (s_axi_rready),
        .o_rd_count               (int_r_count),
        .o_rd_data                ({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser})
    );

endmodule : axi_slave_rd
