//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: axil4_slave_rd
        // Purpose: Axil4 Slave Rd module
        //
        // Documentation: rtl/amba/PRD.md
        // Subsystem: amba
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        module axil4_slave_rd
        #(
            // AXI-Lite parameters
            parameter int AXIL_ADDR_WIDTH    = 32,
            parameter int AXIL_DATA_WIDTH    = 32,
        
            // Skid buffer depths
            parameter int SKID_DEPTH_AR     = 2,
            parameter int SKID_DEPTH_R      = 4,
        
            // Derived parameters
            parameter int AW       = AXIL_ADDR_WIDTH,
            parameter int DW       = AXIL_DATA_WIDTH,
            parameter int ARSize   = AW+3,  // addr + prot
            parameter int RSize    = DW+2   // data + resp
        )
        (
            // Global Clock and Reset
 004718     input  logic aclk,
%000002     input  logic aresetn,
        
            // Slave AXI-Lite Interface (Input Side)
            // Read address channel (AR)
%000000     input  logic [AW-1:0]              s_axil_araddr,
%000000     input  logic [2:0]                 s_axil_arprot,
 000020     input  logic                       s_axil_arvalid,
%000003     output logic                       s_axil_arready,
        
            // Read data channel (R)
%000000     output logic [DW-1:0]              s_axil_rdata,
%000000     output logic [1:0]                 s_axil_rresp,
 000016     output logic                       s_axil_rvalid,
 000016     input  logic                       s_axil_rready,
        
            // Master AXI-Lite Interface (Output Side to memory or backend)
            // Read address channel (AR)
%000000     output logic [AW-1:0]              fub_araddr,
%000000     output logic [2:0]                 fub_arprot,
 000017     output logic                       fub_arvalid,
%000007     input  logic                       fub_arready,
        
            // Read data channel (R)
%000000     input  logic [DW-1:0]              fub_rdata,
%000000     input  logic [1:0]                 fub_rresp,
 000016     input  logic                       fub_rvalid,
%000002     output logic                       fub_rready,
        
            // Status outputs for clock gating
 000017     output logic                       busy
        );
        
            // Internal connections for skid buffer
%000000     logic [3:0]                int_ar_count;
%000000     logic [ARSize-1:0]         int_ar_pkt;
 000017     logic                      int_skid_arvalid;
%000007     logic                      int_skid_arready;
        
%000000     logic [3:0]                int_r_count;
%000000     logic [RSize-1:0]          int_r_pkt;
 000016     logic                      int_skid_rvalid;
 000016     logic                      int_skid_rready;
        
            // Busy signal indicates activity in the buffers
            assign busy = (int_ar_count > 0) || (int_r_count > 0) ||
                            s_axil_arvalid || fub_rvalid;
        
            // Instantiate AR Skid Buffer
            gaxi_skid_buffer #(
                .DEPTH(SKID_DEPTH_AR),
                .DATA_WIDTH(ARSize),
                .INSTANCE_NAME("AXIL_AR_SKID")
            ) i_ar_channel (
                .axi_aclk               (aclk),
                .axi_aresetn            (aresetn),
                .wr_valid               (s_axil_arvalid),
                .wr_ready               (s_axil_arready),
                .wr_data                ({s_axil_araddr, s_axil_arprot}),
                .rd_valid               (int_skid_arvalid),
                .rd_ready               (int_skid_arready),
                .rd_count               (int_ar_count),
                .rd_data                (int_ar_pkt),
                /* verilator lint_off PINCONNECTEMPTY */
                .count                  ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
        
            // Unpack AR signals from SKID buffer
            assign {fub_araddr, fub_arprot} = int_ar_pkt;
            assign fub_arvalid = int_skid_arvalid;
            assign int_skid_arready = fub_arready;
        
            // Instantiate R channel for read data from memory back to the master
            gaxi_skid_buffer #(
                .DEPTH(SKID_DEPTH_R),
                .DATA_WIDTH(RSize),
                .INSTANCE_NAME("AXIL_R_SKID")
            ) i_r_channel (
                .axi_aclk               (aclk),
                .axi_aresetn            (aresetn),
                .wr_valid               (fub_rvalid),
                .wr_ready               (fub_rready),
                .wr_data                ({fub_rdata, fub_rresp}),
                .rd_valid               (int_skid_rvalid),
                .rd_ready               (int_skid_rready),
                .rd_count               (int_r_count),
                .rd_data                ({s_axil_rdata, s_axil_rresp}),
                /* verilator lint_off PINCONNECTEMPTY */
                .count                  ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
        
            assign s_axil_rvalid = int_skid_rvalid;
            assign int_skid_rready = s_axil_rready;
        
        endmodule : axil4_slave_rd
        
