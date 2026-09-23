`timescale 1ns / 1ps

`include "reset_defs.svh"

// Module: cmdrsp_router
// Description: Routes CMD/RSP transactions based on address
//
// Routing Architecture:
//   - m0: retired (0x000-0x03F now takes the default route; m0 tied inactive)
//   - Default route:   Everything else → Configuration registers (peakrdl_to_cmdrsp)
//
// This ensures PeakRDL config space can handle any register address
// (including future additions like 0x220-0x230 descriptor engine config)
// without requiring router updates.
//
// The perf-profiler registers are NOT decoded here. They were hand-decoded
// in this module over 0x040-0x0FF; they are RDL registers now (PERF_CONFIG
// @ 0x2B0, PERF_DATA_LOW/HIGH and PERF_STATUS @ 0x2D0-0x2D8) and reach the
// config space by the default route like any other register. This module
// has no perf port.
//
// Protocol: CMD/RSP handshake protocol
//   - Command phase: valid/ready handshake with address, write flag, data
//   - Response phase: valid/ready handshake with read data or error

module cmdrsp_router #(
    parameter int ADDR_WIDTH = 12,  // Total address width
    parameter int DATA_WIDTH = 32
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // CMD/RSP Slave (from apb4_slave_cdc)
    input  logic                    s_cmd_valid,
    output logic                    s_cmd_ready,
    input  logic                    s_cmd_pwrite,
    input  logic [ADDR_WIDTH-1:0]   s_cmd_paddr,
    input  logic [DATA_WIDTH-1:0]   s_cmd_pwdata,
    output logic                    s_rsp_valid,
    input  logic                    s_rsp_ready,
    output logic [DATA_WIDTH-1:0]   s_rsp_prdata,
    output logic                    s_rsp_pslverr,

    // CMD/RSP Master 0: Descriptor kick-off (0x000-0x03F)
    output logic                    m0_cmd_valid,
    input  logic                    m0_cmd_ready,
    output logic                    m0_cmd_pwrite,
    output logic [ADDR_WIDTH-1:0]   m0_cmd_paddr,
    output logic [DATA_WIDTH-1:0]   m0_cmd_pwdata,
    input  logic                    m0_rsp_valid,
    output logic                    m0_rsp_ready,
    input  logic [DATA_WIDTH-1:0]   m0_rsp_prdata,
    input  logic                    m0_rsp_pslverr,

    // CMD/RSP Master 1: Configuration registers (default route for everything not m0)
    output logic                    m1_cmd_valid,
    input  logic                    m1_cmd_ready,
    output logic                    m1_cmd_pwrite,
    output logic [ADDR_WIDTH-1:0]   m1_cmd_paddr,
    output logic [DATA_WIDTH-1:0]   m1_cmd_pwdata,
    input  logic                    m1_rsp_valid,
    output logic                    m1_rsp_ready,
    input  logic [DATA_WIDTH-1:0]   m1_rsp_prdata,
    input  logic                    m1_rsp_pslverr
);

    //=========================================================================
    // Address Decode
    //=========================================================================
    logic addr_hit_m0;   // 0x000-0x03F - Descriptor kick-off (explicit)
    logic addr_hit_m1;   // Everything else - Configuration registers (default route)

    always_comb begin
        // 0x000-0x03F used to be carved out to a kick block, which snooped the
        // raw command stream to turn a descriptor-address WRITE into a kick.
        // Those addresses are now ordinary stored registers in the PeakRDL
        // block (launch moved to KICK_ENABLE), so the range falls through to
        // the default m1 route with everything else. m0 is retained, tied
        // inactive, so the router's port map is unchanged for other users.
        addr_hit_m0   = 1'b0;
        // The 0x040-0x0FF perf-profiler window used to be carved out here and
        // decoded by hand below. Those four registers are RDL registers now
        // (PERF_DATA_LOW/HIGH/STATUS @ 0x2D0-0x2D8; PERF_CONFIG was already
        // @ 0x2B0 and the copy here drove dangling nets), so the range falls
        // through to m1 like everything else.
        addr_hit_m1   = !addr_hit_m0;
    end

    //=========================================================================
    // Selection Tracking (for response routing)
    //=========================================================================
    logic r_sel_m0;
    logic r_sel_m1;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sel_m0   <= 1'b0;
            r_sel_m1   <= 1'b0;
        end else begin
            // Capture selection when command accepted
            if (s_cmd_valid && s_cmd_ready) begin
                r_sel_m0   <= addr_hit_m0;
                r_sel_m1   <= addr_hit_m1;
            end
            // Clear selection when response accepted
            if (s_rsp_valid && s_rsp_ready) begin
                r_sel_m0   <= 1'b0;
                r_sel_m1   <= 1'b0;
            end
        end
    )

    //=========================================================================
    // Command Routing
    //=========================================================================
    assign m0_cmd_valid  = s_cmd_valid && addr_hit_m0;
    assign m0_cmd_pwrite = s_cmd_pwrite;
    assign m0_cmd_paddr  = s_cmd_paddr;
    assign m0_cmd_pwdata = s_cmd_pwdata;

    // m1 gets everything that doesn't go to m0 (default route)
    assign m1_cmd_valid  = s_cmd_valid && addr_hit_m1;
    assign m1_cmd_pwrite = s_cmd_pwrite;
    assign m1_cmd_paddr  = s_cmd_paddr;
    assign m1_cmd_pwdata = s_cmd_pwdata;

    // Command ready (mux based on address, default to m1)
    assign s_cmd_ready = addr_hit_m0 ? m0_cmd_ready :
                         m1_cmd_ready;  // Default route to m1 for everything else

    //=========================================================================
    // Response Routing
    //=========================================================================
    // Default to m1 response if m0 was not selected
    assign s_rsp_valid   = r_sel_m0 ? m0_rsp_valid :
                           m1_rsp_valid;  // Default route

    assign s_rsp_prdata  = r_sel_m0 ? m0_rsp_prdata :
                           m1_rsp_prdata;  // Default route

    assign s_rsp_pslverr = r_sel_m0 ? m0_rsp_pslverr :
                           m1_rsp_pslverr;  // Default route (m1 handles errors)

    assign m0_rsp_ready = r_sel_m0 && s_rsp_ready;
    assign m1_rsp_ready = r_sel_m1 && s_rsp_ready;

endmodule : cmdrsp_router
