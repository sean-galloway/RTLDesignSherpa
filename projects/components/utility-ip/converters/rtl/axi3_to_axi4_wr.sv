// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi3_to_axi4_wr
// Purpose: AXI3 to AXI4 Protocol Converter (WRITE-ONLY)
//
// Description:
//   Converts AXI3 protocol to AXI4 for WRITE path only by:
//   - Zero-extending AXI3 AWLEN (4 bits) to AXI4 AWLEN (8 bits)
//   - Mapping AXI3 2-bit AWLOCK to AXI4 1-bit AWLOCK
//     (normal -> 1'b0, locked -> 1'b0, exclusive -> 1'b1)
//   - Passing through ID, address, size, burst, cache, prot, user
//   - Stripping the AXI3 WID signal; AXI4 W has no id concept
//   - Passing through WDATA, WSTRB, WLAST, WUSER
//   - Passing through B channel (bid, bresp, buser)
//
//   Every channel passes straight through, so any number of writes may be
//   in flight. The contract is AXI3 write-interleave depth 1: W bursts come
//   in AW order (W may lead its AW). A simulation-only check,
//   ASSERT_A3_WID_STABLE, fires if WID changes inside a burst or a burst's
//   WID is not the AWID of the AW it pairs with in order. (Until 2026-10-18
//   the converter took one write at a time, holding AW from acceptance to
//   B: a master's writes ran at beats / (beats + round trip), bridge W7.)
//
//   Standalone write-only implementation. For read conversion, use
//   axi3_to_axi4_rd.sv.
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI3/AXI4 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI3/AXI4 side (0-1024)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - Write-only: No read path support
//   - No write-data interleaving: W bursts must follow AW order
//
// Author: RTL Design Sherpa
// Created: 2026-10-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi3_to_axi4_wr #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Calculated Parameters
    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI3 Write Interface (Input - AXI3 Protocol)
    //==========================================================================

    // Write Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi3_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi3_awaddr,
    input  logic [3:0]                  s_axi3_awlen,
    input  logic [2:0]                  s_axi3_awsize,
    input  logic [1:0]                  s_axi3_awburst,
    input  logic [1:0]                  s_axi3_awlock,
    input  logic [3:0]                  s_axi3_awcache,
    input  logic [2:0]                  s_axi3_awprot,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi3_awuser,
    input  logic                        s_axi3_awvalid,
    output logic                        s_axi3_awready,

    // Write Data Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi3_wid,
    input  logic [AXI_DATA_WIDTH-1:0]   s_axi3_wdata,
    input  logic [STRB_WIDTH-1:0]       s_axi3_wstrb,
    input  logic                        s_axi3_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi3_wuser,
    input  logic                        s_axi3_wvalid,
    output logic                        s_axi3_wready,

    // Write Response Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi3_bid,
    output logic [1:0]                  s_axi3_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi3_buser,
    output logic                        s_axi3_bvalid,
    input  logic                        s_axi3_bready,

    //==========================================================================
    // Master AXI4 Write Interface (Output - Full Protocol)
    //==========================================================================

    // Write Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awlock,
    output logic [3:0]                  m_axi_awcache,
    output logic [2:0]                  m_axi_awprot,
    output logic [3:0]                  m_axi_awqos,
    output logic [3:0]                  m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_awuser,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    // Write Data Channel
    output logic [AXI_DATA_WIDTH-1:0]   m_axi_wdata,
    output logic [STRB_WIDTH-1:0]       m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_wuser,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // Write Response Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi_buser,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready
);

    //==========================================================================
    // AXI3 to AXI4 Write Address Channel Mapping
    //==========================================================================

    assign s_axi3_awready = m_axi_awready;
    assign m_axi_awvalid  = s_axi3_awvalid;

    assign m_axi_awid     = s_axi3_awid;
    assign m_axi_awaddr   = s_axi3_awaddr;
    assign m_axi_awlen    = {4'b0, s_axi3_awlen};
    assign m_axi_awsize   = s_axi3_awsize;
    assign m_axi_awburst  = s_axi3_awburst;
    assign m_axi_awlock   = (s_axi3_awlock == 2'b01) ? 1'b1 : 1'b0;
    assign m_axi_awcache  = s_axi3_awcache;
    assign m_axi_awprot   = s_axi3_awprot;
    assign m_axi_awqos    = 4'b0;
    assign m_axi_awregion = 4'b0;
    assign m_axi_awuser   = s_axi3_awuser;

    //==========================================================================
    // AXI3 to AXI4 Write Data Channel: WID Stripping
    //==========================================================================

    assign s_axi3_wready = m_axi_wready;
    assign m_axi_wvalid  = s_axi3_wvalid;

    assign m_axi_wdata   = s_axi3_wdata;
    assign m_axi_wstrb   = s_axi3_wstrb;
    assign m_axi_wlast   = s_axi3_wlast;
    assign m_axi_wuser   = s_axi3_wuser;

    //==========================================================================
    // AXI4 to AXI3 Write Response Channel Pass-Through
    //==========================================================================

    assign s_axi3_bid    = m_axi_bid;
    assign s_axi3_bresp  = m_axi_bresp;
    assign s_axi3_buser  = m_axi_buser;
    assign s_axi3_bvalid = m_axi_bvalid;
    assign m_axi_bready  = s_axi3_bready;

    //==========================================================================
    // WID Order Check (simulation only)
    //==========================================================================
    // AXI4 W has no ID, so the WID is dropped; that is only correct if W
    // bursts arrive in AW order. Pair the n-th AW with the n-th W burst --
    // in whichever order they arrive -- and compare IDs; also hold WID
    // stable inside a burst. A contract check on the attached master, not
    // logic the converter needs: it costs no gates.
`ifndef SYNTHESIS
    // synthesis translate_off
    logic [AXI_ID_WIDTH-1:0] chk_awids [$];
    logic [AXI_ID_WIDTH-1:0] chk_wids  [$];
    logic                    chk_in_burst;
    logic [AXI_ID_WIDTH-1:0] chk_burst_wid;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            chk_awids.delete();
            chk_wids.delete();
            chk_in_burst  <= 1'b0;
            chk_burst_wid <= '0;
        end else begin
            if (s_axi3_awvalid && s_axi3_awready)
                chk_awids.push_back(s_axi3_awid);
            if (s_axi3_wvalid && s_axi3_wready) begin
                if (chk_in_burst && (s_axi3_wid != chk_burst_wid))
                    $error("ASSERT_A3_WID_STABLE: s_axi3_wid (0x%0h) changed mid-burst (burst WID 0x%0h)",
                           s_axi3_wid, chk_burst_wid);
                if (!chk_in_burst)
                    chk_wids.push_back(s_axi3_wid);
                chk_in_burst  <= !s_axi3_wlast;
                chk_burst_wid <= s_axi3_wid;
            end
            if ((chk_awids.size() > 0) && (chk_wids.size() > 0)) begin
                if (chk_awids[0] != chk_wids[0])
                    $error("ASSERT_A3_WID_STABLE: W burst WID 0x%0h differs from its AWID 0x%0h (W out of AW order)",
                           chk_wids[0], chk_awids[0]);
                void'(chk_awids.pop_front());
                void'(chk_wids.pop_front());
            end
        end
    )
    // synthesis translate_on
`endif

endmodule : axi3_to_axi4_wr
