// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_to_peakrdl
// Purpose:
//   AXI4-Lite slave to the PeakRDL-regblock passthrough CPU interface, the
//   AXI-Lite counterpart of apb4_to_peakrdl (same clock, no CDC).
//
// Documentation: projects/components/utility-ip/converters/README.md
// Subsystem: converters
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: axil4_to_peakrdl
//==============================================================================
// Description:
//   One transaction at a time. A write needs both AW and W before it issues
//   one cpuif request (req_is_wr = 1) and returns B when the regblock
//   acknowledges; a read issues on AR and returns R with the acknowledged data.
//   Writes and reads are arbitrated write-first when both are pending; the
//   other waits, so ordering as seen by the regblock is the order of issue.
//   Regblock errors map to SLVERR. cpuif_req_stall_* hold the request.
//
//   Sized for register access from a UART bridge, not for throughput: one
//   outstanding transaction is the point, because the PeakRDL passthrough
//   interface acknowledges one request at a time.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH: AXI-Lite and cpuif byte address width. Default 12.
//   DATA_WIDTH: 32, as PeakRDL generates. Default 32.
//
//==============================================================================

module axil4_to_peakrdl #(
    parameter int ADDR_WIDTH = 12,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // AXI4-Lite slave
    input  logic [ADDR_WIDTH-1:0]   s_axil_awaddr,
    /* verilator lint_off UNUSEDSIGNAL */
    input  logic [2:0]              s_axil_awprot,
    /* verilator lint_on UNUSEDSIGNAL */
    input  logic                    s_axil_awvalid,
    output logic                    s_axil_awready,
    input  logic [DATA_WIDTH-1:0]   s_axil_wdata,
    input  logic [STRB_WIDTH-1:0]   s_axil_wstrb,
    input  logic                    s_axil_wvalid,
    output logic                    s_axil_wready,
    output logic [1:0]              s_axil_bresp,
    output logic                    s_axil_bvalid,
    input  logic                    s_axil_bready,
    input  logic [ADDR_WIDTH-1:0]   s_axil_araddr,
    /* verilator lint_off UNUSEDSIGNAL */
    input  logic [2:0]              s_axil_arprot,
    /* verilator lint_on UNUSEDSIGNAL */
    input  logic                    s_axil_arvalid,
    output logic                    s_axil_arready,
    output logic [DATA_WIDTH-1:0]   s_axil_rdata,
    output logic [1:0]              s_axil_rresp,
    output logic                    s_axil_rvalid,
    input  logic                    s_axil_rready,

    // PeakRDL passthrough cpuif
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

    typedef enum logic [2:0] {IDLE, WR_REQ, WR_WAIT, WR_RESP, RD_REQ, RD_WAIT, RD_RESP} state_t;
    state_t r_state;

    logic [ADDR_WIDTH-1:0] r_addr;
    logic [DATA_WIDTH-1:0] r_wdata;
    logic [STRB_WIDTH-1:0] r_wstrb;
    logic [DATA_WIDTH-1:0] r_rdata;
    logic                  r_err;

    // accept AW and W together (both must be valid), write-first arbitration
    assign s_axil_awready = (r_state == IDLE) && s_axil_awvalid && s_axil_wvalid;
    assign s_axil_wready  = s_axil_awready;
    assign s_axil_arready = (r_state == IDLE) && s_axil_arvalid && !(s_axil_awvalid && s_axil_wvalid);

    assign s_axil_bvalid  = (r_state == WR_RESP);
    assign s_axil_bresp   = r_err ? 2'b10 : 2'b00;
    assign s_axil_rvalid  = (r_state == RD_RESP);
    assign s_axil_rdata   = r_rdata;
    assign s_axil_rresp   = r_err ? 2'b10 : 2'b00;

    assign cpuif_req       = (r_state == WR_REQ) || (r_state == RD_REQ);
    assign cpuif_req_is_wr = (r_state == WR_REQ);
    assign cpuif_addr      = r_addr;
    assign cpuif_wr_data   = r_wdata;
    always_comb begin
        for (int i = 0; i < STRB_WIDTH; i++) cpuif_wr_biten[i*8 +: 8] = {8{r_wstrb[i]}};
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_state <= IDLE;
            r_addr  <= '0;
            r_wdata <= '0;
            r_wstrb <= '0;
            r_rdata <= '0;
            r_err   <= 1'b0;
        end else begin
            case (r_state)
                IDLE: begin
                    if (s_axil_awvalid && s_axil_wvalid) begin
                        r_addr  <= s_axil_awaddr;
                        r_wdata <= s_axil_wdata;
                        r_wstrb <= s_axil_wstrb;
                        r_state <= WR_REQ;
                    end else if (s_axil_arvalid) begin
                        r_addr  <= s_axil_araddr;
                        r_state <= RD_REQ;
                    end
                end
                // the regblock may acknowledge in the request cycle or later
                WR_REQ: if (!cpuif_req_stall_wr) begin
                    if (cpuif_wr_ack) begin r_err <= cpuif_wr_err; r_state <= WR_RESP; end
                    else r_state <= WR_WAIT;
                end
                WR_WAIT: if (cpuif_wr_ack) begin
                    r_err   <= cpuif_wr_err;
                    r_state <= WR_RESP;
                end
                WR_RESP: if (s_axil_bready) r_state <= IDLE;
                RD_REQ: if (!cpuif_req_stall_rd) begin
                    if (cpuif_rd_ack) begin
                        r_rdata <= cpuif_rd_data; r_err <= cpuif_rd_err; r_state <= RD_RESP;
                    end else r_state <= RD_WAIT;
                end
                RD_WAIT: if (cpuif_rd_ack) begin
                    r_rdata <= cpuif_rd_data;
                    r_err   <= cpuif_rd_err;
                    r_state <= RD_RESP;
                end
                RD_RESP: if (s_axil_rready) r_state <= IDLE;
                default: r_state <= IDLE;
            endcase
        end
    )

endmodule : axil4_to_peakrdl
