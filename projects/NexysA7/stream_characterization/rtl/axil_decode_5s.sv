// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: axil_decode_5s
// Purpose: 1-master -> 5-slave AXI4-Lite address decoder.
//
// One inbound AXI4-Lite master (from uart_axil_bridge) is fanned out to
// five downstream slaves based on address windows. A single transaction
// (read OR write) is in flight at a time; the UART command protocol is
// naturally serialized so this is fine.
//
// Slave address map (inputs are parameterized so the harness can change):
//   S0: STREAM APB         (config)
//   S1: harness_csr        (control/status)
//   S2: desc_ram           (descriptor preload)
//   S3: stream err FIFO    (read only)
//   S4: debug_sram         (trace read)
//
// A request that falls outside all slave windows returns DECERR.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil_decode_5s #(
    parameter int AW = 32,
    parameter int DW = 32,
    // Each slave's base and size (size must be power of two)
    parameter logic [AW-1:0] S0_BASE = 32'h0000_0000,
    parameter int            S0_SIZE = 32'h0000_1000,  // 4 KB
    parameter logic [AW-1:0] S1_BASE = 32'h0001_0000,
    parameter int            S1_SIZE = 32'h0000_0100,  // 256 B
    parameter logic [AW-1:0] S2_BASE = 32'h0002_0000,
    parameter int            S2_SIZE = 32'h0001_0000,  // 64 KB
    parameter logic [AW-1:0] S3_BASE = 32'h0003_0000,
    parameter int            S3_SIZE = 32'h0000_0040,  // 64 B
    parameter logic [AW-1:0] S4_BASE = 32'h0004_0000,
    parameter int            S4_SIZE = 32'h0004_0000   // 256 KB
) (
    input  logic            aclk,
    input  logic            aresetn,

    // =====================================================================
    // Slave-side: one inbound AXI4-Lite master connects here
    // =====================================================================
    input  logic [AW-1:0]   s_awaddr,
    input  logic [2:0]      s_awprot,
    input  logic            s_awvalid,
    output logic            s_awready,

    input  logic [DW-1:0]   s_wdata,
    input  logic [DW/8-1:0] s_wstrb,
    input  logic            s_wvalid,
    output logic            s_wready,

    output logic [1:0]      s_bresp,
    output logic            s_bvalid,
    input  logic            s_bready,

    input  logic [AW-1:0]   s_araddr,
    input  logic [2:0]      s_arprot,
    input  logic            s_arvalid,
    output logic            s_arready,

    output logic [DW-1:0]   s_rdata,
    output logic [1:0]      s_rresp,
    output logic            s_rvalid,
    input  logic            s_rready,

    // =====================================================================
    // Master-side: five downstream AXI4-Lite slaves
    // =====================================================================
    output logic [AW-1:0]   m0_awaddr, m1_awaddr, m2_awaddr, m3_awaddr, m4_awaddr,
    output logic [2:0]      m0_awprot, m1_awprot, m2_awprot, m3_awprot, m4_awprot,
    output logic            m0_awvalid, m1_awvalid, m2_awvalid, m3_awvalid, m4_awvalid,
    input  logic            m0_awready, m1_awready, m2_awready, m3_awready, m4_awready,

    output logic [DW-1:0]   m0_wdata,  m1_wdata,  m2_wdata,  m3_wdata,  m4_wdata,
    output logic [DW/8-1:0] m0_wstrb,  m1_wstrb,  m2_wstrb,  m3_wstrb,  m4_wstrb,
    output logic            m0_wvalid, m1_wvalid, m2_wvalid, m3_wvalid, m4_wvalid,
    input  logic            m0_wready, m1_wready, m2_wready, m3_wready, m4_wready,

    input  logic [1:0]      m0_bresp,  m1_bresp,  m2_bresp,  m3_bresp,  m4_bresp,
    input  logic            m0_bvalid, m1_bvalid, m2_bvalid, m3_bvalid, m4_bvalid,
    output logic            m0_bready, m1_bready, m2_bready, m3_bready, m4_bready,

    output logic [AW-1:0]   m0_araddr, m1_araddr, m2_araddr, m3_araddr, m4_araddr,
    output logic [2:0]      m0_arprot, m1_arprot, m2_arprot, m3_arprot, m4_arprot,
    output logic            m0_arvalid, m1_arvalid, m2_arvalid, m3_arvalid, m4_arvalid,
    input  logic            m0_arready, m1_arready, m2_arready, m3_arready, m4_arready,

    input  logic [DW-1:0]   m0_rdata,  m1_rdata,  m2_rdata,  m3_rdata,  m4_rdata,
    input  logic [1:0]      m0_rresp,  m1_rresp,  m2_rresp,  m3_rresp,  m4_rresp,
    input  logic            m0_rvalid, m1_rvalid, m2_rvalid, m3_rvalid, m4_rvalid,
    output logic            m0_rready, m1_rready, m2_rready, m3_rready, m4_rready
);

    // =========================================================================
    // Address hit functions
    // =========================================================================
    function automatic logic in_window(
        input logic [AW-1:0] addr,
        input logic [AW-1:0] base,
        input int            size
    );
        return (addr >= base) && (addr < (base + AW'(size)));
    endfunction

    // =========================================================================
    // Write-channel routing
    //
    // A write transaction is "owned" by one slave from AW accept through B ack.
    // Simple 2-state FSM tracks the owner. For the UART protocol we only ever
    // have one outstanding txn, so no need for sophisticated bookkeeping.
    // =========================================================================

    logic [2:0] r_wsel;   // which slave is servicing the current write (0..4, or 7=decerr)
    logic       r_wbusy;

    logic [2:0] w_wsel;
    always_comb begin
        if      (in_window(s_awaddr, S0_BASE, S0_SIZE)) w_wsel = 3'd0;
        else if (in_window(s_awaddr, S1_BASE, S1_SIZE)) w_wsel = 3'd1;
        else if (in_window(s_awaddr, S2_BASE, S2_SIZE)) w_wsel = 3'd2;
        else if (in_window(s_awaddr, S3_BASE, S3_SIZE)) w_wsel = 3'd3;
        else if (in_window(s_awaddr, S4_BASE, S4_SIZE)) w_wsel = 3'd4;
        else                                            w_wsel = 3'd7;  // decerr
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wbusy <= 1'b0;
            r_wsel  <= 3'd0;
        end else begin
            if (!r_wbusy && s_awvalid) begin
                r_wbusy <= 1'b1;
                r_wsel  <= w_wsel;
            end else if (r_wbusy && s_bvalid && s_bready) begin
                r_wbusy <= 1'b0;
            end
        end
    )

    // Active selection: use incoming w_wsel before r_wbusy latches
    logic [2:0] wsel_active;
    assign wsel_active = r_wbusy ? r_wsel : w_wsel;

    // AW channel fanout
    assign m0_awaddr  = s_awaddr; assign m0_awprot = s_awprot;
    assign m1_awaddr  = s_awaddr; assign m1_awprot = s_awprot;
    assign m2_awaddr  = s_awaddr; assign m2_awprot = s_awprot;
    assign m3_awaddr  = s_awaddr; assign m3_awprot = s_awprot;
    assign m4_awaddr  = s_awaddr; assign m4_awprot = s_awprot;

    assign m0_awvalid = s_awvalid && (wsel_active == 3'd0);
    assign m1_awvalid = s_awvalid && (wsel_active == 3'd1);
    assign m2_awvalid = s_awvalid && (wsel_active == 3'd2);
    assign m3_awvalid = s_awvalid && (wsel_active == 3'd3);
    assign m4_awvalid = s_awvalid && (wsel_active == 3'd4);

    // W channel fanout
    assign m0_wdata = s_wdata; assign m0_wstrb = s_wstrb;
    assign m1_wdata = s_wdata; assign m1_wstrb = s_wstrb;
    assign m2_wdata = s_wdata; assign m2_wstrb = s_wstrb;
    assign m3_wdata = s_wdata; assign m3_wstrb = s_wstrb;
    assign m4_wdata = s_wdata; assign m4_wstrb = s_wstrb;

    assign m0_wvalid = s_wvalid && (wsel_active == 3'd0);
    assign m1_wvalid = s_wvalid && (wsel_active == 3'd1);
    assign m2_wvalid = s_wvalid && (wsel_active == 3'd2);
    assign m3_wvalid = s_wvalid && (wsel_active == 3'd3);
    assign m4_wvalid = s_wvalid && (wsel_active == 3'd4);

    // B channel ready fanout
    assign m0_bready = s_bready && (r_wsel == 3'd0);
    assign m1_bready = s_bready && (r_wsel == 3'd1);
    assign m2_bready = s_bready && (r_wsel == 3'd2);
    assign m3_bready = s_bready && (r_wsel == 3'd3);
    assign m4_bready = s_bready && (r_wsel == 3'd4);

    // Upstream mux
    always_comb begin
        s_awready = 1'b0;
        s_wready  = 1'b0;
        s_bvalid  = 1'b0;
        s_bresp   = 2'b00;
        case (wsel_active)
            3'd0: begin s_awready = m0_awready; s_wready = m0_wready; end
            3'd1: begin s_awready = m1_awready; s_wready = m1_wready; end
            3'd2: begin s_awready = m2_awready; s_wready = m2_wready; end
            3'd3: begin s_awready = m3_awready; s_wready = m3_wready; end
            3'd4: begin s_awready = m4_awready; s_wready = m4_wready; end
            default: begin
                // DECERR path: accept AW/W and emit B with DECERR
                s_awready = 1'b1;
                s_wready  = 1'b1;
            end
        endcase
        case (r_wsel)
            3'd0: begin s_bvalid = m0_bvalid; s_bresp = m0_bresp; end
            3'd1: begin s_bvalid = m1_bvalid; s_bresp = m1_bresp; end
            3'd2: begin s_bvalid = m2_bvalid; s_bresp = m2_bresp; end
            3'd3: begin s_bvalid = m3_bvalid; s_bresp = m3_bresp; end
            3'd4: begin s_bvalid = m4_bvalid; s_bresp = m4_bresp; end
            3'd7: begin s_bvalid = r_wbusy;   s_bresp = 2'b11; end  // DECERR
            default: ;
        endcase
    end

    // =========================================================================
    // Read-channel routing (same pattern as write)
    // =========================================================================

    logic [2:0] r_rsel;
    logic       r_rbusy;

    logic [2:0] w_rsel;
    always_comb begin
        if      (in_window(s_araddr, S0_BASE, S0_SIZE)) w_rsel = 3'd0;
        else if (in_window(s_araddr, S1_BASE, S1_SIZE)) w_rsel = 3'd1;
        else if (in_window(s_araddr, S2_BASE, S2_SIZE)) w_rsel = 3'd2;
        else if (in_window(s_araddr, S3_BASE, S3_SIZE)) w_rsel = 3'd3;
        else if (in_window(s_araddr, S4_BASE, S4_SIZE)) w_rsel = 3'd4;
        else                                            w_rsel = 3'd7;
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rbusy <= 1'b0;
            r_rsel  <= 3'd0;
        end else begin
            if (!r_rbusy && s_arvalid) begin
                r_rbusy <= 1'b1;
                r_rsel  <= w_rsel;
            end else if (r_rbusy && s_rvalid && s_rready) begin
                r_rbusy <= 1'b0;
            end
        end
    )

    logic [2:0] rsel_active;
    assign rsel_active = r_rbusy ? r_rsel : w_rsel;

    // AR channel fanout
    assign m0_araddr  = s_araddr; assign m0_arprot = s_arprot;
    assign m1_araddr  = s_araddr; assign m1_arprot = s_arprot;
    assign m2_araddr  = s_araddr; assign m2_arprot = s_arprot;
    assign m3_araddr  = s_araddr; assign m3_arprot = s_arprot;
    assign m4_araddr  = s_araddr; assign m4_arprot = s_arprot;

    assign m0_arvalid = s_arvalid && (rsel_active == 3'd0);
    assign m1_arvalid = s_arvalid && (rsel_active == 3'd1);
    assign m2_arvalid = s_arvalid && (rsel_active == 3'd2);
    assign m3_arvalid = s_arvalid && (rsel_active == 3'd3);
    assign m4_arvalid = s_arvalid && (rsel_active == 3'd4);

    // R channel ready fanout
    assign m0_rready = s_rready && (r_rsel == 3'd0);
    assign m1_rready = s_rready && (r_rsel == 3'd1);
    assign m2_rready = s_rready && (r_rsel == 3'd2);
    assign m3_rready = s_rready && (r_rsel == 3'd3);
    assign m4_rready = s_rready && (r_rsel == 3'd4);

    always_comb begin
        s_arready = 1'b0;
        s_rvalid  = 1'b0;
        s_rdata   = '0;
        s_rresp   = 2'b00;
        case (rsel_active)
            3'd0: s_arready = m0_arready;
            3'd1: s_arready = m1_arready;
            3'd2: s_arready = m2_arready;
            3'd3: s_arready = m3_arready;
            3'd4: s_arready = m4_arready;
            default: s_arready = 1'b1;  // DECERR path: accept AR
        endcase
        case (r_rsel)
            3'd0: begin s_rvalid = m0_rvalid; s_rdata = m0_rdata; s_rresp = m0_rresp; end
            3'd1: begin s_rvalid = m1_rvalid; s_rdata = m1_rdata; s_rresp = m1_rresp; end
            3'd2: begin s_rvalid = m2_rvalid; s_rdata = m2_rdata; s_rresp = m2_rresp; end
            3'd3: begin s_rvalid = m3_rvalid; s_rdata = m3_rdata; s_rresp = m3_rresp; end
            3'd4: begin s_rvalid = m4_rvalid; s_rdata = m4_rdata; s_rresp = m4_rresp; end
            3'd7: begin s_rvalid = r_rbusy;   s_rdata = 32'hDEAD_BEEF; s_rresp = 2'b11; end
            default: ;
        endcase
    end

endmodule : axil_decode_5s
