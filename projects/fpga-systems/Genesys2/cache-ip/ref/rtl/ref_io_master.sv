// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ref_io_master
// Purpose:
//   The reference rig's doorbell master on onyx's ACE-Lite IO port (onyx
//   TASK-001 step 7, D1): one single-beat read or write per go pulse from
//   the harness CSR (IO_ADDR / IO_WDATA / IO_CTRL), the response and the
//   read data back on IO_STATUS / IO_RDATA.  A shareable access carries
//   AxDOMAIN Outer Shareable (ReadOnce / WriteUnique); a non-shareable one
//   carries Non-shareable (ReadNoSnoop / WriteNoSnoop).  It is the host's
//   hand on the IO port -- slow, one transaction at a time, exact -- so the
//   board can show an IO read seeing a cache's dirty line and an IO write
//   invalidating the caches' copies.  Not a traffic generator.
//
// Documentation: projects/components/cache-ip/onyx-ace-ccu/docs/onyx_has/ch04_interfaces/05_io_port_ace_lite.md
// Subsystem: fpga-systems / cache-ip reference rig
//
// Author: sean galloway
// Created: 2026-11-23
//==============================================================================
// Module: ref_io_master
//==============================================================================
// Description:
//   go_i (one-cycle pulse) with write_i / shareable_i / addr_i / wdata_i /
//   wstrb_i latched: a write issues AW then one W beat (WLAST) and waits
//   for B; a read issues AR and waits for one R beat (RLAST).  busy_o is
//   high from the go to the response; done_o rises with the response and
//   holds until the next go; resp_o is the BRESP / RRESP[1:0]; rdata_o the
//   read beat.  Every address and data field is held stable while VALID is
//   high (AXI).  A go while busy is ignored.
//
//------------------------------------------------------------------------------
// Parameters:
//   ADDR_WIDTH / BUS_WIDTH / ID_WIDTH / USER_WIDTH -- the IO port's.
//   AXI_ID -- the ID the doorbell's transactions carry (reads and writes).
//------------------------------------------------------------------------------
// Notes:
//   - Single clock / active-low reset (aclk / aresetn); ALWAYS_FF_RST macros.
//   - A control FSM of five states; no data moves through it beat by beat
//     (one beat per transaction), so the house no-FSM-on-the-datapath rule
//     is not in play.
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: ref_harness (REF_CACHE_SEL 4 / 5), driven by
//     ref_harness_csr's IO_* registers
//   - Drives: onyx_top's io_* port
//------------------------------------------------------------------------------
// Test:
//   Location: projects/fpga-systems/Genesys2/cache-ip/ref/dv/tests/test_ref_harness_axil.py
//   Run: cd projects/fpga-systems/Genesys2/cache-ip/ref/dv/tests && make clean-all && make run-all-gate-parallel
//==============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module ref_io_master #(
    parameter int ADDR_WIDTH = 32,
    parameter int BUS_WIDTH  = 64,
    parameter int ID_WIDTH   = 8,
    parameter int USER_WIDTH = 1,
    parameter logic [7:0] AXI_ID = 8'hE0,
    localparam int STRB_W = BUS_WIDTH / 8
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // the doorbell (harness CSR)
    input  logic                    go_i,          // one-cycle pulse
    input  logic                    write_i,
    input  logic                    shareable_i,
    input  logic [ADDR_WIDTH-1:0]   addr_i,
    input  logic [BUS_WIDTH-1:0]    wdata_i,
    input  logic [STRB_W-1:0]       wstrb_i,
    output logic                    busy_o,
    output logic                    done_o,        // holds until the next go
    output logic [1:0]              resp_o,
    output logic [BUS_WIDTH-1:0]    rdata_o,

    // onyx's ACE-Lite IO port
    output logic [ID_WIDTH-1:0]     io_arid,
    output logic [ADDR_WIDTH-1:0]   io_araddr,
    output logic [7:0]              io_arlen,
    output logic [2:0]              io_arsize,
    output logic [1:0]              io_arburst,
    output logic                    io_arlock,
    output logic [3:0]              io_arcache,
    output logic [2:0]              io_arprot,
    output logic [3:0]              io_arqos,
    output logic [3:0]              io_arregion,
    output logic [USER_WIDTH-1:0]   io_aruser,
    output logic [3:0]              io_arsnoop,
    output logic [1:0]              io_ardomain,
    output logic [1:0]              io_arbar,
    output logic                    io_arvalid,
    input  logic                    io_arready,
    input  logic [ID_WIDTH-1:0]     io_rid,
    input  logic [BUS_WIDTH-1:0]    io_rdata,
    input  logic [1:0]              io_rresp,
    input  logic                    io_rlast,
    input  logic [USER_WIDTH-1:0]   io_ruser,
    input  logic                    io_rvalid,
    output logic                    io_rready,
    output logic [ID_WIDTH-1:0]     io_awid,
    output logic [ADDR_WIDTH-1:0]   io_awaddr,
    output logic [7:0]              io_awlen,
    output logic [2:0]              io_awsize,
    output logic [1:0]              io_awburst,
    output logic                    io_awlock,
    output logic [3:0]              io_awcache,
    output logic [2:0]              io_awprot,
    output logic [3:0]              io_awqos,
    output logic [3:0]              io_awregion,
    output logic [USER_WIDTH-1:0]   io_awuser,
    output logic [2:0]              io_awsnoop,
    output logic [1:0]              io_awdomain,
    output logic [1:0]              io_awbar,
    output logic                    io_awvalid,
    input  logic                    io_awready,
    output logic [BUS_WIDTH-1:0]    io_wdata,
    output logic [STRB_W-1:0]       io_wstrb,
    output logic                    io_wlast,
    output logic [USER_WIDTH-1:0]   io_wuser,
    output logic                    io_wvalid,
    input  logic                    io_wready,
    input  logic [ID_WIDTH-1:0]     io_bid,
    input  logic [1:0]              io_bresp,
    input  logic [USER_WIDTH-1:0]   io_buser,
    input  logic                    io_bvalid,
    output logic                    io_bready
);

    localparam logic [2:0] S_IDLE = 3'd0;
    localparam logic [2:0] S_AR   = 3'd1;
    localparam logic [2:0] S_R    = 3'd2;
    localparam logic [2:0] S_AW   = 3'd3;
    localparam logic [2:0] S_W    = 3'd4;
    localparam logic [2:0] S_B    = 3'd5;

    logic [2:0]            r_state;
    logic                  r_done;
    logic [1:0]            r_resp;
    logic [BUS_WIDTH-1:0]  r_rdata;
    logic                  r_sh;
    logic [ADDR_WIDTH-1:0] r_addr;
    logic [BUS_WIDTH-1:0]  r_wdata;
    logic [STRB_W-1:0]     r_wstrb;

    // IHI0022 AxDOMAIN: 00 Non-shareable, 10 Outer Shareable
    wire [1:0] w_domain = r_sh ? 2'b10 : 2'b00;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_state <= S_IDLE;
            r_done  <= 1'b0;
            r_resp  <= 2'b00;
            r_rdata <= '0;
            r_sh    <= 1'b0;
            r_addr  <= '0;
            r_wdata <= '0;
            r_wstrb <= '0;
        end else begin
            unique case (r_state)
                S_IDLE: begin
                    if (go_i) begin
                        r_done  <= 1'b0;
                        r_sh    <= shareable_i;
                        r_addr  <= addr_i;
                        r_wdata <= wdata_i;
                        r_wstrb <= wstrb_i;
                        r_state <= write_i ? S_AW : S_AR;
                    end
                end
                S_AR: if (io_arready) r_state <= S_R;
                S_R: begin
                    if (io_rvalid) begin
                        r_rdata <= io_rdata;
                        r_resp  <= io_rresp;
                        if (io_rlast) begin
                            r_done  <= 1'b1;
                            r_state <= S_IDLE;
                        end
                    end
                end
                S_AW: if (io_awready) r_state <= S_W;
                S_W:  if (io_wready)  r_state <= S_B;
                S_B: begin
                    if (io_bvalid) begin
                        r_resp  <= io_bresp;
                        r_done  <= 1'b1;
                        r_state <= S_IDLE;
                    end
                end
                default: r_state <= S_IDLE;
            endcase
        end
    )

    assign busy_o  = (r_state != S_IDLE);
    assign done_o  = r_done;
    assign resp_o  = r_resp;
    assign rdata_o = r_rdata;

    // one full-width INCR beat; ReadOnce / WriteUnique in the shareable
    // domain (AxSNOOP 0), the same encodings non-shareable; no barrier
    assign io_arid     = ID_WIDTH'(AXI_ID);
    assign io_araddr   = r_addr;
    assign io_arlen    = 8'd0;
    assign io_arsize   = 3'($clog2(STRB_W));
    assign io_arburst  = 2'b01;
    assign io_arlock   = 1'b0;
    assign io_arcache  = 4'b0000;
    assign io_arprot   = 3'b000;
    assign io_arqos    = 4'b0000;
    assign io_arregion = 4'b0000;
    assign io_aruser   = '0;
    assign io_arsnoop  = 4'h0;
    assign io_ardomain = w_domain;
    assign io_arbar    = 2'b00;
    assign io_arvalid  = (r_state == S_AR);
    assign io_rready   = (r_state == S_R);

    assign io_awid     = ID_WIDTH'(AXI_ID);
    assign io_awaddr   = r_addr;
    assign io_awlen    = 8'd0;
    assign io_awsize   = 3'($clog2(STRB_W));
    assign io_awburst  = 2'b01;
    assign io_awlock   = 1'b0;
    assign io_awcache  = 4'b0000;
    assign io_awprot   = 3'b000;
    assign io_awqos    = 4'b0000;
    assign io_awregion = 4'b0000;
    assign io_awuser   = '0;
    assign io_awsnoop  = 3'b000;
    assign io_awdomain = w_domain;
    assign io_awbar    = 2'b00;
    assign io_awvalid  = (r_state == S_AW);
    assign io_wdata    = r_wdata;
    assign io_wstrb    = r_wstrb;
    assign io_wlast    = 1'b1;
    assign io_wuser    = '0;
    assign io_wvalid   = (r_state == S_W);
    assign io_bready   = (r_state == S_B);

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_resp;
    assign unused_resp = &{1'b0, io_rid, io_ruser, io_bid, io_buser};
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : ref_io_master
