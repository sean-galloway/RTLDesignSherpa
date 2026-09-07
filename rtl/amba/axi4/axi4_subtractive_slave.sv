// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_subtractive_slave
// Purpose: Catch-all slave for addresses no positively-decoded slave claims.
//          Completes the transaction with an ERROR response instead of
//          leaving it unanswered, and reports the hit on the monitor bus.
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-07
//
// WHY THIS EXISTS
// ---------------
// A positively-decoded fabric answers only addresses that fall in some
// slave's range. An address in none of them selects nothing: the one-hot
// select is all-zero, no slave sees AWVALID/ARVALID, READY never rises, and
// the master waits forever. A hang is the worst possible failure here --
// it destroys the evidence. There is no response to inspect, no error bit to
// read, and the offending address is whatever the master still has latched.
//
// Subtractive decode makes the catch-all the `else` of the decode chain, so
// the one-hot is never all-zero and the hang cannot occur by construction.
// This module is what that `else` points at. It:
//
//   * completes WRITES  -- sinks every W beat, returns one B per AW
//   * completes READS   -- returns AxLEN+1 beats, RLAST on the last
//   * answers with DECERR (2'b11), the AXI4 code for "no slave at this
//     address". Not SLVERR: nothing failed to service the request, there
//     was nothing there to service it.
//   * returns a READ_FILL pattern (0xDEADBEEF) rather than zeros, because
//     zeros are indistinguishable from real memory and DEADBEEF is not
//   * emits one monbus ERROR packet per offending AW/AR, carrying the
//     address, so the hit raises the fabric's existing interrupt and lands
//     in the same CSR path as every other monitor event
//
// The response is ALWAYS an error. There is no OKAY mode and no parameter
// to select one: a mode switch here would be a place for lint, simulation
// and synthesis to disagree about what the fabric does, which is a failure
// this repository has already paid for once (see reset_defs.svh).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_subtractive_slave
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int AXI_ID_WIDTH    = 8,
    parameter int AXI_ADDR_WIDTH  = 32,
    parameter int AXI_DATA_WIDTH  = 32,
    parameter int AXI_USER_WIDTH  = 1,

    // Read data returned for every beat. Replicated to AXI_DATA_WIDTH.
    parameter logic [31:0] READ_FILL = 32'hDEAD_BEEF,

    // Monitor identity, as elsewhere in the fabric.
    parameter logic [7:0]  UNIT_ID   = 8'h0,
    parameter logic [15:0] AGENT_ID  = 16'h0,
    parameter bit          ENABLE_MONBUS = 1'b1,

    // Short names
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH
) (
    input  logic            aclk,
    input  logic            aresetn,

    // ---- AXI4 slave port -------------------------------------------------
    input  logic [IW-1:0]   s_axi_awid,
    input  logic [AW-1:0]   s_axi_awaddr,
    input  logic [7:0]      s_axi_awlen,
    input  logic            s_axi_awvalid,
    output logic            s_axi_awready,

    input  logic [DW-1:0]   s_axi_wdata,
    input  logic            s_axi_wlast,
    input  logic            s_axi_wvalid,
    output logic            s_axi_wready,

    output logic [IW-1:0]   s_axi_bid,
    output logic [1:0]      s_axi_bresp,
    output logic [UW-1:0]   s_axi_buser,
    output logic            s_axi_bvalid,
    input  logic            s_axi_bready,

    input  logic [IW-1:0]   s_axi_arid,
    input  logic [AW-1:0]   s_axi_araddr,
    input  logic [7:0]      s_axi_arlen,
    input  logic            s_axi_arvalid,
    output logic            s_axi_arready,

    output logic [IW-1:0]   s_axi_rid,
    output logic [DW-1:0]   s_axi_rdata,
    output logic [1:0]      s_axi_rresp,
    output logic            s_axi_rlast,
    output logic [UW-1:0]   s_axi_ruser,
    output logic            s_axi_rvalid,
    input  logic            s_axi_rready,

    // ---- monitor bus -----------------------------------------------------
    output logic            monbus_valid,
    input  logic            monbus_ready,
    output monitor_packet_t monbus_packet
);

    localparam logic [1:0] RESP_DECERR = 2'b11;

    // ---------------------------------------------------------------------
    // Read fill pattern, replicated to the bus width.
    // ---------------------------------------------------------------------
    localparam int FILL_REPS = (DW + 31) / 32;
    logic [FILL_REPS*32-1:0] w_fill_wide;
    assign w_fill_wide = {FILL_REPS{READ_FILL}};

    // ---------------------------------------------------------------------
    // WRITE PATH
    //
    // W is ALWAYS ready. AXI4 permits write data to arrive before its
    // address, and a slave that gates WREADY on having seen AW deadlocks
    // against a master that does so -- which would reintroduce, on the
    // error path, exactly the hang this module exists to remove.
    // So: sink W unconditionally, count WLASTs, and pair each AW with one
    // completed data phase.
    // ---------------------------------------------------------------------
    assign s_axi_wready = 1'b1;

    logic [3:0] r_wlast_credits;      // completed data phases not yet answered
    logic       w_wlast_taken;

    logic [IW-1:0] r_bid;
    logic          r_b_pending;

    // Accept a new AW only when the single B slot is free. One outstanding
    // write is ample for an error path and keeps the ordering trivially
    // correct.
    assign s_axi_awready = !r_b_pending;

    wire w_aw_fire   = s_axi_awvalid && s_axi_awready;
    wire w_wlast_fire = s_axi_wvalid && s_axi_wready && s_axi_wlast;
    wire w_b_fire    = s_axi_bvalid && s_axi_bready;

    // B is released once its data phase has completed.
    assign w_wlast_taken = r_b_pending && (r_wlast_credits != 4'd0);

    assign s_axi_bvalid = w_wlast_taken;
    assign s_axi_bid    = r_bid;
    assign s_axi_bresp  = RESP_DECERR;
    assign s_axi_buser  = '0;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wlast_credits <= '0;
            r_bid           <= '0;
            r_b_pending     <= 1'b0;
        end else begin
            if (w_aw_fire) begin
                r_bid       <= s_axi_awid;
                r_b_pending <= 1'b1;
            end else if (w_b_fire) begin
                r_b_pending <= 1'b0;
            end

            // Saturating credit counter: a master that streams write data
            // with no matching AW must not wrap the count and manufacture
            // responses for writes that were never addressed.
            case ({w_wlast_fire, w_b_fire})
                2'b10: if (r_wlast_credits != 4'hF) r_wlast_credits <= r_wlast_credits + 4'd1;
                2'b01: if (r_wlast_credits != 4'd0) r_wlast_credits <= r_wlast_credits - 4'd1;
                default: ;   // both or neither: net zero
            endcase
        end
    )

    // ---------------------------------------------------------------------
    // READ PATH
    //
    // AxLEN+1 beats, RLAST on the last. Returning a single beat for a burst
    // would hang the master just as surely as returning none.
    // ---------------------------------------------------------------------
    logic [IW-1:0] r_rid;
    logic [7:0]    r_beats_left;
    logic          r_r_active;

    assign s_axi_arready = !r_r_active;

    wire w_ar_fire = s_axi_arvalid && s_axi_arready;
    wire w_r_fire  = s_axi_rvalid  && s_axi_rready;

    assign s_axi_rvalid = r_r_active;
    assign s_axi_rid    = r_rid;
    assign s_axi_rdata  = w_fill_wide[DW-1:0];
    assign s_axi_rresp  = RESP_DECERR;
    assign s_axi_ruser  = '0;
    assign s_axi_rlast  = r_r_active && (r_beats_left == 8'd0);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rid        <= '0;
            r_beats_left <= '0;
            r_r_active   <= 1'b0;
        end else if (w_ar_fire) begin
            r_rid        <= s_axi_arid;
            r_beats_left <= s_axi_arlen;
            r_r_active   <= 1'b1;
        end else if (w_r_fire) begin
            if (r_beats_left == 8'd0) begin
                r_r_active <= 1'b0;
            end else begin
                r_beats_left <= r_beats_left - 8'd1;
            end
        end
    )

    // ---------------------------------------------------------------------
    // MONITOR REPORT
    //
    // One ERROR packet per offending address phase, carrying the address so
    // software can see WHICH access was unmapped rather than merely that one
    // was. Same event code the address-range checker uses, so existing
    // decoders need no change.
    // ---------------------------------------------------------------------
    if (ENABLE_MONBUS) begin : g_monbus
        logic          r_rpt_valid;
        logic [AW-1:0] r_rpt_addr;
        logic [IW-1:0] r_rpt_id;

        // AW wins a same-cycle tie; the AR is reported when it is accepted,
        // which cannot be the same cycle because ARREADY is low while a read
        // is active and the tie only arises on a free cycle.
        wire w_rpt_fire = w_aw_fire || w_ar_fire;

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_rpt_valid <= 1'b0;
                r_rpt_addr  <= '0;
                r_rpt_id    <= '0;
            end else begin
                if (w_rpt_fire) begin
                    r_rpt_valid <= 1'b1;
                    r_rpt_addr  <= w_aw_fire ? s_axi_awaddr : s_axi_araddr;
                    r_rpt_id    <= w_aw_fire ? s_axi_awid   : s_axi_arid;
                end else if (monbus_valid && monbus_ready) begin
                    r_rpt_valid <= 1'b0;
                end
            end
        )

        logic [8:0]  w_chan_id;
        logic [59:0] w_addr_payload;

        if (IW >= 9) begin : g_chan_wide
            assign w_chan_id = r_rpt_id[8:0];
        end else begin : g_chan_narrow
            assign w_chan_id = {{(9-IW){1'b0}}, r_rpt_id};
        end

        if (AW >= 60) begin : g_addr_wide
            assign w_addr_payload = r_rpt_addr[59:0];
        end else begin : g_addr_narrow
            assign w_addr_payload = {{(60-AW){1'b0}}, r_rpt_addr};
        end

        assign monbus_valid  = r_rpt_valid;
        assign monbus_packet = create_monitor_packet(
            PktTypeError,                    // [127:124]
            protocol_type_t'(PROTOCOL_AXI),  // [108:105]
            AXI_ERR_ADDR_RANGE,              // [104: 97]  8'h0D
            w_chan_id,                       // [ 96: 88]
            UNIT_ID,                         // [ 71: 64]
            AGENT_ID,                        // [ 87: 72]
            {4'hF, w_addr_payload}           // [ 63:  0]  4'hF = no-range sentinel
        );
    end else begin : g_no_monbus
        assign monbus_valid  = 1'b0;
        assign monbus_packet = '0;
    end

    // ---------------------------------------------------------------------
    // Deliberately unused inputs, named so the reason survives.
    //   awlen  -- the write data phase is framed by WLAST, not by a count,
    //             so the burst length carries no information here.
    //   wdata  -- writes are dropped. There is nowhere for the data to go
    //             and inventing a destination would be worse than saying so.
    // Tied into a named net rather than waived with a lint pragma: a pragma
    // suppresses the whole category, including the next accidentally-dropped
    // signal.
    // ---------------------------------------------------------------------
    /* verilator lint_off UNUSED */
    wire _unused_subtractive = &{1'b0, s_axi_awlen, s_axi_wdata};
    /* verilator lint_on UNUSED */

endmodule : axi4_subtractive_slave
