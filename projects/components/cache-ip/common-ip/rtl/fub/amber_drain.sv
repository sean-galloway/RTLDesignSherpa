// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_drain
// Purpose:
//   AXI4 write-master sequencing engine for the amber MESI L1 (MAS
//   ch02_blocks/06 + ch03_interfaces/02): on drain_start from amber_control
//   it takes the staged dirty victim {addr, data} and issues one whole-line
//   INCR write-back burst to the downstream memory, retiring with
//   drain_done only after the B response. DECISION D3: the engine drives the
//   fub_axi_* upstream side of the house axi4_master_wr wrapper -- the
//   wrapper's AW/W/B skids and the responder own transport; this module is
//   pure sequencing plus the victim payload register.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/06_fill_drain.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: amber_drain
//==============================================================================
// Description:
//   Five-state engine, single outstanding (the blocking pipeline launches a
//   drain only from CTRL_MISS_DRAIN and waits drain_done, MAS ch03/02):
//
//     D_IDLE  sample drain_start; latch victim_addr / victim_data (the
//             payload pins model amber_control's staged payload outputs,
//             which hold stable for the whole drain window by construction;
//             latching here makes the engine independent of that courtesy)
//             -> D_AW
//     D_AW    assert fub_axi_awvalid with the latched victim address and
//             the burst parameters (AWLEN = FILL_BEATS-1, AWSIZE =
//             log2(BUS_WIDTH/8), AWBURST = INCR); on the AW handshake the
//             wrapper's AW skid has accepted the request -> D_W
//     D_W     forward the victim beats directly from the payload register,
//             one per handshake, WSTRB all-1s every beat, WLAST on the final
//             beat; the wrapper's W skid (DEPTH=4) absorbs responder
//             backpressure, so no local queue is needed (DECISION D-6);
//             after the WLAST handshake -> D_B
//     D_B     wait for the B response (the victim buffer owns the line until
//             the WB ack per the control-side SINK_WB_ACK contract); on the
//             B handshake -> D_DONE
//     D_DONE  drain_done pulses one cycle (MAS ch03/02: one cycle after the
//             B handshake) -> D_IDLE
//
//   AXI payload-hold laws hold by construction: every channel presents its
//   payload from a register that only advances (or retires) on the
//   handshake.
//
//------------------------------------------------------------------------------
// DECISION D-6 / D11 queue inventory (this module):
//   - NO local queue: victim beats forward directly from the latched
//     payload register (AW already accepted; the wrapper's W skid absorbs,
//     D-6). The D11 queue for the write path is axi4_master_wr's AW skid
//     (DEPTH=2) + W skid (DEPTH=4) + B skid (DEPTH=2) -- house wrappers,
//     not re-implemented.
//   - Remaining storage: the victim address register, the victim line
//     register, and the beat counter.
//------------------------------------------------------------------------------
//
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per amber_pkg defaults (HAS Table 5.0)
//     Type: int
//   AXI_ID_WIDTH / AXI_USER_WIDTH:
//     Description: fub_axi id/user field widths, matching the wrapper
//     Type: int
//
//------------------------------------------------------------------------------
// Notes:
//   - BRESP is accepted but not acted on: the pair-rig memory responder is
//     always OKAY (plain AXI4 memory per MAS ch03/02); error responses are
//     a rig-integration concern, recorded for Task 14.
//   - Illegal/unmapped state encodings recover to D_IDLE (defensive: the
//     cache pipeline stays live; there is no error-state contract for the
//     sequencing engines in MAS ch02).
//   - RTL addition over the MAS ch02/06 interface table (which still shows
//     the pre-D3 drain_beat_* W-channel pins): the victim {addr, data}
//     arrives as engine inputs and the W channel is the wrapper's fub side.
//     Recorded in the testplan + Task 14 errata.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_core (test harness: dv/tb/amber_fill_drain_th.sv)
//   - Transport: axi4_master_wr (house wrapper; skids inside)
//   - Package: amber_pkg (geometry defaults)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_fill_drain.py
//   Plan: dv/testplans/amber_drain_testplan.yaml
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_fill_drain.py -v
//
//==============================================================================

module amber_drain
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int SETS           = AMBER_SETS,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    localparam int STRB_W           = BUS_WIDTH / 8,
    localparam int FILL_BEATS       = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH = $clog2(FILL_BEATS),
    localparam int LINE_WIDTH       = LINE_BYTES * 8,
    localparam int IW               = AXI_ID_WIDTH,
    localparam int UW               = AXI_USER_WIDTH
)(
    input  logic clk,
    input  logic rst_n,

    // amber_control handshake + staged victim payload (MAS ch02_blocks/06;
    // the payload pins model ctrl_victim_addr_in / ctrl_victim_data_in)
    input  logic                    drain_start,
    input  logic [ADDR_WIDTH-1:0]   victim_addr,
    input  logic [LINE_WIDTH-1:0]   victim_data,
    output logic                    drain_done,

    // fub_axi upstream side of axi4_master_wr (DECISION D3)
    output logic [IW-1:0]   fub_axi_awid,
    output logic [ADDR_WIDTH-1:0] fub_axi_awaddr,
    output logic [7:0]      fub_axi_awlen,
    output logic [2:0]      fub_axi_awsize,
    output logic [1:0]      fub_axi_awburst,
    output logic            fub_axi_awlock,
    output logic [3:0]      fub_axi_awcache,
    output logic [2:0]      fub_axi_awprot,
    output logic [3:0]      fub_axi_awqos,
    output logic [3:0]      fub_axi_awregion,
    output logic [UW-1:0]   fub_axi_awuser,
    output logic            fub_axi_awvalid,
    input  logic            fub_axi_awready,
    output logic [BUS_WIDTH-1:0] fub_axi_wdata,
    output logic [STRB_W-1:0]    fub_axi_wstrb,
    output logic            fub_axi_wlast,
    output logic [UW-1:0]   fub_axi_wuser,
    output logic            fub_axi_wvalid,
    input  logic            fub_axi_wready,
    input  logic [IW-1:0]   fub_axi_bid,
    input  logic [1:0]      fub_axi_bresp,
    input  logic [UW-1:0]   fub_axi_buser,
    input  logic            fub_axi_bvalid,
    output logic            fub_axi_bready
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the arrays)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_drain: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_drain: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0 || FILL_BEATS < 2)
            $error("amber_drain: LINE_BYTES / BUS_WIDTH*8 must be a power of two >= 2");
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_drain: BUS_WIDTH must be a multiple of 8");
    end

    // ------------------------------------------------------------------
    // FSM: D_IDLE -> D_AW -> D_W -> D_B -> D_DONE -> D_IDLE
    // (illegal encodings recover to D_IDLE)
    // ------------------------------------------------------------------
    localparam logic [2:0] D_IDLE = 3'd0;
    localparam logic [2:0] D_AW   = 3'd1;
    localparam logic [2:0] D_W    = 3'd2;
    localparam logic [2:0] D_B    = 3'd3;
    localparam logic [2:0] D_DONE = 3'd4;

    logic [2:0]            state_q, state_d;
    logic [ADDR_WIDTH-1:0] addr_q;
    logic [LINE_WIDTH-1:0] data_q;
    logic [BEAT_INDEX_WIDTH-1:0] beat_cnt_q;

    // ------------------------------------------------------------------
    // Next-state logic
    // ------------------------------------------------------------------
    always_comb begin
        state_d = state_q;
        unique case (state_q)
            D_IDLE: begin
                if (drain_start) state_d = D_AW;
            end
            D_AW: begin
                if (fub_axi_awvalid && fub_axi_awready) state_d = D_W;
            end
            D_W: begin
                if (fub_axi_wvalid && fub_axi_wready && fub_axi_wlast)
                    state_d = D_B;
            end
            D_B: begin
                if (fub_axi_bvalid && fub_axi_bready) state_d = D_DONE;
            end
            D_DONE: state_d = D_IDLE;
            default: state_d = D_IDLE;   // defensive recovery
        endcase
    end

    // ------------------------------------------------------------------
    // State + context registers
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            state_q    <= D_IDLE;
            addr_q     <= '0;
            data_q     <= '0;
            beat_cnt_q <= '0;
        end else begin
            state_q <= state_d;
            if (state_q == D_IDLE && drain_start) begin
                addr_q     <= victim_addr;
                data_q     <= victim_data;
                beat_cnt_q <= '0;
            end else if (state_q == D_W && fub_axi_wvalid && fub_axi_wready
                         && !fub_axi_wlast) begin
                beat_cnt_q <= beat_cnt_q + 1'b1;
            end
        end
    )

    // ------------------------------------------------------------------
    // Outputs
    // ------------------------------------------------------------------
    // AW channel: burst parameters per MAS ch03/02
    assign fub_axi_awid     = '0;
    assign fub_axi_awaddr   = addr_q;
    assign fub_axi_awlen    = 8'(FILL_BEATS - 1);
    assign fub_axi_awsize   = 3'($clog2(STRB_W));
    assign fub_axi_awburst  = 2'b01;             // INCR
    assign fub_axi_awlock   = 1'b0;
    assign fub_axi_awcache  = 4'b0;
    assign fub_axi_awprot   = 3'b0;
    assign fub_axi_awqos    = 4'b0;
    assign fub_axi_awregion = 4'b0;
    assign fub_axi_awuser   = '0;
    assign fub_axi_awvalid  = (state_q == D_AW);

    // W channel: victim beats forwarded directly (D-6); payload from the
    // latched line register, so it holds under responder backpressure
    assign fub_axi_wdata    = data_q[32'(beat_cnt_q) * BUS_WIDTH
                                     +: BUS_WIDTH];
    assign fub_axi_wstrb    = {STRB_W{1'b1}};
    assign fub_axi_wlast    = (beat_cnt_q == BEAT_INDEX_WIDTH'(FILL_BEATS - 1));
    assign fub_axi_wuser    = '0;
    assign fub_axi_wvalid   = (state_q == D_W);

    // B channel: the response retires the transaction
    assign fub_axi_bready   = (state_q == D_B);

    // control side
    assign drain_done       = (state_q == D_DONE);

endmodule : amber_drain
