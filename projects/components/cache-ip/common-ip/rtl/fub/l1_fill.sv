// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_fill
// Purpose:
//   AXI4 read-master sequencing engine for the cache-ip shared MESI L1 (MAS
//   ch02_blocks/06 + ch03_interfaces/02): on fill_start from l1_control
//   it issues one whole-line INCR read burst to the downstream memory and
//   forwards the received beats, in order, on the fill_beat_* control-side
//   pins (data array port A + pending-fill bypass at integration). DECISION
//   D3: the engine drives the fub_axi_* upstream side of the house
//   axi4_master_rd wrapper -- the wrapper's AR/R skids and the responder own
//   transport; this module is pure sequencing.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/06_fill_drain.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: l1_fill
//==============================================================================
// Description:
//   Four-state engine, single outstanding (the blocking pipeline launches a
//   fill only from CTRL_MISS_FILL and waits fill_done, MAS ch03/02):
//
//     F_IDLE  sample fill_start; latch fill_addr / fill_req_class. All
//             coherent read classes issue an AR; CleanUnique / MakeUnique
//             are no-data AR transactions (ARLEN = 0) and complete through
//             F_R after a single RLAST beat. Otherwise -> F_AR for a true
//             fill.
//     F_AR    assert fub_axi_arvalid with the latched line address and the
//             burst parameters (ARLEN = FILL_BEATS-1 for true fills,
//             ARLEN = 0 for no-data ARs, ARSIZE = log2(BUS_WIDTH/8),
//             ARBURST = INCR); on the AR handshake -> F_R.
//     F_R     accept R beats into the staging FIFO (true fills only).
//             fub_axi_rready is the FIFO's wr_ready: it never drops on
//             beat-output-side stalls, only at a genuinely full FIFO
//             (DECISION D-6). The burst ends on RLAST (AXI-defined); -> F_DONE.
//     F_DONE  fill_done pulses one cycle (MAS ch03/02: one cycle after
//             RLAST acceptance) -> F_IDLE.
//
//   Beat outputs are the FIFO's read side presented unconditionally (no
//   backpressure input: the landed control contract makes the beat consumer
//   -- data array port A write -- always-ready, and pf_data_valid
//   accumulates on fill_beat_valid/fill_beat_idx, MAS ch02/06). Because a
//   new fill cannot start until the control path cycles (>= 5 cycles from
//   fill_done to the next fill_start) and DEPTH=4, the FIFO is always fully
//   drained before the next burst; the pop counter simply wraps at
//   FILL_BEATS, which equals a per-fill reset under that invariant.
//
//------------------------------------------------------------------------------
// DECISION D-6 / D11 queue inventory (this module):
//   - gaxi_fifo_sync u_stage, DEPTH=4 -- the R-beat staging queue: snoop-
//     imposed port-A stalls can pause data-array writes without dropping
//     fub_axi_rready (D-6; D11 queue #1 of the fill/drain pair).
//   - AR channel: axi4_master_rd's AR skid (DEPTH=2) -- not re-implemented.
//   - R channel: axi4_master_rd's R skid (DEPTH=4) upstream of this FIFO --
//     not re-implemented.
//   - Remaining storage: the address register and the pop counter only.
//------------------------------------------------------------------------------
//
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per l1_pkg defaults (HAS Table 5.0)
//     Type: int
//   AXI_ID_WIDTH / AXI_USER_WIDTH:
//     Description: fub_axi id/user field widths, matching the wrapper
//     Type: int
//
//------------------------------------------------------------------------------
// Notes:
//   - RRESP[1:0] is accepted but not acted on: the pair-rig memory responder
//     is always OKAY (plain AXI4 memory per MAS ch03/02); error responses are
//     a rig-integration concern, recorded for Task 14.
//   - RRESP[2] (PassDirty) is captured across the burst and reported on
//     fill_pass_dirty so l1_control can install a dirty line as M.
//   - Illegal/unmapped state encodings recover to F_IDLE (defensive: the
//     cache pipeline stays live; there is no error-state contract for the
//     sequencing engines in MAS ch02).
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: l1_core (test harness: dv/tb/amber_fill_drain_th.sv)
//   - Transport: axi4_master_rd (house wrapper; skids inside)
//   - Queue: gaxi_fifo_sync (house)
//   - Package: l1_pkg (geometry defaults, amber_ace_req_t)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_fill_drain.py
//   Plan: dv/testplans/amber_fill_testplan.yaml
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_fill_drain.py -v
//
//==============================================================================

module l1_fill
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int SETS           = AMBER_SETS,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    localparam int LINE_OFFSET_WIDTH = $clog2(LINE_BYTES),
    localparam int STRB_W            = BUS_WIDTH / 8,
    localparam int FILL_BEATS        = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH  = $clog2(FILL_BEATS),
    localparam int IW                = AXI_ID_WIDTH,
    localparam int UW                = AXI_USER_WIDTH
)(
    input  logic clk,
    input  logic rst_n,

    // l1_control handshake (MAS ch02_blocks/06 binding port group)
    input  logic                        fill_start,
    input  logic [ADDR_WIDTH-1:0]       fill_addr,
    input  logic [2:0]                  fill_req_class,
    output logic                        fill_done,
    output logic                        fill_beat_valid,
    output logic [BUS_WIDTH-1:0]        fill_beat_data,
    output logic [BEAT_INDEX_WIDTH-1:0] fill_beat_idx,
    output logic                        fill_last,
    output logic                        fill_pass_dirty,
    // AR accepted and the response phase begun (F_R/F_DONE). l1_control
    // qualifies the pending-fill snoop bypass with this: a fill whose AR
    // is still seeking acceptance can never produce beats while the pair
    // fabric parks on the snoop's own response (BUG-002).
    output logic                        fill_inflight,

    // fub_axi upstream side of axi4_master_rd (DECISION D3)
    output logic [IW-1:0]   fub_axi_arid,
    output logic [ADDR_WIDTH-1:0] fub_axi_araddr,
    output logic [7:0]      fub_axi_arlen,
    output logic [2:0]      fub_axi_arsize,
    output logic [1:0]      fub_axi_arburst,
    output logic            fub_axi_arlock,
    output logic [3:0]      fub_axi_arcache,
    output logic [2:0]      fub_axi_arprot,
    output logic [3:0]      fub_axi_arqos,
    output logic [3:0]      fub_axi_arregion,
    output logic [UW-1:0]   fub_axi_aruser,
    output logic            fub_axi_arvalid,
    input  logic            fub_axi_arready,
    input  logic [IW-1:0]   fub_axi_rid,
    input  logic [BUS_WIDTH-1:0] fub_axi_rdata,
    input  logic [3:0]      fub_axi_rresp,
    input  logic            fub_axi_rlast,
    input  logic [UW-1:0]   fub_axi_ruser,
    input  logic            fub_axi_rvalid,
    output logic            fub_axi_rready
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the arrays)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("l1_fill: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("l1_fill: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0 || FILL_BEATS < 2)
            $error("l1_fill: LINE_BYTES / BUS_WIDTH*8 must be a power of two >= 2");
        if ((BUS_WIDTH % 8) != 0)
            $error("l1_fill: BUS_WIDTH must be a multiple of 8");
    end

    // ------------------------------------------------------------------
    // FSM: F_IDLE -> F_AR -> F_R -> F_DONE -> F_IDLE (upgrade: straight
    // to F_DONE; illegal encodings recover to F_IDLE)
    // ------------------------------------------------------------------
    localparam logic [1:0] F_IDLE = 2'd0;
    localparam logic [1:0] F_AR   = 2'd1;
    localparam logic [1:0] F_R    = 2'd2;
    localparam logic [1:0] F_DONE = 2'd3;

    logic [1:0]              state_q, state_d;
    logic [ADDR_WIDTH-1:0]   addr_q;
    logic [2:0]              class_q;
    logic                    no_data_class_q;
    logic                    pass_dirty_q;

    // ------------------------------------------------------------------
    // R-beat staging queue (DECISION D-6 / D11 queue inventory)
    // ------------------------------------------------------------------
    logic                   stage_wr_valid;
    logic                   stage_wr_ready;
    logic                   stage_rd_valid;
    logic [BUS_WIDTH-1:0]   stage_rd_data;
    logic [BEAT_INDEX_WIDTH-1:0] pop_cnt_q;

    gaxi_fifo_sync #(
        .DATA_WIDTH (BUS_WIDTH),
        .DEPTH      (4)
    ) u_stage (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (stage_wr_valid),
        .wr_ready    (stage_wr_ready),
        .wr_data     (fub_axi_rdata),
        .rd_ready    (1'b1),           // beat consumer is always-ready
        .count       (),
        .rd_valid    (stage_rd_valid),
        .rd_data     (stage_rd_data)
    );

    // ------------------------------------------------------------------
    // No-data AR classes: CleanUnique and MakeUnique complete with a single
    // R response beat that carries no data (IHI0022 no-data AR transactions).
    // ------------------------------------------------------------------
    always_comb begin
        no_data_class_q = (class_q == AMBER_ACE_CLEAN_UNIQUE)
                       || (class_q == AMBER_ACE_MAKE_UNIQUE);
    end

    // ------------------------------------------------------------------
    // Next-state logic
    // ------------------------------------------------------------------
    always_comb begin
        state_d = state_q;
        unique case (state_q)
            F_IDLE: begin
                if (fill_start) state_d = F_AR;
            end
            F_AR: begin
                if (fub_axi_arvalid && fub_axi_arready) state_d = F_R;
            end
            F_R: begin
                if (fub_axi_rvalid && fub_axi_rready && fub_axi_rlast)
                    state_d = F_DONE;
            end
            F_DONE: state_d = F_IDLE;
            default: state_d = F_IDLE;   // defensive recovery
        endcase
    end

    // ------------------------------------------------------------------
    // State + context registers
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            state_q        <= F_IDLE;
            addr_q         <= '0;
            class_q        <= AMBER_ACE_READ_NOT_SHARED_DIRTY;
            pass_dirty_q   <= 1'b0;
            pop_cnt_q      <= '0;
        end else begin
            state_q <= state_d;
            if (state_q == F_IDLE && fill_start) begin
                addr_q  <= fill_addr;
                class_q <= fill_req_class;
                pass_dirty_q <= 1'b0;
            end
            if (state_q == F_R && fub_axi_rvalid && fub_axi_rready) begin
                pass_dirty_q <= pass_dirty_q | fub_axi_rresp[2];
            end
            // beat presentation counter: wraps at FILL_BEATS, which equals
            // a per-fill reset because the FIFO always drains before the
            // next fill (control path >= 5 cycles, DEPTH=4)
            if (stage_rd_valid) begin
                pop_cnt_q <= (pop_cnt_q == BEAT_INDEX_WIDTH'(FILL_BEATS - 1))
                             ? '0 : pop_cnt_q + 1'b1;
            end
        end
    )

    // ------------------------------------------------------------------
    // Outputs
    // ------------------------------------------------------------------
    // AR channel: burst parameters per MAS ch03/02
    assign fub_axi_arid     = '0;
    assign fub_axi_araddr   = addr_q;
    assign fub_axi_arlen    = no_data_class_q ? 8'h0
                                              : 8'(FILL_BEATS - 1);
    assign fub_axi_arsize   = 3'($clog2(STRB_W));
    assign fub_axi_arburst  = 2'b01;             // INCR
    assign fub_axi_arlock   = 1'b0;
    assign fub_axi_arcache  = AMBER_ACE_AX_CACHE;
    assign fub_axi_arprot   = 3'b0;
    assign fub_axi_arqos    = 4'b0;
    assign fub_axi_arregion = 4'b0;
    assign fub_axi_aruser   = '0;
    assign fub_axi_arvalid  = (state_q == F_AR);

    // R channel: the FIFO absorbs beats without dropping rready (D-6).
    // No-data AR transactions consume the single RLAST beat but do not
    // push it into the staging FIFO, so the data array sees no fill beats.
    assign fub_axi_rready   = (state_q == F_R) && stage_wr_ready;
    assign stage_wr_valid   = (state_q == F_R) && fub_axi_rvalid
                              && !no_data_class_q;

    // control side
    assign fill_done        = (state_q == F_DONE);
    assign fill_pass_dirty  = pass_dirty_q;
    assign fill_inflight    = (state_q == F_R) || (state_q == F_DONE);
    assign fill_beat_valid  = stage_rd_valid;
    assign fill_beat_data   = stage_rd_data;
    assign fill_beat_idx    = pop_cnt_q;
    assign fill_last        = (pop_cnt_q == BEAT_INDEX_WIDTH'(FILL_BEATS - 1));

endmodule : l1_fill
