// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: rd_cl_aligner_fub
// Purpose: Drive `dfi_rddata_en` at the right cycle for an issued READ,
//          capture the PHY's `dfi_rddata` beats (DFI_RATE DRAM beats
//          packed per DFI cycle), and stream them out to the axi_intake's
//          R-emit FSM as DRAM-beat-wide `rd_inject_*` handshakes. Pulse
//          `rd_beat_we` back to the rd CAM per accepted beat so the
//          slot retires after `len` beats.
//
// Body design:
//          Single-burst FSM:
//            IDLE → WAIT_EN → ACTIVE → IDLE
//
//          * WAIT_EN counts down t_rddata_en_i cycles after the OP_RD
//            handshake. This is the PHY-defined latency from a READ
//            command on the DFI control bus to the cycle the controller
//            asserts dfi_rddata_en.
//          * ACTIVE concurrently runs three counters:
//              - en_remaining   : dfi_rddata_en pulses left to drive
//                                 (= ceil(len / DFI_RATE) DFI cycles)
//              - dfi_captured   : DFI cycles received from the PHY
//                                 (advances on every dfi_rddata_valid_i)
//              - beats_emitted  : DRAM beats handshaken to rd_inject
//                                 (= 0..len)
//            The PHY may begin returning rddata before en falls (overlap)
//            or after a delay up to t_phy_rdlat (PHY-defined). The FSM
//            stays in ACTIVE until beats_emitted == len.
//          * rd_inject_valid_o is gated on "buffer has a beat the emit
//            counter hasn't consumed yet" — i.e., emit can chase the
//            captured DFI cycles in real time without an extra DRAIN
//            phase. rd_beat_we_o pulses on every accepted handshake.
//
// v1 limitations (TODO markers):
//   (TODO multi-outstanding) Single in-flight read at a time. The rd CAM
//   allows up to RD_CAM_DEPTH=16 concurrent slots; v2 should add a
//   per-slot context + reorder logic. rd_in_order_i is wired as a
//   placeholder port for that follow-on.
//
//   (TODO OOO across IDs) When multi-outstanding lands, the default
//   behavior should be OOO across IDs (in-order within each ID, per
//   AXI4 spec); rd_in_order_i=1 forces strict issue-order.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rd_cl_aligner_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int RD_CAM_DEPTH    = 16,
    parameter int AXI_ID_WIDTH    = 4,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DFI_RATE        = 2,
    parameter int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DFI_VALID_WIDTH = 1,
    parameter int DFI_EN_WIDTH    = 1,
    parameter int MAX_BURST_LEN   = 256,

    parameter int RSL = $clog2(RD_CAM_DEPTH),
    parameter int IW  = AXI_ID_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int RATE_LOG2 = $clog2(DFI_RATE)
) (
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,

    // ----- live MR values (CL/AL kept for future scheduler sanity check) -----
    input  logic [3:0]                    cl_i,
    input  logic [3:0]                    al_i,

    // ----- PHY timing (DFI Initialization Status Register-loaded) -----
    input  logic [7:0]                    t_rddata_en_i,

    // ----- TODO: multi-outstanding ordering mode -----
    //   rd_in_order_i = 1 forces strict issue-order completion across IDs.
    //   rd_in_order_i = 0 allows OOO across IDs (AXI4-compliant).
    //   Currently unused in v1 (single-in-flight is intrinsically in-order).
    input  logic                          rd_in_order_i,

    // ----- read-op handshake from scheduler -----
    input  logic                          op_valid_i,
    output logic                          op_ready_o,
    input  logic [RSL-1:0]                op_slot_i,
    input  logic [IW-1:0]                 op_id_i,
    input  logic [BLW-1:0]                op_len_i,

    // ----- DFI read data interface -----
    output logic [DFI_EN_WIDTH-1:0]       dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]     dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0]    dfi_rddata_valid_i,

    // ----- rd_inject into axi_frontend (one DRAM beat per cycle) -----
    output logic                          rd_inject_valid_o,
    input  logic                          rd_inject_ready_i,
    output logic [IW-1:0]                 rd_inject_id_o,
    output logic [DRAM_BEAT_WIDTH-1:0]    rd_inject_data_o,
    output logic                          rd_inject_last_o,

    // ----- per-beat strobe to rd CAM (beat retire) -----
    output logic                          rd_beat_we_o,
    output logic [RSL-1:0]                rd_beat_slot_o
);

    //=========================================================================
    // FSM states
    //=========================================================================
    typedef enum logic [1:0] {
        S_IDLE    = 2'd0,
        S_WAIT_EN = 2'd1,
        S_ACTIVE  = 2'd2
    } state_e;

    state_e         r_state;

    // Per-burst context
    logic [RSL-1:0] r_cur_slot;
    logic [IW-1:0]  r_cur_id;
    logic [BLW-1:0] r_cur_len;
    logic [7:0]     r_wait_cnt;

    // ACTIVE-state counters
    logic [BLW:0]   r_en_remaining;     // DFI en pulses left to drive
    logic [BLW:0]   r_dfi_captured;     // DFI cycles received
    logic [BLW-1:0] r_beats_emitted;    // DRAM beats handshaken

    // DFI cycle staging: one entry per DFI cycle received. Buffer indexed by
    // the lower MAX_LOG2 bits of dfi_captured so we don't pay for a wide
    // mux when MAX_BURST_LEN is power-of-two.
    localparam int MAX_LOG2     = $clog2(MAX_BURST_LEN);
    localparam int MAX_DFI_CYC  = (MAX_BURST_LEN + DFI_RATE - 1) / DFI_RATE;
    localparam int DFI_CYC_LOG2 = $clog2(MAX_DFI_CYC);

    logic [DFI_DATA_WIDTH-1:0] r_stage [MAX_DFI_CYC];

    //=========================================================================
    // Pre-compute DFI cycles needed for the current burst.
    //=========================================================================
    logic [BLW:0] w_dfi_cycles_total;
    assign w_dfi_cycles_total = ({1'b0, r_cur_len} + (BLW+1)'(DFI_RATE - 1))
                              >> RATE_LOG2;

    //=========================================================================
    // Combinational: which DRAM beat are we emitting this cycle, and is
    // that beat available in the staging buffer yet?
    //=========================================================================
    logic [DFI_CYC_LOG2-1:0] w_emit_dfi_idx;
    logic [RATE_LOG2-1:0]    w_emit_rate_idx;
    assign w_emit_dfi_idx  = r_beats_emitted[BLW-1:RATE_LOG2];
    assign w_emit_rate_idx = r_beats_emitted[RATE_LOG2-1:0];

    // Beat is available if its containing DFI cycle has already been captured.
    logic w_emit_available;
    assign w_emit_available = ({1'b0, r_beats_emitted} >> RATE_LOG2)
                            < r_dfi_captured;

    // Are we in the middle of a burst? (live in ACTIVE)
    logic w_in_active;
    assign w_in_active = (r_state == S_ACTIVE);

    // Current emit beat extracted from the staging buffer.
    logic [DRAM_BEAT_WIDTH-1:0] w_emit_data;
    assign w_emit_data = r_stage[w_emit_dfi_idx]
                       [w_emit_rate_idx * DRAM_BEAT_WIDTH +: DRAM_BEAT_WIDTH];

    //=========================================================================
    // Sequential FSM
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state         <= S_IDLE;
            r_cur_slot      <= '0;
            r_cur_id        <= '0;
            r_cur_len       <= '0;
            r_wait_cnt      <= '0;
            r_en_remaining  <= '0;
            r_dfi_captured  <= '0;
            r_beats_emitted <= '0;
        end else begin
            unique case (r_state)

                S_IDLE: begin
                    if (op_valid_i && op_ready_o) begin
                        r_cur_slot      <= op_slot_i;
                        r_cur_id        <= op_id_i;
                        r_cur_len       <= op_len_i;
                        r_wait_cnt      <= t_rddata_en_i;
                        r_en_remaining  <= '0;
                        r_dfi_captured  <= '0;
                        r_beats_emitted <= '0;
                        r_state         <= S_WAIT_EN;
                    end
                end

                S_WAIT_EN: begin
                    if (r_wait_cnt == 8'd0) begin
                        r_en_remaining <= w_dfi_cycles_total;
                        r_state        <= S_ACTIVE;
                    end else begin
                        r_wait_cnt <= r_wait_cnt - 8'd1;
                    end
                end

                S_ACTIVE: begin
                    // 1. Drive en — decrement on each cycle in ACTIVE
                    //    while there are still pulses left.
                    if (r_en_remaining > '0) begin
                        r_en_remaining <= r_en_remaining - (BLW+1)'(1);
                    end

                    // 2. Capture rddata when valid is high.
                    if (dfi_rddata_valid_i) begin
                        r_stage[r_dfi_captured[DFI_CYC_LOG2-1:0]] <= dfi_rddata_i;
                        r_dfi_captured <= r_dfi_captured + (BLW+1)'(1);
                    end

                    // 3. Emit on accepted rd_inject handshake.
                    if (rd_inject_valid_o && rd_inject_ready_i) begin
                        if ((r_beats_emitted + BLW'(1)) == r_cur_len) begin
                            r_state <= S_IDLE;
                        end
                        r_beats_emitted <= r_beats_emitted + BLW'(1);
                    end
                end

                default: r_state <= S_IDLE;
            endcase
        end
    end)

    //=========================================================================
    // Outputs
    //=========================================================================
    assign op_ready_o       = (r_state == S_IDLE);

    // dfi_rddata_en stays high while there are en pulses left to drive.
    assign dfi_rddata_en_o  = (w_in_active && (r_en_remaining > '0))
                            ? '1 : '0;

    // rd_inject is valid when we're streaming a burst AND the next beat
    // is in the staging buffer.
    assign rd_inject_valid_o = w_in_active && w_emit_available;
    assign rd_inject_id_o    = r_cur_id;
    assign rd_inject_data_o  = w_emit_data;
    assign rd_inject_last_o  = w_in_active
                             && ((r_beats_emitted + BLW'(1)) == r_cur_len);

    // rd_beat_we pulses with each accepted handshake; rd CAM retires
    // a beat per pulse.
    assign rd_beat_we_o     = rd_inject_valid_o && rd_inject_ready_i;
    assign rd_beat_slot_o   = r_cur_slot;

    // v1: cl_i / al_i / rd_in_order_i kept on the port list for the
    // multi-outstanding follow-on; not consumed yet.
    wire unused_v1 = |{ cl_i, al_i, rd_in_order_i };

endmodule : rd_cl_aligner_fub
