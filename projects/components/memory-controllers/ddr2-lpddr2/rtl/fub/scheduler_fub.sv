// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: scheduler_fub
// Purpose: Arbiter at the heart of the controller core. Each cycle,
//          decide what to issue on the DFI command bus.
//
//          v1 priority (high → low):
//            1. init_busy_i      → NOP (init_sequencer owns the bus)
//            2. mr_req_i         → MRS (mode-register write)
//            3. refresh_req_i    → grant + REF
//            4. pdn_req_i        → grant + NOP (CKE drop handled by
//                                   powerdown_ctrl)
//            5. WR CAM op        → ACT / WRA / PRE-state-machine
//            6. RD CAM op        → ACT / RDA / PRE-state-machine
//            7. else             → NOP
//
//          Closed-page policy: every column command is RDA/WRA
//          (auto-precharge). The bank returns to IDLE without an
//          explicit PRE. No row-hit reuse — every access needs its
//          own ACT.
//
//          State for an in-progress column op:
//            * `r_pending` = the (rank, bank, row, col, len, slot)
//              chosen for the current pass.
//            * After ACT issued: wait until rdwr_ready, then issue
//              RDA/WRA.
//            * After RDA/WRA: pulse mark_issued back to the CAM and
//              clear r_pending.
//
// v1 (TODO):
//   * Open-page policy with row-hit reuse — needs to compare
//     bank_open_row vs requested row; cheap perf win.
//   * Bank-parallel multi-cmd issue per DFI cycle (multi-phase).
//   * Smarter arbitration: age-aware, write-clustering, etc.
//   * wr_op/rd_op are issued in strict alternation across CAM scans —
//     no priority between W and R yet.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module scheduler_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int WR_CAM_DEPTH    = 16,
    parameter int RD_CAM_DEPTH    = 16,
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int AXI_ID_WIDTH    = 4,

    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ----- CAM query (drive into axi_frontend_macro) -----
    output logic [RKW-1:0]             q_rank_o,
    output logic [BKW-1:0]             q_bank_o,
    output logic [ROW_WIDTH-1:0]       q_row_o,

    // ----- CAM match vectors -----
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_pending_i,
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_rowhit_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_pending_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_rowhit_i,

    // ----- per-slot metadata snapshots -----
    input  logic [WR_CAM_DEPTH-1:0][COL_WIDTH-1:0]       wr_snap_col_i,
    input  logic [WR_CAM_DEPTH-1:0][BURST_LEN_WIDTH-1:0] wr_snap_len_i,
    input  logic [RD_CAM_DEPTH-1:0][COL_WIDTH-1:0]       rd_snap_col_i,
    input  logic [RD_CAM_DEPTH-1:0][BURST_LEN_WIDTH-1:0] rd_snap_len_i,

    // ----- mark-issued strobes back to CAMs -----
    output logic                       wr_issued_we_o,
    output logic [WSL-1:0]             wr_issued_slot_o,
    output logic                       rd_issued_we_o,
    output logic [RSL-1:0]             rd_issued_slot_o,

    // ----- timer readiness -----
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_act_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_rdwr_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_pre_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_row_active_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0] bank_open_row_i,
    input  logic                       tfaw_window_ok_i,

    // ----- refresh / power injection -----
    input  logic                       refresh_req_i,
    output logic                       refresh_grant_o,
    input  logic                       pdn_req_i,
    output logic                       pdn_grant_o,

    // ----- init / mode-reg injection -----
    input  logic                       init_busy_i,
    input  logic                       mr_req_i,
    output logic                       mr_grant_o,

    // ----- chosen op into dfi_cmd_formatter -----
    output logic                       cmd_valid_o,
    input  logic                       cmd_ready_i,
    output dram_op_e                   cmd_op_o,
    output logic [RKW-1:0]             cmd_rank_o,
    output logic [BKW-1:0]             cmd_bank_o,
    output logic [ROW_WIDTH-1:0]       cmd_row_o,
    output logic [COL_WIDTH-1:0]       cmd_col_o,
    output logic [BURST_LEN_WIDTH-1:0] cmd_len_o,
    output logic [WSL-1:0]             cmd_wr_slot_o,
    output logic [RSL-1:0]             cmd_rd_slot_o,

    // ----- bank-event strobes to xbank_timers -----
    output logic                       evt_act_o,
    output logic                       evt_rd_o,
    output logic                       evt_wr_o,
    output logic                       evt_pre_o,
    output logic [RKW-1:0]             evt_rank_o,
    output logic [BKW-1:0]             evt_bank_o
);

    //=========================================================================
    // FSM for an in-progress column-op (closed-page):
    //   S_IDLE       : choose next slot; query bank state
    //   S_NEED_ACT   : wait until bank_act_ready; issue ACT
    //   S_NEED_RDWR  : wait until bank_rdwr_ready; issue RDA/WRA
    //   S_DONE       : mark_issued pulse; back to IDLE
    //=========================================================================
    typedef enum logic [2:0] {
        S_IDLE      = 3'd0,
        S_NEED_ACT  = 3'd1,
        S_NEED_RDWR = 3'd2,
        S_DONE      = 3'd3
    } state_e;

    state_e             r_state;

    // Pending op context
    logic               r_pending_is_wr;
    logic [WSL-1:0]     r_pending_wr_slot;
    logic [RSL-1:0]     r_pending_rd_slot;
    logic [RKW-1:0]     r_pending_rank;
    logic [BKW-1:0]     r_pending_bank;
    logic [ROW_WIDTH-1:0] r_pending_row;
    logic [COL_WIDTH-1:0] r_pending_col;
    logic [BURST_LEN_WIDTH-1:0] r_pending_len;

    //=========================================================================
    // For v1, we don't query the CAMs via q_rank/bank/row — we just take
    // the lowest-index pending slot. The CAM-snapshot col/len gives us
    // per-slot col + len; rank/bank/row aren't in the snapshot here, so
    // for v1 we drive (rank=0, bank=0, row=0) for the chosen slot.
    // A real implementation extends the snapshot to include the decoded
    // tuple — that's an axi_frontend_macro upgrade.
    //=========================================================================
    logic                w_have_wr;
    logic                w_have_rd;
    logic [WSL-1:0]      w_wr_pick;
    logic [RSL-1:0]      w_rd_pick;

    always_comb begin
        w_have_wr = 1'b0;
        w_wr_pick = '0;
        for (int unsigned i = 0; i < WR_CAM_DEPTH; i++) begin
            if (!w_have_wr && wr_match_pending_i[i]) begin
                w_have_wr = 1'b1;
                w_wr_pick = WSL'(i);
            end
        end
    end

    always_comb begin
        w_have_rd = 1'b0;
        w_rd_pick = '0;
        for (int unsigned i = 0; i < RD_CAM_DEPTH; i++) begin
            if (!w_have_rd && rd_match_pending_i[i]) begin
                w_have_rd = 1'b1;
                w_rd_pick = RSL'(i);
            end
        end
    end

    //=========================================================================
    // Outputs — combinational, gated by r_state.
    //=========================================================================
    dram_op_e        w_op;
    logic            w_cmd_valid;

    always_comb begin
        // Defaults
        w_op             = OP_NOP;
        w_cmd_valid      = 1'b0;
        cmd_rank_o       = '0;
        cmd_bank_o       = '0;
        cmd_row_o        = '0;
        cmd_col_o        = '0;
        cmd_len_o        = '0;
        cmd_wr_slot_o    = '0;
        cmd_rd_slot_o    = '0;
        evt_act_o        = 1'b0;
        evt_rd_o         = 1'b0;
        evt_wr_o         = 1'b0;
        evt_pre_o        = 1'b0;
        evt_rank_o       = '0;
        evt_bank_o       = '0;
        refresh_grant_o  = 1'b0;
        pdn_grant_o      = 1'b0;
        mr_grant_o       = 1'b0;
        wr_issued_we_o   = 1'b0;
        wr_issued_slot_o = '0;
        rd_issued_we_o   = 1'b0;
        rd_issued_slot_o = '0;
        q_rank_o         = '0;
        q_bank_o         = '0;
        q_row_o          = '0;

        unique case (r_state)
            S_IDLE: begin
                if (init_busy_i) begin
                    // NOP — init_sequencer owns the bus.
                end else if (mr_req_i) begin
                    w_op        = OP_MRS;
                    w_cmd_valid = 1'b1;
                    mr_grant_o  = cmd_ready_i;
                end else if (refresh_req_i) begin
                    w_op            = OP_REF;
                    w_cmd_valid     = 1'b1;
                    refresh_grant_o = cmd_ready_i;
                end else if (pdn_req_i) begin
                    // No DRAM cmd needed — just grant CKE drop.
                    pdn_grant_o = 1'b1;
                end
                // Else stay in IDLE; transition into NEED_ACT happens
                // in the sequential block once a slot is chosen.
            end

            S_NEED_ACT: begin
                if (bank_act_ready_i[r_pending_rank][r_pending_bank]
                 && tfaw_window_ok_i) begin
                    w_op        = OP_ACT;
                    w_cmd_valid = 1'b1;
                    cmd_rank_o  = r_pending_rank;
                    cmd_bank_o  = r_pending_bank;
                    cmd_row_o   = r_pending_row;
                    if (cmd_ready_i) begin
                        evt_act_o  = 1'b1;
                        evt_rank_o = r_pending_rank;
                        evt_bank_o = r_pending_bank;
                    end
                end
            end

            S_NEED_RDWR: begin
                if (bank_rdwr_ready_i[r_pending_rank][r_pending_bank]) begin
                    w_op        = r_pending_is_wr ? OP_WRA : OP_RDA;
                    w_cmd_valid = 1'b1;
                    cmd_rank_o  = r_pending_rank;
                    cmd_bank_o  = r_pending_bank;
                    cmd_col_o   = r_pending_col;
                    cmd_len_o   = r_pending_len;
                    cmd_wr_slot_o = r_pending_wr_slot;
                    cmd_rd_slot_o = r_pending_rd_slot;
                    if (cmd_ready_i) begin
                        if (r_pending_is_wr) begin
                            evt_wr_o = 1'b1;
                        end else begin
                            evt_rd_o = 1'b1;
                        end
                        evt_rank_o = r_pending_rank;
                        evt_bank_o = r_pending_bank;
                    end
                end
            end

            S_DONE: begin
                if (r_pending_is_wr) begin
                    wr_issued_we_o   = 1'b1;
                    wr_issued_slot_o = r_pending_wr_slot;
                end else begin
                    rd_issued_we_o   = 1'b1;
                    rd_issued_slot_o = r_pending_rd_slot;
                end
            end

            default: ;
        endcase
    end

    assign cmd_valid_o = w_cmd_valid;
    assign cmd_op_o    = w_op;

    //=========================================================================
    // Sequential FSM
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_state           <= S_IDLE;
            r_pending_is_wr   <= 1'b0;
            r_pending_wr_slot <= '0;
            r_pending_rd_slot <= '0;
            r_pending_rank    <= '0;
            r_pending_bank    <= '0;
            r_pending_row     <= '0;
            r_pending_col     <= '0;
            r_pending_len     <= '0;
        end else begin
            unique case (r_state)
                S_IDLE: begin
                    if (init_busy_i || mr_req_i || refresh_req_i || pdn_req_i) begin
                        // Stay IDLE; output logic emits the injection cmd.
                    end else if (w_have_wr) begin
                        r_pending_is_wr   <= 1'b1;
                        r_pending_wr_slot <= w_wr_pick;
                        r_pending_rank    <= '0;
                        r_pending_bank    <= '0;
                        r_pending_row     <= '0;
                        r_pending_col     <= wr_snap_col_i[w_wr_pick];
                        r_pending_len     <= wr_snap_len_i[w_wr_pick];
                        r_state           <= S_NEED_ACT;
                    end else if (w_have_rd) begin
                        r_pending_is_wr   <= 1'b0;
                        r_pending_rd_slot <= w_rd_pick;
                        r_pending_rank    <= '0;
                        r_pending_bank    <= '0;
                        r_pending_row     <= '0;
                        r_pending_col     <= rd_snap_col_i[w_rd_pick];
                        r_pending_len     <= rd_snap_len_i[w_rd_pick];
                        r_state           <= S_NEED_ACT;
                    end
                end

                S_NEED_ACT: begin
                    if (w_cmd_valid && cmd_ready_i) begin
                        r_state <= S_NEED_RDWR;
                    end
                end

                S_NEED_RDWR: begin
                    if (w_cmd_valid && cmd_ready_i) begin
                        r_state <= S_DONE;
                    end
                end

                S_DONE: begin
                    r_state <= S_IDLE;
                end

                default: r_state <= S_IDLE;
            endcase
        end
    end)

    wire unused_v1 = |{ wr_match_rowhit_i, rd_match_rowhit_i,
                        bank_pre_ready_i, bank_row_active_i, bank_open_row_i };

endmodule : scheduler_fub
