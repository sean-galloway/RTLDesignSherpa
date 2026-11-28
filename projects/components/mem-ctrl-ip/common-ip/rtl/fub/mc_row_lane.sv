// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_row_lane
// Purpose: The DUAL_ISSUE row lane, shared by both scheduler pick cores
//          (mc_cmd_arb_frfcfs, pumice; mc_cmd_arb_bank, granite). On a DFI 1:2
//          word the main lane carries a column on its phase; this lane puts a
//          demand ACT or PRE to ANOTHER bank on DFI_PHASE.row_phase beside it,
//          one row command per word (memory-controllers MC-014, pumice
//          TASK-047, MC-028).
//
//          Three stages, as both cores had them:
//            candidates  per (bank, direction) pair, from the core's REGISTERED
//                        requests: a row request whose bank has no column
//                        pending in either direction (and, DIR_RULE = 1, of the
//                        riding column's direction only)
//            pick        ACT before PRE, then one pair (PICK_MODE)
//            register    {vld, pair, class[, row]}: HOLD keeps it, an update
//                        loads this cycle's pick, otherwise it is dropped
//            fire        the live bank state and timers, the core's own terms
//                        (core_ok_i, core_fire_i); the HOLD rule (HOLD_MODE)
//
//          MC-028 step A (2026-11-28) moved the two cores' copies here with
//          their rules unchanged. Where the copies disagreed, the disagreement
//          is a parameter below, set per core; step B settles each one on
//          measurement and removes it. Proven against both cores' pre-MC-028
//          copies (formal/mc_common/mc_row_lane).
//
// Parameters:
//   - NUM_BANKS: banks; pairs are NPAIR = 2 * NUM_BANKS, pair p = {bank, is_wr}
//   - ROW_WIDTH: row address width (LATCH_ROW only)
//   - PICK_MODE: 0 = age tie-break then rotor (rr over aged_i / below_i, the
//                bank core's); 1 = per-direction priority, read unless the
//                class's write-first flag and a write candidate (FR-FCFS core,
//                at most one candidate per direction and class)
//   - DIR_RULE:  0 = either direction; 1 = only ride_wr_i's direction (the
//                FR-FCFS fix of 2026-11-27, be8d7cd76)
//   - HOLD_MODE: 0 = held while the bank is in the state the command needs
//                (closed or closing_i for an ACT, open for a PRE); 1 = held
//                while the gate (ok) holds and the class's lookahead timer
//                says it opens within the pipe
//   - LATCH_ROW: 1 = the ACT's row is latched with the pick (load_row_i);
//                0 = no row register, the core looks the row up (row_o = 0)
// Notes:
//   - Everything into the candidate and pick stages must be registers (both
//     cores' timing rested on that; the pick reads none of the main select).
//   - The fire stage never drives en_i into fire: a core that wants the
//     runtime enable in the gate puts it in core_ok_i.
//   - No assertions here; properties live in formal/mc_common/mc_row_lane.
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_row_lane #(
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int PICK_MODE = 0,
    parameter bit DIR_RULE  = 1'b0,
    parameter int HOLD_MODE = 0,
    parameter bit LATCH_ROW = 1'b0,
    localparam int NPAIR = 2*NUM_BANKS,
    localparam int PAIRW = (NPAIR > 1) ? $clog2(NPAIR) : 1,
    localparam int BKW   = (NUM_BANKS > 1) ? $clog2(NUM_BANKS) : 1
) (
    input  logic                  aclk,
    input  logic                  aresetn,

    // runtime enable (DUAL_ISSUE && dual_issue_en_i); gates the ride flags
    input  logic                  en_i,

    // ---- candidates (registers only) --------------------------------------
    input  logic [NPAIR-1:0]      row_req_i,    // any row request (the ride flag)
    input  logic [NPAIR-1:0]      act_req_i,    // demand ACT request
    input  logic [NPAIR-1:0]      pre_req_i,    // demand PRE request
    input  logic [NPAIR-1:0]      col_pend_i,   // a column is pending on the pair
    input  logic                  ride_wr_i,    // the riding column's direction (DIR_RULE)

    // ---- pick --------------------------------------------------------------
    input  logic                  load_en_i,    // the core lets the lane load this cycle
    input  logic [NPAIR-1:0]      aged_i,       // PICK_MODE 0
    input  logic [NPAIR-1:0]      below_i,      // PICK_MODE 0: pairs below the rotor
    input  logic                  act_wrf_i,    // PICK_MODE 1: write first, ACT class
    input  logic                  pre_wrf_i,    // PICK_MODE 1: write first, PRE class

    // ---- register ----------------------------------------------------------
    input  logic                  upd_i,        // load (else drop) when not holding
    input  logic [ROW_WIDTH-1:0]  load_row_i,   // LATCH_ROW: the picked ACT's row

    // ---- fire (live) -------------------------------------------------------
    input  logic [NUM_BANKS-1:0]  bank_row_active_i,
    input  logic [NUM_BANKS-1:0]  bank_act_ready_i,
    input  logic [NUM_BANKS-1:0]  bank_pre_ready_i,
    input  logic [NUM_BANKS-1:0]  bank_act_ready_la_i,  // HOLD_MODE 1
    input  logic [NUM_BANKS-1:0]  bank_pre_ready_la_i,  // HOLD_MODE 1
    input  logic [NUM_BANKS-1:0]  closing_i,            // HOLD_MODE 0: closing, an ACT may wait
    input  logic                  tfaw_ok_i,
    input  logic                  trrd_ok_i,
    input  logic                  rfc_busy_i,
    input  logic                  core_ok_i,    // the core's gate terms (both fire and hold)
    input  logic                  core_fire_i,  // the core's fire-only terms

    // ---- outputs -----------------------------------------------------------
    output logic                  ride_any_o,   // en_i && a rideable row request
    output logic                  ride_act_o,   // en_i && a rideable ACT
    output logic                  ride_pre_o,   // en_i && a rideable PRE
    output logic                  load_o,       // the register loads a pick this edge
    output logic [NPAIR-1:0]      pick_onehot_o,
    output logic [PAIRW-1:0]      pick_pair_o,
    output logic                  pick_act_o,   // the pick's class is ACT (else PRE)
    output logic                  vld_o,
    output logic [PAIRW-1:0]      pair_o,
    output logic [BKW-1:0]        bank_o,
    output logic                  act_o,        // the held class is ACT (else PRE)
    output logic [ROW_WIDTH-1:0]  row_o,
    output logic                  fire_o,
    output logic                  act_fire_o,
    output logic                  pre_fire_o,
    output logic                  hold_o
);

    // ---- helpers -----------------------------------------------------------
    function automatic logic [NPAIR-1:0] lsb_onehot(input logic [NPAIR-1:0] v);
        logic [NPAIR-1:0] o;
        for (int i = 0; i < NPAIR; i++) begin
            o[i] = v[i];
            for (int j = 0; j < i; j++) o[i] = o[i] & ~v[j];
        end
        return o;
    endfunction
    function automatic logic [NPAIR-1:0] rr_onehot(input logic [NPAIR-1:0] s,
                                                   input logic [NPAIR-1:0] aged,
                                                   input logic [NPAIR-1:0] below);
        logic [NPAIR-1:0] sa, sau, su;
        sa  = s & aged;
        sau = sa & ~below;
        su  = s & ~below;
        if (|sa) return (|sau) ? lsb_onehot(sau) : lsb_onehot(sa);
        else     return (|su)  ? lsb_onehot(su)  : lsb_onehot(s);
    endfunction

    logic [NPAIR-1:0] w_wr_mask;
    always_comb for (int p = 0; p < NPAIR; p++) w_wr_mask[p] = p[0];

    // ---- candidates --------------------------------------------------------
    // A bank with a column pending is streaming an open row: an ACT there is
    // impossible and a PRE there would close it under the column.
    logic [NUM_BANKS-1:0] w_bank_busy;
    logic [NPAIR-1:0]     w_ok_pair, w_row_cand, w_act_cand, w_pre_cand;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++)
            w_bank_busy[b] = col_pend_i[2*b] || col_pend_i[2*b+1];
        for (int p = 0; p < NPAIR; p++)
            w_ok_pair[p] = !w_bank_busy[p >> 1] && (!DIR_RULE || (p[0] == ride_wr_i));
        w_row_cand = row_req_i & w_ok_pair;
        w_act_cand = act_req_i & w_ok_pair;
        w_pre_cand = pre_req_i & w_ok_pair;
    end
    assign ride_any_o = en_i && (|w_row_cand);
    assign ride_act_o = en_i && (|w_act_cand);
    assign ride_pre_o = en_i && (|w_pre_cand);

    // ---- pick --------------------------------------------------------------
    logic [NPAIR-1:0] w_sel;
    logic             w_pick_act;
    assign w_pick_act = |w_act_cand;
    assign w_sel      = w_pick_act ? w_act_cand : w_pre_cand;
    generate if (PICK_MODE == 0) begin : g_pick_rr
        assign pick_onehot_o = rr_onehot(w_sel, aged_i, below_i);
        wire _unused_pick = &{1'b0, act_wrf_i, pre_wrf_i};
    end else begin : g_pick_dir
        logic [NPAIR-1:0] w_sel_rd, w_sel_wr;
        logic             w_wrf;
        assign w_sel_rd = w_sel & ~w_wr_mask;
        assign w_sel_wr = w_sel &  w_wr_mask;
        assign w_wrf    = w_pick_act ? act_wrf_i : pre_wrf_i;
        assign pick_onehot_o = lsb_onehot(((|w_sel_rd) && !(w_wrf && (|w_sel_wr))) ? w_sel_rd : w_sel_wr);
        wire _unused_pick = &{1'b0, aged_i, below_i};
    end endgenerate
    always_comb begin
        pick_pair_o = '0;
        for (int p = 0; p < NPAIR; p++) if (pick_onehot_o[p]) pick_pair_o |= PAIRW'(p);
    end
    assign pick_act_o = w_pick_act;
    assign load_o     = load_en_i && (|w_sel);

    // ---- register ----------------------------------------------------------
    // r_vld is set only by a load (a non-empty pick) or kept by a hold, so a
    // valid register always holds an ACT or a PRE.
    logic             r_vld, r_act;
    logic [PAIRW-1:0] r_pair;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_vld <= 1'b0; r_act <= 1'b0; r_pair <= '0;
        end else if (hold_o) begin
            r_vld <= 1'b1;
        end else if (upd_i) begin
            r_vld     <= load_o;
            r_pair    <= pick_pair_o;
            r_act     <= w_pick_act;
        end else begin
            r_vld <= 1'b0;
        end
    )
    generate if (LATCH_ROW) begin : g_row
        logic [ROW_WIDTH-1:0] r_row;
        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn))   r_row <= '0;
            else if (!hold_o && upd_i)    r_row <= load_row_i;
        )
        assign row_o = r_row;
    end else begin : g_no_row
        assign row_o = '0;
        wire _unused_row = &{1'b0, load_row_i};
    end endgenerate
    assign vld_o     = r_vld;
    assign pair_o    = r_pair;
    assign bank_o    = BKW'(r_pair >> 1);
    assign act_o     = r_act;

    // ---- fire --------------------------------------------------------------
    logic w_state_ok, w_timer_ok, w_ok, w_la_ok;
    always_comb begin
        w_state_ok = r_act ? !bank_row_active_i[bank_o] : bank_row_active_i[bank_o];
        w_timer_ok = r_act ? (bank_act_ready_i[bank_o] && tfaw_ok_i && trrd_ok_i)
                           : bank_pre_ready_i[bank_o];
        w_la_ok    = r_act ? bank_act_ready_la_i[bank_o] : bank_pre_ready_la_i[bank_o];
        w_ok       = r_vld && w_state_ok && !(r_act && rfc_busy_i) && core_ok_i;
    end
    assign fire_o     = w_ok && w_timer_ok && core_fire_i;
    assign act_fire_o = fire_o &&  r_act;
    assign pre_fire_o = fire_o && !r_act;
    generate if (HOLD_MODE == 0) begin : g_hold_state
        assign hold_o = r_vld && !fire_o
                     && (r_act ? (!bank_row_active_i[bank_o] || closing_i[bank_o])
                               : bank_row_active_i[bank_o]);
        wire _unused_hold = &{1'b0, w_la_ok, bank_act_ready_la_i, bank_pre_ready_la_i};
    end else begin : g_hold_la
        assign hold_o = w_ok && !fire_o && w_la_ok;
        wire _unused_hold = &{1'b0, closing_i};
    end endgenerate

endmodule : mc_row_lane
