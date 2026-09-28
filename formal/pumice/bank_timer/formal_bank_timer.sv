// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for bank_timer -- pumice's per-bank JEDEC timing gate.
//
// WHY THIS BLOCK FIRST. It is the thing that stops the controller violating the
// DRAM: every ACT/RD/WR/PRE the arbiter issues is permitted by one of the
// safe_*_o outputs here. pumice had NO formal coverage at all while 366 blocks
// elsewhere in the repo did, and this is the block where a wrong answer damages
// a device rather than a measurement.
//
// It is also the block whose contract is already WRITTEN DOWN precisely: the
// signal-contract K-maps (pumice TASK-029) state each safe_* as a sum of
// products and state three cross-module implications the arbiter leans on --
// safe_act => !row_valid, safe_pre => row_valid, ap_pending => row_valid. Those
// implications are asserted here. Two of them are the reason the arbiter's
// rd_act_m / rd_pre_m maps render "DIFFERS": the arbiter re-states a term this
// block already guarantees, and until now "already guarantees" was an argument
// rather than a proof.
//
// WHAT IS PROVED, in two families:
//
//   JEDEC SPACING (the temporal properties, and the point of the block):
//     * ACT -> ACT  >= tRC     even with an intervening PRE
//     * PRE -> ACT  >= tRP
//     * ACT -> RD/WR >= tRCD
//     * ACT -> PRE  >= tRAS
//     * RD  -> PRE  >= tRTP
//     * WR  -> PRE  >= tWR
//
//   STRUCTURAL INVARIANTS (what the rest of the design may assume):
//     * safe_act => row closed;  safe_rd/wr and safe_pre => row open
//     * ap_pending => row open   (the K-map's claim, now proved)
//     * safe_act is mutually exclusive with safe_rd and with safe_pre
//     * auto-precharge fires at most once per arming
//     * at LA=0 each advisory output equals its live twin
//
// BOUNDED ON PURPOSE. The timing inputs are CSR-programmed and then stable, so
// they are `anyconst` here, and they are constrained to 1..4 -- a BMC deep
// enough to count a real tRC of 60 would be 60+ cycles of unrolling for no
// extra confidence, since the counter is the same counter at 4 as at 60. What
// the small bound buys is that the SPACING properties can be checked
// exhaustively within a shallow depth.

`timescale 1ns / 1ps

//
// YOSYS-COMPATIBLE FORM. The DUT arrives pre-flattened by sv2v (yosys cannot
// parse pumice_pkg.sv: a multi-line `return` in a package function stops its
// Verilog frontend at pumice_pkg.sv:131). This wrapper is read directly by
// yosys, so it carries no package import and states every property as an
// IMMEDIATE assertion inside `always @(posedge clk)` -- the concurrent
// `assert property (@(posedge clk) ...)` form is not accepted by that frontend.
// Every property here is a single-cycle implication, so nothing is lost: the
// elapsed-cycle counters below carry the temporal part explicitly.

module formal_bank_timer #(
    parameter int ROW_WIDTH = 4,      // narrow: the row value is opaque here
    parameter int TW        = 4,
    parameter int LA        = 0
) (
    input logic clk,
    input logic rst_n
);

    // ---- CSR-programmed timings: constant, and small enough to unroll -------
    (* anyconst *) reg [TW-1:0] t_rcd, t_rp, t_ras, t_rc, t_wr, t_rtp;
    always @(*) begin
        assume (t_rcd >= 1 && t_rcd <= 4);
        assume (t_rp  >= 1 && t_rp  <= 4);
        assume (t_ras >= 1 && t_ras <= 4);
        assume (t_rc  >= 1 && t_rc  <= 4);
        assume (t_wr  >= 1 && t_wr  <= 4);
        assume (t_rtp >= 1 && t_rtp <= 4);
    end

    // ---- free command strobes ----------------------------------------------
    (* anyseq *) reg set_act, set_rd, set_wr, set_pre, set_ap;
    (* anyseq *) reg [ROW_WIDTH-1:0] row;

    // SINGLE ISSUE. The controller issues at most one DRAM command per cycle and
    // the parent gates these by bank, so two strobes in one cycle is not a state
    // the hardware reaches. Without this the RTL's ACT > PRE > auto-PRE priority
    // still resolves, but the JEDEC spacing questions stop being well posed --
    // "how long after the ACT" has no answer if a PRE shared its cycle.
    always @(*) assume ($countones({set_act, set_rd, set_wr, set_pre}) <= 1);

    wire safe_act, safe_rd, safe_wr, safe_pre;
    wire safe_act_la, safe_rdwr_la, safe_pre_la;
    wire row_valid, obs_rcd_nz, obs_preblk_nz, obs_ras_nz, obs_ap_pending;
    wire [ROW_WIDTH-1:0] open_row;
    wire [2:0]  state;   // bank_state_e, flattened by sv2v

    bank_timer #(.ROW_WIDTH(ROW_WIDTH), .TW(TW), .LA(LA)) dut (
        .clk(clk), .rst_n(rst_n),
        .t_rcd_i(t_rcd), .t_rp_i(t_rp), .t_ras_i(t_ras),
        .t_rc_i(t_rc), .t_wr_i(t_wr), .t_rtp_i(t_rtp),
        .set_act_i(set_act), .set_rd_i(set_rd), .set_wr_i(set_wr),
        .set_pre_i(set_pre), .set_ap_i(set_ap), .row_i(row),
        .safe_act_o(safe_act), .safe_rd_o(safe_rd), .safe_wr_o(safe_wr),
        .safe_pre_o(safe_pre),
        .safe_act_la_o(safe_act_la), .safe_rdwr_la_o(safe_rdwr_la),
        .safe_pre_la_o(safe_pre_la),
        .row_valid_o(row_valid), .open_row_o(open_row), .state_o(state),
        .obs_rcd_nz_o(obs_rcd_nz), .obs_preblk_nz_o(obs_preblk_nz),
        .obs_ras_nz_o(obs_ras_nz), .obs_ap_pending_o(obs_ap_pending)
    );

    // THE ENVIRONMENT OBEYS THE GATE. This block is a permission gate: the
    // arbiter issues a command only in a cycle where the matching safe_*_o is
    // high. Without this stated, the engine issues a RD+AP at a CLOSED bank and
    // arms r_ap_pending with row_valid low -- a state the RTL has no guard
    // against (the `else if (set_rd_i || set_wr_i) r_ap_pending <= set_ap_i;`
    // arm is unconditional), and from which w_ap_fire would later reload tRP and
    // block an ACT for no reason. It is unreachable in the system, but only
    // because of this contract, so the contract is written down rather than
    // assumed silently.
    //
    // This is NOT circular with the spacing properties below. Those assert on
    // safe_*_o -- that the GATE does not open early. The assumption constrains
    // only when the environment may PUSH a command through an already-open
    // gate. A gate that opened early would still be caught.
    //
    // No combinational loop: every safe_*_o is a function of registers alone.
    always @(*) if (rst_n) begin
        assume (!set_act || safe_act);
        assume (!set_rd  || safe_rd);
        assume (!set_wr  || safe_wr);
        assume (!set_pre || safe_pre);
    end

    // ---- formal infrastructure ---------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Hold reset for the first two cycles, then release it and keep it
    // released: these are properties about running behaviour, not about reset.
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // Elapsed-cycle counters since each command, saturating. `cnt_*` answers
    // "how many cycles since the last X", which is what a spacing property
    // needs and what the DUT deliberately does not expose.
    localparam int CW = TW + 3;
    reg [CW-1:0] cnt_act, cnt_pre, cnt_rd, cnt_wr;
    reg          seen_act, seen_pre, seen_rd, seen_wr;

    always @(posedge clk) begin
        if (!rst_n) begin
            cnt_act <= 0; cnt_pre <= 0; cnt_rd <= 0; cnt_wr <= 0;
            seen_act <= 1'b0; seen_pre <= 1'b0; seen_rd <= 1'b0; seen_wr <= 1'b0;
        end else begin
            if (set_act) begin cnt_act <= 0; seen_act <= 1'b1; end
            else if (cnt_act != {CW{1'b1}}) cnt_act <= cnt_act + 1'b1;

            if (set_pre) begin cnt_pre <= 0; seen_pre <= 1'b1; end
            else if (cnt_pre != {CW{1'b1}}) cnt_pre <= cnt_pre + 1'b1;

            if (set_rd) begin cnt_rd <= 0; seen_rd <= 1'b1; end
            else if (cnt_rd != {CW{1'b1}}) cnt_rd <= cnt_rd + 1'b1;

            if (set_wr) begin cnt_wr <= 0; seen_wr <= 1'b1; end
            else if (cnt_wr != {CW{1'b1}}) cnt_wr <= cnt_wr + 1'b1;
        end
    end

    // One-cycle history, for the two properties that span an edge. `|=>` is not
    // available in the immediate form, so the antecedent is registered instead.
    reg r_ap_armed, r_ap_pending_d;
    always @(posedge clk) begin
        r_ap_armed     <= obs_ap_pending && !obs_preblk_nz && !obs_ras_nz;
        r_ap_pending_d <= obs_ap_pending;
    end

    // =====================================================================
    // FAMILY 1 -- JEDEC spacing. Each says: the gate cannot open early.
    // =====================================================================
    always @(posedge clk) if (rst_n) begin
        // tRC: an ACT reloads tRC, and no ACT may be permitted until it
        // elapses -- this is the one that survives an intervening PRE, which
        // is why tRC exists separately from tRP.
        if (seen_act && cnt_act < t_rc)  a_trc:  assert (!safe_act);

        // tRP: a PRE reloads tRP; no ACT until it elapses.
        if (seen_pre && cnt_pre < t_rp)  a_trp:  assert (!safe_act);

        // tRCD: ACT -> first column command.
        if (seen_act && cnt_act < t_rcd) a_trcd: assert (!(safe_rd || safe_wr));

        // tRAS: ACT -> PRE.
        if (seen_act && cnt_act < t_ras) a_tras: assert (!safe_pre);

        // tRTP: RD -> PRE. Read recovery. The `cnt_rd <= cnt_wr` guard picks
        // the more recent of the two column commands: the block tracks one
        // precharge-block counter, so the older command's window is already
        // subsumed and asserting on it would be asserting the wrong timing.
        if (seen_rd && cnt_rd < t_rtp && cnt_rd <= cnt_wr)
            a_trtp: assert (!safe_pre);

        // tWR: WR -> PRE. Write recovery -- the longer of the two, and the one
        // whose anchor was wrong once before (the pumice timing-derivation fix).
        if (seen_wr && cnt_wr < t_wr && cnt_wr <= cnt_rd)
            a_twr:  assert (!safe_pre);
    end

    // =====================================================================
    // FAMILY 2 -- structural invariants the rest of the design assumes.
    // =====================================================================
    always @(posedge clk) if (rst_n) begin
        // The three K-map implications (pumice TASK-029). The first two are why
        // the arbiter's activate and precharge maps render DIFFERS: the arbiter
        // re-states a term this block guarantees.
        if (safe_act)               a_act_implies_closed: assert (!row_valid);
        if (safe_rd || safe_wr)     a_col_implies_open:   assert (row_valid);
        if (safe_pre)               a_pre_implies_open:   assert (row_valid);

        // The K-map for w_ap_fire omits row_valid as an axis, arguing
        // ap_pending implies it. That argument is checked here.
        if (obs_ap_pending)         a_ap_implies_open:    assert (row_valid);

        // A bank cannot be simultaneously safe to open and safe to use or close.
        a_excl_act_col: assert (!(safe_act && (safe_rd || safe_wr)));
        a_excl_act_pre: assert (!(safe_act && safe_pre));

        // safe_rd and safe_wr are one expression in the RTL; if they ever
        // diverge, a reader of either is wrong about the other.
        a_rd_eq_wr: assert (safe_rd == safe_wr);

        // An auto-precharge, once armed, fires at most once: the firing edge
        // clears both ap_pending and row_valid, so it cannot re-fire without a
        // new column command.
        if (f_past_valid > 2 && r_ap_armed)
            a_ap_single_fire: assert ((!obs_ap_pending && !row_valid) || set_act);

        // A column command with auto-precharge must not leave the row usable.
        if (obs_ap_pending)
            a_ap_kills_columns: assert (!(safe_rd || safe_wr));

        // At LA=0 the advisory outputs are defined to equal their live twins. A
        // scheduler that read one expecting the other would be reading a
        // promise the block never made.
        if (LA == 0) begin
            a_la_act: assert (safe_act_la  == safe_act);
            a_la_col: assert (safe_rdwr_la == safe_rd);
            a_la_pre: assert (safe_pre_la  == safe_pre);
        end
    end

    // =====================================================================
    // COVER -- the proofs above are vacuous if the interesting states are
    // unreachable, so each is reached explicitly.
    // =====================================================================
    always @(posedge clk) if (rst_n) begin
        // a bank recovers and is allowed to reopen
        c_act_permitted: cover (seen_act && safe_act);
        // tRCD elapses and a column command is allowed
        c_col_permitted: cover (safe_rd);
        // tRAS and the recovery windows elapse and a close is allowed
        c_pre_permitted: cover (safe_pre);
        // auto-precharge actually fires: armed, then gone with the row closed
        c_ap_fires:      cover (r_ap_pending_d && !obs_ap_pending && !row_valid);
        // tRP elapses after a PRE and the bank may open again
        c_pre_then_act:  cover (seen_pre && safe_act);
    end

endmodule
