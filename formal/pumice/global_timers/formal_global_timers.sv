// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for global_timers -- the constraint trackers that span banks.
//
// WHY THIS BLOCK. It is the third leg of pumice's JEDEC device safety.
// bank_timer holds the PER-BANK windows; this holds the ones no single bank can
// see: tFAW (at most four ACTs in a rolling window -- a thermal and power limit,
// not a data one), tRRD (ACT-to-ACT anywhere in the rank), and the shared-DQ
// windows tWTR / tRTW / tCCD.
//
// THE QUESTION THIS FILE ASKS. The block does not GATE anything. It reports
// readiness and the scheduler does the gating -- and every one of its outputs is
// STRICT-FLOPPED, so what the scheduler reads is the state of one cycle ago.
// The property that matters is therefore not "the counters count", it is:
//
//     IF the scheduler issues only when this block says it may,
//     THEN is JEDEC actually satisfied?
//
// THE ANSWER IS NO, and that is the result of this file. Asked with exactly
// that assumption and nothing more, the engine produces a four-step
// counterexample: the readiness outputs stay high for one cycle after the
// command that should have cleared them, so a second command goes out inside
// the window. The full trace, and the arbiter comments showing the consumer
// already compensates for it, are at the assumption block below.
//
// What is proved here is therefore the contract the consumer actually
// implements: the published flag PLUS one cycle of the consumer's own. The
// assertions check the REAL JEDEC spacing against an independent history kept
// in this wrapper -- nothing here reads a counter the DUT maintains; the
// wrapper times the commands itself.
//
// WHAT IS PROVED
//   * tFAW: no fifth ACT inside t_faw of the fourth-previous one
//   * tRRD: ACT to ACT
//   * tCCD: column command to column command
//   * tWTR: WR to RD   (the shared DQ bus turning around)
//   * tRTW: RD to WR
//   * the obs_* debug flags agree with the readiness outputs they shadow
//
// BOUNDED ON PURPOSE. Timings are anyconst and small; the counters are the same
// counters at 6 as at 60, and a small bound is what lets the tFAW window be
// exercised exhaustively rather than sampled.
//
// SINGLE RANK. NUM_RANKS=1 is the board configuration. The per-rank structures
// are replicated, not interacting -- tFAW and tRRD are per-rank by construction
// -- so a second rank re-proves the same logic against a second copy.
//
// YOSYS-COMPATIBLE FORM. DUT pre-flattened by sv2v; immediate assertions.

`timescale 1ns / 1ps

module formal_global_timers #(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8
) (
    input logic mc_clk,
    input logic mc_rst_n
);

    // ---- CSR-programmed timings: stable once init has run -------------------
    (* anyconst *) reg [7:0] t_faw_i, t_rrd_i, t_wtr_global_i, t_rtw_i, t_ccd_i;
    always @(*) begin
        // tFAW MUST BE ABLE TO BIND, and getting this ceiling wrong made
        // a_tfaw VACUOUS -- it passed against a DUT whose tFAW window had been
        // deliberately broken (mutation: install every ACT into slot 0, so the
        // other three never fill and the window never closes).
        //
        // The reason is that tRRD already spaces the ACTs. One ACT reloads tRRD
        // and the readiness flop needs a further cycle to catch up, so the
        // minimum achievable ACT-to-ACT spacing here is t_rrd + 2 = 3. Four ACTs
        // therefore span at least 9 cycles, and the fifth arrives 12 cycles
        // after the first -- so ANY t_faw at or below 12 is satisfied by tRRD
        // alone, whatever the tFAW logic does. The proof was checking tRRD
        // twice and tFAW not at all.
        //
        // A ceiling above that span is what makes tFAW the binding constraint,
        // and the mutation now fails as it should. c_faw_blocks was also
        // unreachable at the original ceiling of 6, which was the first hint.
        assume (t_faw_i >= 2 && t_faw_i <= 20);
        assume (t_rrd_i >= 1 && t_rrd_i <= 3);
        assume (t_wtr_global_i >= 1 && t_wtr_global_i <= 3);
        assume (t_rtw_i >= 1 && t_rtw_i <= 3);
        assume (t_ccd_i >= 1 && t_ccd_i <= 3);
    end

    (* anyseq *) reg evt_act_i, evt_rd_i, evt_wr_i;
    wire [0:0] evt_act_rank_i = 1'b0;      // NUM_RANKS = 1

    wire [NUM_RANKS-1:0] tfaw_window_ok_o, trrd_window_ok_o;
    wire                 twtr_global_ok_o, trtw_window_ok_o, tccd_window_ok_o;
    wire [NUM_RANKS-1:0] obs_faw_nz_o, obs_trrd_nz_o;
    wire                 obs_twtr_nz_o, obs_trtw_nz_o, obs_tccd_nz_o;

    global_timers #(.NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS)) dut (
        .mc_clk(mc_clk), .mc_rst_n(mc_rst_n),
        .t_faw_i(t_faw_i), .t_rrd_i(t_rrd_i),
        .t_wtr_global_i(t_wtr_global_i), .t_rtw_i(t_rtw_i), .t_ccd_i(t_ccd_i),
        .evt_act_i(evt_act_i), .evt_act_rank_i(evt_act_rank_i),
        .evt_rd_i(evt_rd_i), .evt_wr_i(evt_wr_i),
        .tfaw_window_ok_o(tfaw_window_ok_o), .trrd_window_ok_o(trrd_window_ok_o),
        .twtr_global_ok_o(twtr_global_ok_o), .trtw_window_ok_o(trtw_window_ok_o),
        .tccd_window_ok_o(tccd_window_ok_o),
        .obs_faw_nz_o(obs_faw_nz_o), .obs_trrd_nz_o(obs_trrd_nz_o),
        .obs_twtr_nz_o(obs_twtr_nz_o), .obs_trtw_nz_o(obs_trtw_nz_o),
        .obs_tccd_nz_o(obs_tccd_nz_o)
    );

    // ---- formal infrastructure ---------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge mc_clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!mc_rst_n);
    always @(posedge mc_clk) if (f_past_valid >= 2) assume (mc_rst_n);

    // =========================================================================
    // THE ENVIRONMENT CONTRACT -- and the one-cycle seam that makes it what it
    // is. THIS IS THE FINDING OF THIS FILE, so it is written out in full.
    //
    // The first version of this wrapper assumed only what the block PUBLISHES:
    // issue when the matching *_ok_o output is high. The engine refuted that in
    // four steps:
    //
    //     t=2  evt_rd_i=1                 -> reloads tCCD=2, tRTW=1 on the edge
    //     t=3  tccd_window_ok_o=1         -> STILL HIGH: the outputs are
    //          trtw_window_ok_o=1            strict-flopped, so they report the
    //                                        counters as they were BEFORE the
    //                                        reload landed
    //     t=3  evt_wr_i=1                 -> permitted, and issues one cycle
    //                                        after the read: age_col=0 against
    //                                        t_ccd=2, age_rd=0 against t_rtw=1
    //     t=4  both flags finally drop
    //
    // Every readiness output has this seam: the gate stays open for exactly one
    // cycle after the command that should have closed it. So obeying these
    // outputs alone does NOT satisfy JEDEC, and the block's real contract is
    // weaker than its port list suggests.
    //
    // THE CONSUMER ALREADY KNOWS. This is not an unreported hazard; it is an
    // unwritten-down one. pumice_cmd_arbiter.sv says of tCCD:
    //
    //     "tccd_ok_i is a flop that reloads on the column FIRE ... This
    //      REPLACES the flopped global tccd_ok_i on the column masks ...
    //      tccd_ok_i stays an input for observability only."
    //
    // and of the turnarounds, under the heading "ONE-CYCLE BLIND SPOT (board
    // round 2)", it adds `!(w_fire_out && r_do_rd)` terms because the flags
    // alone let "a WRITE picked in the very cycle a READ fires out" go one cycle
    // behind it -- found on a board ILA capture, tRTW of 20 honoured as 1.
    //
    // So the assumption below is the contract the arbiter actually implements:
    // the published flag, PLUS one cycle of the consumer's own. That is what is
    // proved here. What is NOT proved is that this block alone is sufficient --
    // it is not, and a future consumer that trusts the port list without adding
    // its own term will violate tCCD and tRTW. See pumice ISSUE-018.
    // =========================================================================
    reg f_act_d, f_col_d;
    always @(posedge mc_clk) begin
        if (!mc_rst_n) begin f_act_d <= 1'b0; f_col_d <= 1'b0; end
        else begin
            f_act_d <= evt_act_i;
            f_col_d <= evt_rd_i || evt_wr_i;
        end
    end

    always @(*) if (mc_rst_n) begin
        // One DRAM command per cycle: the DFI carries one command slot.
        assume ($countones({evt_act_i, evt_rd_i, evt_wr_i}) <= 1);

        // An ACT needs a free tFAW slot and an elapsed tRRD -- plus the
        // consumer's own one-cycle term, for the seam described above.
        assume (!evt_act_i || (tfaw_window_ok_o[0] && trrd_window_ok_o[0]
                               && !f_act_d));
        // A column command needs tCCD, and a RD additionally needs the write
        // recovery on the shared DQ bus while a WR needs the read turnaround.
        assume (!evt_rd_i || (tccd_window_ok_o && twtr_global_ok_o && !f_col_d));
        assume (!evt_wr_i || (tccd_window_ok_o && trtw_window_ok_o && !f_col_d));
    end

    // =========================================================================
    // INDEPENDENT HISTORY. The wrapper times the commands itself; it does not
    // read any counter the DUT keeps.
    // =========================================================================
    localparam int AW = 10;                       // ages saturate well past t_faw
    reg [AW-1:0] age_act, age_rd, age_wr, age_col;
    reg          seen_act, seen_rd, seen_wr, seen_col;

    // Ages of the four most recent ACTs, faw_age[3] being the oldest of them.
    reg [AW-1:0] faw_age [4];
    reg [2:0]    n_act;                           // saturating count of ACTs so far

    integer i;
    always @(posedge mc_clk) begin
        if (!mc_rst_n) begin
            age_act <= 0; age_rd <= 0; age_wr <= 0; age_col <= 0;
            seen_act <= 0; seen_rd <= 0; seen_wr <= 0; seen_col <= 0;
            n_act <= 0;
            for (i = 0; i < 4; i = i + 1) faw_age[i] <= {AW{1'b1}};
        end else begin
            if (evt_act_i) begin age_act <= 0; seen_act <= 1'b1; end
            else if (age_act != {AW{1'b1}}) age_act <= age_act + 1'b1;

            if (evt_rd_i) begin age_rd <= 0; seen_rd <= 1'b1; end
            else if (age_rd != {AW{1'b1}}) age_rd <= age_rd + 1'b1;

            if (evt_wr_i) begin age_wr <= 0; seen_wr <= 1'b1; end
            else if (age_wr != {AW{1'b1}}) age_wr <= age_wr + 1'b1;

            if (evt_rd_i || evt_wr_i) begin age_col <= 0; seen_col <= 1'b1; end
            else if (age_col != {AW{1'b1}}) age_col <= age_col + 1'b1;

            // tFAW history: every recorded ACT ages, and a new one shifts in.
            for (i = 0; i < 4; i = i + 1)
                if (faw_age[i] != {AW{1'b1}}) faw_age[i] <= faw_age[i] + 1'b1;
            if (evt_act_i) begin
                faw_age[3] <= (faw_age[2] == {AW{1'b1}}) ? {AW{1'b1}} : faw_age[2] + 1'b1;
                faw_age[2] <= (faw_age[1] == {AW{1'b1}}) ? {AW{1'b1}} : faw_age[1] + 1'b1;
                faw_age[1] <= (faw_age[0] == {AW{1'b1}}) ? {AW{1'b1}} : faw_age[0] + 1'b1;
                // 1, not 0: this is read on a LATER cycle, so by the time anyone
                // looks, one cycle has elapsed. Seeding it at 0 made every age
                // one low, which happens to make the assertion stricter rather
                // than weaker -- but a history that is quietly off by one is not
                // something to leave in a proof and rely on the direction of.
                faw_age[0] <= 1;
                if (n_act != 3'd7) n_act <= n_act + 1'b1;
            end
        end
    end

    // =========================================================================
    // FAMILY 1 -- JEDEC spacing, measured by this wrapper, not by the DUT.
    // =========================================================================
    always @(posedge mc_clk) if (mc_rst_n && f_past_valid > 2) begin
        // tFAW: this ACT is the fifth only if four earlier ones exist; the
        // oldest of those four must have fallen out of the window.
        if (evt_act_i && n_act >= 3'd4)
            a_tfaw: assert (faw_age[3] >= {2'b0, t_faw_i});

        // tRRD: ACT to ACT within the rank.
        if (evt_act_i && seen_act)
            a_trrd: assert (age_act >= {2'b0, t_rrd_i});

        // tCCD: column to column, either direction.
        if ((evt_rd_i || evt_wr_i) && seen_col)
            a_tccd: assert (age_col >= {2'b0, t_ccd_i});

        // tWTR: the DQ bus turning from write to read.
        if (evt_rd_i && seen_wr)
            a_twtr: assert (age_wr >= {2'b0, t_wtr_global_i});

        // tRTW: and back from read to write.
        if (evt_wr_i && seen_rd)
            a_trtw: assert (age_rd >= {2'b0, t_rtw_i});
    end

    // =========================================================================
    // FAMILY 2 -- the debug view must match the view the scheduler acts on.
    // obs_* is combinational and the readiness outputs are flopped, so obs_*
    // leads by exactly one cycle. A debug read that disagreed would misdirect
    // any investigation of a spacing violation.
    // =========================================================================
    reg f_faw_nz_d, f_trrd_nz_d, f_twtr_nz_d, f_trtw_nz_d, f_tccd_nz_d;
    always @(posedge mc_clk) begin
        f_faw_nz_d  <= obs_faw_nz_o[0];
        f_trrd_nz_d <= obs_trrd_nz_o[0];
        f_twtr_nz_d <= obs_twtr_nz_o;
        f_trtw_nz_d <= obs_trtw_nz_o;
        f_tccd_nz_d <= obs_tccd_nz_o;
    end

    always @(posedge mc_clk) if (mc_rst_n && f_past_valid > 3) begin
        a_obs_faw:  assert (tfaw_window_ok_o[0] == !f_faw_nz_d);
        a_obs_trrd: assert (trrd_window_ok_o[0] == !f_trrd_nz_d);
        a_obs_twtr: assert (twtr_global_ok_o    == !f_twtr_nz_d);
        a_obs_trtw: assert (trtw_window_ok_o    == !f_trtw_nz_d);
        a_obs_tccd: assert (tccd_window_ok_o    == !f_tccd_nz_d);
    end

    // =========================================================================
    // COVER
    // =========================================================================
    always @(posedge mc_clk) if (mc_rst_n) begin
        c_four_acts:   cover (n_act >= 3'd4);               // the window fills
        c_fifth_act:   cover (evt_act_i && n_act >= 3'd4);  // tFAW actually bites
        c_faw_blocks:  cover (!tfaw_window_ok_o[0]);        // the block says no
        c_wr_then_rd:  cover (evt_rd_i && seen_wr);         // DQ turnaround
        c_rd_then_wr:  cover (evt_wr_i && seen_rd);
        c_ccd_blocks:  cover (!tccd_window_ok_o);
    end

endmodule
