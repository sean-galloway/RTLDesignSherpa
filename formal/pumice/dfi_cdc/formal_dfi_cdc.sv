// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for pumice_dfi_cdc -- THE clock-domain crossing of pumice.
//
// WHY THIS WRAPPER IS SMALL, DELIBERATELY. All six FIFOs here are
// `gaxi_fifo_async`, and that FIFO is ALREADY PROVED multiclock in
// formal/cdc/gaxi_fifo_async -- Gray pointers, arbitrary clock drift. What
// that proof cannot see is the logic this block adds AROUND the FIFOs: the
// token/data pairing gating, the level->edge->token->sticky-latch chains, and
// this block's own port wiring. That is what is proved here, in a
// single-clock configuration (ctl_clk tied to dfi_clk), which is the worst
// case for the logic and a special case of the FIFO.
//
// WHAT IS PROVED
//
//   FAMILY 1 -- TOKEN/DATA PAIRING, the one with a real hazard in it. A write
//   burst crosses as data words plus, on the last word, a "burst staged" TOKEN
//   in a second FIFO. The two are gated differently:
//
//       wd_ready_o   = w_wd_data_ready && w_wtok_ready
//       w_wtok_push  = wd_valid_i && wd_last_i && w_wd_data_ready
//       (data FIFO)  wr_valid = wd_valid_i && w_wtok_ready
//
//   If those ever disagree, a burst's data crosses without its token -- the
//   PHY waits forever for a burst it already has -- or a token crosses without
//   its data, and the PHY drives a burst of nothing. Proved: the accepted
//   token push is EXACTLY the accepted last beat (instantaneously, and as a
//   lifetime count), and the PHY port never presents more staged bursts than
//   the controller completed.
//
//   FAMILY 2 -- NO BEAT LOST OR DUPLICATED ACROSS THE BOUNDARY. For each of
//   the three payload streams (cmd, wrdata, rddata) the wrapper keeps a
//   shadow of everything pushed on the source port and proves: a pop is never
//   counted that was not pushed (no fabrication on the far side), and what
//   pops on the far side is bit-for-bit what was pushed, in order. This is
//   the end-to-end statement of the crossing at this block's ports; the
//   metastability/Gray-pointer half of "no beat lost" under real clock drift
//   is gaxi_fifo_async's own proof, not re-derived here.
//
//   FAMILY 3 -- INIT TOKEN SEMANTICS. The push into each init token FIFO is
//   EXACTLY a RISING EDGE of its level (a level held high must not re-push and
//   re-run init), the sticky latches are MONOTONIC (init cannot un-complete),
//   a sticky latch is never set without a token actually pushed (no spurious
//   init), and an init token is never pushed into a full token FIFO (the two
//   token FIFOs leave wr_ready unconnected in the RTL, so a drop would be
//   silent -- the probe surfaces it).
//
// HOW INTERNALS ARE OBSERVED -- AND WHY THE OLD WAY IS GONE. The first
// version of this wrapper probed DUT internals hierarchically (`dut.w_*`),
// and read nets that demonstrably were not the source signals: yosys 0.62
// does NOT resolve dotted references from the wrapper into the DUT in this
// flow -- every one "elaborates" as an IMPLICIT WIRE (frontend warning
// "Identifier ... is implicitly declared"), and in formal mode an undriven
// wire is a FREE INPUT. (The same mechanism leaves wr_data_cam's disabled
// SRAM-readback shadow tracking free wires, which is why that
// counterexample could never be corroborated.) The same failure was
// reproduced here against non-parametrized instances, plain-Verilog children,
// and `prep -flatten`: it never resolves. So this wrapper uses NO dotted
// references. The generated (untracked) flat file carries probe OUTPUT PORTS
// on the DUT -- o_p_w_wd_data_ready, o_p_w_wtok_ready, o_p_w_wtok_push,
// o_p_w_istart_push, o_p_w_icmp_push, and the two init-token wr_ready nets,
// which the RTL leaves dangling and the probe injection fills in. The
// injection script (inject_probes.py) verifies every source hookup INSTANCE
// BY INSTANCE against the sv2v output before wiring and fails the build if
// the flat names drift -- the audit is part of the flow, not a notebook
// entry. The audit assertions below (a_aud_*) then tie each probe back to
// the port-level equations from the source, so a probe wired to the wrong
// net fails the proof instead of quietly proving nothing.
//
// ONE CLOCK, STATED AS A LIMITATION. ctl_clk and dfi_clk are tied together
// here. That makes this a proof about the block's LOGIC around the crossing,
// not a re-derivation of the crossing: the crossing itself under arbitrary
// clock relation is what gaxi_fifo_async's multiclock proof covers. All
// properties below are port-level statements that hold regardless; tying the
// clocks removes the synchronizer latency so the covers land inside a
// 20-cycle depth.
//
// ENVIRONMENT. The ONLY assumptions are reset discipline (asserted low at
// time 0, released after two cycles) -- see the assume block. Every valid and
// every pop input is free, including popping `pwr_staged_pop_i` whenever the
// PHY likes; counting is qualified by the DUT's own valids, so nothing in
// FAMILY 1 or 2 is assumed about the environment's behaviour. The hazard in
// FAMILY 1 is entirely internal gating, and no input assumption touches it.
//
// MUTATION EVIDENCE (patched copies of cdc_flat.v under /tmp/dfi_cdc_mut,
// never the tracked RTL; each run as its own sby task against THIS wrapper,
// BMC depth 12 -- every planted defect fails inside ~12 cycles). A property
// that cannot fail is not coverage; all eight fail:
//
//   MUTATION (patch on the generated flat)              FIRST ASSERTION THAT FAILED
//   m1_tok_drop_last   w_wtok_push loses && wd_last_i   a_token_per_burst   (F1)
//   m2_ready_drop_tokgate wd_ready_o loses && w_wtok_ready a_aud_wd_ready  (F1)
//   m3_staged_valid_tied u_wtok_fifo.rd_valid <- prd_valid_i a_no_extra_staged (F1)
//   m4_cmd_data_invert u_cmd_fifo.wr_data <- ~cmd_data_i a_cmd_integrity    (F2)
//   m5_rd_data_bypass  u_rd_fifo.rd_data <- prd_data_i  a_rd_integrity      (F2)
//   m6_rd_valid_tied   u_rd_fifo.rd_valid <- cmd_valid_i a_rd_nofab         (F2)
//   m7_istart_level_push w_istart_push loses && !r_istart_d a_istart_edge   (F3)
//   m8_pinit_not_sticky sticky latch made transparent  a_pinit_start_sticky (F3)
//
// Coverage of the families by the mutations: F1 token/data pairing (m1-m3),
// F2 no-beat-lost-or-duplicated end to end (m4-m6), F3 rising-edge push and
// the sticky chain (m7-m8). The driver is /tmp/dfi_cdc_mut/run_mutations.py
// (regenerates the patched flats + sby tasks and reruns all eight).
// RESULT: 8/8 FAIL as recorded above -- every property family fails on at
// least one mutation.
//
// YOSYS-COMPATIBLE FORM. DUT pre-flattened by sv2v; immediate assertions in
// `always @(posedge clk)`; concurrent `assert property` rejected by this
// frontend (TASK-035 traps). Assertions are labelled and loop-free: a labelled
// assertion inside a for loop creates one cell per iteration with the same
// name and yosys rejects the build. Counters and shadows start at the same
// cycle the assertions start (f_past_valid > 2), per the "counters must start
// where the assertion starts" trap.

`timescale 1ns / 1ps

module formal_dfi_cdc #(
    parameter int CMD_DW = 4,
    parameter int WD_DW  = 4,
    parameter int RD_DW  = 4,
    parameter int CMD_DEPTH = 4,
    parameter int WD_DEPTH  = 4,
    parameter int RD_DEPTH  = 4,
    parameter int TOK_DEPTH = 4
) (
    input logic clk,
    input logic rstn
);

    (* anyseq *) reg              cmd_valid_i, wd_valid_i, wd_last_i;
    (* anyseq *) reg [CMD_DW-1:0] cmd_data_i;
    (* anyseq *) reg [WD_DW-1:0]  wd_data_i;
    (* anyseq *) reg              init_start_i;
    (* anyseq *) reg              pcmd_ready_i, pwd_ready_i, pwr_staged_pop_i;
    (* anyseq *) reg              prd_valid_i;
    (* anyseq *) reg [RD_DW-1:0]  prd_data_i;
    (* anyseq *) reg              pinit_complete_i;
    (* anyseq *) reg              rd_ready_i;

    wire cmd_ready_o, wd_ready_o, init_complete_o;
    wire pcmd_valid_o; wire [CMD_DW-1:0] pcmd_data_o;
    wire pwd_valid_o;  wire [WD_DW-1:0]  pwd_data_o;
    wire pwr_staged_valid_o;
    wire prd_ready_o;
    wire rd_valid_o;   wire [RD_DW-1:0]  rd_data_o;
    wire pinit_start_o;

    // Probe ports, wired to the source nets by inject_probes.py (see header).
    // The two token-ready probes are nets the RTL leaves dangling; the
    // injection fills those hookups so a drop would be visible.
    wire p_w_wd_data_ready, p_w_wtok_ready, p_w_wtok_push;
    wire p_w_istart_push, p_w_icmp_push;
    wire p_w_istart_tok_ready, p_w_icmp_tok_ready;

    pumice_dfi_cdc #(
        .CMD_DW(CMD_DW), .WD_DW(WD_DW), .RD_DW(RD_DW),
        .CMD_DEPTH(CMD_DEPTH), .WD_DEPTH(WD_DEPTH), .RD_DEPTH(RD_DEPTH),
        .TOK_DEPTH(TOK_DEPTH)
    ) dut (
        .ctl_clk(clk), .ctl_rstn(rstn), .dfi_clk(clk), .dfi_rstn(rstn),
        .cmd_valid_i(cmd_valid_i), .cmd_ready_o(cmd_ready_o), .cmd_data_i(cmd_data_i),
        .wd_valid_i(wd_valid_i), .wd_ready_o(wd_ready_o), .wd_data_i(wd_data_i),
        .wd_last_i(wd_last_i),
        .init_start_i(init_start_i), .init_complete_o(init_complete_o),
        .rd_valid_o(rd_valid_o), .rd_ready_i(rd_ready_i), .rd_data_o(rd_data_o),
        .pcmd_valid_o(pcmd_valid_o), .pcmd_ready_i(pcmd_ready_i), .pcmd_data_o(pcmd_data_o),
        .pwd_valid_o(pwd_valid_o), .pwd_ready_i(pwd_ready_i), .pwd_data_o(pwd_data_o),
        .pwr_staged_valid_o(pwr_staged_valid_o), .pwr_staged_pop_i(pwr_staged_pop_i),
        .pinit_start_o(pinit_start_o),
        .prd_valid_i(prd_valid_i), .prd_ready_o(prd_ready_o), .prd_data_i(prd_data_i),
        .pinit_complete_i(pinit_complete_i),
        .o_p_w_wd_data_ready(p_w_wd_data_ready),
        .o_p_w_wtok_ready(p_w_wtok_ready),
        .o_p_w_wtok_push(p_w_wtok_push),
        .o_p_w_istart_push(p_w_istart_push),
        .o_p_w_icmp_push(p_w_icmp_push),
        .w_istart_tok_ready(p_w_istart_tok_ready),
        .w_icmp_tok_ready(p_w_icmp_tok_ready)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rstn);
    always @(posedge clk) if (f_past_valid >= 2) assume (rstn);

    // Handshakes, counted nowhere else (the "count handshakes, not offered
    // signals" trap: a push qualified by only half its ready condition stores
    // nothing).
    wire w_wd       = wd_valid_i  && wd_ready_o;
    wire w_tok_fire = p_w_wtok_push && p_w_wtok_ready;
    wire w_cmd_push = cmd_valid_i && cmd_ready_o;
    wire w_cmd_pop  = pcmd_valid_o && pcmd_ready_i;
    wire w_wd_pop   = pwd_valid_o  && pwd_ready_i;
    wire w_rd_push  = prd_valid_i  && prd_ready_o;
    wire w_rd_pop   = rd_valid_o   && rd_ready_i;

    // =====================================================================
    // FAMILY 1 -- TOKEN / DATA PAIRING
    // =====================================================================
    reg [9:0] f_last_beats, f_tok_pushes, f_staged_pops;
    always @(posedge clk) begin
        // Reset on !rstn ONLY: rstn is released while f_past_valid is still 2,
        // and from that cycle the DUT already stores pushes -- a shadow that
        // stays in reset until f_past_valid > 2 misses them and mismatches
        // forever after (the counter-window trap, this time with the DUT
        // active one cycle before the counters). Assertions stay gated at
        // f_past_valid > 2 below.
        if (!rstn) begin
            f_last_beats <= 0; f_tok_pushes <= 0; f_staged_pops <= 0;
        end else begin
            if (w_wd && wd_last_i) f_last_beats <= f_last_beats + 1'b1;
            if (w_tok_fire) f_tok_pushes <= f_tok_pushes + 1'b1;
            if (pwr_staged_valid_o && pwr_staged_pop_i)
                f_staged_pops <= f_staged_pops + 1'b1;
        end
    end

    always @(posedge clk) if (rstn && f_past_valid > 2) begin
        // The probes really are the source signals: each is tied back to the
        // port-level equation it is meant to carry. These five are the whole
        // name-resolution audit; a mis-wired probe fails here.
        a_aud_wd_ready: assert (wd_ready_o == (p_w_wd_data_ready && p_w_wtok_ready));
        a_aud_tok_push: assert (p_w_wtok_push == ((wd_valid_i && wd_last_i) && p_w_wd_data_ready));

        // The accepted token push IS the accepted last beat. Algebraically
        // identical in the source; asserted so a wiring change that breaks
        // the algebra cannot pass:
        //   w_tok_fire = wd_valid_i && wd_last_i && w_wd_data_ready && w_wtok_ready
        //   w_wd       = wd_valid_i &&              w_wd_data_ready && w_wtok_ready
        a_pair_fire_eq: assert (w_tok_fire == (w_wd && wd_last_i));
        a_token_per_burst: assert (f_tok_pushes == f_last_beats);

        // The PHY port never presents more staged bursts than the controller
        // completed. Counting is qualified by pwr_staged_valid_o itself, so
        // the environment popping an empty FIFO (valid low) is not counted
        // and no environment contract is needed for this to be meaningful.
        a_no_extra_staged: assert (f_staged_pops <= f_last_beats);
    end

    // =====================================================================
    // FAMILY 2 -- NO BEAT LOST OR DUPLICATED ACROSS THE BOUNDARY
    // Shadow of every payload pushed, per stream. The far-side pop must be
    // one that was pushed (never fabricated), and bit-for-bit the pushed
    // value, in order. Mod-16 indexing is sound because the FIFOs never hold
    // more than their depth (<= 4 outstanding < 16 shadow slots).
    // =====================================================================
    reg [CMD_DW-1:0] f_cmd_shadow [0:15];
    reg [WD_DW-1:0]  f_wd_shadow  [0:15];
    reg [RD_DW-1:0]  f_rd_shadow  [0:15];
    reg [7:0] f_cmd_push_n, f_cmd_pop_n;
    reg [7:0] f_wd_push_n,  f_wd_pop_n;
    reg [7:0] f_rd_push_n,  f_rd_pop_n;

    integer mi;
    always @(posedge clk) begin
        // Reset on !rstn ONLY: rstn is released while f_past_valid is still 2,
        // and from that cycle the DUT already stores pushes -- a shadow that
        // stays in reset until f_past_valid > 2 misses them and mismatches
        // forever after (the counter-window trap, this time with the DUT
        // active one cycle before the counters). Assertions stay gated at
        // f_past_valid > 2 below.
        if (!rstn) begin
            f_cmd_push_n <= 0; f_cmd_pop_n <= 0;
            f_wd_push_n  <= 0; f_wd_pop_n  <= 0;
            f_rd_push_n  <= 0; f_rd_pop_n  <= 0;
            for (mi = 0; mi < 16; mi = mi + 1) begin
                f_cmd_shadow[mi] <= 0;
                f_wd_shadow[mi]  <= 0;
                f_rd_shadow[mi]  <= 0;
            end
        end else begin
            if (w_cmd_push) begin
                f_cmd_shadow[f_cmd_push_n[3:0]] <= cmd_data_i;
                f_cmd_push_n <= f_cmd_push_n + 1'b1;
            end
            if (w_cmd_pop) f_cmd_pop_n <= f_cmd_pop_n + 1'b1;
            if (w_wd) begin
                f_wd_shadow[f_wd_push_n[3:0]] <= wd_data_i;
                f_wd_push_n <= f_wd_push_n + 1'b1;
            end
            if (w_wd_pop) f_wd_pop_n <= f_wd_pop_n + 1'b1;
            if (w_rd_push) begin
                f_rd_shadow[f_rd_push_n[3:0]] <= prd_data_i;
                f_rd_push_n <= f_rd_push_n + 1'b1;
            end
            if (w_rd_pop) f_rd_pop_n <= f_rd_pop_n + 1'b1;
        end
    end

    always @(posedge clk) if (rstn && f_past_valid > 2) begin
        a_cmd_nofab: assert (f_cmd_pop_n <= f_cmd_push_n);
        a_wd_nofab:  assert (f_wd_pop_n  <= f_wd_push_n);
        a_rd_nofab:  assert (f_rd_pop_n  <= f_rd_push_n);
        if (w_cmd_pop) a_cmd_integrity: assert (pcmd_data_o == f_cmd_shadow[f_cmd_pop_n[3:0]]);
        if (w_wd_pop)  a_wd_integrity:  assert (pwd_data_o  == f_wd_shadow[f_wd_pop_n[3:0]]);
        if (w_rd_pop)  a_rd_integrity:  assert (rd_data_o   == f_rd_shadow[f_rd_pop_n[3:0]]);
    end

    // =====================================================================
    // FAMILY 3 -- INIT TOKEN SEMANTICS
    // =====================================================================
    reg f_istart_d, f_icmp_d;
    always @(posedge clk) begin
        if (!rstn) begin f_istart_d <= 1'b0; f_icmp_d <= 1'b0; end
        else begin f_istart_d <= init_start_i; f_icmp_d <= pinit_complete_i; end
    end

    reg f_pinit_start_d, f_init_complete_d;
    always @(posedge clk) begin
        if (!rstn) begin f_pinit_start_d <= 1'b0; f_init_complete_d <= 1'b0; end
        else begin f_pinit_start_d <= pinit_start_o; f_init_complete_d <= init_complete_o; end
    end

    reg [7:0] f_istart_pushes, f_icmp_pushes;
    always @(posedge clk) begin
        // Reset on !rstn ONLY: rstn is released while f_past_valid is still 2,
        // and from that cycle the DUT already stores pushes -- a shadow that
        // stays in reset until f_past_valid > 2 misses them and mismatches
        // forever after (the counter-window trap, this time with the DUT
        // active one cycle before the counters). Assertions stay gated at
        // f_past_valid > 2 below.
        if (!rstn) begin
            f_istart_pushes <= 0; f_icmp_pushes <= 0;
        end else begin
            if (p_w_istart_push) f_istart_pushes <= f_istart_pushes + 1'b1;
            if (p_w_icmp_push)   f_icmp_pushes   <= f_icmp_pushes + 1'b1;
        end
    end

    always @(posedge clk) if (rstn && f_past_valid > 2) begin
        // The probes are the source signals (header: name-resolution audit).
        a_aud_istart: assert (p_w_istart_push == (init_start_i && !f_istart_d));
        a_aud_icmp:   assert (p_w_icmp_push   == (pinit_complete_i && !f_icmp_d));

        // The push is EXACTLY a rising edge: a level held high pushes once,
        // never repeatedly (which would re-run init).
        a_istart_edge: assert (p_w_istart_push == (init_start_i && !f_istart_d));
        a_icmp_edge:   assert (p_w_icmp_push   == (pinit_complete_i && !f_icmp_d));

        // The sticky latches are MONOTONIC: init cannot un-complete.
        if (f_pinit_start_d)   a_pinit_start_sticky: assert (pinit_start_o);
        if (f_init_complete_d) a_init_complete_sticky: assert (init_complete_o);

        // A sticky latch never sets without a token actually pushed.
        if (pinit_start_o && !f_pinit_start_d)
            a_pinit_rise_real: assert (f_istart_pushes != 0);
        if (init_complete_o && !f_init_complete_d)
            a_icomp_rise_real: assert (f_icmp_pushes != 0);

        // The token FIFOs leave wr_ready unconnected in the RTL, so a push
        // into a full FIFO would be a SILENT drop. Proved it never happens.
        a_istart_tok_nodrop: assert (!p_w_istart_push || p_w_istart_tok_ready);
        a_icmp_tok_nodrop:   assert (!p_w_icmp_push   || p_w_icmp_tok_ready);
    end

    // =====================================================================
    // COVER
    // =====================================================================
    always @(posedge clk) if (rstn) begin
        c_burst_staged: cover (pwr_staged_valid_o && pwr_staged_pop_i);
        c_two_bursts:   cover (f_last_beats == 2);
        c_tok_push:     cover (w_tok_fire);
        c_cmd:          cover (w_cmd_push);
        c_cmd_cross:    cover (w_cmd_pop);
        c_wd:           cover (w_wd);
        c_wd_cross:     cover (w_wd_pop);
        c_rd_push:      cover (w_rd_push);
        c_rd:           cover (w_rd_pop);
        c_istart_push:  cover (p_w_istart_push);
        c_istart:       cover (pinit_start_o);
        c_icmp_push:    cover (p_w_icmp_push);
        c_icomplete:    cover (init_complete_o);
    end

endmodule
