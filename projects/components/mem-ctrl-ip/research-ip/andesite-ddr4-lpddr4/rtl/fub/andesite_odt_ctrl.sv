// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_odt_ctrl
// Purpose: DDR4 per-rank ODT pin policy from the scheduler grant tap
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// New block (no carry) per andesite_mas ch02_blocks/08_odt_ctrl.md: a tap,
// not an arbiter -- it watches the grant stream, decodes the per-rank
// policy state, and drives the ODT pins after the ODTL-family latencies.
// ODT transitions never stall commands (HAS Ch 3.5 requirement 3).
//
// LPDDR4 scope (MAS page): termination there is MR-programmed at init
// time, so this block is DDR4-scoped; nothing here claims LPDDR4 pins.
//
// Author: sean galloway
// Created: 2026-10-04 (andesite, NEW)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_odt_ctrl
    import andesite_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int RKW       = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1
)(
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    // ----- init seam: init_sequencer owns the pin until init_done -----
    input  logic                 init_done_i,
    input  logic [NUM_RANKS-1:0] init_odt_i,

    // ----- scheduler grant tap (the only input the policy needs) -----
    input  logic                 grant_valid_i,
    input  dram_op_e             grant_op_i,
    input  logic [RKW-1:0]       grant_rank_i,

    // ----- ODTL-family latencies, runtime CSRs (JESD79-4 speed bin) -----
    input  logic [7:0]           odtlon_i,     // command -> ODT active
    input  logic [7:0]           odtloff_i,    // burst -> ODT inactive
    input  logic [7:0]           odt_turn_i,   // write-to-read ODT turnaround
    input  logic [7:0]           tadc_i,       // command-to-ODT-change

    // ----- MR images (the RTT VALUES are init-side; carried here as the
    //       observability/derivation contract, never driven per state) -----
    input  logic [2:0]           rtt_nom_img_i,
    input  logic [2:0]           rtt_wr_img_i,
    input  logic [2:0]           rtt_park_img_i,

    // ----- per-rank ODT pin and telemetry -----
    output logic [NUM_RANKS-1:0] odt_pin_o,
    output logic [NUM_RANKS*2-1:0] hist_state_o,
    output logic [NUM_RANKS*8-1:0] trans_count_o
);

    // Policy states per the MAS 08 fence (2-bit telemetry encoding):
    //   PARK     -- no rank selected (RTT_PARK); pin asserted
    //   RD_NOM   -- a read granted to any rank: this rank presents RTT_NOM
    //   RD_SELF  -- a read granted to THIS rank: its ODT goes off
    //   WR       -- a write granted to THIS rank: RTT_WR
    typedef enum logic [1:0] {
        ST_PARK    = 2'd0,
        ST_RD_NOM  = 2'd1,
        ST_RD_SELF = 2'd2,
        ST_WR      = 2'd3
    } odt_state_e;

    function automatic logic pin_of(input odt_state_e s);
        // ODT asserted for every state except RD_SELF. Which Rtt the DRAM
        // presents is its own MR business; the pin only says on/off.
        return (s != ST_RD_SELF);
    endfunction

    odt_state_e              r_state [NUM_RANKS];
    logic [NUM_RANKS-1:0]    r_pin;
    logic [7:0]              r_cnt   [NUM_RANKS];
    logic [7:0]              r_trans [NUM_RANKS];
    logic                    r_owned;   // init seam: ownership transferred

    // Next-state decode for one rank from the grant tap.
    function automatic odt_state_e decode(
        input odt_state_e cur,
        input int         rank,
        input logic       tap_valid,
        input dram_op_e   tap_op,
        input int         tap_rank
    );
        odt_state_e ns = cur;
        if (tap_valid) begin
            if ((tap_op == OP_RD) || (tap_op == OP_RDA)) begin
                ns = (rank == tap_rank) ? ST_RD_SELF : ST_RD_NOM;
            end else if ((tap_op == OP_WR) || (tap_op == OP_WRA)) begin
                ns = (rank == tap_rank) ? ST_WR : ST_PARK;
            end
        end
        return ns;
    endfunction

    // Latency for a transition: assertion via ODTLon, the read-self release
    // via ODTLoff, the write-to-read picture change via the turnaround,
    // everything else via tADC.
    function automatic logic [7:0] latency_of(
        input odt_state_e cur, input odt_state_e ns
    );
        if (ns == ST_WR)                  return odtlon_i;
        else if (ns == ST_RD_SELF)        return (cur == ST_WR) ? odt_turn_i : odtloff_i;
        else                              return tadc_i;
    endfunction

    for (genvar g = 0; g < NUM_RANKS; g++) begin : g_rank
        `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
            if (`RST_ASSERTED(mc_rst_n)) begin
                r_state[g] <= ST_PARK;
                r_pin[g]   <= 1'b0;
                r_cnt[g]   <= 8'd0;
                r_trans[g] <= 8'd0;
            end else if (!r_owned) begin
                // Init seam: policy parked at PARK; the pin itself belongs
                // to init_sequencer until init_done (output mux below).
                // init_odt_i is sampled as the starting pin value, and the
                // handoff schedules the settle into the park policy after
                // tADC -- a named, bounded seam, not a glitch.
                r_state[g] <= ST_PARK;
                r_pin[g]   <= init_odt_i[g];
                r_cnt[g]   <= tadc_i;
                r_trans[g] <= 8'd0;
            end else begin
                automatic odt_state_e ns = decode(r_state[g], g,
                                                  grant_valid_i, grant_op_i,
                                                  int'(grant_rank_i));
                if (ns != r_state[g]) begin
                    r_state[g] <= ns;
                    r_cnt[g]   <= latency_of(r_state[g], ns);
                    if (r_trans[g] != 8'hFF) begin
                        r_trans[g] <= r_trans[g] + 8'd1;
                    end
                end else if (r_cnt[g] != 8'd0) begin
                    r_cnt[g] <= r_cnt[g] - 8'd1;
                end else begin
                    // Countdown done: the pin settles to the policy state.
                    r_pin[g] <= pin_of(r_state[g]);
                end
            end
        end)

        assign hist_state_o[g*2 +: 2]   = r_state[g];
        assign trans_count_o[g*8 +: 8]  = r_trans[g];
    end

    // Ownership and the seam mux. The pin is a passthrough while init owns
    // it; afterwards it is the registered policy pin -- Q of a flop either
    // way, per the family convention.
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_owned <= 1'b0;
        end else if (init_done_i) begin
            r_owned <= 1'b1;
        end
    end)

    assign odt_pin_o = r_owned ? r_pin : init_odt_i;

endmodule : andesite_odt_ctrl
