// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: char_gen_axi_mux
// Purpose: N:1 grant-hold round-robin mux for a single AXI4 address channel
//
// Documentation: ddr2_char_framework/rtl/char_gen_unit.sv (sole consumer)
//==============================================================================
// Description:
//   One AXI4 address channel (AW or AR), N requesters, one output. The payload
//   is opaque: char_gen_unit packs the channel's fields into PAYLOAD_WIDTH bits
//   and unpacks them on the far side, so this module carries no AXI field
//   knowledge and is identical for both directions.
//
//   Why a bespoke arbiter instead of rtl/common/arbiter_round_robin:
//     That arbiter registers its grant, and in WAIT_GNT_ACK mode a single
//     continuously-requesting client gets a mandatory dead cycle after every
//     ack -- one address per two clocks. On a characterization engine whose
//     entire job is to saturate the controller, an arbiter that halves the
//     address rate puts the measurement bottleneck inside the measuring
//     instrument. At AxLEN=1 (the outstanding-vs-latency sweep) that alone
//     would cap the read path at 50% of peak and the "cliff" being looked for
//     would be the harness, not the DRAM.
//
//     So the pick here is combinational -- request to m_valid in zero cycles,
//     full rate with one requester or N -- and the only state is the lock that
//     AXI requires: once VALID is asserted the payload may not change until
//     READY, so the winner is latched for the duration of a stalled handshake
//     and released on completion.
//
//   Fairness: the pointer advances past the winner on every completed
//   handshake, so N saturated requesters interleave one-for-one. There is no
//   weighting and no QoS; the generators are meant to contend evenly and any
//   asymmetry in the result should come from the DRAM, not from here.
//==============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module char_gen_axi_mux #(
    parameter int N             = 2,
    parameter int PAYLOAD_WIDTH = 32,
    // Aliases
    parameter int SELW = (N > 1) ? $clog2(N) : 1
) (
    input  logic clk,
    input  logic rst_n,

    //---- Requester side --------------------------------------------------
    input  logic [N-1:0]              s_valid,
    output logic [N-1:0]              s_ready,
    input  logic [PAYLOAD_WIDTH-1:0]  s_payload [N],

    //---- Merged side -----------------------------------------------------
    output logic                      m_valid,
    input  logic                      m_ready,
    output logic [PAYLOAD_WIDTH-1:0]  m_payload,
    // Index of the requester currently presented on m_payload. Valid only
    // while m_valid; char_gen_unit uses it both to prefix the outgoing ID and
    // to record W ordering, and both of those sample it on the handshake.
    output logic [SELW-1:0]           m_sel,

    //---- Flow control ----------------------------------------------------
    // Held high by the consumer to stop new grants (the write path uses it to
    // stall AW when the W-order queue is full). Asserting it does not break an
    // in-progress handshake: a locked grant stays locked until its READY.
    input  logic                      block
);

    generate
    if (N == 1) begin : g_passthru
        //---------------------------------------------------------------
        // One requester: no arbitration to do, and no lock needed because
        // nothing can steal the channel mid-handshake.
        //---------------------------------------------------------------
        assign m_valid    = s_valid[0] && !block;
        assign s_ready[0] = m_ready && !block;
        assign m_payload  = s_payload[0];
        assign m_sel      = '0;

    end else begin : g_arb

        //---------------------------------------------------------------
        // Round-robin pick
        //---------------------------------------------------------------
        // r_ptr names the client that gets first refusal this cycle. The pick
        // is "lowest set bit at or above r_ptr, else lowest set bit overall",
        // which is the textbook rotate-and-priority-encode written without the
        // rotate: masking is cheaper than two barrel shifters and N is small.
        logic [SELW-1:0]  r_ptr;
        logic [N-1:0]     w_mask;       // clients at or above r_ptr
        logic [N-1:0]     w_hi, w_lo;   // lowest-set-bit of each half
        logic [N-1:0]     w_pick;       // one-hot combinational winner

        // Lock: the grant that a stalled handshake is holding.
        logic [N-1:0]     r_lock;
        logic             r_locked;

        logic [N-1:0]     w_gnt;
        logic [SELW-1:0]  w_sel;
        logic             w_hs;

        always_comb begin
            w_mask = '0;
            for (int i = 0; i < N; i++) begin
                w_mask[i] = (SELW'(i) >= r_ptr);
            end
        end

        // Isolate the lowest set bit: x & (-x).
        assign w_hi = (s_valid & w_mask) & (~(s_valid & w_mask) + N'(1));
        assign w_lo = s_valid & (~s_valid + N'(1));
        assign w_pick = (|(s_valid & w_mask)) ? w_hi : w_lo;

        // A locked grant outranks a fresh pick; `block` only gates fresh ones.
        assign w_gnt = r_locked ? r_lock : (block ? '0 : w_pick);

        always_comb begin
            w_sel = '0;
            for (int i = 0; i < N; i++) begin
                if (w_gnt[i]) w_sel = SELW'(i);
            end
        end

        assign m_valid   = |(w_gnt & s_valid);
        assign m_payload = s_payload[w_sel];
        assign m_sel     = w_sel;
        assign s_ready   = w_gnt & {N{m_ready}};
        assign w_hs      = m_valid && m_ready;

        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                r_ptr    <= '0;
                r_lock   <= '0;
                r_locked <= 1'b0;
            end else begin
                if (w_hs) begin
                    // Completed: release the lock and step past the winner.
                    r_locked <= 1'b0;
                    r_lock   <= '0;
                    r_ptr    <= (w_sel == SELW'(N-1)) ? '0 : (w_sel + SELW'(1));
                end else if (m_valid) begin
                    // VALID asserted and not taken: AXI forbids changing the
                    // payload now, so freeze this winner until its READY.
                    r_locked <= 1'b1;
                    r_lock   <= w_gnt;
                end else if (r_locked) begin
                    // Locked, but the winner dropped VALID before READY. That
                    // is an AXI violation upstream, not something that can
                    // happen with the pattern generators -- but holding the
                    // lock on a master that has gone quiet wedges every OTHER
                    // generator with no error anywhere, which is the worst way
                    // for a harness to fail. Release instead, and do not
                    // advance the pointer: nothing was served.
                    r_locked <= 1'b0;
                    r_lock   <= '0;
                end
            end
        )
    end
    endgenerate

endmodule : char_gen_axi_mux
