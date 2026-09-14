// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_deliv_merge
// Purpose: Multi-IOAPIC routing -- merge N delivery channels onto one
//          (RLB-008).
//
// Documentation: projects/components/retro_legacy_blocks/docs/ioapic_mas/
// Subsystem: retro_legacy_blocks/ioapic
//
// Created: 2026-09-14
//
//==============================================================================
// WHAT THIS IS, AND WHY IT IS NOT INSIDE apb4_ioapic
//==============================================================================
// A system with more than one IOAPIC has more than one delivery channel, and
// they all address the same set of local APICs. Something has to merge them,
// and it must say WHICH IOAPIC a message came from, because the EOI that
// eventually retires it has to reach the IOAPIC holding that pin's Remote IRR.
// That is the whole of "multi-IOAPIC routing" at this level.
//
// It is a COMPANION, exactly like ioapic_lowest_pri_arb, and for the same
// reason. RLB-008 records Sean's 2026-09-11 interface decision: the delivery
// channel stays a payload plus a valid/ready handshake plus a status so that a
// bridge can carry that shape onto a bus. Merging inside the block would mean
// apb4_ioapic growing N-1 sibling channels on its port list, which is the one
// thing that decision rules out. So apb4_ioapic.f does not reference this
// file, nothing instantiates it by default, and adding it changes no existing
// configuration.
//
// Unlike ioapic_lowest_pri_arb this module DOES take clk/rst_n, and the
// asymmetry is deliberate: arbitration across a multi-cycle handshake is
// sequential. The sibling is combinational and its clock ports were removed
// because they were decoration; here they carry the arbiter's state.
//
//==============================================================================
// BEHAVIOUR
//==============================================================================
// Round robin over the requesting sources, in ACK mode, so a grant is HELD for
// the whole delivery handshake rather than rotating underneath it. Fairness is
// the arbiter's: each continuously requesting source is served within NUM_SRC
// transactions, so a busy IOAPIC cannot starve a quiet one.
//
// The granted source owns the merged channel until its handshake completes:
//   m_valid     follows grant_valid (request == src_valid, so a grant implies
//               a pending message).
//   the payload is the granted source's, muxed by grant_id.
//   m_src_id    is that grant_id -- the routing information the merge exists
//               to add.
//   src_ready   is asserted to the granted source only.
//   src_retry   is asserted to the granted source only, and only on a
//               completing handshake, preserving ioapic_core's contract that
//               retry is qualified by the handshake and means "taken, and
//               nobody could accept". Broadcasting it would make every other
//               IOAPIC replay an interrupt that was never theirs.
//
// EOI IS DELIBERATELY ABSENT. An EOI needs no arbitration: it is a broadcast
// that every IOAPIC matches against its own Remote IRR by vector. Routing it
// through here would be pure pass-through, and a port that only passes a
// signal along is not an interface -- the same judgement that removed
// ioapic_lowest_pri_arb's clk/rst_n. Wire eoi_in/eoi_vector to all IOAPICs
// directly.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module ioapic_deliv_merge #(
    parameter int NUM_SRC = 2,         // Number of IOAPIC delivery channels
    // Derived, do not override. It sizes a PORT, so it has to live in the
    // parameter list: a localparam in the module body is declared after the
    // port list and cannot size one. arbiter_round_robin derives its N the
    // same way for the same reason.
    parameter int SRC_IDX_W = (NUM_SRC > 1) ? $clog2(NUM_SRC) : 1
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // Source delivery channels, one per IOAPIC (from each irq_out_*)
    input  logic [NUM_SRC-1:0]      src_valid,
    input  logic [7:0]              src_vector     [NUM_SRC],
    input  logic [7:0]              src_dest       [NUM_SRC],
    input  logic [NUM_SRC-1:0]      src_dest_mode,
    input  logic [2:0]              src_deliv_mode [NUM_SRC],
    output logic [NUM_SRC-1:0]      src_ready,
    output logic [NUM_SRC-1:0]      src_retry,

    // Merged delivery channel, to the LAPIC cluster (or to
    // ioapic_lowest_pri_arb, which consumes exactly this shape)
    output logic                    m_valid,
    output logic [7:0]              m_vector,
    output logic [7:0]              m_dest,
    output logic                    m_dest_mode,
    output logic [2:0]              m_deliv_mode,
    output logic [SRC_IDX_W-1:0]    m_src_id,
    input  logic                    m_ready,
    input  logic                    m_retry
);

    logic [NUM_SRC-1:0]     w_grant;
    logic [NUM_SRC-1:0]     w_grant_ack;
    logic [SRC_IDX_W-1:0]   w_grant_id;
    logic                   w_grant_valid;

    // ------------------------------------------------------------------
    // Grant acknowledge
    // ------------------------------------------------------------------
    // The ready term is load-bearing. rtl/amba/monitor/monbus_arbiter.sv
    // records what happens without it: `grant && valid` alone acks every
    // cycle while the sink backpressures, so the grant rotates continuously
    // with ZERO transfers, which breaks the arbiter's grant-hold contract and
    // makes fairness depend on the phase of m_ready. That bug has its own
    // regression (val/amba/test_monbus_arbiter_grant_hold.py). The ack must be
    // the transfer actually completing.
    always_comb begin
        for (int i = 0; i < NUM_SRC; i++) begin
            w_grant_ack[i] = w_grant[i] && src_valid[i] && m_ready;
        end
    end

    arbiter_round_robin #(
        .CLIENTS      (NUM_SRC),
        .WAIT_GNT_ACK (1)            // hold the grant across the handshake
    ) u_arb (
        .clk          (clk),
        .rst_n        (rst_n),
        .block_arb    (1'b0),
        .request      (src_valid),
        .grant_ack    (w_grant_ack),
        .grant_valid  (w_grant_valid),
        .grant        (w_grant),
        .grant_id     (w_grant_id),
        // last_grant is the arbiter's debug output and nothing here reads it.
        // An earlier draft wired it to a signal purely because the port
        // exists, which verilator -Wall correctly called out -- the same
        // judgement that removed ioapic_lowest_pri_arb's clk/rst_n. The
        // waiver is inline, at the site, so the empty pin and the reason for
        // it are read together (rtl/amba/axis4/axis4_master.sv does the same).
        /* verilator lint_off PINCONNECTEMPTY */
        .last_grant   ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ------------------------------------------------------------------
    // Merged channel: the granted source's message, plus its id
    // ------------------------------------------------------------------
    assign m_valid      = w_grant_valid;
    assign m_vector     = src_vector[w_grant_id];
    assign m_dest       = src_dest[w_grant_id];
    assign m_dest_mode  = src_dest_mode[w_grant_id];
    assign m_deliv_mode = src_deliv_mode[w_grant_id];
    assign m_src_id     = w_grant_id;

    // ------------------------------------------------------------------
    // Back to the sources: granted one only
    // ------------------------------------------------------------------
    always_comb begin
        for (int i = 0; i < NUM_SRC; i++) begin
            src_ready[i] = w_grant[i] && m_ready;
            // Qualified by the handshake, exactly as ioapic_core qualifies
            // irq_out_retry. Only the source whose message was just consumed
            // is told the delivery was refused.
            src_retry[i] = w_grant[i] && m_ready && m_retry;
        end
    end

    // ------------------------------------------------------------------
    // Elaboration-time parameter check
    // ------------------------------------------------------------------
    // An elaboration-time $error, not an assertion: [[no-assertions-in-rtl]]
    // keeps assert/assume/cover out of synthesizable modules entirely, and
    // this is the one sanctioned form.
`ifndef SYNTHESIS
    initial begin : param_check
        if (NUM_SRC < 2)
            $error("ioapic_deliv_merge: NUM_SRC must be >= 2 (got %0d); a single IOAPIC needs no merge", NUM_SRC);
        if (NUM_SRC > 16)
            $error("ioapic_deliv_merge: NUM_SRC must be <= 16 (got %0d)", NUM_SRC);
    end
`endif

endmodule : ioapic_deliv_merge
