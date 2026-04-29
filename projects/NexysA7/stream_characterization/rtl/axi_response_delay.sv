// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_response_delay
// Purpose: Per-burst response delay for an AXI valid/ready channel
//
// Description:
//   Models real memory-style latency on an AXI response channel: when a
//   new burst begins (rising edge of s_valid after an idle gap), stall
//   the handshake for i_delay_cycles cycles. After that delay expires,
//   every beat of the burst flows through combinationally at full rate.
//
//   This matches the behavior the DMA engine + SRAM/FIFO sizing was
//   designed to absorb (round-trip latency to first response data, then
//   line-rate streaming for the rest of the burst). The previous
//   implementation held *every* beat for N cycles, which corresponds to
//   a memory whose throughput is rate-limited per beat — not realistic,
//   and not absorbable by any FIFO depth.
//
// Behavior:
//   - i_delay_cycles == 0: pure combinational pass-through.
//   - i_delay_cycles >  0: when s_valid rises (or each time s_valid is
//                          re-asserted after a gap), hold the handshake
//                          for N cycles, then pass beats through with
//                          zero added latency until s_valid drops again.
//
// Notes:
//   - Burst boundary detection relies on s_valid going low for at least
//     one cycle between bursts. The slaves we use (axi4_slave_rd /
//     axi4_slave_wr_crc_check) cycle through IDLE between bursts so this
//     is satisfied. If a slave streams two bursts back-to-back without
//     dropping valid, only the first will be delayed.
//   - During the delay window the slave holds its current beat on its
//     output (s_ready==0 back-pressures it). No internal data buffer is
//     needed — beats are forwarded combinationally once the delay
//     expires.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_response_delay #(
    parameter int DATA_WIDTH = 64,
    parameter int DELAY_W    = 16
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // Per-burst hold time. 0 = pure pass-through.
    input  logic [DELAY_W-1:0]      i_delay_cycles,

    // Slave-facing input (from response-producing model)
    input  logic [DATA_WIDTH-1:0]   s_data,
    input  logic                    s_valid,
    output logic                    s_ready,

    // Master-facing output (to response-consuming master)
    output logic [DATA_WIDTH-1:0]   m_data,
    output logic                    m_valid,
    input  logic                    m_ready
);

    // Cycles still to wait before this burst's first beat is allowed
    // through. Re-armed to i_delay_cycles whenever s_valid is low (i.e.
    // between bursts, or before the very first burst).
    logic [DELAY_W-1:0] r_remaining;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_remaining <= '0;
        end else begin
            if (!s_valid) begin
                // Idle: arm the delay counter for the next burst start.
                // (Tracking the runtime knob here means changing
                // i_delay_cycles between bursts takes effect on the
                // next burst, not mid-burst.)
                r_remaining <= i_delay_cycles;
            end else if (r_remaining != '0) begin
                // In the delay window — count down each cycle s_valid
                // is held high (the slave is waiting for s_ready).
                r_remaining <= r_remaining - 1'b1;
            end
            // r_remaining stays at 0 once the delay has expired; beats
            // flow through at line rate until s_valid drops again, at
            // which point the !s_valid branch above re-arms the counter.
        end
    )

    // Pass-through is enabled once the delay has expired. While
    // r_remaining > 0, m_valid is held low (master sees no beat) and
    // s_ready is held low (slave keeps the beat parked on its output).
    wire w_pass = (r_remaining == '0);

    assign m_valid = s_valid && w_pass;
    assign s_ready = m_ready && w_pass;
    assign m_data  = s_data;

endmodule : axi_response_delay
