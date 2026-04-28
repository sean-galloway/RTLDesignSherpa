// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_response_delay
// Purpose: Configurable per-beat response delay for an AXI valid/ready channel
//
// Description:
//   Generic single-beat delay pipe that sits in the response path between an
//   AXI slave model and the AXI master that consumes it (e.g. between
//   axi4_slave_rd_pattern_gen.s_axi_r* and STREAM's m_axi_rd_r*, or between
//   axi4_slave_wr_crc_check.s_axi_b* and STREAM's m_axi_wr_b*).
//
//   The block is purely a valid/ready/data pipe — it does not understand AXI
//   semantics. Pack the channel signals (rid/rdata/rresp/rlast/ruser, or
//   bid/bresp/buser) into the DATA_WIDTH input and unpack them on the output.
//
// Behavior:
//   - i_delay_cycles == 0: pure combinational pass-through. m_valid/m_data
//                          come directly from s_valid/s_data; s_ready follows
//                          m_ready. Zero added latency, zero throughput hit.
//                          A beat that was held when delay went to zero
//                          drains first.
//   - i_delay_cycles >  0: each accepted beat is parked in a one-deep
//                          register and held for i_delay_cycles cycles before
//                          being released to the consumer. Effective max
//                          throughput becomes 1 beat / (i_delay_cycles + 1)
//                          cycles, which is exactly the knob we want for
//                          long-term-bandwidth experiments.
//
// Parameters:
//   - DATA_WIDTH : Width of the packed channel payload.
//   - DELAY_W    : Bit-width of the i_delay_cycles input (max delay value
//                  that can be programmed at runtime is 2**DELAY_W - 1).
//
// Notes:
//   - For bursts, the delay is applied per beat — the slave can only push
//     a new beat once the previous beat has been released. This matches the
//     "memory-latency model" intent rather than a one-shot per-burst delay.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_response_delay #(
    parameter int DATA_WIDTH = 64,
    parameter int DELAY_W    = 16
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // Runtime delay knob (cycles). 0 = pure pass-through (bypass);
    // any non-zero value injects N cycles of per-beat hold time.
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

    logic [DATA_WIDTH-1:0] r_buf_data;
    logic                  r_buf_valid;
    logic [DELAY_W-1:0]    r_counter;       // Counts down from i_delay_cycles to 0
    logic                  w_delay_active;  // Runtime knob says "delay this beat"
    logic                  w_held_ready;    // Held beat is past its delay window

    assign w_delay_active = (i_delay_cycles != '0);

    // A beat is ready to leave the buffer when its counter has expired, OR
    // when the runtime knob is currently zero (so a leftover beat captured
    // during a previous delay period drains immediately).
    assign w_held_ready = r_buf_valid && (!w_delay_active || (r_counter == '0));

    // Output muxing:
    //   - If a beat is held in the buffer, it must drain via the master port
    //     (regardless of the current runtime knob) before any pass-through
    //     can resume.
    //   - Otherwise (buffer empty), bypass mode is a clean combinational
    //     pass-through; delay mode just gates m_valid until something is
    //     captured and counted down.
    assign m_valid = r_buf_valid ? w_held_ready
                                 : (!w_delay_active && s_valid);
    assign m_data  = r_buf_valid ? r_buf_data : s_data;

    // Slave-side ready:
    //   - Buffer empty in delay mode: accept a new beat (it will be captured).
    //   - Buffer empty in bypass mode: pass m_ready straight through.
    //   - Buffer full: hold the slave off until the held beat drains.
    assign s_ready = r_buf_valid ? 1'b0
                                 : (w_delay_active ? 1'b1 : m_ready);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_buf_data  <= '0;
            r_buf_valid <= 1'b0;
            r_counter   <= '0;
        end else begin
            // Capture: in delay mode, snap a beat from the slave into the
            // held register and start its delay counter.
            if (w_delay_active && s_valid && s_ready) begin
                r_buf_data  <= s_data;
                r_buf_valid <= 1'b1;
                r_counter   <= i_delay_cycles;
            end
            // Tick the delay counter while a beat is being held.
            else if (r_buf_valid && r_counter != '0 && w_delay_active) begin
                r_counter <= r_counter - 1'b1;
            end

            // Release: master accepts the held beat.
            if (r_buf_valid && w_held_ready && m_ready) begin
                r_buf_valid <= 1'b0;
                r_counter   <= '0;
            end
        end
    )

endmodule : axi_response_delay
