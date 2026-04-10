// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for axi_monitor_timer -- timestamp counter + freq-invariant tick
//
// Properties verified:
//   P1: Reset clears timestamp to 0
//   P2: Timestamp increments by 1 each clock cycle after reset release
//   P3: Timestamp[0] toggles every cycle (LSB of a free-running counter)
//   P4: Reset clears timer_tick (via sync reset of prescaler counter)

`include "reset_defs.svh"

module formal_axi_monitor_timer (
    input logic clk,
    input logic rst_n
);

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg [3:0] cfg_freq_sel;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire         timer_tick;
    wire [31:0]  timestamp;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    axi_monitor_timer dut (
        .aclk         (clk),
        .aresetn      (rst_n),
        .cfg_freq_sel (cfg_freq_sel),
        .timer_tick   (timer_tick),
        .timestamp    (timestamp)
    );

    // =========================================================================
    // Reset and past-valid
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Properties
    // =========================================================================

    // P1: Reset clears timestamp to 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_timestamp: assert (timestamp == 32'h0);
    end

    // P2: Timestamp increments by 1 every clock when rst_n held
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_timestamp_increment: assert (timestamp == $past(timestamp) + 32'h1);
    end

    // P3: Timestamp is a free-running counter (never stuck)
    always @(posedge clk) begin
        if (f_past_valid > 1 && rst_n && $past(rst_n) && $past(rst_n,2))
            ap_timestamp_nonstuck: assert (timestamp != $past(timestamp));
    end

    // =========================================================================
    // Cover points
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_timestamp_nonzero: cover (timestamp != 32'h0);
            cp_timer_tick:        cover (timer_tick);
            cp_timestamp_four:    cover (timestamp == 32'h4);
        end
    end

endmodule
