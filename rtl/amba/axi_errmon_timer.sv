`timescale 1ns / 1ps
/**
 * AXI Interrupt Bus Frequency Invariant Timer
 *
 * This module provides a configurable timer for timeout detection in the
 * AXI Error Monitor. It uses the counter_freq_invariant module to generate
 * timing ticks based on the frequency selection provided, allowing the
 * timeout thresholds to remain consistent across different clock frequencies.
 */
module axi_errmon_timer (
    // Global Clock and Reset
    input  logic        aclk,
    input  logic        aresetn,

    // Timer configuration
    input  logic [3:0]  i_cfg_freq_sel,    // Frequency selection

    // Timer outputs
    output logic        o_timer_tick,      // Timer tick signal
    output logic [31:0] o_timestamp        // Global timestamp counter
);

    // Counter for timestamp generation
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            o_timestamp <= '0;
        end else begin
            // Increment timestamp counter every clock cycle
            o_timestamp <= o_timestamp + 1'b1;
        end
    end

    // Use counter_freq_invariant for generating timer ticks
    counter_freq_invariant #(
        .COUNTER_WIDTH(1),        // Only need 1-bit counter
        .PRESCALER_MAX(65536)     // Maximum prescaler value
    ) timer_counter (
        .i_clk(aclk),
        .i_rst_n(aresetn),
        .i_sync_reset_n(1'b1),    // No synchronous reset needed
        .i_freq_sel(i_cfg_freq_sel),
        .o_counter(),             // Not used
        .o_tick(o_timer_tick)     // This is the tick signal we need
    );

endmodule : axi_errmon_timer
