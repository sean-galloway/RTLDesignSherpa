// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for debounce (yosys-compatible)
// Instantiates DUT and properties together.
// Properties use only port-level signals (no hierarchical internal access).
// Run with: sby debounce.sby
//
// Debounce timing:
//   Shift registers update on long_tick (registered).
//   w_debounced_signals = &shift_reg (combinational).
//   button_out <= w_debounced_signals every cycle (registered).
//   So button_out reflects shift_reg state from the SAME cycle
//   (shift_reg updates, combinational decodes, output reg captures on next edge).

module formal_debounce #(
    parameter int N              = 2,
    parameter int DEBOUNCE_DELAY = 3,
    parameter bit PRESSED_STATE  = 1
) (
    input logic         clk,
    input logic         rst_n,
    input logic         long_tick,
    input logic [N-1:0] button_in
);

    // DUT outputs
    logic [N-1:0] button_out;

    // Instantiate DUT
    debounce #(
        .N             (N),
        .DEBOUNCE_DELAY(DEBOUNCE_DELAY),
        .PRESSED_STATE (PRESSED_STATE)
    ) dut (
        .clk       (clk),
        .rst_n     (rst_n),
        .long_tick (long_tick),
        .button_in (button_in),
        .button_out(button_out)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Assumptions: start in reset, hold for at least 3 cycles
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid < 3) assume (!rst_n);
        if (f_past_valid >= 3) assume (rst_n);
    end

    // Keep long_tick off during reset so shift registers are cleanly zeroed
    always @(posedge clk) begin
        if (!rst_n) assume (!long_tick);
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, output is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_output: assert (button_out == '0);
    end

    // Output stability: if no long_tick for TWO consecutive cycles and
    // system is well out of reset, output cannot change.
    // (Shift reg unchanged for 2 cycles means w_debounced is stable,
    //  so the registered output stabilizes on the second cycle.)
    always @(posedge clk) begin
        if (f_past_valid >= 5 && rst_n && $past(rst_n) && $past(rst_n, 2)) begin
            if (!$past(long_tick) && !$past(long_tick, 2))
                ap_stable_no_ticks: assert (button_out == $past(button_out));
        end
    end

    // =========================================================================
    // Constrained scenario: channel 0 held pressed for DEBOUNCE_DELAY ticks
    // =========================================================================
    // Track how many consecutive tick cycles channel 0 input matched pressed
    reg [7:0] f_consec_pressed;
    reg [7:0] f_consec_released;
    reg [7:0] f_tick_count;

    always @(posedge clk) begin
        if (!rst_n) begin
            f_consec_pressed  <= 0;
            f_consec_released <= 0;
            f_tick_count      <= 0;
        end else if (long_tick) begin
            f_tick_count <= f_tick_count + (f_tick_count < 8'hFF ? 1 : 0);
            if ((PRESSED_STATE && button_in[0]) || (!PRESSED_STATE && !button_in[0])) begin
                f_consec_pressed  <= f_consec_pressed + (f_consec_pressed < 8'hFF ? 1 : 0);
                f_consec_released <= 0;
            end else begin
                f_consec_pressed  <= 0;
                f_consec_released <= f_consec_released + (f_consec_released < 8'hFF ? 1 : 0);
            end
        end
    end

    // After enough tick cycles with button not pressed, output must be 0.
    // Use $past because button_out registers w_debounced one cycle after
    // the shift register updates. So we check that the counter was already
    // at DEBOUNCE_DELAY on the PREVIOUS cycle (meaning shift_reg was full
    // at previous posedge, combinational decode was done, registered output
    // captures it on this posedge).
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= 6 && $past(rst_n)
            && $past(f_consec_released) >= DEBOUNCE_DELAY)
            ap_released_output_low: assert (button_out[0] == 1'b0);
    end

    // After enough tick cycles with button pressed, output must be 1.
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= 6 && $past(rst_n)
            && $past(f_consec_pressed) >= DEBOUNCE_DELAY)
            ap_pressed_output_high: assert (button_out[0] == 1'b1);
    end

    // If fewer than DEBOUNCE_DELAY total ticks have occurred on the
    // previous cycle, output stays 0 (not enough samples yet).
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= 6 && $past(rst_n)
            && $past(f_tick_count) < DEBOUNCE_DELAY)
            ap_insufficient_ticks: assert (button_out[0] == 1'b0);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: button press detected (output goes high for channel 0)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_button_press: cover (button_out[0] && !$past(button_out[0]));
    end

    // Cover: button release detected (output goes low for channel 0)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_button_release: cover (!button_out[0] && $past(button_out[0]));
    end

    // Cover: long_tick active
    always @(posedge clk) begin
        if (rst_n)
            cp_long_tick: cover (long_tick);
    end

    // Cover: multiple channels pressed simultaneously
    always @(posedge clk) begin
        if (rst_n)
            cp_multi_channel: cover (button_out == {N{1'b1}});
    end

endmodule
