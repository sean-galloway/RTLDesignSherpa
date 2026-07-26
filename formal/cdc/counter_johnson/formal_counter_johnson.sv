// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for counter_johnson (yosys-compatible)
// Proves Johnson code single-bit change, reset, hold, and cycle length.

module formal_counter_johnson #(
    parameter int WIDTH = 4
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable
);

    // DUT outputs
    logic [WIDTH-1:0] counter_gray;

    // Instantiate DUT
    counter_johnson #(.WIDTH(WIDTH)) dut (
        .clk          (clk),
        .rst_n        (rst_n),
        .enable       (enable),
        .counter_gray (counter_gray)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, counter_gray is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset: assert (counter_gray == '0);
    end

    // Johnson property: at most 1 bit changes per enabled step
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(enable))
            ap_single_bit: assert ($countones(counter_gray ^ $past(counter_gray)) <= 1);
    end

    // Hold when disabled: counter_gray unchanged
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && !$past(enable))
            ap_hold: assert (counter_gray == $past(counter_gray));
    end

    // Shift property: when enabled, new value is {old[WIDTH-2:0], ~old[WIDTH-1]}
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(enable))
            ap_shift: assert (
                counter_gray == {$past(counter_gray[WIDTH-2:0]), ~$past(counter_gray[WIDTH-1])}
            );
    end

    // =========================================================================
    // Cycle tracking for Johnson sequence length = 2*WIDTH
    // =========================================================================
    reg [$clog2(2*WIDTH+1)-1:0] f_step_count = 0;

    always @(posedge clk) begin
        if (!rst_n)
            f_step_count <= 0;
        else if (enable) begin
            if (f_step_count == 2*WIDTH - 1)
                f_step_count <= 0;
            else
                f_step_count <= f_step_count + 1;
        end
    end

    // After exactly 2*WIDTH enabled steps from reset, counter returns to 0
    always @(posedge clk) begin
        if (f_past_valid > 2 && rst_n && $past(rst_n) && $past(enable) && f_step_count == 0)
            ap_cycle_len: assert (counter_gray == '0);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Reach the all-ones pattern (midpoint of Johnson sequence)
    always @(posedge clk) begin
        if (rst_n)
            cp_all_ones: cover (counter_gray == {WIDTH{1'b1}});
    end

    // Full cycle: return to zero after non-zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_wrap: cover (counter_gray == '0 && $past(counter_gray) != '0);
    end

    // MSB transitions
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_msb_rise: cover (counter_gray[WIDTH-1] && !$past(counter_gray[WIDTH-1]));
    end

endmodule
