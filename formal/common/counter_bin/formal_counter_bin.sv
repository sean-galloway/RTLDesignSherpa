// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for counter_bin (yosys-compatible)
// Instantiates DUT and properties together.
// Run with: sby counter_bin.sby

module formal_counter_bin #(
    parameter int WIDTH = 4,
    parameter int MAX = 6
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable
);

    // DUT outputs
    logic [WIDTH-1:0] counter_bin_curr;
    logic [WIDTH-1:0] counter_bin_next;

    // Instantiate DUT
    counter_bin #(
        .WIDTH(WIDTH),
        .MAX(MAX)
    ) dut (
        .clk              (clk),
        .rst_n            (rst_n),
        .enable           (enable),
        .counter_bin_curr (counter_bin_curr),
        .counter_bin_next (counter_bin_next)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Assumptions: start in reset, release after 2 cycles
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, counter is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_value: assert (counter_bin_curr == '0);
    end

    // Normal increment
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(enable) && $past(counter_bin_curr[WIDTH-2:0]) != (WIDTH-1)'(MAX - 1))
                ap_increment: assert (counter_bin_curr == $past(counter_bin_curr) + 1);
        end
    end

    // Wraparound: MSB flips
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(enable) && $past(counter_bin_curr[WIDTH-2:0]) == (WIDTH-1)'(MAX - 1))
                ap_wrap_msb: assert (counter_bin_curr[WIDTH-1] == !$past(counter_bin_curr[WIDTH-1]));
        end
    end

    // Wraparound: lower bits clear
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(enable) && $past(counter_bin_curr[WIDTH-2:0]) == (WIDTH-1)'(MAX - 1))
                ap_wrap_lower: assert (counter_bin_curr[WIDTH-2:0] == '0);
        end
    end

    // Hold when disabled
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (!$past(enable))
                ap_hold: assert (counter_bin_curr == $past(counter_bin_curr));
        end
    end

    // Next value preview matches registered output
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_next_preview: assert (counter_bin_curr == $past(counter_bin_next));
    end

    // Lower bits always in valid range
    always @(posedge clk) begin
        if (rst_n)
            ap_lower_range: assert (counter_bin_curr[WIDTH-2:0] < MAX);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    always @(posedge clk) begin
        if (rst_n)
            cp_at_max: cover (counter_bin_curr[WIDTH-2:0] == (WIDTH-1)'(MAX - 1));
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_wrap: cover (counter_bin_curr[WIDTH-2:0] == '0
                         && $past(counter_bin_curr[WIDTH-2:0]) == (WIDTH-1)'(MAX - 1));
    end

    always @(posedge clk) begin
        if (rst_n)
            cp_msb_set: cover (counter_bin_curr[WIDTH-1] == 1'b1);
    end

endmodule
