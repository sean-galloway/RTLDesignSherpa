// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for counter_bin_load (yosys-compatible)
// Instantiates DUT and properties together.
// Run with: sby counter_bin_load.sby

module formal_counter_bin_load #(
    parameter int WIDTH = 5,
    parameter int MAX = 15
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    input  logic             add_enable,
    input  logic [WIDTH-1:0] add_value,
    input  logic             load,
    input  logic [WIDTH-1:0] load_value
);

    // DUT outputs
    logic [WIDTH-1:0] counter_bin_curr;
    logic [WIDTH-1:0] counter_bin_next;

    // Instantiate DUT
    counter_bin_load #(
        .WIDTH(WIDTH),
        .MAX(MAX)
    ) dut (
        .clk              (clk),
        .rst_n            (rst_n),
        .enable           (enable),
        .add_enable       (add_enable),
        .add_value        (add_value),
        .load             (load),
        .load_value       (load_value),
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

    // Constrain load_value and add_value to valid FIFO pointer range [0, 2*MAX-1]
    always @(posedge clk) begin
        if (rst_n) begin
            assume (load_value < WIDTH'(2 * MAX));
            assume (add_value < WIDTH'(2 * MAX));
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, counter is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_value: assert (counter_bin_curr == '0);
    end

    // Load has highest priority: overrides enable and add_enable
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(load))
                ap_load_priority: assert (counter_bin_curr == $past(load_value));
        end
    end

    // Add_enable with zero value: holds or wraps (when load not active)
    // Note: if counter >= 2*MAX, even adding 0 causes a wraparound
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(add_enable) && !$past(load) && $past(add_value) == '0) begin
                if ($past(counter_bin_curr) < WIDTH'(2 * MAX))
                    ap_add_zero_hold: assert (counter_bin_curr == $past(counter_bin_curr));
            end
        end
    end

    // Enable increments by 1 (when load and add not active, not at wrap point)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(enable) && !$past(load) && !$past(add_enable)) begin
                if ($past(counter_bin_curr[WIDTH-2:0]) != (WIDTH-1)'(MAX - 1))
                    ap_enable_increment: assert (counter_bin_curr == $past(counter_bin_curr) + 1);
            end
        end
    end

    // Enable wraparound: MSB flips, lower bits clear
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(enable) && !$past(load) && !$past(add_enable)) begin
                if ($past(counter_bin_curr[WIDTH-2:0]) == (WIDTH-1)'(MAX - 1)) begin
                    ap_enable_wrap_msb: assert (counter_bin_curr[WIDTH-1] == !$past(counter_bin_curr[WIDTH-1]));
                    ap_enable_wrap_lower: assert (counter_bin_curr[WIDTH-2:0] == '0);
                end
            end
        end
    end

    // Hold when no operation active
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (!$past(load) && !$past(add_enable) && !$past(enable))
                ap_hold: assert (counter_bin_curr == $past(counter_bin_curr));
        end
    end

    // Next value preview matches registered output
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_next_preview: assert (counter_bin_curr == $past(counter_bin_next));
    end

    // Counter value fits in WIDTH bits (basic sanity)
    // Note: Unlike counter_bin (enable-only), add operations can set lower
    // bits to any value in [0, 2^(WIDTH-1)-1], so the stricter counter_bin
    // range check (lower < MAX) does not apply here.

    // Enable-only lower range: when counter is only modified by enable
    // (not load or add), lower bits stay in [0, MAX-1]
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(enable) && !$past(load) && !$past(add_enable))
                ap_enable_lower_range: assert (counter_bin_curr[WIDTH-2:0] < MAX);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover load operation
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_load: cover ($past(load) && counter_bin_curr == $past(load_value));
    end

    // Cover add operation
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_add: cover ($past(add_enable) && !$past(load));
    end

    // Cover enable increment
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_enable: cover ($past(enable) && !$past(load) && !$past(add_enable));
    end

    // Cover wraparound via enable
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_wrap: cover (counter_bin_curr[WIDTH-2:0] == '0
                         && $past(counter_bin_curr[WIDTH-2:0]) == (WIDTH-1)'(MAX - 1)
                         && $past(enable) && !$past(load) && !$past(add_enable));
    end

endmodule
