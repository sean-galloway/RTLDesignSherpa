// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for counter_load_clear (yosys-compatible)
// Instantiates DUT and properties together.
// Run with: sby counter_load_clear.sby

module formal_counter_load_clear #(
    parameter int MAX = 15
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    clear,
    input  logic                    increment,
    input  logic                    load,
    input  logic [$clog2(MAX)-1:0]  loadval
);

    localparam int W = $clog2(MAX);

    // DUT outputs
    logic [W-1:0] count;
    logic         done;

    // Instantiate DUT
    counter_load_clear #(
        .MAX(MAX)
    ) dut (
        .clk       (clk),
        .rst_n     (rst_n),
        .clear     (clear),
        .increment (increment),
        .load      (load),
        .loadval   (loadval),
        .count     (count),
        .done      (done)
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

    // Constrain loadval to valid range
    always @(posedge clk) begin
        if (rst_n) assume (loadval < W'(MAX));
    end

    // =========================================================================
    // Ghost match register (tracks what the DUT match register should be)
    // =========================================================================
    reg [W-1:0] f_match = 0;
    always @(posedge clk) begin
        if (!rst_n)
            f_match <= 0;
        else if (load)
            f_match <= loadval;
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, count is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_count: assert (count == '0);
    end

    // After reset, done is high (count==0 matches match_val==0)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_done: assert (done == 1'b1);
    end

    // Done signal is combinational: done == (count == match_val)
    always @(posedge clk) begin
        if (rst_n)
            ap_done_def: assert (done == (count == f_match));
    end

    // Clear overrides increment: count goes to 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(clear))
                ap_clear_priority: assert (count == '0);
        end
    end

    // Load updates match register
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(load))
                ap_load_match: assert (f_match == $past(loadval));
        end
    end

    // Increment when not clearing, not done, and no concurrent load changing match:
    // count increases by 1 (use explicit width cast to avoid SMT extension issues)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(increment) && !$past(clear) && !$past(done) && !$past(load))
                ap_increment: assert (count == W'($past(count) + 1));
        end
    end

    // Wraparound: when done and incrementing (not clearing, no concurrent load), count goes to 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(increment) && !$past(clear) && $past(done) && !$past(load))
                ap_wrap: assert (count == '0);
        end
    end

    // Hold: when not incrementing and not clearing
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (!$past(increment) && !$past(clear))
                ap_hold: assert (count == $past(count));
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover done assertion (after counting up from non-zero)
    always @(posedge clk) begin
        if (rst_n && f_past_valid > 2)
            cp_done: cover (done && count > 0);
    end

    // Cover clear operation
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_clear: cover ($past(clear) && count == '0);
    end

    // Cover load operation
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_load: cover ($past(load) && f_match == $past(loadval) && $past(loadval) > 0);
    end

    // Cover increment to done (done fires after counting up)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_count_to_done: cover (done && $past(!done) && $past(increment));
    end

endmodule
