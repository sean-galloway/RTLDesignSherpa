// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for counter_bingray (yosys-compatible)
// Proves Gray code correctness: single-bit change, bin/gray sync, wraparound.

module formal_counter_bingray #(
    parameter int WIDTH = 4
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable
);

    // DUT outputs
    logic [WIDTH-1:0] counter_bin;
    logic [WIDTH-1:0] counter_bin_next;
    logic [WIDTH-1:0] counter_gray;

    // Instantiate DUT
    counter_bingray #(.WIDTH(WIDTH)) dut (
        .clk              (clk),
        .rst_n            (rst_n),
        .enable           (enable),
        .counter_bin      (counter_bin),
        .counter_bin_next (counter_bin_next),
        .counter_gray     (counter_gray)
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

    // After reset, all outputs zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_bin:  assert (counter_bin == '0);
            ap_reset_gray: assert (counter_gray == '0);
        end
    end

    // Gray code formula: gray = bin ^ (bin >> 1)
    always @(posedge clk) begin
        if (rst_n)
            ap_gray_formula: assert (counter_gray == (counter_bin ^ (counter_bin >> 1)));
    end

    // Single-bit change property: gray code changes at most 1 bit per step
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(enable))
            ap_single_bit: assert ($countones(counter_gray ^ $past(counter_gray)) == 1);
    end

    // No change when disabled
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && !$past(enable)) begin
            ap_hold_bin:  assert (counter_bin == $past(counter_bin));
            ap_hold_gray: assert (counter_gray == $past(counter_gray));
        end
    end

    // Increment: when enabled, binary counter increments by 1 (mod 2^WIDTH)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(enable))
            ap_increment: assert (counter_bin == WIDTH'($past(counter_bin) + 1));
    end

    // Next preview matches registered output
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            ap_next_preview: assert (counter_bin == $past(counter_bin_next));
    end

    // Next value is combinational: bin_next = enable ? (bin+1) mod 2^W : bin
    always @(posedge clk) begin
        if (rst_n) begin
            if (enable)
                ap_next_en: assert (counter_bin_next == WIDTH'(counter_bin + 1));
            else
                ap_next_dis: assert (counter_bin_next == counter_bin);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Reach max value (all 1s in binary)
    always @(posedge clk) begin
        if (rst_n)
            cp_max: cover (counter_bin == {WIDTH{1'b1}});
    end

    // Wrap: transition from all-1s to all-0s
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_wrap: cover (counter_bin == '0 && $past(counter_bin) == {WIDTH{1'b1}});
    end

    // Gray MSB transitions
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_gray_msb: cover (counter_gray[WIDTH-1] && !$past(counter_gray[WIDTH-1]));
    end

endmodule
