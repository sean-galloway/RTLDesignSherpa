// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for shifter_lfsr (yosys-compatible)
// Instantiates DUT and properties together.
// Run with: sby shifter_lfsr.sby

module formal_shifter_lfsr #(
    parameter int WIDTH           = 4,
    parameter int TAP_INDEX_WIDTH = 2,
    parameter int TAP_COUNT       = 2
) (
    input logic                              clk,
    input logic                              rst_n,
    input logic                              enable,
    input logic                              seed_load,
    input logic [WIDTH-1:0]                  seed_data,
    input logic [TAP_COUNT*TAP_INDEX_WIDTH-1:0] taps
);

    // DUT outputs
    logic [WIDTH-1:0] lfsr_out;
    logic             lfsr_done;

    // Instantiate DUT
    shifter_lfsr #(
        .WIDTH          (WIDTH),
        .TAP_INDEX_WIDTH(TAP_INDEX_WIDTH),
        .TAP_COUNT      (TAP_COUNT)
    ) dut (
        .clk      (clk),
        .rst_n    (rst_n),
        .enable   (enable),
        .seed_load(seed_load),
        .seed_data(seed_data),
        .taps     (taps),
        .lfsr_out (lfsr_out),
        .lfsr_done(lfsr_done)
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

    // Constrain seed to non-zero (all-zeros is lock-up for XOR LFSR)
    always @(*) begin
        assume (seed_data != '0);
    end

    // Constrain taps to valid positions (1..WIDTH)
    always @(*) begin
        for (int i = 0; i < TAP_COUNT; i++) begin
            assume (taps[i*TAP_INDEX_WIDTH +: TAP_INDEX_WIDTH] >= 1);
            assume (taps[i*TAP_INDEX_WIDTH +: TAP_INDEX_WIDTH] <= WIDTH);
        end
    end

    // Keep seed and taps stable after reset release (so lfsr_done is meaningful)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            assume (seed_data == $past(seed_data));
            assume (taps == $past(taps));
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, LFSR register is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_value: assert (lfsr_out == '0);
    end

    // Seed load: when enable and seed_load are both high, register loads seed
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(enable) && $past(seed_load))
                ap_seed_load: assert (lfsr_out == $past(seed_data));
        end
    end

    // Hold when disabled: register does not change
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (!$past(enable))
                ap_hold: assert (lfsr_out == $past(lfsr_out));
        end
    end

    // Shift behavior: when enabled without seed_load, LFSR shifts left
    // Upper bits come from previous lower bits
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(enable) && !$past(seed_load))
                ap_shift_upper: assert (lfsr_out[WIDTH-1:1] == $past(lfsr_out[WIDTH-2:0]));
        end
    end

    // lfsr_done is combinationally correct
    always @(*) begin
        if (rst_n)
            ap_done_definition: assert (lfsr_done == (lfsr_out == seed_data));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: enable shifting (non-zero state after seed load + shift)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n)
            cp_enable_shift: cover (lfsr_out != '0 && !seed_load && enable);
    end

    // Cover: lfsr_done asserted
    always @(posedge clk) begin
        if (rst_n)
            cp_lfsr_done: cover (lfsr_done);
    end

    // Cover: LFSR running (non-zero, not at seed)
    always @(posedge clk) begin
        if (rst_n)
            cp_running: cover (lfsr_out != '0 && !lfsr_done);
    end

endmodule
