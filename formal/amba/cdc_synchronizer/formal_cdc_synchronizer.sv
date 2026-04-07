// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for cdc_synchronizer (yosys-compatible)
// Single clock model -- verifies synchronizer pipeline logic.
//
// Properties:
//   - Reset clears output
//   - After FLOP_COUNT stable cycles, input appears on output
//   - Output changes only when input has been changing
// Cover:
//   - Signal propagation through pipeline

module formal_cdc_synchronizer #(
    parameter int WIDTH      = 4,
    parameter int FLOP_COUNT = 2
) (
    input wire clk,
    input wire rst_n
);

    // Use anyconst: solver picks one constant value and holds it.
    // This models a quasi-static CDC input (the expected use case).
    (* anyconst *) wire [WIDTH-1:0] d_const;

    wire [WIDTH-1:0] async_in = d_const;
    wire [WIDTH-1:0] sync_out;

    cdc_synchronizer #(
        .WIDTH      (WIDTH),
        .FLOP_COUNT (FLOP_COUNT)
    ) dut (
        .clk      (clk),
        .rst_n    (rst_n),
        .async_in (async_in),
        .sync_out (sync_out)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid < 2) assume (!rst_n);
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: Reset clears output to zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_zero: assert (sync_out == '0);
    end

    // P2: After FLOP_COUNT cycles of stable input, output matches input.
    // Reset deasserts at cycle 3 (f_past_valid=2 triggers assume rst_n).
    // First valid capture at cycle 3, propagates through FLOP_COUNT stages.
    // So at f_past_valid >= FLOP_COUNT+2, output should match constant input.
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= (FLOP_COUNT + 3))
            ap_propagation: assert (sync_out == d_const);
    end

    // P3: Once output matches input (constant), output stays stable
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && f_past_valid >= (FLOP_COUNT + 4))
            ap_output_stable: assert (sync_out == $past(sync_out));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: non-zero output
    always @(posedge clk) begin
        if (rst_n)
            cp_nonzero: cover (sync_out != '0);
    end

    // Cover: all-ones output
    always @(posedge clk) begin
        if (rst_n)
            cp_all_ones: cover (sync_out == {WIDTH{1'b1}});
    end

    // Cover: output matches constant input (propagation complete)
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= (FLOP_COUNT + 3))
            cp_match: cover (sync_out == d_const && d_const != '0);
    end

endmodule
