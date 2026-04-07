// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for reset_sync (yosys-compatible)
// Proves: async assert, sync deassert after N cycles, reset clears shift register.
//
// Parameters: N=3, KEEP_ATTRS=0, IN_ACTIVE_LOW=1, OUT_ACTIVE_LOW=1, ASYNC_ASSERT=1
// Single clock model -- the key property is the N-stage pipeline behavior.

module formal_reset_sync #(
    parameter int N              = 3,
    parameter bit KEEP_ATTRS     = 1'b0,
    parameter bit IN_ACTIVE_LOW  = 1'b1,
    parameter bit OUT_ACTIVE_LOW = 1'b1,
    parameter bit ASYNC_ASSERT   = 1'b1
) (
    input logic clk,
    input logic rst_n   // raw async reset input (active-low)
);

    logic sync_rst_n;

    reset_sync #(
        .N              (N),
        .KEEP_ATTRS     (KEEP_ATTRS),
        .IN_ACTIVE_LOW  (IN_ACTIVE_LOW),
        .OUT_ACTIVE_LOW (OUT_ACTIVE_LOW),
        .ASYNC_ASSERT   (ASYNC_ASSERT)
    ) dut (
        .clk        (clk),
        .rst_n      (rst_n),
        .sync_rst_n (sync_rst_n)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Hold reset asserted for at least 2 cycles, then release
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid < 2) assume (!rst_n);
    end

    // =========================================================================
    // Internal view: normalized active-HIGH reset signals
    // =========================================================================
    wire rst_in_h  = IN_ACTIVE_LOW  ? ~rst_n     : rst_n;
    wire rst_out_h = OUT_ACTIVE_LOW ? ~sync_rst_n : sync_rst_n;

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: When input reset is asserted, output reset must be asserted.
    // (async assert -- within 1 cycle if ASYNC_ASSERT=1)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_in_h)
            ap_assert_propagates: assert (rst_out_h);
    end

    // P2: After reset release, output stays asserted for N-1 more cycles.
    // Track consecutive cycles of deassertion on input.
    reg [7:0] f_deassert_count = 0;
    always @(posedge clk) begin
        if (rst_in_h)
            f_deassert_count <= 0;
        else
            f_deassert_count <= f_deassert_count + (f_deassert_count < 8'hFF);
    end

    // Output must remain asserted until N cycles of input deassertion
    always @(posedge clk) begin
        if (f_past_valid > 0 && !rst_in_h && f_deassert_count < N)
            ap_deassert_delay: assert (rst_out_h);
    end

    // P3: After N cycles of input deassertion, output deasserts.
    always @(posedge clk) begin
        if (f_past_valid > 0 && !rst_in_h && f_deassert_count >= N)
            ap_deassert_complete: assert (!rst_out_h);
    end

    // P4: Immediately after reset assertion, output is asserted.
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_asserted: assert (rst_out_h);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover assert sequence: reset asserted then deasserted
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n)
            cp_deasserted: cover (!rst_out_h);
    end

    // Cover the transition from asserted to deasserted output
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_transition: cover (!rst_out_h && $past(rst_out_h));
    end

    // Cover reset re-assertion after being deasserted
    always @(posedge clk) begin
        if (f_past_valid > 0)
            cp_reassert: cover (rst_out_h && $past(!rst_out_h));
    end

endmodule
