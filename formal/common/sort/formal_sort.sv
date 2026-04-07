// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for sort (yosys-compatible)
// Verifies pipelined odd-even transposition sort network.

module formal_sort #(
    parameter int NUM_VALS = 4,
    parameter int SIZE     = 8
) (
    input logic clk,
    input logic rst_n,
    input logic valid_in,
    input logic [NUM_VALS*SIZE-1:0] data
);

    logic [NUM_VALS*SIZE-1:0] sorted;
    logic                     done;

    sort #(
        .NUM_VALS(NUM_VALS),
        .SIZE    (SIZE)
    ) dut (
        .clk     (clk),
        .rst_n   (rst_n),
        .data    (data),
        .valid_in(valid_in),
        .sorted  (sorted),
        .done    (done)
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
    // Helper: unpack sorted output into individual values
    // =========================================================================
    logic [SIZE-1:0] s [NUM_VALS];
    generate
        genvar gi;
        for (gi = 0; gi < NUM_VALS; gi++) begin : gen_unpack
            assign s[gi] = sorted[gi*SIZE +: SIZE];
        end
    endgenerate

    // =========================================================================
    // Capture input snapshot when valid_in is asserted, so we can check
    // the permutation property NUM_VALS cycles later when done fires.
    // Use a shift register of snapshots.
    // =========================================================================
    logic [NUM_VALS*SIZE-1:0] f_snap [0:NUM_VALS-1];
    logic                     f_snap_valid [0:NUM_VALS-1];

    always @(posedge clk) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_VALS; i++) begin
                f_snap[i] <= '0;
                f_snap_valid[i] <= 1'b0;
            end
        end else begin
            f_snap[0] <= data;
            f_snap_valid[0] <= valid_in;
            for (int i = 1; i < NUM_VALS; i++) begin
                f_snap[i] <= f_snap[i-1];
                f_snap_valid[i] <= f_snap_valid[i-1];
            end
        end
    end

    // The snapshot that corresponds to the current done signal
    logic [NUM_VALS*SIZE-1:0] f_captured_input;
    logic                     f_captured_valid;
    assign f_captured_input = f_snap[NUM_VALS-1];
    assign f_captured_valid = f_snap_valid[NUM_VALS-1];

    // Unpack captured input
    logic [SIZE-1:0] f_in [NUM_VALS];
    generate
        for (gi = 0; gi < NUM_VALS; gi++) begin : gen_unpack_in
            assign f_in[gi] = f_captured_input[gi*SIZE +: SIZE];
        end
    endgenerate

    // =========================================================================
    // Safety properties: done signal timing
    // =========================================================================

    // done tracks the valid pipeline (only check after reset released)
    always @(posedge clk) begin
        if (f_past_valid >= 2 && rst_n)
            ap_done_matches_pipe: assert (done == f_captured_valid);
    end

    // After reset, done is deasserted
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_done: assert (!done);
    end

    // =========================================================================
    // Safety properties: output is sorted (descending - largest at index 0)
    // The RTL swaps when [i] < [i+1], so it sorts descending.
    // Only check when done is legitimately asserted (after reset).
    // =========================================================================

    generate
        for (gi = 0; gi < NUM_VALS - 1; gi++) begin : gen_sorted_check
            always @(posedge clk)
                if (f_past_valid >= 2 && rst_n && done)
                    assert (s[gi] >= s[gi+1]);
        end
    endgenerate

    // =========================================================================
    // Safety properties: permutation check
    // Every input value must appear in the output (sum-based check).
    // This catches value creation/destruction but not duplication of equal vals.
    // =========================================================================

    // Sum of all input values
    logic [SIZE+$clog2(NUM_VALS)-1:0] f_sum_in;
    always_comb begin
        f_sum_in = '0;
        for (int i = 0; i < NUM_VALS; i++)
            f_sum_in = f_sum_in + {{($clog2(NUM_VALS)){1'b0}}, f_in[i]};
    end

    // Sum of all output values
    logic [SIZE+$clog2(NUM_VALS)-1:0] f_sum_out;
    always_comb begin
        f_sum_out = '0;
        for (int i = 0; i < NUM_VALS; i++)
            f_sum_out = f_sum_out + {{($clog2(NUM_VALS)){1'b0}}, s[i]};
    end

    // XOR of all input values (second permutation invariant)
    logic [SIZE-1:0] f_xor_in;
    always_comb begin
        f_xor_in = '0;
        for (int i = 0; i < NUM_VALS; i++)
            f_xor_in = f_xor_in ^ f_in[i];
    end

    // XOR of all output values
    logic [SIZE-1:0] f_xor_out;
    always_comb begin
        f_xor_out = '0;
        for (int i = 0; i < NUM_VALS; i++)
            f_xor_out = f_xor_out ^ s[i];
    end

    always @(posedge clk) begin
        if (f_past_valid >= 2 && rst_n && done)
            ap_permutation_sum: assert (f_sum_in == f_sum_out);
    end

    always @(posedge clk) begin
        if (f_past_valid >= 2 && rst_n && done)
            ap_permutation_xor: assert (f_xor_in == f_xor_out);
    end

    // =========================================================================
    // Safety properties: reset clears output
    // =========================================================================

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_sorted: assert (sorted == '0);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: done asserted with sorted output
    always @(posedge clk)
        cp_done: cover (f_past_valid >= 2 && rst_n && done);

    // Cover: all equal values
    always @(posedge clk)
        cp_all_equal: cover (f_past_valid >= 2 && rst_n && done
                             && s[0] == s[1] && s[1] == s[2] && s[2] == s[3]);

    // Cover: all distinct values in descending order
    always @(posedge clk)
        cp_distinct_desc: cover (f_past_valid >= 2 && rst_n && done
                                 && s[0] > s[1] && s[1] > s[2] && s[2] > s[3]);

    // Cover: max spread (largest and smallest values)
    always @(posedge clk)
        cp_max_spread: cover (f_past_valid >= 2 && rst_n && done
                              && s[0] == {SIZE{1'b1}} && s[NUM_VALS-1] == '0);

endmodule
