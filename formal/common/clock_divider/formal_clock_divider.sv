// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for clock_divider (yosys-compatible)
// Proves reset behavior and that divided_clk outputs change over time.

module formal_clock_divider #(
    parameter int N             = 2,
    parameter int PO_WIDTH      = 8,
    parameter int COUNTER_WIDTH = 16
) (
    input  logic                      clk,
    input  logic                      rst_n,
    input  logic [(N*PO_WIDTH-1):0]   pickoff_points
);

    // DUT outputs
    logic [N-1:0] divided_clk;

    // Instantiate DUT
    clock_divider #(
        .N(N),
        .PO_WIDTH(PO_WIDTH),
        .COUNTER_WIDTH(COUNTER_WIDTH)
    ) dut (
        .clk            (clk),
        .rst_n          (rst_n),
        .pickoff_points (pickoff_points),
        .divided_clk    (divided_clk)
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
    // Environment assumptions
    // =========================================================================

    // Constrain pickoff_points to valid range so outputs are meaningful
    // Each pickoff point should be < COUNTER_WIDTH
    genvar gi;
    generate
        for (gi = 0; gi < N; gi++) begin : gen_assume_pickoff
            always @(posedge clk) begin
                if (rst_n)
                    assume (pickoff_points[gi*PO_WIDTH +: PO_WIDTH] < COUNTER_WIDTH);
            end
        end
    endgenerate

    // Hold pickoff_points stable after reset (avoid runtime change glitches)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            assume (pickoff_points == $past(pickoff_points));
    end

    // =========================================================================
    // Ghost model: track internal counter independently
    // =========================================================================
    reg [COUNTER_WIDTH-1:0] f_counter = 0;

    always @(posedge clk) begin
        if (!rst_n)
            f_counter <= 0;
        else
            f_counter <= f_counter + 1;
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset: all divided_clk outputs must be 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
assert (divided_clk == {N{1'b0}});
    end

    // After reset: ghost counter is 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
assert (f_counter == 0);
    end

    // Each divided_clk output tracks the appropriate counter bit (registered)
    // divided_clk[i] == counter_bit at pickoff point, but registered (1 cycle delay)
    generate
        for (gi = 0; gi < N; gi++) begin : gen_assert_tracking
            wire [PO_WIDTH-1:0] w_po = pickoff_points[gi*PO_WIDTH +: PO_WIDTH];
            // Clamp to valid range (matching RTL behavior)
            localparam int ADDR_WIDTH = $clog2(COUNTER_WIDTH);
            wire [ADDR_WIDTH-1:0] w_addr = (w_po < COUNTER_WIDTH) ?
                                            w_po[ADDR_WIDTH-1:0] :
                                            ADDR_WIDTH'(COUNTER_WIDTH - 1);

            // After 2 valid cycles with reset deasserted, divided_clk tracks the
            // previous counter bit value (registered output = 1 cycle latency)
            always @(posedge clk) begin
                if (f_past_valid >= 3 && rst_n && $past(rst_n) && $past(rst_n, 2)) begin
assert (divided_clk[gi] == $past(f_counter[w_addr]));
                end
            end
        end
    endgenerate

    // divided_clk outputs are always valid bits (0 or 1) -- trivially true for logic
    // but included for completeness
    always @(posedge clk) begin
        if (rst_n)
assert ((divided_clk & ~{N{1'b1}}) == 0);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: divided_clk[0] toggles (goes high)
    always @(posedge clk) begin
        if (rst_n)
cover (divided_clk[0] == 1'b1);
    end

    // Cover: divided_clk[0] transitions from 0 to 1
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
cover (divided_clk[0] == 1'b1 && $past(divided_clk[0]) == 1'b0);
    end

    // Cover: divided_clk[1] goes high (slower output)
    always @(posedge clk) begin
        if (rst_n)
cover (divided_clk[1] == 1'b1);
    end

    // Cover: both outputs high simultaneously
    always @(posedge clk) begin
        if (rst_n)
cover (divided_clk == {N{1'b1}});
    end

endmodule
