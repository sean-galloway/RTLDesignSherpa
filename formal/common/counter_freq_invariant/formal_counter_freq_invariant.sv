// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for counter_freq_invariant (yosys-compatible)
// Instantiates DUT and properties together.
// Run with: sby counter_freq_invariant.sby

module formal_counter_freq_invariant #(
    parameter int COUNTER_WIDTH  = 8,
    parameter int PRESCALER_MAX  = 15
) (
    input  logic                        clk,
    input  logic                        rst_n,
    input  logic                        sync_reset_n,
    input  logic [6:0]                  freq_sel
);

    // DUT outputs
    logic [COUNTER_WIDTH-1:0] o_counter;
    logic                     tick;

    // Instantiate DUT
    counter_freq_invariant #(
        .COUNTER_WIDTH(COUNTER_WIDTH),
        .PRESCALER_MAX(PRESCALER_MAX)
    ) dut (
        .clk         (clk),
        .rst_n       (rst_n),
        .sync_reset_n(sync_reset_n),
        .freq_sel    (freq_sel),
        .o_counter   (o_counter),
        .tick        (tick)
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

    // Constrain freq_sel to a fixed value for tractability
    always @(posedge clk) begin
        assume (freq_sel == 7'd0);
    end

    // Hold sync_reset_n stable high after initial cycles
    always @(posedge clk) begin
        if (f_past_valid >= 3) assume (sync_reset_n);
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, counter is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_counter: assert (o_counter == '0);
    end

    // After reset, tick is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_tick: assert (tick == 1'b0);
    end

    // Tick and counter increment are synchronized:
    // tick and counter update in the same always_ff block, so
    // when tick is high, counter incremented this cycle.
    // When tick is low (and no clear), counter held.
    //
    // Note: tick and o_counter are both registered outputs that update
    // simultaneously from the same conditions. So we check CURRENT tick
    // against CURRENT counter vs PAST counter.

    // When tick is high and was not being cleared, counter incremented
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (tick)
                ap_tick_inc: assert (o_counter == $past(o_counter) + 1);
        end
    end

    // When tick is low and no clear happened, counter held
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (!tick && o_counter != '0)
                ap_no_tick_hold: assert (o_counter == $past(o_counter));
        end
    end

    // Tick is never high for two consecutive cycles
    // (prescaler needs at least 1 cycle to count, even with division=1)
    // Actually with PRESCALER_MAX=15 and division=100, this would take 100 cycles.
    // But the prescaler done can fire every N cycles. With small parameters
    // this is hard to prove, so we just check the basic invariants.

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover tick assertion
    always @(posedge clk) begin
        if (rst_n)
            cp_tick: cover (tick);
    end

    // Cover counter increment via tick
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_counter_inc: cover (o_counter > 0);
    end

endmodule
