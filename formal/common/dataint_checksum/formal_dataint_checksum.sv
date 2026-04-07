// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for dataint_checksum (yosys-compatible)

module formal_dataint_checksum #(
    parameter int WIDTH = 8
) (
    input logic             clk,
    input logic             rst_n,
    input logic             reset,
    input logic             valid,
    input logic [WIDTH-1:0] data
);

    logic [WIDTH-1:0] chksum;

    dataint_checksum #(.WIDTH(WIDTH)) dut (
        .clk   (clk),
        .rst_n (rst_n),
        .reset (reset),
        .valid (valid),
        .data  (data),
        .chksum(chksum)
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

    // Shadow accumulator to track expected checksum
    reg [WIDTH-1:0] f_shadow = '0;
    always @(posedge clk) begin
        if (!rst_n)
            f_shadow <= '0;
        else if (reset)
            f_shadow <= '0;
        else if (valid)
            f_shadow <= f_shadow + data;
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After hardware reset, checksum is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_hw_reset: assert (chksum == '0);
    end

    // After soft reset, checksum is zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(reset))
            ap_soft_reset: assert (chksum == '0);
    end

    // Checksum matches shadow accumulator at all times
    always @(posedge clk) begin
        if (rst_n)
            ap_tracks_shadow: assert (chksum == f_shadow);
    end

    // When valid is deasserted and no reset, checksum holds
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && !$past(valid) && !$past(reset))
            ap_hold: assert (chksum == $past(chksum));
    end

    // Accumulation: when valid, new value = old + data
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(valid) && !$past(reset))
            ap_accumulate: assert (chksum == ($past(chksum) + $past(data)));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: accumulation over multiple cycles
    always @(posedge clk) begin
        if (f_past_valid >= 4)
            cp_multi_accum: cover (rst_n && chksum != '0);
    end

    // Cover: soft reset clears nonzero checksum
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_soft_reset_clears: cover ($past(chksum) != '0 && $past(reset) && chksum == '0);
    end

    // Cover: checksum wraps around (overflow)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(valid) && !$past(reset))
            cp_overflow: cover (chksum < $past(chksum));
    end

    // Cover: consecutive valid cycles
    always @(posedge clk) begin
        if (f_past_valid >= 2)
            cp_consecutive: cover (rst_n && $past(valid) && $past(valid, 2));
    end

endmodule
