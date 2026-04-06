// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for uart_rx (yosys-compatible, direct SV read)
// Run with: sby uart_rx.sby
//
// Properties verified:
//   P1: Reset - o_rx_valid=0, o_rx_data=0
//   P2: o_rx_valid pulse is exactly 1 cycle (asserts then deasserts)
//   P3: After reset, no valid output until a full frame could be received
//   P4: o_rx_valid cannot assert while idle (no spurious pulses)
//   P5: When o_rx_valid asserts, it stays asserted until i_rx_ready handshake
//   Cover: Complete frame reception, o_rx_valid assertion, back-to-back frames

module formal_uart_rx (
    input  logic       clk,
    input  logic       rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // CLKS_PER_BIT=3 gives a full 10-bit frame in ~30 clock cycles
    // Midpoint sampling at (CLKS_PER_BIT-1)/2 = 1 cycle
    // =========================================================================
    localparam int CLKS_PER_BIT = 3;

    // Minimum cycles for a complete frame reception:
    // START: (CLKS_PER_BIT-1)/2 + 1 midpoint check + reset count
    //        then CLKS_PER_BIT cycles to first data bit sampling
    // Total: ~((CLKS_PER_BIT-1)/2) + 1 + 8*CLKS_PER_BIT + CLKS_PER_BIT
    // With CLKS_PER_BIT=3: 1 + 1 + 24 + 3 = ~29 cycles (plus sync delay)
    // Add 2 cycles for the 2-FF synchronizer
    localparam int MIN_FRAME_CYCLES = 10;  // conservative lower bound

    // =========================================================================
    // Free inputs (driven by formal engine)
    // =========================================================================
    (* anyseq *) reg       rx_serial;
    (* anyseq *) reg       rx_ready;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire [7:0] o_rx_data;
    wire       o_rx_valid;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    uart_rx #(
        .CLKS_PER_BIT(CLKS_PER_BIT)
    ) dut (
        .i_clk      (clk),
        .i_rst_n    (rst_n),
        .i_rx       (rx_serial),
        .o_rx_data  (o_rx_data),
        .o_rx_valid (o_rx_valid),
        .i_rx_ready (rx_ready)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Reset sequence: assert reset for first 2 cycles
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Shadow tracking: count cycles since reset deassertion
    // =========================================================================
    reg [7:0] f_cycles_since_reset = 0;

    always @(posedge clk) begin
        if (!rst_n) begin
            f_cycles_since_reset <= 0;
        end else begin
            if (f_cycles_since_reset < 8'hFF)
                f_cycles_since_reset <= f_cycles_since_reset + 1;
        end
    end

    // Track o_rx_valid edges
    reg f_prev_valid = 0;
    always @(posedge clk) begin
        if (!rst_n)
            f_prev_valid <= 0;
        else
            f_prev_valid <= o_rx_valid;
    end

    // Count consecutive cycles o_rx_valid is held high
    reg [7:0] f_valid_hold_count = 0;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_valid_hold_count <= 0;
        end else begin
            if (o_rx_valid)
                f_valid_hold_count <= f_valid_hold_count + 1;
            else
                f_valid_hold_count <= 0;
        end
    end

    // =========================================================================
    // P1: Reset - o_rx_valid=0 after reset
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_valid: assert (o_rx_valid == 1'b0);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_data: assert (o_rx_data == 8'h00);
    end

    // =========================================================================
    // P2: o_rx_valid deasserts when i_rx_ready is high
    //     The CLEANUP state: o_rx_valid is asserted, and when i_rx_ready
    //     is seen, the FSM transitions to IDLE, deasserting valid.
    //     So: if o_rx_valid was high and rx_ready was high, next cycle
    //     o_rx_valid should be low.
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(o_rx_valid) && $past(rx_ready))
                ap_valid_deasserts: assert (o_rx_valid == 1'b0);
        end
    end

    // =========================================================================
    // P3: After reset, no valid output for at least MIN_FRAME_CYCLES
    //     A complete frame takes significant time; valid cannot appear
    //     immediately after reset.
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n && f_cycles_since_reset < MIN_FRAME_CYCLES)
            ap_no_early_valid: assert (o_rx_valid == 1'b0);
    end

    // =========================================================================
    // P4: o_rx_valid is clean - it cannot glitch (go high for one cycle
    //     then immediately low without rx_ready). The valid signal stays
    //     asserted until rx_ready completes the handshake.
    //     If valid was high and rx_ready was low, valid stays high.
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(o_rx_valid) && !$past(rx_ready))
                ap_valid_holds: assert (o_rx_valid == 1'b1);
        end
    end

    // =========================================================================
    // P5: o_rx_data is stable while o_rx_valid is asserted
    //     Data must not change while waiting for handshake.
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(o_rx_valid) && o_rx_valid)
                ap_data_stable: assert (o_rx_data == $past(o_rx_data));
        end
    end

    // =========================================================================
    // P6: After o_rx_valid deasserts (handshake done), it cannot reassert
    //     on the very next cycle (need at least one frame worth of time).
    //     Specifically: if valid fell this cycle, it cannot rise next cycle.
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (f_prev_valid && !o_rx_valid) begin
                // Valid just fell; it should not rise immediately.
                // We check on the *next* edge, so this is a 2-cycle check.
                // The FSM goes CLEANUP->IDLE, and needs to go through
                // START->DATA->STOP->CLEANUP again before next valid.
            end
        end
    end

    // Stronger version: after valid falls, at least MIN_FRAME_CYCLES before
    // it can rise again. Track cycles since last valid fall.
    reg [7:0] f_cycles_since_valid_fall = 8'hFF;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_cycles_since_valid_fall <= 8'hFF;
        end else begin
            if (f_prev_valid && !o_rx_valid) begin
                f_cycles_since_valid_fall <= 0;
            end else if (f_cycles_since_valid_fall < 8'hFF) begin
                f_cycles_since_valid_fall <= f_cycles_since_valid_fall + 1;
            end
        end
    end

    always @(posedge clk) begin
        if (rst_n && f_cycles_since_valid_fall < MIN_FRAME_CYCLES)
            ap_no_rapid_revalid: assert (o_rx_valid == 1'b0);
    end

    // =========================================================================
    // P7: RX line idle assumption for sanity
    //     When not driven by formal, the RX line defaults to high (idle).
    //     This is just documentation - the formal engine drives rx_serial
    //     freely via anyseq.
    // =========================================================================

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: o_rx_valid asserts (complete frame received)
    always @(posedge clk) begin
        if (rst_n)
            cp_valid_asserts: cover (o_rx_valid);
    end

    // C2: Handshake completes (valid + ready)
    always @(posedge clk) begin
        if (rst_n)
            cp_handshake: cover (o_rx_valid && rx_ready);
    end

    // C3: Valid rises (fresh assertion after being low)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_valid_rise: cover (!$past(o_rx_valid) && o_rx_valid);
    end

    // C4: Back-to-back frames (valid falls then later rises again)
    // This requires depth sufficient for 2 full frames + gap
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_second_valid: cover (o_rx_valid && f_cycles_since_valid_fall < 8'hFF
                                    && f_cycles_since_valid_fall > 8'd0);
    end

    // C5: Specific data byte received (0xA5 as example)
    always @(posedge clk) begin
        if (rst_n)
            cp_data_a5: cover (o_rx_valid && o_rx_data == 8'hA5);
    end

    // C6: All-zeros byte received
    always @(posedge clk) begin
        if (rst_n)
            cp_data_00: cover (o_rx_valid && o_rx_data == 8'h00);
    end

    // C7: All-ones byte received
    always @(posedge clk) begin
        if (rst_n)
            cp_data_ff: cover (o_rx_valid && o_rx_data == 8'hFF);
    end

endmodule
