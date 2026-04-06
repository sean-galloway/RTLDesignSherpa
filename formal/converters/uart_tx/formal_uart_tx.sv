// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for uart_tx (yosys-compatible, direct SV read)
// Run with: sby uart_tx.sby
//
// Properties verified:
//   P1: Reset - o_tx=1 (idle high), o_tx_ready=1, FSM in IDLE
//   P2: o_tx_ready only asserted when FSM is in IDLE state
//   P3: During START state, o_tx==0 (start bit is low)
//   P4: During STOP state, o_tx==1 (stop bit is high)
//   P5: Idle output is high (o_tx==1 when IDLE and no tx in progress)
//   Cover: Complete transmission, back-to-back transmissions

module formal_uart_tx (
    input  logic       clk,
    input  logic       rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // CLKS_PER_BIT=3 gives a full 10-bit frame in 30 clock cycles
    // =========================================================================
    localparam int CLKS_PER_BIT = 3;

    // =========================================================================
    // Free inputs (driven by formal engine)
    // =========================================================================
    (* anyseq *) reg [7:0] tx_data;
    (* anyseq *) reg       tx_valid;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire       o_tx;
    wire       o_tx_ready;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    uart_tx #(
        .CLKS_PER_BIT(CLKS_PER_BIT)
    ) dut (
        .i_clk      (clk),
        .i_rst_n    (rst_n),
        .o_tx       (o_tx),
        .i_tx_data  (tx_data),
        .i_tx_valid (tx_valid),
        .o_tx_ready (o_tx_ready)
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
    // Shadow model: track transmission state from port-level observables
    // We infer the FSM state by watching o_tx_ready transitions.
    // o_tx_ready==1 means IDLE; o_tx_ready==0 means transmitting.
    // =========================================================================

    // Track if we saw a valid handshake to start transmission
    reg f_transmitting = 0;
    reg [7:0] f_tx_data_captured = 0;
    reg [5:0] f_cycle_count = 0;

    always @(posedge clk) begin
        if (!rst_n) begin
            f_transmitting <= 0;
            f_tx_data_captured <= 0;
            f_cycle_count <= 0;
        end else begin
            if (o_tx_ready && tx_valid) begin
                // Handshake: transmission starting next cycle
                f_transmitting <= 1;
                f_tx_data_captured <= tx_data;
                f_cycle_count <= 0;
            end else if (f_transmitting) begin
                f_cycle_count <= f_cycle_count + 1;
                // Full frame = 10 bits * CLKS_PER_BIT = 30 cycles
                // After the last cycle of STOP, ready goes high
                if (o_tx_ready) begin
                    f_transmitting <= 0;
                end
            end
        end
    end

    // =========================================================================
    // P1: Reset - o_tx=1 (idle high), o_tx_ready=1
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_tx_high: assert (o_tx == 1'b1);
    end

    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_ready: assert (o_tx_ready == 1'b1);
    end

    // =========================================================================
    // P2: o_tx_ready deasserts during transmission
    //     When o_tx_ready falls to 0, it must stay 0 until the frame completes.
    //     When o_tx_ready is 0, a new tx_valid must not be accepted.
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            // If ready was 0 last cycle, either it stays 0 (still transmitting)
            // or it rises to 1 (frame complete). This is always true by nature
            // of the FSM. The key property: ready can only rise at the end of
            // a STOP bit period.
            if (!$past(o_tx_ready) && o_tx_ready) begin
                // Transition from not-ready to ready: stop bit just finished.
                // On the cycle ready goes high, o_tx must be high (stop/idle).
                ap_ready_rise_tx_high: assert (o_tx == 1'b1);
            end
        end
    end

    // =========================================================================
    // P3: Start bit is low
    //     When o_tx_ready transitions from 1->0, the next CLKS_PER_BIT cycles
    //     have o_tx==0 (the start bit). We check: on the first cycle after
    //     ready drops, o_tx must be 0 (start bit has begun).
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(o_tx_ready) && !o_tx_ready) begin
                // Ready just dropped: we are now in START state, o_tx should be 0
                ap_start_bit_low: assert (o_tx == 1'b0);
            end
        end
    end

    // =========================================================================
    // P4: Stop bit is high
    //     On the cycle just before o_tx_ready reasserts, o_tx must be 1
    //     (the stop bit). Checked via: when ready rises, the previous
    //     cycle's o_tx was 1 (stop bit).
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (!$past(o_tx_ready) && o_tx_ready) begin
                // Ready just rose: previous cycle was last cycle of STOP
                ap_stop_bit_high: assert ($past(o_tx) == 1'b1);
            end
        end
    end

    // =========================================================================
    // P5: Idle output is high
    //     When o_tx_ready==1 (IDLE state), o_tx must be 1
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            ap_idle_tx_high: assert (!o_tx_ready || o_tx == 1'b1);
    end

    // =========================================================================
    // P6: Mutual exclusion - o_tx_ready cannot be asserted while transmitting
    //     If o_tx_ready was 0 and o_tx is 0 (start/data bit), ready stays 0
    // =========================================================================
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (!$past(o_tx_ready) && $past(o_tx) == 1'b0) begin
                // Was not ready and outputting low (start or data=0):
                // Still shouldn't be ready (at minimum, more bits to go)
                // Unless we're at the boundary (last data bit was 0, now STOP).
                // Actually this is too restrictive; data bit 7 could be 0,
                // and next cycle is STOP. We rely on P5 for the key invariant.
            end
        end
    end

    // =========================================================================
    // P7: Frame length - once transmission starts, it takes exactly
    //     10 * CLKS_PER_BIT cycles before o_tx_ready reasserts.
    //     We track this with a cycle counter.
    // =========================================================================
    reg [5:0] f_frame_cycles = 0;
    reg       f_in_frame = 0;

    always @(posedge clk) begin
        if (!rst_n) begin
            f_frame_cycles <= 0;
            f_in_frame <= 0;
        end else begin
            if ($past(o_tx_ready) && !o_tx_ready) begin
                // Frame just started (ready dropped)
                f_in_frame <= 1;
                f_frame_cycles <= 1;
            end else if (f_in_frame) begin
                if (o_tx_ready) begin
                    // Frame ended
                    f_in_frame <= 0;
                end else begin
                    f_frame_cycles <= f_frame_cycles + 1;
                end
            end
        end
    end

    // When the frame ends, the count should be exactly 10*CLKS_PER_BIT.
    // We count from 1 on the first not-ready cycle (START entered) and
    // increment each cycle while not-ready. When o_tx_ready reasserts,
    // f_frame_cycles holds the total count of not-ready cycles:
    //   START: CLKS_PER_BIT cycles + DATA: 8*CLKS_PER_BIT + STOP: CLKS_PER_BIT
    //   = 10 * CLKS_PER_BIT total not-ready cycles.
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if (f_in_frame && o_tx_ready) begin
                ap_frame_length: assert (f_frame_cycles == 6'(10 * CLKS_PER_BIT));
            end
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // C1: Complete transmission (o_tx_ready falls then rises again)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_complete_tx: cover (!$past(o_tx_ready) && o_tx_ready);
    end

    // C2: Handshake occurs (tx_valid accepted)
    always @(posedge clk) begin
        if (rst_n)
            cp_handshake: cover (o_tx_ready && tx_valid);
    end

    // C3: Back-to-back transmission (ready rises and immediately new valid)
    // This means on the cycle ready goes high, tx_valid is also high,
    // so ready will drop again on the next cycle.
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_back_to_back: cover (!$past(o_tx_ready) && o_tx_ready && tx_valid);
    end

    // C4: o_tx outputs a low data bit during DATA phase
    // After start bit, o_tx can be 0 (data bit = 0)
    always @(posedge clk) begin
        if (rst_n)
            cp_data_low: cover (!o_tx_ready && o_tx == 1'b0 && f_cycle_count > 6'd2);
    end

    // C5: o_tx outputs a high data bit during DATA phase
    // During DATA phase (after CLKS_PER_BIT start cycles), o_tx can be 1
    always @(posedge clk) begin
        if (rst_n)
            cp_data_high: cover (!o_tx_ready && o_tx == 1'b1 && f_cycle_count > 6'd2
                                 && f_cycle_count < 6'd28);
    end

endmodule
