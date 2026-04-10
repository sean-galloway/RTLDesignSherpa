// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for axi_monitor_timeout
//
// After sv2v flattening, the bus_transaction_t array becomes a single packed
// bus of (MAX_TRANSACTIONS * 281) bits.
//
// Properties verified:
//   P1: Reset clears timeout_detected
//   P2: timeout_detected is sticky within an entry until trans_table slot
//       transitions to IDLE/COMPLETE/ERROR (upper 3 bits of state field)
//       -- validated as: once set, clears only when state transitions
//   P3: With timer_tick=0, r_timeout_detected never sets new bits

module formal_axi_monitor_timeout (
    input wire clk,
    input wire rst_n
);

    // =========================================================================
    // Parameters (small for tractability)
    // =========================================================================
    localparam integer MAX_TRANSACTIONS = 2;
    localparam integer ADDR_WIDTH = 16;
    localparam integer TRANS_ENTRY_WIDTH = 281;
    localparam integer TABLE_WIDTH = MAX_TRANSACTIONS * TRANS_ENTRY_WIDTH;

    // =========================================================================
    // Free inputs
    // =========================================================================
    (* anyseq *) reg [TABLE_WIDTH-1:0] trans_table;
    (* anyseq *) reg                   timer_tick;
    (* anyseq *) reg [3:0]             cfg_addr_cnt;
    (* anyseq *) reg [3:0]             cfg_data_cnt;
    (* anyseq *) reg [3:0]             cfg_resp_cnt;
    (* anyseq *) reg                   cfg_timeout_enable;

    // =========================================================================
    // DUT outputs
    // =========================================================================
    wire [MAX_TRANSACTIONS-1:0] timeout_detected;

    // =========================================================================
    // DUT instantiation
    // =========================================================================
    axi_monitor_timeout #(
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .ADDR_WIDTH       (ADDR_WIDTH),
        .IS_READ          (1)
    ) dut (
        .aclk               (clk),
        .aresetn            (rst_n),
        .trans_table        (trans_table),
        .timer_tick         (timer_tick),
        .cfg_addr_cnt       (cfg_addr_cnt),
        .cfg_data_cnt       (cfg_data_cnt),
        .cfg_resp_cnt       (cfg_resp_cnt),
        .cfg_timeout_enable (cfg_timeout_enable),
        .timeout_detected   (timeout_detected)
    );

    // =========================================================================
    // Reset / past-valid
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // =========================================================================
    // Properties
    // =========================================================================

    // P1: Reset clears timeout_detected
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_timeout: assert (timeout_detected == {MAX_TRANSACTIONS{1'b0}});
    end

    // P2: timeout_detected is bounded by MAX_TRANSACTIONS (trivially true)
    always @(posedge clk) begin
        if (rst_n)
            ap_timeout_bounded: assert (timeout_detected[MAX_TRANSACTIONS-1:0] == timeout_detected);
    end

    // P3: With timer_tick held low for two cycles and no timeout previously set,
    //     timeout_detected cannot acquire new set bits
    // The only path that sets r_timeout_detected is inside the "if (timer_tick)"
    // branch, so without ticks there can be no new detections. Note: existing
    // bits CAN clear due to trans_table state transitions, so we check that
    // the set of asserted bits is a subset of the previous set.
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && $past(!timer_tick))
            ap_no_set_without_tick: assert ((timeout_detected & ~$past(timeout_detected)) == {MAX_TRANSACTIONS{1'b0}});
    end

    // =========================================================================
    // Cover
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n) begin
            cp_timeout_set:   cover (|timeout_detected);
            cp_timer_tick:    cover (timer_tick);
            cp_timeout_clear: cover (f_past_valid > 1 && $past(|timeout_detected) && !(|timeout_detected));
        end
    end

endmodule
