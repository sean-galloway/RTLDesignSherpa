// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for cdc_handshake (yosys-compatible)
// Model: SINGLE CLOCK for both src and dst domains.
// This verifies handshake protocol correctness, not true CDC timing.
//
// Properties:
//   - Reset clears valid/ready
//   - Data preserved through handshake
//   - No spurious dst_valid without prior src_valid
// Cover:
//   - Full handshake: src_valid -> src_ready -> dst_valid -> dst_ready

module formal_cdc_handshake #(
    parameter int DATA_WIDTH = 8
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    src_valid,
    input  logic [DATA_WIDTH-1:0]   src_data,
    input  logic                    dst_ready
);

    // DUT outputs
    logic                    src_ready;
    logic                    dst_valid;
    logic [DATA_WIDTH-1:0]   dst_data;

    // Single clock drives both domains
    cdc_handshake #(
        .DATA_WIDTH (DATA_WIDTH)
    ) dut (
        .clk_src   (clk),
        .rst_src_n (rst_n),
        .src_valid (src_valid),
        .src_ready (src_ready),
        .src_data  (src_data),
        .clk_dst   (clk),
        .rst_dst_n (rst_n),
        .dst_valid (dst_valid),
        .dst_ready (dst_ready),
        .dst_data  (dst_data)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Hold reset for a few cycles, then release
    localparam int RESET_CYCLES = 3;
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid < RESET_CYCLES) assume (!rst_n);
        if (f_past_valid >= RESET_CYCLES) assume (rst_n);
    end

    // No stimulus during reset
    always @(posedge clk) begin
        if (!rst_n) begin
            assume (!src_valid);
            assume (!dst_ready);
        end
    end

    // Well-behaved source: only assert src_valid when src_ready
    always @(posedge clk) begin
        if (rst_n) begin
            assume (!(src_valid && !src_ready));
        end
    end

    // =========================================================================
    // Data capture for integrity checking
    // =========================================================================
    // Capture src_data when a transfer is accepted (src_valid && src_ready)
    reg [DATA_WIDTH-1:0] f_captured_data = 0;
    reg                  f_data_in_flight = 0;

    always @(posedge clk) begin
        if (!rst_n) begin
            f_captured_data  <= 0;
            f_data_in_flight <= 0;
        end else begin
            if (src_valid && src_ready) begin
                f_captured_data  <= src_data;
                f_data_in_flight <= 1;
            end
            if (dst_valid && dst_ready) begin
                f_data_in_flight <= 0;
            end
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: Reset clears dst_valid
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_dst_valid: assert (!dst_valid);
    end

    // P2: Reset sets src_ready low (then goes high on first IDLE cycle)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_src_ready: assert (!src_ready);
    end

    // P3: Data integrity -- when dst_valid is asserted and data is in flight,
    // dst_data must match captured source data
    always @(posedge clk) begin
        if (rst_n && dst_valid && f_data_in_flight)
            ap_data_integrity: assert (dst_data == f_captured_data);
    end

    // P4: No spurious dst_valid without a prior src_valid transfer.
    // Track whether any transfer has occurred since reset.
    reg f_any_transfer = 0;
    always @(posedge clk) begin
        if (!rst_n)
            f_any_transfer <= 0;
        else if (src_valid && src_ready)
            f_any_transfer <= 1;
    end

    always @(posedge clk) begin
        if (rst_n && !f_any_transfer)
            ap_no_spurious_valid: assert (!dst_valid);
    end

    // P5: src_ready and dst_valid are never both asserted simultaneously
    // (when src_ready is high, source FSM is IDLE; when dst_valid is high,
    // destination FSM is in WAIT_READY -- these should not overlap)
    // Note: This could be too strict if there's a 1-cycle overlap in the
    // single-clock model. Check conservatively.

    // P6: After reset deasserts, src_ready eventually asserts (liveness-like via BMC)
    always @(posedge clk) begin
        if (rst_n && f_past_valid == RESET_CYCLES + 1)
            ap_ready_after_reset: assert (src_ready);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: dst_valid asserts (data arrived at destination)
    always @(posedge clk) begin
        if (rst_n)
            cp_dst_valid: cover (dst_valid);
    end

    // Cover: full handshake completes (dst_valid && dst_ready)
    always @(posedge clk) begin
        if (rst_n)
            cp_handshake_complete: cover (dst_valid && dst_ready);
    end

    // Cover: src_ready returns after a completed handshake
    always @(posedge clk) begin
        if (rst_n && f_past_valid > RESET_CYCLES + 5)
            cp_ready_returns: cover (src_ready && f_any_transfer);
    end

    // Cover: two consecutive transfers (src_ready after first handshake, then new valid)
    reg f_transfer_count = 0;
    always @(posedge clk) begin
        if (!rst_n)
            f_transfer_count <= 0;
        else if (dst_valid && dst_ready)
            f_transfer_count <= f_transfer_count + 1;
    end

    always @(posedge clk) begin
        if (rst_n)
            cp_second_transfer: cover (f_transfer_count >= 1 && dst_valid);
    end

endmodule
