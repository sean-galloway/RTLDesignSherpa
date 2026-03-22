// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for ECC Hamming SECDED encode-decode roundtrip (yosys-compatible)
// Proves: encode then decode recovers original data, no error flags on clean path.

module formal_ecc_roundtrip #(
    parameter int WIDTH = 4
) (
    input  logic clk,
    input  logic rst_n
);

    // =========================================================================
    // Derived parameters (must match encoder/decoder)
    // =========================================================================
    localparam int ParityBits = $clog2(WIDTH + $clog2(WIDTH) + 1);
    localparam int TotalWidth = WIDTH + ParityBits + 1;

    // =========================================================================
    // Unconstrained data input (held constant across all cycles)
    // =========================================================================
    (* anyconst *) logic [WIDTH-1:0] data_in;

    // =========================================================================
    // Encoder (combinational)
    // =========================================================================
    logic [TotalWidth-1:0] encoded;

    dataint_ecc_hamming_encode_secded #(
        .WIDTH(WIDTH),
        .DEBUG(0)
    ) u_enc (
        .data         (data_in),
        .encoded_data (encoded)
    );

    // =========================================================================
    // Decoder (registered, 1-cycle latency)
    // =========================================================================
    logic [WIDTH-1:0] decoded_data;
    logic             error_detected;
    logic             double_error_detected;

    dataint_ecc_hamming_decode_secded #(
        .WIDTH(WIDTH),
        .DEBUG(0)
    ) u_dec (
        .clk                  (clk),
        .rst_n                (rst_n),
        .enable               (1'b1),
        .hamming_data         (encoded),
        .data                 (decoded_data),
        .error_detected       (error_detected),
        .double_error_detected(double_error_detected)
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
    // Safety properties
    // =========================================================================

    // After reset, decoder outputs are zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_data:   assert (decoded_data == '0);
            ap_reset_err:    assert (!error_detected);
            ap_reset_dbl:    assert (!double_error_detected);
        end
    end

    // Roundtrip: after 1 cycle of normal operation, decoded data matches input
    // The decoder registers its output, so we need f_past_valid >= 3
    // (cycle 0: reset asserted, cycle 1: reset asserted, cycle 2: reset deasserted,
    //  cycle 3: first valid decode output)
    always @(posedge clk) begin
        if (f_past_valid >= 3 && rst_n && $past(rst_n))
            ap_roundtrip: assert (decoded_data == data_in);
    end

    // No error flags for clean (unmodified) codewords
    always @(posedge clk) begin
        if (f_past_valid >= 3 && rst_n && $past(rst_n)) begin
            ap_no_error:     assert (!error_detected);
            ap_no_dbl_error: assert (!double_error_detected);
        end
    end

    // SECDED parity bit (MSB) is XOR of all lower bits
    always @(posedge clk) begin
        if (rst_n)
            ap_secded_parity: assert (encoded[TotalWidth-1] == ^encoded[TotalWidth-2:0]);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover the roundtrip for all-zeros data
    always @(posedge clk) begin
        if (rst_n)
            cp_zero_data: cover (decoded_data == '0 && data_in == '0 && !error_detected);
    end

    // Cover the roundtrip for all-ones data
    always @(posedge clk) begin
        if (rst_n)
            cp_ones_data: cover (decoded_data == {WIDTH{1'b1}} && data_in == {WIDTH{1'b1}});
    end

    // Cover successful decode (non-zero data matches)
    always @(posedge clk) begin
        if (f_past_valid >= 3 && rst_n)
            cp_roundtrip_ok: cover (decoded_data == data_in && data_in != '0);
    end

endmodule
