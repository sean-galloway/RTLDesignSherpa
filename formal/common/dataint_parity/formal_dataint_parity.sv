// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for dataint_parity (yosys-compatible)

module formal_dataint_parity #(
    parameter int CHUNKS    = 4,
    parameter int WIDTH     = 32,
    parameter int CHUNKSIZE = WIDTH / CHUNKS
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0]  data_in;
    (* anyconst *) logic [CHUNKS-1:0] parity_in;
    (* anyconst *) logic              parity_type;

    logic [CHUNKS-1:0] parity;
    logic [CHUNKS-1:0] parity_err;

    dataint_parity #(.CHUNKS(CHUNKS), .WIDTH(WIDTH)) dut (
        .data_in    (data_in),
        .parity_in  (parity_in),
        .parity_type(parity_type),
        .parity     (parity),
        .parity_err (parity_err)
    );

    // Compute reference parity for each chunk
    wire [CHUNKS-1:0] ref_parity;
    generate
        genvar i;
        for (i = 0; i < CHUNKS; i++) begin : gen_ref
            localparam int LO = i * CHUNKSIZE;
            localparam int HI = (i < CHUNKS - 1) ? ((i + 1) * CHUNKSIZE) - 1 : WIDTH - 1;
            // Even parity: XOR of chunk bits. Odd parity: inverted.
            assign ref_parity[i] = parity_type ? ^data_in[HI:LO] : ~^data_in[HI:LO];
        end
    endgenerate

    // Parity output matches reference for each chunk
    always @(posedge clk)
        ap_parity_correct: assert (parity == ref_parity);

    // When parity_in matches computed parity, no errors
    always @(posedge clk)
        if (parity_in == parity)
            ap_no_error: assert (parity_err == '0);

    // When parity_in differs from computed parity, error bits are set correctly
    generate
        for (i = 0; i < CHUNKS; i++) begin : gen_err_check
            always @(posedge clk)
                assert (parity_err[i] == (parity[i] != parity_in[i]));
        end
    endgenerate

    // Error detected iff parity mismatch
    always @(posedge clk)
        ap_err_iff_mismatch: assert (parity_err == (parity ^ parity_in));

    // Cover: no errors (parity_in matches)
    always @(posedge clk)
        cp_no_errors: cover (parity_err == '0);

    // Cover: single chunk error
    always @(posedge clk)
        cp_single_error: cover ($onehot(parity_err));

    // Cover: all chunks have errors
    always @(posedge clk)
        cp_all_errors: cover (&parity_err);

    // Cover: even parity mode
    always @(posedge clk)
        cp_even_parity: cover (parity_type == 1'b1 && parity_err == '0);

    // Cover: odd parity mode
    always @(posedge clk)
        cp_odd_parity: cover (parity_type == 1'b0 && parity_err == '0);

endmodule
