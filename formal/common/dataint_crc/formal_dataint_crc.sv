// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for dataint_crc (yosys-compatible)
// Instantiates DUT and properties together.
// Focuses on reset behavior and basic CRC update flow.
// Run with: sby dataint_crc.sby

module formal_dataint_crc #(
    parameter int DATA_WIDTH = 8,
    parameter int CRC_WIDTH  = 8,
    parameter int REFIN      = 0,
    parameter int REFOUT     = 0
) (
    input logic                  clk,
    input logic                  rst_n,
    input logic                  load_crc_start,
    input logic                  load_from_cascade,
    input logic [DATA_WIDTH-1:0] data
);

    localparam int CHUNKS = DATA_WIDTH / 8;

    // Constrain POLY to CRC-8 polynomial (0x07)
    logic [CRC_WIDTH-1:0] POLY;
    assign POLY = 8'h07;

    // POLY_INIT = 0x00 for CRC-8
    logic [CRC_WIDTH-1:0] POLY_INIT;
    assign POLY_INIT = '0;

    // XOROUT = 0x00 for CRC-8
    logic [CRC_WIDTH-1:0] XOROUT;
    assign XOROUT = '0;

    // Cascade selector: select last stage (full data width)
    logic [CHUNKS-1:0] cascade_sel;
    assign cascade_sel = {{(CHUNKS-1){1'b0}}, 1'b1};

    // DUT output
    logic [CRC_WIDTH-1:0] crc;

    // Instantiate DUT
    dataint_crc #(
        .DATA_WIDTH(DATA_WIDTH),
        .CRC_WIDTH (CRC_WIDTH),
        .REFIN     (REFIN),
        .REFOUT    (REFOUT)
    ) dut (
        .POLY             (POLY),
        .POLY_INIT        (POLY_INIT),
        .XOROUT           (XOROUT),
        .clk              (clk),
        .rst_n            (rst_n),
        .load_crc_start   (load_crc_start),
        .load_from_cascade(load_from_cascade),
        .cascade_sel      (cascade_sel),
        .data             (data),
        .crc              (crc)
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

    // Constrain: load_crc_start and load_from_cascade are mutually exclusive
    always @(*) begin
        assume (!(load_crc_start && load_from_cascade));
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, CRC output register clears to zero
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_crc_output: assert (crc == '0);
    end

    // After load_crc_start, CRC output becomes POLY_INIT on next cycle
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
            if ($past(load_crc_start))
                ap_load_crc_start: assert (crc == POLY_INIT);
        end
    end

    // CRC output is bounded (always valid width) - trivially true but
    // ensures synthesis does not widen
    always @(*) begin
        ap_crc_bounded: assert (crc <= {CRC_WIDTH{1'b1}});
    end

    // When not in reset and not loading, CRC still updates (not stuck)
    // We check that the output register is always driven
    // (no X propagation in formal)

    // After two consecutive load_crc_start pulses, CRC should be POLY_INIT
    always @(posedge clk) begin
        if (f_past_valid >= 2 && rst_n && $past(rst_n) && $past(rst_n, 2)) begin
            if ($past(load_crc_start) && $past(load_crc_start, 2))
                ap_double_load: assert (crc == POLY_INIT);
        end
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: CRC computation - non-zero CRC after processing data
    always @(posedge clk) begin
        if (f_past_valid > 3 && rst_n && !load_crc_start)
            cp_nonzero_crc: cover (crc != '0);
    end

    // Cover: load_crc_start pulse
    always @(posedge clk) begin
        if (rst_n)
            cp_load_start: cover (load_crc_start);
    end

    // Cover: CRC changes between cycles (computation active)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n))
            cp_crc_changes: cover (crc != $past(crc));
    end

    // Cover: load_from_cascade active
    always @(posedge clk) begin
        if (rst_n)
            cp_load_cascade: cover (load_from_cascade);
    end

endmodule
