`timescale 1ns / 1ps

// Generic CRC Block
module dataint_crc #(
    parameter ALGO_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int DATA_WIDTH = 64,  // Adjustable data width
    parameter int CHUNKS = DATA_WIDTH / 8,
    parameter int CRC_WIDTH = 64,  // CRC polynomial width
    parameter logic [CRC_WIDTH-1:0] POLY = 64'h42F0E1EBA9EA3693,
    parameter logic [CRC_WIDTH-1:0] POLY_INIT = 64'hFFFFFFFFFFFFFFFF,
    parameter int REFIN = 1,
    parameter int REFOUT = 1,
    parameter logic [CRC_WIDTH-1:0] XOROUT = 64'hFFFFFFFFFFFFFFFF
) (
    input  logic                  i_clk,
    i_rst_n,
    input  logic                  i_load_crc_start,
    input  logic                  i_load_from_cascade,
    input  logic [    CHUNKS-1:0] i_cascade_sel,        // one hot encoded
    input  logic [DATA_WIDTH-1:0] i_data,
    output logic [ CRC_WIDTH-1:0] o_crc
);
    localparam int CW = CRC_WIDTH;
    localparam int DW = DATA_WIDTH;
    localparam int CH = CHUNKS;

    logic [CW-1:0] r_crc_value = POLY_INIT;
    logic [CW-1:0] w_poly = POLY;
    logic [7:0] w_block_data[0:CH-1];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [CW-1:0] w_cascade[0:CH-1];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [CW-1:0] w_result, w_result_xor, w_selected_cascade_output;

    ////////////////////////////////////////////////////////////////////////////
    // Reflect input data if REFIN is enabled
    genvar i, j, idx;
    generate
        if (REFIN) begin : gen_reflect_inputs
            for (genvar i = 0; i < CH; i++) begin : gen_ch_reflect
                for (genvar j = 0; j < 8; j++) begin : gen_bit_reflect
                    assign w_block_data[i][j] = i_data[i*8+7-j];
                end
            end
        end else begin : gen_direct_assign_inputs
            for (genvar i = 0; i < CH; i++) begin : gen_ch_direct
                assign w_block_data[i] = i_data[i*8+:8];
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////
    // Select the correct drop off point for the cascade depending on the length of data
    always_comb begin
        w_selected_cascade_output = POLY_INIT;  // Default to initial value
        for (int i = 0; i < CH; i++) begin
            if (i_cascade_sel[i]) begin
                w_selected_cascade_output = w_cascade[i];
            end
        end
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n) r_crc_value <= 'b0;
        else if (i_load_crc_start) r_crc_value <= POLY_INIT;  // Reset the CRC to the initial value
        else if (i_load_from_cascade)
            r_crc_value <= w_selected_cascade_output;  // Use pre-selected output
    end

    ////////////////////////////////////////////////////////////////////////////
    // Generate dataint_xor_shift_cascades dynamically based on DATA_WIDTH
    generate
        for (i = 0; i < CH; i++) begin : gen_xor_shift_cascade
            if (i == 0) begin : gen_xor_cascade_0
                dataint_crc_xor_shift_cascade #(
                    .CRC_WIDTH(CRC_WIDTH)
                ) dataint_crc_xor_shift_cascade_0 (
                    .i_block_input(r_crc_value),
                    .i_poly(w_poly),
                    .i_data_input(w_block_data[i]),
                    .ow_block_output(w_cascade[i])
                );
            end else begin : gen_xor_cascade_N
                dataint_crc_xor_shift_cascade #(
                    .CRC_WIDTH(CRC_WIDTH)
                ) dataint_crc_xor_shift_cascade_N (
                    .i_block_input(w_cascade[i-1]),
                    .i_poly(w_poly),
                    .i_data_input(w_block_data[i]),
                    .ow_block_output(w_cascade[i])
                );
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////
    // CRC logic, reflections, and output muxing as before, adjusted for new generate blocks
    generate
        if (REFOUT == 1) begin : gen_reflect_result
            for (idx = 0; idx < CW; idx = idx + 1) assign w_result[idx] = r_crc_value[(CW-1)-idx];
        end else assign w_result = r_crc_value;
    endgenerate

    // The final xor'd output
    assign w_result_xor = w_result ^ XOROUT;

    ////////////////////////////////////////////////////////////////////////////
    // flop the output path
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n) o_crc <= 'b0;
        else if (i_load_crc_start) o_crc <= POLY_INIT;  // Reset the CRC to the initial value
        else o_crc <= w_result_xor;
    end

    /////////////////////////////////////////////////////////////////////////
    // error checking
    // synopsys translate_off
    // Generate a version of the memory for waveforms
    logic [(CH*8)-1:0] flat_w_block_data;
    generate
        for (i = 0; i < CH; i++) begin : gen_flatten_w_block_data
            assign flat_w_block_data[i*8+:8] = w_block_data[i];
        end
    endgenerate

    logic [(CW*CH)-1:0] flat_w_cascade;
    generate
        for (i = 0; i < CH; i++) begin : gen_flatten_w_cascade
            assign flat_w_cascade[i*CW+:CW] = w_cascade[i];
        end
    endgenerate

endmodule : dataint_crc
