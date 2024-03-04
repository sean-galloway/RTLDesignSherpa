`timescale 1ns / 1ps

// Generic CRC Block

// ------------------------------------------------------------------------------------------------------------------------
// |     Algorithm      | CRC_WIDTH |         POLY         |      POLY_INIT       | REFIN | REFOUT |        XOROUT        |
// |--------------------|-----------|----------------------|----------------------|-------|--------|----------------------|
// | CRC-8              |         8 | 8'h07                | 8'h00                |     0 |      0 | 8'h00                |
// | CRC-8_CDMA2000     |         8 | 8'h9B                | 8'hFF                |     0 |      0 | 8'h00                |
// | CRC-8_DARC         |         8 | 8'h39                | 8'h00                |     1 |      1 | 8'h00                |
// | CRC-8_DVB-S2       |         8 | 8'hD5                | 8'h00                |     0 |      0 | 8'h00                |
// | CRC-8_EBU          |         8 | 8'h1D                | 8'hFF                |     1 |      1 | 8'h00                |
// | CRC-8_I-CODE       |         8 | 8'h1D                | 8'hFD                |     0 |      0 | 8'h00                |
// | CRC-8_ITU          |         8 | 8'h07                | 8'h00                |     0 |      0 | 8'h55                |
// | CRC-8_MAXIM        |         8 | 8'h31                | 8'h00                |     1 |      1 | 8'h00                |
// | CRC-8_ROHC         |         8 | 8'h07                | 8'hFF                |     1 |      1 | 8'h00                |
// | CRC-8_WCDMA        |         8 | 8'h9B                | 8'h00                |     1 |      1 | 8'h00                |
// ------------------------------------------------------------------------------------------------------------------------
// | CRC-16_ARC         |        16 | 16'h8005             | 16'h0000             |     1 |      1 | 16'h0000             |
// | CRC-16_AUG-CCITT   |        16 | 16'h1021             | 16'h1D0F             |     0 |      0 | 16'h0000             |
// | CRC-16_BUYPASS     |        16 | 16'h8005             | 16'h0000             |     0 |      0 | 16'h0000             |
// | CRC-16_CCITT-FALSE |        16 | 16'h1021             | 16'hFFFF             |     0 |      0 | 16'h0000             |
// | CRC-16_CDMA2000    |        16 | 16'hC867             | 16'hFFFF             |     0 |      0 | 16'h0000             |
// | CRC-16_DDS-110     |        16 | 16'h8005             | 16'h800D             |     0 |      0 | 16'h0000             |
// | CRC-16_DECT-R      |        16 | 16'h0589             | 16'h0000             |     0 |      0 | 16'h0001             |
// | CRC-16_DECT-X      |        16 | 16'h0589             | 16'h0000             |     0 |      0 | 16'h0000             |
// | CRC-16_DNP         |        16 | 16'h3D65             | 16'h0000             |     1 |      1 | 16'hFFFF             |
// | CRC-16_EN-13757    |        16 | 16'h3D65             | 16'h0000             |     0 |      0 | 16'hFFFF             |
// | CRC-16_GENIBUS     |        16 | 16'h1021             | 16'hFFFF             |     0 |      0 | 16'hFFFF             |
// | CRC-16_KERMIT      |        16 | 16'h1021             | 16'h0000             |     1 |      1 | 16'h0000             |
// | CRC-16_MAXIM       |        16 | 16'h8005             | 16'h0000             |     1 |      1 | 16'hFFFF             |
// | CRC-16_MCRF4XX     |        16 | 16'h1021             | 16'hFFFF             |     1 |      1 | 16'h0000             |
// | CRC-16_MODBUS      |        16 | 16'h8005             | 16'hFFFF             |     1 |      1 | 16'h0000             |
// | CRC-16_RIELLO      |        16 | 16'h1021             | 16'hB2AA             |     1 |      1 | 16'h0000             |
// | CRC-16_T10-DIF     |        16 | 16'h8BB7             | 16'h0000             |     0 |      0 | 16'h0000             |
// | CRC-16_TELEDISK    |        16 | 16'hA097             | 16'h0000             |     0 |      0 | 16'h0000             |
// | CRC-16_TMS37157    |        16 | 16'h1021             | 16'h89EC             |     1 |      1 | 16'h0000             |
// | CRC-16_USB         |        16 | 16'h8005             | 16'hFFFF             |     1 |      1 | 16'hFFFF             |
// | CRC-16_X-25        |        16 | 16'h1021             | 16'hFFFF             |     1 |      1 | 16'hFFFF             |
// | CRC-16_XMODEM      |        16 | 16'h1021             | 16'h0000             |     0 |      0 | 16'h0000             |
// | CRC-A              |        16 | 16'h1021             | 16'hC6C6             |     1 |      1 | 16'h0000             |
// ------------------------------------------------------------------------------------------------------------------------
// | CRC-32             |        32 | 32'h04C11DB7         | 32'hFFFFFFFF         |     1 |      1 | 32'hFFFFFFFF         |
// | CRC-32_BZIP2       |        32 | 32'h04C11DB7         | 32'hFFFFFFFF         |     0 |      0 | 32'hFFFFFFFF         |
// | CRC-32_JAMCRC      |        32 | 32'h04C11DB7         | 32'hFFFFFFFF         |     1 |      1 | 32'h00000000         |
// | CRC-32_MPEG-2      |        32 | 32'h04C11DB7         | 32'hFFFFFFFF         |     0 |      0 | 32'h00000000         |
// | CRC-32_POSIX       |        32 | 32'h04C11DB7         | 32'h00000000         |     0 |      0 | 32'hFFFFFFFF         |
// | CRC-32_SATA        |        32 | 32'h04C11DB7         | 32'h52325032         |     0 |      0 | 32'h00000000         |
// | CRC-32_XFER        |        32 | 32'h000000AF         | 32'h00000000         |     0 |      0 | 32'h00000000         |
// | CRC-32C            |        32 | 32'h1EDC6F41         | 32'hFFFFFFFF         |     1 |      1 | 32'hFFFFFFFF         |
// | CRC-32D            |        32 | 32'hA833982B         | 32'hFFFFFFFF         |     1 |      1 | 32'hFFFFFFFF         |
// | CRC-32Q            |        32 | 32'h814141AB         | 32'h00000000         |     0 |      0 | 32'h00000000         |
// ------------------------------------------------------------------------------------------------------------------------
// | CRC-40_GSM         |        40 | 40'h4820009          | 40'h0000000000       |     0 |      0 | 40'hFFFFFFFFFF       |
// ------------------------------------------------------------------------------------------------------------------------
// | CRC-64_ECMA-182    |        64 | 64'h42F0E1EBA9EA3693 | 64'h0000000000000000 |     0 |      0 | 64'h0000000000000000 |
// | CRC-64_GO-ISO      |        64 | 64'h000000000000001B | 64'hFFFFFFFFFFFFFFFF |     1 |      1 | 64'hFFFFFFFFFFFFFFFF |
// | CRC-64_MS          |        64 | 64'h259C84CBA6426349 | 64'hFFFFFFFFFFFFFFFF |     1 |      1 | 64'h0000000000000000 |
// | CRC-64_REDIS       |        64 | 64'hAD93D23594C935A9 | 64'h0000000000000000 |     1 |      1 | 64'h0000000000000000 |
// | CRC-64_WE          |        64 | 64'h42F0E1EBA9EA3693 | 64'hFFFFFFFFFFFFFFFF |     0 |      0 | 64'hFFFFFFFFFFFFFFFF |
// | CRC-64_XZ          |        64 | 64'h42F0E1EBA9EA3693 | 64'hFFFFFFFFFFFFFFFF |     1 |      1 | 64'hFFFFFFFFFFFFFFFF |
// ------------------------------------------------------------------------------------------------------------------------

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

    // synopsys translate_off
    initial begin
        $dumpfile("waves.vcd");
        $dumpvars(0, dataint_crc);
    end
    // synopsys translate_on

endmodule : dataint_crc
