`timescale 1ns / 1ps

// Generic CRC Block
// ------------------------------------------------------------------------------------------
// |     Algorithm      | CRC_WIDTH |    Poly    |    Init    | RefIn | RefOut |   XorOut   |
// |--------------------|-----------|------------|------------|-------|--------|------------|
// | CRC-8              |         8 | 0x07       | 0x00       |     0 |      0 | 0x00       |
// | CRC-8/CDMA2000     |         8 | 0x9B       | 0xFF       |     0 |      0 | 0x00       |
// | CRC-8/DARC         |         8 | 0x39       | 0x00       |     1 |      1 | 0x00       |
// | CRC-8/DVB-S2       |         8 | 0xD5       | 0x00       |     0 |      0 | 0x00       |
// | CRC-8/EBU          |         8 | 0x1D       | 0xFF       |     1 |      1 | 0x00       |
// | CRC-8/I-CODE       |         8 | 0x1D       | 0xFD       |     0 |      0 | 0x00       |
// | CRC-8/ITU          |         8 | 0x07       | 0x00       |     0 |      0 | 0x55       |
// | CRC-8/MAXIM        |         8 | 0x31       | 0x00       |     1 |      1 | 0x00       |
// | CRC-8/ROHC         |         8 | 0x07       | 0xFF       |     1 |      1 | 0x00       |
// | CRC-8/WCDMA        |         8 | 0x9B       | 0x00       |     1 |      1 | 0x00       |
// ------------------------------------------------------------------------------------------
// | CRC-16/ARC         |        16 | 0x8005     | 0x0000     |     1 |      1 | 0x0000     |
// | CRC-16/AUG-CCITT   |        16 | 0x1021     | 0x1D0F     |     0 |      0 | 0x0000     |
// | CRC-16/BUYPASS     |        16 | 0x8005     | 0x0000     |     0 |      0 | 0x0000     |
// | CRC-16/CCITT-FALSE |        16 | 0x1021     | 0xFFFF     |     0 |      0 | 0x0000     |
// | CRC-16/CDMA2000    |        16 | 0xC867     | 0xFFFF     |     0 |      0 | 0x0000     |
// | CRC-16/DDS-110     |        16 | 0x8005     | 0x800D     |     0 |      0 | 0x0000     |
// | CRC-16/DECT-R      |        16 | 0x0589     | 0x0000     |     0 |      0 | 0x0001     |
// | CRC-16/DECT-X      |        16 | 0x0589     | 0x0000     |     0 |      0 | 0x0000     |
// | CRC-16/DNP         |        16 | 0x3D65     | 0x0000     |     1 |      1 | 0xFFFF     |
// | CRC-16/EN-13757    |        16 | 0x3D65     | 0x0000     |     0 |      0 | 0xFFFF     |
// | CRC-16/GENIBUS     |        16 | 0x1021     | 0xFFFF     |     0 |      0 | 0xFFFF     |
// | CRC-16/KERMIT      |        16 | 0x1021     | 0x0000     |     1 |      1 | 0x0000     |
// | CRC-16/MAXIM       |        16 | 0x8005     | 0x0000     |     1 |      1 | 0xFFFF     |
// | CRC-16/MCRF4XX     |        16 | 0x1021     | 0xFFFF     |     1 |      1 | 0x0000     |
// | CRC-16/MODBUS      |        16 | 0x8005     | 0xFFFF     |     1 |      1 | 0x0000     |
// | CRC-16/RIELLO      |        16 | 0x1021     | 0xB2AA     |     1 |      1 | 0x0000     |
// | CRC-16/T10-DIF     |        16 | 0x8BB7     | 0x0000     |     0 |      0 | 0x0000     |
// | CRC-16/TELEDISK    |        16 | 0xA097     | 0x0000     |     0 |      0 | 0x0000     |
// | CRC-16/TMS37157    |        16 | 0x1021     | 0x89EC     |     1 |      1 | 0x0000     |
// | CRC-16/USB         |        16 | 0x8005     | 0xFFFF     |     1 |      1 | 0xFFFF     |
// | CRC-16/X-25        |        16 | 0x1021     | 0xFFFF     |     1 |      1 | 0xFFFF     |
// | CRC-16/XMODEM      |        16 | 0x1021     | 0x0000     |     0 |      0 | 0x0000     |
// | CRC-A              |        16 | 0x1021     | 0xC6C6     |     1 |      1 | 0x0000     |
// ------------------------------------------------------------------------------------------
// | CRC-32             |        32 | 0x04C11DB7 | 0xFFFFFFFF |     1 |      1 | 0xFFFFFFFF |
// | CRC-32/BZIP2       |        32 | 0x04C11DB7 | 0xFFFFFFFF |     0 |      0 | 0xFFFFFFFF |
// | CRC-32/JAMCRC      |        32 | 0x04C11DB7 | 0xFFFFFFFF |     1 |      1 | 0x00000000 |
// | CRC-32/MPEG-2      |        32 | 0x04C11DB7 | 0xFFFFFFFF |     0 |      0 | 0x00000000 |
// | CRC-32/POSIX       |        32 | 0x04C11DB7 | 0x00000000 |     0 |      0 | 0xFFFFFFFF |
// | CRC-32/SATA        |        32 | 0x04C11DB7 | 0x52325032 |     0 |      0 | 0x00000000 |
// | CRC-32/XFER        |        32 | 0x000000AF | 0x00000000 |     0 |      0 | 0x00000000 |
// | CRC-32C            |        32 | 0x1EDC6F41 | 0xFFFFFFFF |     1 |      1 | 0xFFFFFFFF |
// | CRC-32D            |        32 | 0xA833982B | 0xFFFFFFFF |     1 |      1 | 0xFFFFFFFF |
// | CRC-32Q            |        32 | 0x814141AB | 0x00000000 |     0 |      0 | 0x00000000 |
// ------------------------------------------------------------------------------------------

module dataint_crc #(
    parameter int                      DATA_WIDTH = 32,  // Adjustable data width
    parameter int                      CHUNKS = DATA_WIDTH / 8,
    parameter int                      CRC_WIDTH = 32,   // CRC polynomial width
    parameter logic [CRC_WIDTH-1:0]    POLY = 32'h04C11DB7,
    parameter logic [CRC_WIDTH-1:0]    POLY_INIT = 32'hFFFFFFFF,
    parameter int                      REFIN = 1,
    parameter int                      REFOUT = 1,
    parameter logic [CRC_WIDTH-1:0]    XOROUT = 32'hFFFFFFFF
)(
    input  logic                       i_clk, i_rst_n,
    input  logic                       i_load_crc_start,
    input  logic                       i_load_from_cascade,
    input  logic [CHUNKS-1:0]          i_cascade_sel, // one hot encoded
    input  logic [DATA_WIDTH-1:0]      i_data,
    output logic [CRC_WIDTH-1:0]       o_crc
);
    localparam int CW = CRC_WIDTH;
    localparam int DW = DATA_WIDTH;
    localparam int CH = CHUNKS;

    logic [CW-1:0] r_crc_value = POLY_INIT;
    logic [CW-1:0] w_poly = POLY;
    logic [7:0]    w_block_data [0:CH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [CW-1:0] w_cascade    [0:CH-1]; // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [CW-1:0] w_result, w_result_xor, w_selected_cascade_output, xor_output;

    assign xor_output = XOROUT;

    ////////////////////////////////////////////////////////////////////////////
    // Reflect input data if REFIN is enabled
    generate
    genvar i, j, idx;
    if (REFIN) begin : gen_reflect_inputs
        for(i = 0; i < CH; i = i + 1)
            for(j = 0; j < 8; j = j + 1)
                assign w_block_data[i][j] = i_data[i*8+7-j];
    end else begin : gen_direct_assign_inputs
        for(i = 0; i < CH; i = i + 1)
            assign w_block_data[i] = i_data[i*8+:8];
    end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////
    // Select the correct drop off point for the cascade depending on the length of data
    always_comb begin
        w_selected_cascade_output = POLY_INIT; // Default to initial value
        for (int i = 0; i < CH; i++) begin
            if (i_cascade_sel[i]) begin
                w_selected_cascade_output = w_cascade[i];
            end
        end
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n)
            r_crc_value <= 'b0;
        else if (i_load_crc_start)
            r_crc_value <= POLY_INIT;  // Reset the CRC to the initial value
        else if (i_load_from_cascade)
            r_crc_value <= w_selected_cascade_output; // Use pre-selected output
    end

    ////////////////////////////////////////////////////////////////////////////
    // Generate dataint_xor_shift_cascades dynamically based on DATA_WIDTH
    generate
        for (i = 0; i < CH; i = i + 1) begin : gen_xor_shift_cascade
            if (i==0) begin : gen_xor_cascade_0
                dataint_crc_xor_shift_cascade #(.CRC_WIDTH(CRC_WIDTH))
                dataint_crc_xor_shift_cascade_0 (
                    .i_block_input(r_crc_value),
                    .i_poly(w_poly),
                    .i_data_input(w_block_data[i]),
                    .ow_block_output(w_cascade[i])
                );
            end else begin : gen_xor_cascade_N
                dataint_crc_xor_shift_cascade #(.CRC_WIDTH(CRC_WIDTH))
                dataint_crc_xor_shift_cascade_N (
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
    generate if (REFOUT == 1) begin : gen_reflect_result
        for(idx = 0; idx < CW; idx = idx + 1)
            assign w_result[idx] = r_crc_value[(CW-1)-idx];
        end else
            assign w_result = r_crc_value;
    endgenerate

    // The final xor'd output
    assign w_result_xor = w_result ^ xor_output;

    ////////////////////////////////////////////////////////////////////////////
    // flop the output path
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n)
            o_crc <= 'b0;
        else if (i_load_crc_start)
            o_crc <= POLY_INIT;  // Reset the CRC to the initial value
        else
            o_crc <= w_result_xor;
    end

    /////////////////////////////////////////////////////////////////////////
    // error checking
    // synopsys translate_off
    // Generate a version of the memory for waveforms
    logic [(CH*8)-1:0] flat_w_block_data;
    generate
        for (i = 0; i < CH; i = i + 1) begin : gen_flatten_w_block_data
            assign flat_w_block_data[i*8+:8] = w_block_data[i];
        end
    endgenerate

    logic [(CW*CH)-1:0] flat_w_cascade;
    generate
        for (i = 0; i < CH; i = i + 1) begin : gen_flatten_w_cascade
            assign flat_w_cascade[i*CW+:CW] = w_cascade[i];
        end
    endgenerate

    // synopsys translate_off
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, dataint_crc);
    end
    // synopsys translate_on

endmodule : dataint_crc
