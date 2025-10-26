// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: dataint_crc
// Purpose: //   Parameterized CRC (Cyclic Redundancy Check) calculator supporting ~300 standard
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: dataint_crc
//==============================================================================
// Description:
//   Parameterized CRC (Cyclic Redundancy Check) calculator supporting ~300 standard
//   CRC algorithms via runtime configuration. Uses cascaded XOR-shift architecture
//   for parallel byte-wise processing. Supports configurable polynomial, initialization
//   value, input/output bit reflection, and final XOR. Critical for data integrity
//   in communication protocols, storage systems, and error detection.
//
// Features:
//   - Supports CRC-8, CRC-16, CRC-32, CRC-64 (any width 8-64 bits)
//   - Runtime programmable polynomial, init, and XOR-out values
//   - Input bit reflection (REFIN) for LSB-first protocols
//   - Output bit reflection (REFOUT) for result formatting
//   - Cascaded architecture for multi-byte parallel processing
//   - Chunk-based computation (processes DATA_WIDTH/8 bytes per cycle)
//   - Variable-length data support via cascade_sel
//   - Registered output for pipelining
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ALGO_NAME:
//     Description: Algorithm name for debug/identification
//     Type: string
//     Default: "DEADF1F0"
//     Constraints: Used for waveform/debug identification only
//
//   DATA_WIDTH:
//     Description: Input data bus width (bits)
//     Type: int
//     Range: 8 to 512 (must be multiple of 8)
//     Default: 64
//     Constraints: DATA_WIDTH = CHUNKS × 8
//
//   CRC_WIDTH:
//     Description: CRC polynomial width (bits)
//     Type: int
//     Range: 8, 16, 32, 64
//     Default: 64
//     Constraints: Common: 8 (CRC-8), 16 (CRC-16), 32 (CRC-32), 64 (CRC-64)
//
//   REFIN:
//     Description: Reflect input data bits (LSB-first protocols)
//     Type: int
//     Range: 0 or 1
//     Default: 1
//     Constraints: 1 = Reverse bit order within each byte, 0 = Direct
//
//   REFOUT:
//     Description: Reflect output CRC bits (result formatting)
//     Type: int
//     Range: 0 or 1
//     Default: 1
//     Constraints: 1 = Reverse CRC bit order, 0 = Direct
//
//   Derived Parameters (localparam - computed automatically):
//     CHUNKS (CH): Number of 8-bit bytes processed per cycle (DATA_WIDTH / 8)
//     CW: Convenience alias for CRC_WIDTH (used in internal signal declarations)
//     DW: Convenience alias for DATA_WIDTH (used in internal signal declarations)
//     CH: Convenience alias for CHUNKS (used in array indexing)
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     POLY[CRC_WIDTH-1:0]:      CRC polynomial (runtime programmable)
//     POLY_INIT[CRC_WIDTH-1:0]: Initial CRC value (seed)
//     XOROUT[CRC_WIDTH-1:0]:    Final XOR mask for output
//     clk:                      Clock input
//     rst_n:                    Asynchronous active-low reset
//     load_crc_start:           Reset CRC to POLY_INIT (start new calc)
//     load_from_cascade:        Load intermediate result from cascade
//     cascade_sel[CHUNKS-1:0]:  One-hot: Select cascade stage (for variable length)
//     data[DATA_WIDTH-1:0]:     Input data to process
//
//   Outputs:
//     crc[CRC_WIDTH-1:0]:       Computed CRC value (registered)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        2 cycles (cascade computation + output register)
//   Throughput:     CHUNKS bytes per cycle
//   Clock-to-Q:     Registered output (1 FF delay)
//   Reset:          Asynchronous (immediate to POLY_INIT)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   CRC Computation Flow:
//   1. Input Reflection (if REFIN=1): Reverse bits within each byte
//   2. Cascade Processing: Each chunk XORs with previous CRC, shifts by 8 bits
//   3. Output Reflection (if REFOUT=1): Reverse all CRC bits
//   4. Final XOR: Result XORed with XOROUT mask
//   5. Register Output: Store result in crc register
//
//   Cascade Architecture:
//   - Stage 0: r_crc_value XOR data[7:0] → w_cascade[0]
//   - Stage 1: w_cascade[0] XOR data[15:8] → w_cascade[1]
//   - Stage N: w_cascade[N-1] XOR data[N*8+7:N*8] → w_cascade[N]
//   - Final: w_cascade[CHUNKS-1] → (reflect) → (XOR) → crc
//
//   Variable-Length Data:
//   - cascade_sel selects which cascade stage contains final result
//   - Example: 3-byte data → cascade_sel = 4'b0100 (select stage 2)
//   - Allows processing 1 to CHUNKS bytes per transaction
//
//   Common CRC Standards (examples):
//   | Algorithm    | Width | POLY       | INIT       | REFIN | REFOUT | XOROUT     |
//   |--------------|-------|------------|------------|-------|--------|------------|
//   | CRC-32       | 32    | 0x04C11DB7 | 0xFFFFFFFF | 1     | 1      | 0xFFFFFFFF |
//   | CRC-16-CCITT | 16    | 0x1021     | 0xFFFF     | 0     | 0      | 0x0000     |
//   | CRC-8        | 8     | 0x07       | 0x00       | 0     | 0      | 0x00       |
//   | CRC-64-ECMA  | 64    | 0x42F0E...| 0x00...    | 0     | 0      | 0x00...    |
//
//   Timing Diagram (CRC-8, DATA_WIDTH=16, 2 chunks):
//
//   {signal: [
//     {name: 'clk',              wave: 'p.........'},
//     {name: 'rst_n',            wave: '01........'},
//     {},
//     {name: 'load_crc_start',   wave: '0.10......'},
//     {name: 'data[15:0]',       wave: 'x..3.4....', data: ['AB','CD']},
//     {name: 'POLY[7:0]',        wave: '2.........', data: ['07']},
//     {},
//     {name: 'r_crc_value[7:0]', wave: 'x.2.3.4...', data: ['00','X1','X2']},
//     {name: 'w_cascade[0][7:0]', wave: 'x..3.4....', data: ['C0','C0']},
//     {name: 'w_cascade[1][7:0]', wave: 'x..3.4....', data: ['C1','C1']},
//     {},
//     {name: 'crc[7:0]',         wave: 'x..2..3.4.', data: ['00','R1','R2']},
//     {},
//     {name: 'Event',            wave: 'x..2.3.4..', data: ['Init','Proc AB','Proc CD']}
//   ]}
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // CRC-32 (Ethernet) - Most common configuration
//   dataint_crc #(
//       .ALGO_NAME("CRC32_ETHERNET"),
//       .DATA_WIDTH(64),      // Process 8 bytes/cycle
//       .CRC_WIDTH(32),
//       .REFIN(1),            // LSB-first input
//       .REFOUT(1)            // LSB-first output
//   ) u_crc32 (
//       .POLY      (32'h04C11DB7),
//       .POLY_INIT (32'hFFFFFFFF),
//       .XOROUT    (32'hFFFFFFFF),
//       .clk       (clk),
//       .rst_n     (rst_n),
//       .load_crc_start  (pkt_start),
//       .load_from_cascade(1'b0),
//       .cascade_sel     (byte_count_onehot),
//       .data      (pkt_data),
//       .crc       (pkt_crc)
//   );
//
//   // CRC-16-CCITT (X.25, HDLC)
//   dataint_crc #(
//       .ALGO_NAME("CRC16_CCITT"),
//       .DATA_WIDTH(32),
//       .CRC_WIDTH(16),
//       .REFIN(0),
//       .REFOUT(0)
//   ) u_crc16 (
//       .POLY      (16'h1021),
//       .POLY_INIT (16'hFFFF),
//       .XOROUT    (16'h0000),
//       .clk       (clk),
//       .rst_n     (rst_n),
//       .load_crc_start(frame_start),
//       .load_from_cascade(1'b0),
//       .cascade_sel(4'b1111),  // All 4 bytes valid
//       .data      (frame_data),
//       .crc       (frame_crc)
//   );
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **DATA_WIDTH must be multiple of 8** (byte-aligned processing)
//   - Supports ~300 CRC standards via parameter configuration
//   - REFIN/REFOUT implement bit-reversal for protocol compatibility
//   - Cascade architecture allows high throughput (multiple bytes/cycle)
//   - load_crc_start: Pulse at start of packet/frame
//   - cascade_sel: Use for variable-length data (one-hot encode last valid chunk)
//   - **Polynomial representation:** Use non-reflected form (e.g., 0x04C11DB7 for CRC-32)
//   - XOROUT: Typically 0x00 or 0xFF...FF depending on standard
//   - **Critical path:** Cascade chain (limits max DATA_WIDTH for timing)
//   - For high speed: Reduce DATA_WIDTH or pipeline cascade stages
//   - Uses dataint_crc_xor_shift_cascade internally (8-bit XOR-shift per stage)
//   - **Synthesis:** Cascade generates CH instances of xor_shift_cascade
//   - Output registered: Adds 1 cycle latency but improves timing
//   - **Common mistake:** Using reflected polynomial (use standard non-reflected form)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - dataint_crc_xor_shift_cascade.sv - Single 8-bit cascade stage (used internally)
//   - dataint_crc_xor_shift.sv - Bit-level XOR-shift (used by cascade)
//   - dataint_parity.sv - Simple parity error detection
//   - dataint_ecc_hamming_encode_secded.sv - ECC encoding (stronger than CRC)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_dataint_crc.py
//   Run: pytest val/common/test_dataint_crc.py -v
//   Coverage: 89%
//   Key Test Scenarios:
//     - CRC-32 (Ethernet) verification against known vectors
//     - CRC-16-CCITT verification
//     - CRC-8 verification
//     - REFIN=0/1 modes
//     - REFOUT=0/1 modes
//     - Variable-length data (cascade_sel)
//     - Multi-cycle packet processing
//
//==============================================================================

`include "reset_defs.svh"
module dataint_crc #(
    parameter string ALGO_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int DATA_WIDTH = 64,     // Adjustable data width
    parameter int CRC_WIDTH = 64,      // CRC polynomial width
    parameter int REFIN = 1,
    parameter int REFOUT = 1
) (
    input  logic [CRC_WIDTH-1:0]  POLY,
    input  logic [CRC_WIDTH-1:0]  POLY_INIT,
    input  logic [CRC_WIDTH-1:0]  XOROUT,
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  load_crc_start,
    input  logic                  load_from_cascade,
    input  logic [    CHUNKS-1:0] cascade_sel,        // one hot encoded
    input  logic [DATA_WIDTH-1:0] data,
    output logic [ CRC_WIDTH-1:0] crc
);

    // =======================================================================
    // Derived Parameters (computed from parameters)
    // =======================================================================
    localparam int CHUNKS = DATA_WIDTH / 8;  // Number of bytes processed per cycle
    localparam int CW = CRC_WIDTH;           // Convenience alias for CRC width
    localparam int DW = DATA_WIDTH;          // Convenience alias for data width
    localparam int CH = CHUNKS;              // Convenience alias for chunks

    logic [CW-1:0] r_crc_value;
    logic [CW-1:0] w_poly;
    logic [7:0]    w_block_data[CH];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [CW-1:0] w_cascade[CH];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic [CW-1:0] w_result, w_result_xor, w_selected_cascade_output;

    assign w_poly = POLY;

    ////////////////////////////////////////////////////////////////////////////
    // Reflect input data if REFIN is enabled
    genvar i, j, idx;
    generate
        // FIX: Use explicit comparison for REFIN
        if (REFIN != 0) begin : gen_reflect_inputs
            for (genvar i = 0; i < CH; i++) begin : gen_ch_reflect
                for (genvar j = 0; j < 8; j++) begin : gen_bit_reflect
                    assign w_block_data[i][j] = data[i*8+7-j];
                end
            end
        end else begin : gen_direct_assign_inputs
            for (genvar i = 0; i < CH; i++) begin : gen_ch_direct
                assign w_block_data[i] = data[i*8+:8];
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////
    // Select the correct drop off point for the cascade depending on the length of data
    always_comb begin
        w_selected_cascade_output = POLY_INIT;  // Default to initial value
        for (int i = 0; i < CH; i++) begin
            if (cascade_sel[i]) begin
                w_selected_cascade_output = w_cascade[i];
            end
        end
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (~rst_n) r_crc_value <= POLY_INIT;
        else if (load_crc_start) r_crc_value <= POLY_INIT;  // Reset the CRC to the initial value
        else if (load_from_cascade)
            r_crc_value <= w_selected_cascade_output;  // Use pre-selected output
    )


    ////////////////////////////////////////////////////////////////////////////
    // Generate dataint_xor_shift_cascades dynamically based on DATA_WIDTH
    generate
        for (i = 0; i < CH; i++) begin : gen_xor_shift_cascade
            if (i == 0) begin : gen_xor_cascade_0
                dataint_crc_xor_shift_cascade #(
                    .CRC_WIDTH(CRC_WIDTH)
                ) dataint_crc_xor_shift_cascade_0 (
                    .block_input(r_crc_value),
                    .poly(w_poly),
                    .data_input(w_block_data[i]),
                    .block_output(w_cascade[i])
                );
            end else begin : gen_xor_cascade_N
                dataint_crc_xor_shift_cascade #(
                    .CRC_WIDTH(CRC_WIDTH)
                ) dataint_crc_xor_shift_cascade_N (
                    .block_input(w_cascade[i-1]),
                    .poly(w_poly),
                    .data_input(w_block_data[i]),
                    .block_output(w_cascade[i])
                );
            end
        end
    endgenerate

    ////////////////////////////////////////////////////////////////////////////
    // CRC logic, reflections, and output muxing as before, adjusted for new generate blocks
    generate
        // FIX: Use explicit comparison for REFOUT
        if (REFOUT != 0) begin : gen_reflect_result
            for (idx = 0; idx < CW; idx = idx + 1) assign w_result[idx] = r_crc_value[(CW-1)-idx];
        end else assign w_result = r_crc_value;
    endgenerate

    // The final xor'd output
    assign w_result_xor = w_result ^ XOROUT;

    ////////////////////////////////////////////////////////////////////////////
    // flop the output path
    `ALWAYS_FF_RST(clk, rst_n,
        if (~rst_n) crc <= 'b0;
        else if (load_crc_start) crc <= POLY_INIT;  // Reset the CRC to the initial value
        else crc <= w_result_xor;
    )


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
    // synopsys translate_on

endmodule : dataint_crc
