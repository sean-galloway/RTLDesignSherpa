// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: dataint_parity
// Purpose: //   Generic multi-chunk parity generator and checker. Divides input data into
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: dataint_parity
//==============================================================================
// Description:
//   Generic multi-chunk parity generator and checker. Divides input data into
//   CHUNKS segments and generates/checks even or odd parity for each chunk
//   independently. Supports both parity generation and error detection modes.
//   Commonly used for simple error detection in memory and communication links.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   CHUNKS:
//     Description: Number of independent parity chunks
//     Type: int
//     Range: 1 to 32
//     Default: 4
//     Constraints: WIDTH must be divisible by CHUNKS (remainder handled in last chunk)
//
//   Derived Parameters (localparam - computed automatically):
//     ChunkSize: Bits per chunk (WIDTH / CHUNKS)
//     ExtraBits: Remainder bits (WIDTH % CHUNKS), added to last chunk
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Combinational logic (no clock/reset required)
//   - parity_type: 1 = even parity, 0 = odd parity
//   - Generation mode: Use parity[CHUNKS-1:0] output
//   - Checking mode: Compare parity_in with parity, check parity_err
//   - parity_err[i]: Asserted when chunk i has parity error
//   - Each chunk processed independently (parallel operation)
//   - Last chunk includes extra bits if WIDTH not evenly divisible
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - dataint_crc.sv - More robust error detection
//   - dataint_ecc_hamming_*.sv - Error correction capability
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_dataint_parity.py
//   Run: pytest val/common/test_dataint_parity.py -v
//
//==============================================================================
// a generic parity generator
module dataint_parity #(
    parameter int CHUNKS = 4,  // Number of Chunks to check parity
    parameter int WIDTH  = 32  // Total Width of the Data
) (
    input  logic [ WIDTH-1:0] data_in,         // data in
    input  logic [CHUNKS-1:0] parity_in,       // parity in for checking
    input  logic              parity_type,  // 1=even, 0=odd
    output logic [CHUNKS-1:0] parity,
    output logic [CHUNKS-1:0] parity_err        // error indicator, valid only if used for checking
);

    localparam int ChunkSize = WIDTH / CHUNKS;
    localparam int ExtraBits = WIDTH % CHUNKS;

    genvar i;
    generate
        for (i = 0; i < CHUNKS; i++) begin : gen_parity
            // Bounds are calculated statically for each iteration of the loop
            localparam int LowerBound = i * ChunkSize;
            localparam int UpperBound = (i < CHUNKS - 1) ? ((i + 1) * ChunkSize) - 1 : WIDTH - 1;

            // Utilize lower_bound and upper_bound as needed here, for example:
            wire calculated_parity = parity_type ? ^data_in[UpperBound:LowerBound] :
                                                    ~^data_in[UpperBound:LowerBound];
            assign parity[i] = calculated_parity;
            assign parity_err[i]  = (calculated_parity != parity_in[i]);
        end
    endgenerate

endmodule : dataint_parity
