// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: simple_sram
// Purpose: Simple Sram module
//
// Documentation: projects/components/stream_fub/PRD.md
// Subsystem: stream_fub
//
// Author: sean galloway
// Created: 2025-10-18

module simple_sram #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32,
    parameter DEPTH = 1 << ADDR_WIDTH,
    parameter NUM_CHUNKS = 1,  // Default to 1 for no chunk enables
    parameter CHUNK_WIDTH = DATA_WIDTH / NUM_CHUNKS
)(
    input  logic                    clk,

    // Write port
    input  logic                    wr_en,
    input  logic [ADDR_WIDTH-1:0]   wr_addr,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    input  logic [NUM_CHUNKS-1:0]   wr_chunk_en,

    // Read port
    input  logic                    rd_en,
    input  logic [ADDR_WIDTH-1:0]   rd_addr,
    output logic [DATA_WIDTH-1:0]   rd_data
);

    // Memory array - initialized to zero
    // FPGA hint: Auto-select RAM style (distributed for small, block for large)
    `ifdef XILINX
        (* ram_style = "auto" *)
    `elsif INTEL
        /* synthesis ramstyle = "AUTO" */
    `endif
    logic [DATA_WIDTH-1:0] mem [DEPTH] = '{default:0};

    // Read pipeline - initialize signals
    logic [ADDR_WIDTH-1:0] rd_addr_q = '0;
    logic                  rd_en_q = 1'b0;

    always_ff @(posedge clk) begin
        rd_addr_q <= rd_addr;
        rd_en_q   <= rd_en;
    end

    // Write logic with optional chunk enables
    generate
        if (NUM_CHUNKS == 1) begin : gen_simple_write
            // Simple write without chunk enables
            always_ff @(posedge clk) begin
                if (wr_en) begin
                    mem[wr_addr] <= wr_data;
                end
            end
        end else begin : gen_chunk_write
            // Write with chunk enables
            genvar i;
            for (i = 0; i < NUM_CHUNKS; i++) begin : gen_chunk_write_loop
                always_ff @(posedge clk) begin
                    if (wr_en && wr_chunk_en[i]) begin
                        mem[wr_addr][(i+1)*CHUNK_WIDTH-1:i*CHUNK_WIDTH] <=
                            wr_data[(i+1)*CHUNK_WIDTH-1:i*CHUNK_WIDTH];
                    end
                end
            end
        end
    endgenerate

    // Read logic - hold data until next read
    initial rd_data = '0;

    always_ff @(posedge clk) begin
        if (rd_en_q) begin
            rd_data <= mem[rd_addr_q];
        end
        // Remove the else clause - hold last read data
    end

endmodule
