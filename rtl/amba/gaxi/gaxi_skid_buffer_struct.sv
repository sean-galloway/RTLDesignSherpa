// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_skid_buffer_struct
// Purpose: Gaxi Skid Buffer Struct module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gaxi_skid_buffer_struct #(
    parameter type STRUCT_TYPE = logic [31:0], // Generic struct type parameter
    parameter int  DEPTH = 2,                  // Must be one of {2, 4, 6, 8}
    parameter      INSTANCE_NAME = "DEADF1F0", // verilog_lint: waive explicit-parameter-storage-type

    // Derived parameters - calculate struct width automatically
    localparam int STRUCT_WIDTH = $bits(STRUCT_TYPE),
    localparam int BUF_WIDTH = STRUCT_WIDTH * DEPTH,
    localparam int SW = STRUCT_WIDTH,
    localparam int BW = BUF_WIDTH
) (
    // Global Clock and Reset
    input  logic          axi_aclk,
    input  logic          axi_aresetn,

    // Input side
    input  logic          wr_valid,
    output logic          wr_ready,
    input  STRUCT_TYPE    wr_data,

    // Output side
    output logic [3:0]    count,
    output logic          rd_valid,
    input  logic          rd_ready,
    output logic [3:0]    rd_count,
    output STRUCT_TYPE    rd_data
);

    // Internal storage as packed array of structs
    STRUCT_TYPE            r_data [DEPTH];
    logic [3:0]            r_data_count;
    logic                  w_wr_xfer;
    logic                  w_rd_xfer;
    STRUCT_TYPE            struct_zeros;

    // Initialize struct to zeros
    initial begin
        struct_zeros = '0;
    end

    assign w_wr_xfer = wr_valid & wr_ready;
    assign w_rd_xfer = rd_valid & rd_ready;

    // Data shift register logic
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            for (int i = 0; i < DEPTH; i++) begin
                r_data[i] <= '0;
            end
            r_data_count <= 'b0;
        end else begin
            if (w_wr_xfer & ~w_rd_xfer) begin
                // Shift in new data at the position indicated by count
                r_data[r_data_count] <= wr_data;
                r_data_count <= r_data_count + 1;
            end else if (~w_wr_xfer & w_rd_xfer) begin
                // Shift out old data - move everything down by one position
                for (int i = 0; i < DEPTH-1; i++) begin
                    r_data[i] <= r_data[i+1];
                end
                r_data[DEPTH-1] <= struct_zeros;
                r_data_count <= r_data_count - 1;
            end else if (w_wr_xfer & w_rd_xfer) begin
                // Shift in new data and shift out old data simultaneously
                // Move existing data down and insert new data at the top valid position
                for (int i = 0; i < DEPTH-1; i++) begin
                    r_data[i] <= r_data[i+1];
                end
                r_data[r_data_count - 1] <= wr_data;
                // Count stays the same since we're adding and removing one
            end
        end
    )


    // Ready and valid signal generation
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            wr_ready <= 1'b0;
            rd_valid <= 1'b0;
        end else begin
            // wr_ready: Can accept write if buffer isn't full or will have space next cycle
            wr_ready <= (32'(r_data_count) <= DEPTH-2) ||
                        (32'(r_data_count) == DEPTH-1 && (~w_wr_xfer || w_rd_xfer)) ||
                        (32'(r_data_count) == DEPTH && w_rd_xfer);

            // rd_valid: Can provide read if buffer has data or will have data next cycle
            rd_valid <= (r_data_count >= 2) ||
                        (r_data_count == 4'b0001 && (~w_rd_xfer || w_wr_xfer)) ||
                        (r_data_count == 4'b0000 && w_wr_xfer);
        end
    )


    // Output assignments
    assign rd_data  = r_data[0];  // Always read from the bottom of the buffer
    assign rd_count = r_data_count;
    assign count    = r_data_count;

    // =======================================================================
    // Debug and Monitoring (synthesis translate_off)
    // =======================================================================

    // synopsys translate_off

    // Debug display for struct contents (optional - useful for debugging)
    always @(posedge axi_aclk) begin
        if (axi_aresetn) begin
            if (w_wr_xfer) begin
                $display("STRUCT_SKID_BUFFER[%s] WR at %0t: count=%0d, data=0x%h",
                            INSTANCE_NAME, $time, r_data_count, wr_data);
            end
            if (w_rd_xfer) begin
                $display("STRUCT_SKID_BUFFER[%s] RD at %0t: count=%0d, data=0x%h",
                            INSTANCE_NAME, $time, r_data_count, rd_data);
            end

            // Warning for potential issues
            if (wr_valid && !wr_ready) begin
                $display("STRUCT_SKID_BUFFER[%s] WARNING: Write stall at %0t (count=%0d)",
                            INSTANCE_NAME, $time, r_data_count);
            end
            if (!rd_valid && rd_ready) begin
                $display("STRUCT_SKID_BUFFER[%s] WARNING: Read underrun at %0t (count=%0d)",
                            INSTANCE_NAME, $time, r_data_count);
            end
        end
    end

    // Structural checks
    initial begin
        if (DEPTH < 2 || DEPTH > 8 || (DEPTH % 2) != 0) begin
            $error("STRUCT_SKID_BUFFER[%s]: Invalid DEPTH=%0d. Must be one of {2, 4, 6, 8}",
                    INSTANCE_NAME, DEPTH);
        end

        $display("STRUCT_SKID_BUFFER[%s]: Initialized with STRUCT_WIDTH=%0d bits, DEPTH=%0d",
                    INSTANCE_NAME, STRUCT_WIDTH, DEPTH);
    end

    // synopsys translate_on

endmodule : gaxi_skid_buffer_struct
