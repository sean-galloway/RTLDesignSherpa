// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Stripped copy of gaxi_skid_buffer_dbldrn for yosys formal verification.
// Change: removed $error(...) call that yosys cannot parse.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gaxi_skid_buffer_dbldrn #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH = 4, // Must be one of {2, 4, 6, 8}
    parameter int DW = DATA_WIDTH,
    parameter int BUF_WIDTH = DATA_WIDTH * DEPTH,
    parameter int BW = BUF_WIDTH
) (
    // Global Clock and Reset
    input  logic          axi_aclk,
    input  logic          axi_aresetn,

    // input side
    input  logic          wr_valid,
    output logic          wr_ready,
    input  logic [DW-1:0] wr_data,

    // output side
    output logic [3:0]    count,
    output logic          rd_valid,
    input  logic          rd_ready,
    input  logic          rd_ready2,    // Double-drain request (only legal when rd_count >= 2)
    output logic [3:0]    rd_count,
    output logic [DW-1:0] rd_data,
    output logic [DW-1:0] rd_data2      // Second data output for double-drain
);

    logic [BW-1:0]         r_data;
    logic [3:0]            r_data_count;
    logic                  w_wr_xfer;
    logic                  w_rd_xfer;
    logic                  w_rd_dbl_xfer;  // Double-drain transfer
    logic [DW-1:0]         zeros;

    assign zeros         = 'b0;
    assign w_wr_xfer     = wr_valid & wr_ready;
    assign w_rd_xfer     = rd_valid & rd_ready & ~rd_ready2;  // Single drain
    assign w_rd_dbl_xfer = rd_valid & rd_ready & rd_ready2 & (r_data_count >= 4'd2);  // Double drain

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_data <= 'b0;
            r_data_count <= 'b0;
        end else begin
            // Priority: double-drain > single-drain
            case ({w_wr_xfer, w_rd_dbl_xfer, w_rd_xfer})
                3'b100: begin  // Write only
                    r_data[(DW * r_data_count) +: DW] <= wr_data;
                    r_data_count <= r_data_count + 1;
                end
                3'b001: begin  // Single read only
                    r_data <= {zeros, r_data[BUF_WIDTH-1:DW]};
                    r_data_count <= r_data_count - 1;
                end
                3'b010: begin  // Double read only
                    r_data <= {{2{zeros}}, r_data[BUF_WIDTH-1:2*DW]};
                    r_data_count <= r_data_count - 2;
                end
                3'b101: begin  // Write + single read
                    r_data <= {zeros, r_data[BUF_WIDTH-1:DW]};
                    r_data[(DW * (32'(r_data_count) - 1)) +: DW] <= wr_data;
                    // Count stays same (write +1, read -1)
                end
                3'b110: begin  // Write + double read
                    r_data <= {{2{zeros}}, r_data[BUF_WIDTH-1:2*DW]};
                    r_data[(DW * (32'(r_data_count) - 2)) +: DW] <= wr_data;
                    r_data_count <= r_data_count - 1;  // Net: write +1, double-read -2 = -1
                end
                default: begin  // 3'b000, 3'b011 (illegal), 3'b111 (illegal)
                    // No changes to r_data or r_data_count
                end
            endcase
        end
    )

    // Ready/valid logic
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            wr_ready <= 1'b0;
            rd_valid <= 1'b0;
        end else begin
            // Write ready: can accept if not full (accounting for drains)
            wr_ready <= (32'(r_data_count) <= DEPTH-2) ||
                        (32'(r_data_count) == DEPTH-1 && (~w_wr_xfer || w_rd_xfer || w_rd_dbl_xfer)) ||
                        (32'(r_data_count) == DEPTH && (w_rd_xfer || w_rd_dbl_xfer));

            // Read valid: have at least one item (or incoming write)
            rd_valid <= (r_data_count >= 2) ||
                        (r_data_count == 4'b0001 && (~w_rd_xfer || w_wr_xfer)) ||
                        (r_data_count == 4'b0000 && w_wr_xfer);
        end
    )

    // Output assignments
    assign rd_data  = r_data[DW-1:0];           // First item (lowest position)
    assign rd_data2 = r_data[2*DW-1:DW];        // Second item (next position)
    assign rd_count = r_data_count;
    assign count    = r_data_count;

    // -------------------------------------------------------------------------
    // Assertion: rd_ready2 only legal when rd_count >= 2
    // (original $error removed for yosys compatibility)
    // -------------------------------------------------------------------------

endmodule : gaxi_skid_buffer_dbldrn
