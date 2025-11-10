`timescale 1ns/1ps
// SPDX-License-Identifier: MIT
// gaxi_regslice.sv
//
// Purpose:
//   Timing-friendly 1-deep elastic stage with AXI-like ready/valid handshakes.
//   Always 1-cycle latency, 1 beat/clk throughput in steady state.
//
// Notes:
//   - Ports are intentionally aligned with gaxi_skid_buffer.*
//   - count/rd_count report 0/1 (buffer empty/full) using 4-bit outputs for compatibility.

`include "reset_defs.svh"

module gaxi_regslice #(
    parameter int    DATA_WIDTH   = 32,
    parameter string INSTANCE_NAME = "REGSL1D",
    // Derived (kept for parity with your style)
    parameter int    DW          = DATA_WIDTH
) (
    // Global Clock and Reset
    input  logic          axi_aclk,
    input  logic          axi_aresetn,

    // Write Interface (Input Side)
    input  logic          wr_valid,
    output logic          wr_ready,
    input  logic [DW-1:0] wr_data,

    // Read Interface (Output Side)
    output logic          rd_valid,
    input  logic          rd_ready,
    output logic [DW-1:0] rd_data,

    // Status/Monitoring (kept for interface compatibility)
    output logic [3:0]    count,     // 0 or 1
    output logic [3:0]    rd_count   // mirror of count
);

    // ------------------------------------------------------------------------
    // Storage
    // ------------------------------------------------------------------------
    logic          r_valid;
    logic [DW-1:0] r_data;

    // Handshake detects
    wire w_wxfer = wr_valid & wr_ready;    // input side transfer occurs
    wire w_rxfer = rd_valid & rd_ready;    // output side transfer occurs

    // ------------------------------------------------------------------------
    // Ready/Valid
    //   - Ready when storage is empty OR we're simultaneously popping downstream
    //   - Valid reflects storage occupancy
    // ------------------------------------------------------------------------
    assign wr_ready = (!r_valid) || (r_valid && rd_ready);  // accept when empty or we will pop
    assign rd_valid = r_valid;
    assign rd_data  = r_data;

    // ------------------------------------------------------------------------
    // Sequential: load/hold/clear
    // ------------------------------------------------------------------------
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_valid <= 1'b0;
            r_data  <= '0;
        end else begin
            unique case ({w_wxfer, w_rxfer})
                2'b10: begin
                    // write only: fill
                    r_valid <= 1'b1;
                    r_data  <= wr_data;
                end
                2'b01: begin
                    // read only: drain
                    r_valid <= 1'b0;
                    // r_data don't care
                end
                2'b11: begin
                    // simultaneous: pass through with registered stage
                    r_valid <= 1'b1;
                    r_data  <= wr_data;
                end
                default: begin
                    // idle: hold
                    r_valid <= r_valid;
                    r_data  <= r_data;
                end
            endcase
        end
    )


    // ------------------------------------------------------------------------
    // Status (interface-compatible with skid buffer)
    // ------------------------------------------------------------------------
    assign count    = r_valid ? 4'd1 : 4'd0;
    assign rd_count = count;

    // ------------------------------------------------------------------------
    // (Optional) Assertions / Diagnostics
    // ------------------------------------------------------------------------
    // synopsys translate_off
    // 1) No write when not ready
    always_ff @(posedge axi_aclk) if (axi_aresetn) begin
        if (wr_valid && !wr_ready) begin
            // Not an error by itself (backpressure), but useful to see hot spots
            // $display("[%s] wr_valid && !wr_ready at %0t", INSTANCE_NAME, $time);
        end
    end
    // 2) No read when not valid
    always_ff @(posedge axi_aclk) if (axi_aresetn) begin
        if (rd_ready && !rd_valid) begin
            // $display("[%s] rd_ready && !rd_valid at %0t", INSTANCE_NAME, $time);
        end
    end
    // 3) Sanity: count must be 0/1 only
    always_ff @(posedge axi_aclk) if (axi_aresetn) begin
        if (count > 4'd1) begin
            $error("[%s] count > 1 (=%0d) @ %0t", INSTANCE_NAME, count, $time);
        end
    end
    // synopsys translate_on

endmodule
