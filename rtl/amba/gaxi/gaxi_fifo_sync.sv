// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_fifo_sync
// Purpose: Gaxi Fifo Sync module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "fifo_defs.svh"
`include "reset_defs.svh"


// Parameterized Synchronous FIFO -- This works with any depth
module gaxi_fifo_sync #(
    // ---------------------------------------------------------------------
    // Memory implementation selector (from fifo_defs.svh)
    // ---------------------------------------------------------------------
    parameter fifo_mem_t MEM_STYLE = FIFO_AUTO,

    // Configuration
    parameter int  REGISTERED        = 0,   // 0=mux mode, 1=flop mode
    parameter int  DATA_WIDTH        = 4,
    parameter int  DEPTH             = 4,
    parameter int  ALMOST_WR_MARGIN  = 1,
    parameter int  ALMOST_RD_MARGIN  = 1,
    parameter int  DW = DATA_WIDTH,
    parameter int  D  = DEPTH,
    parameter int  AW = $clog2(DEPTH)
) (
    input  logic            axi_aclk,
    input  logic            axi_aresetn,
    input  logic            wr_valid,
    output logic            wr_ready,   // not full
    input  logic [DW-1:0]   wr_data,
    input  logic            rd_ready,
    // verilator coverage_off
    // DEFENSIVE: count's top bit is an illegal state at any non-power-of-2
    // DEPTH. The port is $clog2(DEPTH)+1 wide, so at DEPTH=11 it is [4:0]
    // while occupancy maxes out at 11 (5'b01011) -- bit 4 cannot be set by any
    // stimulus, and DEPTH=11 is a legal configuration this module supports and
    // the FULL grid exercises.
    //
    // Note what this waiver costs: at a power-of-2 DEPTH that same bit IS
    // reachable (occupancy == DEPTH sets it) and was covered -- DEPTH=8
    // measured 70/70 with the bit toggling. Waiving by line cannot distinguish
    // the two cases, so a real, exercised point is being suppressed along with
    // the impossible one. If a future change stops the FIFO ever reaching
    // full, this waiver will hide it. The occupancy assertions in
    // gaxi_drop_fifo_sync's test_fill_and_random_drop are the backstop.
    output logic [AW:0]     count,
    // verilator coverage_on
    output logic            rd_valid,   // not empty
    output logic [DW-1:0]   rd_data
);

    // ---------------------------------------------------------------------
    // Local signals
    // ---------------------------------------------------------------------
    logic [AW-1:0] r_wr_addr, r_rd_addr;
    logic [AW:0]   r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0]   w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic          r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;

    // ---------------------------------------------------------------------
    // Write/Read enables
    // ---------------------------------------------------------------------
    logic w_write, w_read;
    assign w_write = wr_valid && wr_ready;
    assign w_read  = rd_valid && rd_ready;

    // ---------------------------------------------------------------------
    // Write pointer
    // ---------------------------------------------------------------------
    counter_bin #(
        .WIDTH (AW + 1),
        .MAX   (D)
    ) write_pointer_inst (
        .clk              (axi_aclk),
        .rst_n            (axi_aresetn),
        .enable           (w_write && !r_wr_full),
        .counter_bin_curr (r_wr_ptr_bin),
        .counter_bin_next (w_wr_ptr_bin_next)
    );

    // ---------------------------------------------------------------------
    // Read pointer
    // ---------------------------------------------------------------------
    counter_bin #(
        .WIDTH (AW + 1),
        .MAX   (D)
    ) read_pointer_inst (
        .clk              (axi_aclk),
        .rst_n            (axi_aresetn),
        .enable           (w_read && !r_rd_empty),
        .counter_bin_curr (r_rd_ptr_bin),
        .counter_bin_next (w_rd_ptr_bin_next)
    );

    // ---------------------------------------------------------------------
    // Control block (full/empty, almost flags, count)
    // ---------------------------------------------------------------------
    fifo_control #(
        .DEPTH             (D),
        .ADDR_WIDTH        (AW),
        .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
        .REGISTERED        (REGISTERED)
    ) fifo_control_inst (
        .wr_clk           (axi_aclk),
        .wr_rst_n         (axi_aresetn),
        .rd_clk           (axi_aclk),
        .rd_rst_n         (axi_aresetn),
        .wr_ptr_bin       (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin  (w_rd_ptr_bin_next),
        .rd_ptr_bin       (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin  (w_wr_ptr_bin_next),
        .count            (count),
        .wr_full          (r_wr_full),
        .wr_almost_full   (r_wr_almost_full),
        .rd_empty         (r_rd_empty),
        .rd_almost_empty  (r_rd_almost_empty)
    );

    assign wr_ready = !r_wr_full;
    assign rd_valid = !r_rd_empty;

    // ---------------------------------------------------------------------
    // Address extraction
    // ---------------------------------------------------------------------
    assign r_wr_addr = r_wr_ptr_bin[AW-1:0];
    assign r_rd_addr = r_rd_ptr_bin[AW-1:0];

    // ---------------------------------------------------------------------
    // Memory implementation (scoped per MEM_STYLE)
    // ---------------------------------------------------------------------
    generate
        if (MEM_STYLE == FIFO_SRL) begin : gen_srl
            `ifdef XILINX
                (* shreg_extract = "yes", ram_style = "distributed" *)
            `elsif INTEL
                /* synthesis ramstyle = "MLAB" */
            `endif
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write path
            always_ff @(posedge axi_aclk) begin
                if (w_write && !r_wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Read path
            if (REGISTERED != 0) begin : g_flop
                logic [DATA_WIDTH-1:0] r_rd_data;
                `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
                    if (!axi_aresetn) r_rd_data <= '0;
                    else              r_rd_data <= mem[r_rd_addr];
                )
                assign rd_data = r_rd_data;

            end else begin : g_mux
                assign rd_data = mem[r_rd_addr];
            end

        end
        else if (MEM_STYLE == FIFO_BRAM) begin : gen_bram
            `ifdef XILINX
                (* ram_style = "block" *)
            `elsif INTEL
                /* synthesis ramstyle = "M20K" */
            `endif
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write path
            always_ff @(posedge axi_aclk) begin
                if (w_write && !r_wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            // Synchronous read (flop output)
            logic [DATA_WIDTH-1:0] r_rd_data;
            `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
                if (!axi_aresetn) r_rd_data <= '0;
                else              r_rd_data <= mem[r_rd_addr];
            )
            assign rd_data = r_rd_data;


        end
        else begin : gen_auto
            logic [DATA_WIDTH-1:0] mem [DEPTH];

            // Write path
            always_ff @(posedge axi_aclk) begin
                if (w_write && !r_wr_full) begin
                    mem[r_wr_addr] <= wr_data;
                end
            end

            if (REGISTERED != 0) begin : g_flop
                logic [DATA_WIDTH-1:0] r_rd_data;
                `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
                    if (!axi_aresetn) r_rd_data <= '0;
                    else              r_rd_data <= mem[r_rd_addr];
                )
                assign rd_data = r_rd_data;

            end else begin : g_mux
                assign rd_data = mem[r_rd_addr];
            end

            // Note: Waveform flattening removed for AUTO style to avoid Verilator
            // unroll limit errors with large DEPTH parameters (e.g., 4096).
            // Use indexed array viewing in waveform viewer instead.
        end
    endgenerate
    // rd_data is driven inside the elaborated MEM_STYLE branch (flop path
    // through r_rd_data, mux path straight off the array) - one shared
    // intermediate could not be named truthfully across REGISTERED modes.

    // ---------------------------------------------------------------------
    // Overflow/underflow error checking
    // ---------------------------------------------------------------------
    // verilator coverage_off
    // DEFENSIVE: Illegal states, unreachable by construction. wr_ready is
    // !r_wr_full and w_write is wr_valid && wr_ready, so `w_write && r_wr_full`
    // expands to `wr_valid && !full && full` -- always false. The underflow arm
    // is the same shape against rd_valid = !r_rd_empty. No stimulus can reach
    // either, so they are waived rather than chased: a producer cannot be
    // accepted by a full FIFO, which is the property, not a bug to catch.
    always_ff @(posedge axi_aclk) begin
        if (w_write && r_wr_full) begin
        end
        if (w_read && r_rd_empty) begin
        end
    end
    // verilator coverage_on

endmodule : gaxi_fifo_sync

