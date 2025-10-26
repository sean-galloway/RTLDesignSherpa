// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_fifo_sync
// Purpose: Gaxi Fifo Sync module
//
// Documentation: rtl/amba/PRD.md
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
    parameter string INSTANCE_NAME   = "DEADF1F0", // for $display debug
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
    output logic [AW:0]     count,
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
    logic [DW-1:0] w_rd_data;

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
                `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
                    if (!axi_aresetn) w_rd_data <= '0;
                    else              w_rd_data <= mem[r_rd_addr];
                )

            end else begin : g_mux
                always_comb w_rd_data = mem[r_rd_addr];
            end

            // synopsys translate_off
            logic [(DW*DEPTH)-1:0] flat_mem_srl;
            genvar i_srl;
            for (i_srl = 0; i_srl < DEPTH; i_srl++) begin : gen_flatten_srl
                assign flat_mem_srl[i_srl*DW+:DW] = mem[i_srl];
            end
            // synopsys translate_on
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
            `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
                if (!axi_aresetn) w_rd_data <= '0;
                else              w_rd_data <= mem[r_rd_addr];
            )


            // synopsys translate_off
            logic [(DW*DEPTH)-1:0] flat_mem_bram;
            genvar i_bram;
            for (i_bram = 0; i_bram < DEPTH; i_bram++) begin : gen_flatten_bram
                assign flat_mem_bram[i_bram*DW+:DW] = mem[i_bram];
            end
            // synopsys translate_on

            initial begin
                if (REGISTERED == 0)
                    $display("NOTE: %s BRAM style uses synchronous read (+1 cycle latency)",
                            INSTANCE_NAME);
            end
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
                `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
                    if (!axi_aresetn) w_rd_data <= '0;
                    else              w_rd_data <= mem[r_rd_addr];
                )

            end else begin : g_mux
                always_comb w_rd_data = mem[r_rd_addr];
            end

            // synopsys translate_off
            logic [(DW*DEPTH)-1:0] flat_mem_auto;
            genvar i_auto;
            for (i_auto = 0; i_auto < DEPTH; i_auto++) begin : gen_flatten_auto
                assign flat_mem_auto[i_auto*DW+:DW] = mem[i_auto];
            end
            // synopsys translate_on
        end
    endgenerate

    assign rd_data = w_rd_data;

    // ---------------------------------------------------------------------
    // Simulation-only overflow/underflow messages
    // ---------------------------------------------------------------------
    // synopsys translate_off
    always_ff @(posedge axi_aclk) begin
        if (w_write && r_wr_full) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s write while fifo full, %t", INSTANCE_NAME, $time);
        end
        if (w_read && r_rd_empty) begin
            $timeformat(-9, 3, " ns", 10);
            $display("Error: %s read while fifo empty, %t", INSTANCE_NAME, $time);
        end
    end
    // synopsys translate_on

endmodule : gaxi_fifo_sync
