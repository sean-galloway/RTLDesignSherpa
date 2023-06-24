`include "macro_inc.svh"
`timescale 1ns / 1ps

// Paramerized Synchronous FIFO
module SyncClockCrossingFifo #(parameter DATA_WIDTH = 8, parameter DEPTH = 27)
(
    input  wire        clk_in,
    input  wire        rst_n,
    input  wire        wr_en,
    input  wire [DATA_WIDTH-1:0] wr_data,
    output wire        wr_full,
    input  wire        rd_en,
    output wire [DATA_WIDTH-1:0] rd_data,
    output wire        rd_empty
);
    reg [DATA_WIDTH-1:0] mem [0:DEPTH-1];
    reg [$clog2(DEPTH)-1:0] wr_ptr_reg;
    reg [$clog2(DEPTH)-1:0] rd_ptr_reg;
    reg [$clog2(DEPTH)-1:0] wr_ptr_next;
    reg [$clog2(DEPTH)-1:0] rd_ptr_next;
    reg wr_full_reg;
    reg rd_empty_reg;

    always @(posedge clk_in or negedge rst_n) begin
        if (~rst_n) begin
            wr_ptr_reg <= 0;
            rd_ptr_reg <= 0;
            wr_full_reg <= 0;
            rd_empty_reg <= 1;
        end else begin
            wr_ptr_reg <= wr_ptr_next;
            rd_ptr_reg <= rd_ptr_next;
            wr_full_reg <= wr_full_reg & ~wr_en | (wr_ptr_reg == DEPTH-1) & wr_en;
            rd_empty_reg <= rd_empty_reg & ~rd_en | (rd_ptr_reg == wr_ptr_reg) & rd_en;
        end
    end

    always @(posedge clk_in or negedge rst_n) begin
        if (~rst_n) begin
            wr_ptr_next <= 0;
            rd_ptr_next <= 0;
        end else begin
            wr_ptr_next <= wr_ptr_reg;
            rd_ptr_next <= rd_ptr_reg;
            if (wr_en & ~wr_full_reg)
                wr_ptr_next <= (wr_ptr_reg + 1) % DEPTH;
            if (rd_en & ~rd_empty_reg)
                rd_ptr_next <= (rd_ptr_reg + 1) % DEPTH;
        end
    end

    always @(posedge clk_in or negedge rst_n) begin
        if (~rst_n) begin
            mem <= '0;
        end else begin
            if (wr_en & ~wr_full_reg)
                mem[wr_ptr_reg] <= wr_data;
            if (rd_en & ~rd_empty_reg)
                rd_data <= mem[rd_ptr_reg];
        end
    end

    assign wr_full = wr_full_reg;
    assign rd_empty = rd_empty_reg;

endmodule

