`timescale 1ns / 1ps

module shifter_universal #(
    parameter int WIDTH = 4
) (
    input                    i_clk,
    input                    i_rst_n,
    input        [      1:0] i_select,    // i_select operation
                                          // 00 = o_pdata = o_pdata
                                          // 01 = right shift
                                          // 10 = left shift
                                          // 11 = o_pdata = i_pdata
    input        [WIDTH-1:0] i_pdata,     // parallel data in
    input                    i_sdata_lt,  // serial left data in
    input                    i_sdata_rt,  // serial right data in
    output logic [WIDTH-1:0] o_pdata,     // parallel data out
    output                   o_sdata_lt,  // serial left data out
    output                   o_sdata_rt   // serial right data out
);

    logic [WIDTH-1:0] w_pdata;

    always_comb begin
        casez (i_select)
            2'b00:   w_pdata = o_pdata;  // Hold (Do nothing)
            2'b01:   w_pdata = {i_sdata_rt, o_pdata[WIDTH-1:1]};  // Right Shift
            2'b10:   w_pdata = {o_pdata[WIDTH-2:0], i_sdata_lt};  // Left Shift - Fixed to use WIDTH parameter
            2'b11:   w_pdata = i_pdata;  // Parallel in - Parallel out
            default: w_pdata = o_pdata;  // Handle X cases - hold current value
        endcase
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) o_pdata <= 0;
        else o_pdata <= w_pdata;
    end

    assign o_sdata_lt = o_pdata[0];
    assign o_sdata_rt = o_pdata[WIDTH-1];

endmodule : shifter_universal
