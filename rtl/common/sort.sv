`timescale 1ns / 1ps

module sort #(
    parameter int NUM_VALS = 5,
    parameter int SIZE     = 16
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic [NUM_VALS*SIZE-1:0] data,
    output logic [NUM_VALS*SIZE-1:0] sorted
);
    logic [NUM_VALS*SIZE-1:0] w_sorted_bus;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) sorted <= 'b0;
        else sorted <= w_sorted_bus;
    end

    integer i, j;
    logic [SIZE-1:0] w_temp;
    logic [SIZE-1:0] w_array[1:NUM_VALS];

    always_comb begin
        // Initialize w_array to avoid latch inference
        w_temp = 'b0;
        for (i = 0; i <= NUM_VALS; i++) begin
            w_array[i] = 0;
        end

        for (i = 0; i < NUM_VALS; i++) begin
            w_array[i+1] = data[i*SIZE+:SIZE];
        end

        for (i = NUM_VALS; i > 0; i = i - 1) begin
            for (j = 1; j < i; j++) begin
                if (w_array[j] < w_array[j+1]) begin
                    w_temp       = w_array[j];
                    w_array[j]   = w_array[j+1];
                    w_array[j+1] = w_temp;
                end
            end
        end

        for (i = 0; i < NUM_VALS; i++) begin
            w_sorted_bus[i*SIZE+:SIZE] = w_array[i+1];
        end
    end
endmodule
