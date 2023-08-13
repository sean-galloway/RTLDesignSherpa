`timescale 1ns / 1ps

module clock_pulse #(
     parameter int WIDTH = 10     // Width of the generated pulse in clock cycles
) (
    input  logic i_clk,           // Input clock signal
    input  logic i_rst_n,         // Input reset signal
    output logic ow_pulse         // Output pulse signal
);

    logic [WIDTH-1:0] r_counter;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n)
            r_counter <= 'b0;
        else
            if (r_counter < WIDTH)
                r_counter <= r_counter + 1;
            else
                r_counter <= 0;
    end

    assign ow_pulse = (counter == WIDTH-1);

endmodule : clock_pulse