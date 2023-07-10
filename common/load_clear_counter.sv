`timescale 1ns / 1ps

module load_clear_counter #(parameter MAX=32) (
    input  wire                   clk, rst_n,
    input  wire                   clear, increment, load,
    input  wire [$clog2(MAX)-1:0] loadval,                  // this loads the match value for ending the counter
    output reg  [$clog2(MAX)-1:0] count,
    output reg                    done
);

    reg [$clog2(MAX)-1:0] match_val;

    always @(posedge clk, negedge rst_n) begin
        if (!rst_n) count <= 'b0;
        else if (clear) count <= 'b0;
        else if (load)  match_val <= loadval;
        else if (increment) begin
            count <= (count == match_val) ? 'b0 : count + 'b1;
        end
    end

    assign done = count == 'b0;
    
endmodule