`timescale 1ns / 1ps

module interval_weighted_round_robin #(
    parameter N=4, // Agents
    parameter W=32, // Windows
    parameter CONFIG_WIDTH=4 // Config Width
) (
    input clk,
    input rst_n,
    input [N-1:0] request,
    input [N*CONFIG_WIDTH-1:0] cfg_reg,
    output reg [N-1:0] grant
);

    reg [N-1:0] pri;
    reg [N-1:0] round_robin_counter;
    reg [N-1:0] valid_request;
    reg [W-1:0] window_count;
    reg [CONFIG_WIDTH-1:0] window_config;
    reg grant_set;
    reg grant_pulse;

    generate
        genvar i;
        generate
            for (i = 0; i < W; i = i + 1) begin : WINDOW_ASSIGN
                wire [CONFIG_WIDTH-1:0] tmp_window_config = cfg_reg[(i+1)*CONFIG_WIDTH-1 : i*CONFIG_WIDTH];
                always @(posedge clk or negedge rst_n) begin
                    if (!rst_n) begin
                        if (window_count == i)
                            window_config <= 0;
                    end
                    else begin
                        if (window_count == i)
                            window_config <= tmp_window_config;
                    end
                end
            end
        endgenerate
    endgenerate

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pri <= 0;
            round_robin_counter <= 0;
            valid_request <= 0;
            window_count <= 0;
            grant_set <= 0;
            grant_pulse <= 0;
        end
        else begin
        if (request !== 0) begin
            valid_request <= request;
            pri <= valid_request & ~grant_set;

            if (window_count >= W)
                window_count <= 0;
            else
                window_count <= window_count + 1;

            round_robin_counter <= round_robin_counter + 1;

            if (round_robin_counter >= N)
                round_robin_counter <= 0;
        end

        grant_set <= 0;
        if (valid_request !== 0) begin
            if (pri === 0) begin
                grant_set <= 1;
                pri <= valid_request & ~(1 << round_robin_counter);
            end
        end

        if (grant_set) begin
            grant_pulse <= 1;
        end
        else begin
            grant_pulse <= 0;
        end
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            grant <= 0;
        end
        else begin
            if (grant_pulse) begin
                grant <= 1 << round_robin_counter;
            end
            else begin
                grant <= 0;
            end
        end
    end

endmodule

