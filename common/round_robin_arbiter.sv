`timescale 1ns / 1ps

module round_robin_arbiter #(parameter N=4) (
    input              clk,
    input              rst_n,
    input      [N-1:0] request,
    output reg [N-1:0] grant
);

    reg [N-1:0] pri;
    reg [N-1:0] round_robin_counter;
    reg [N-1:0] valid_request;
    reg grant_set;
    reg grant_pulse;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pri <= 0;
            round_robin_counter <= 0;
            valid_request <= 0;
            grant_set <= 0;
            grant_pulse <= 0;
        end
        else begin
            if (request !== 0) begin
                valid_request <= request;
                pri <= valid_request & ~grant_set;
                round_robin_counter <= round_robin_counter + 1;
                if (round_robin_counter >= N)
                    round_robin_counter <= 0;
            end

            grant_set <= 0;
            if (valid_request !== 0) begin
                if (pri !== 0 && valid_request[round_robin_counter]) begin
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

