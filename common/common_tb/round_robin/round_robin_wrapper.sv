`timescale 1ns / 1ps

module round_robin_wrapper #(parameter N=4) (
    input              clk,
    input              rst_n,
    input              write_A, write_B, write_C, write_D, start_pwm,
    input [7:0]        wr_data_A, wr_data_B, wr_data_C, wr_data_D, rd_data_E,
    output reg         wr_full_A, wr_full_B, wr_full_C, wr_full_D,
    output reg         read_E
);

logic        write_E;
logic [7:0]  rd_data_A, rd_data_B, rd_data_C, rd_data_D;
logic [7:0]  wr_data_E;
logic        pwm_sig, done;
logic [10:0] count;
logic [N-1:0]  request, grant;

sync_fifo
#(
    .DATA_WIDTH       (8),
    .DEPTH            (16),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_sync_fifo_A")
)
u_sync_fifo_A (
    .clk             (clk),
    .rst_n           (rst_n),
    .write           (write_A),
    .wr_data         (wr_data_A),
    .wr_full         (wr_full_A),
    .wr_almost_full  (wr_almost_full_A),
    .read            (read_A),
    .rd_data         (rd_data_A),
    .rd_empty        (rd_empty_A),
    .rd_almost_empty (rd_almost_empty_A)
);

sync_fifo
#(
    .DATA_WIDTH       (8),
    .DEPTH            (8),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_sync_fifo_B")
)
u_sync_fifo_B (
    .clk             (clk),
    .rst_n           (rst_n),
    .write           (write_B),
    .wr_data         (wr_data_B),
    .wr_full         (wr_full_B),
    .wr_almost_full  (wr_almost_full_B),
    .read            (read_B),
    .rd_data         (rd_data_B),
    .rd_empty        (rd_empty_B),
    .rd_almost_empty (rd_almost_empty_B)
);

sync_fifo
#(
    .DATA_WIDTH       (8),
    .DEPTH            (4),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_sync_fifo_C")
)
u_sync_fifo_C (
    .clk             (clk),
    .rst_n           (rst_n),
    .write           (write_C),
    .wr_data         (wr_data_C),
    .wr_full         (wr_full_C),
    .wr_almost_full  (wr_almost_full_C),
    .read            (read_C),
    .rd_data         (rd_data_C),
    .rd_empty        (rd_empty_C),
    .rd_almost_empty (rd_almost_empty_C)
);

sync_fifo
#(
    .DATA_WIDTH       (8),
    .DEPTH            (4),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_sync_fifo_D")
)
u_sync_fifo_D (
    .clk             (clk),
    .rst_n           (rst_n),
    .write           (write_D),
    .wr_data         (wr_data_D),
    .wr_full         (wr_full_D),
    .wr_almost_full  (wr_almost_full_D),
    .read            (read_D),
    .rd_data         (rd_data_D),
    .rd_empty        (rd_empty_D),
    .rd_almost_empty (rd_almost_empty_D)
);

pwm
#(
    .MAX            (2048)
)
u_pwm(
    .clk          (clk),
    .rst_n        (rst_n),
    .high_count   (11'h07F),
    .low_count    (11'h10),
    .repeat_count (11'b0 ),
    .start        (start_pwm),
    .done         (done),
    .pwm_sig      (pwm_sig),
    .count        (count)
);

assign read_A = grant[0];
assign read_B = grant[1];
assign read_C = grant[2];
assign read_D = grant[3];

assign req_A = !rd_empty_A;
assign req_B = !rd_empty_B;
assign req_C = !rd_empty_C;
assign req_D = !rd_empty_D;

assign req_A_mask = !rd_empty_A && !rd_almost_empty_A;
assign req_B_mask = !rd_empty_B && !rd_almost_empty_B;
assign req_C_mask = !rd_empty_C && !rd_almost_empty_C;
assign req_D_mask = !rd_empty_D && !rd_almost_empty_D;
logic [3:0] req_orig;
logic [3:0] req_mask;

always_comb begin
    req_orig = {req_D, req_C, req_B, req_A};
    req_mask = {req_D_mask, req_C_mask, req_B_mask, req_A_mask};
end

assign request = (pwm_sig)? {4'b0000} : ($countones(req_orig)>1) ? req_orig : req_mask;

round_robin_arbiter
#(
    .CLIENTS (4)
)
u_round_robin_arbiter(
    .clk     (clk),
    .rst_n   (rst_n),
    .req     (request),
    .gnt     (grant)
);

assign wr_data_E = grant[3] ? rd_data_D : grant[2] ? rd_data_C : grant[1] ? rd_data_B : rd_data_A;
assign write_E = |grant;

sync_fifo
#(
    .DATA_WIDTH       (8),
    .DEPTH            (4),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_sync_fifo_E")
)
u_sync_fifo_E (
    .clk             (clk),
    .rst_n           (rst_n),
    .write           (write_E),
    .wr_data         (wr_data_E),
    .wr_full         (wr_full_E),
    .wr_almost_full  (wr_almost_full_E),
    .read            (read_E),
    .rd_data         (rd_data_E),
    .rd_empty        (rd_empty_E),
    .rd_almost_empty (rd_almost_empty_E)
);

assign read_E = !rd_empty_E;
// always @(posedge clk or negedge rst_n) begin
//     if (!rst_n) read_E <= 'b0;
//     else        read_E <= !rd_empty_E;
// end

// synopsys translate_off					$(CWD)/../../../common/weighted_round_robin.sv \

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, round_robin_wrapper);
end
// synopsys translate_on
endmodule