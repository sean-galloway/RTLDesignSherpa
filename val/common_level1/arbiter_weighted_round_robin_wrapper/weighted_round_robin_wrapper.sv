`timescale 1ns / 1ps

module weighted_round_robin_wrapper #(parameter int N=4) (
    input              i_clk,
    input              i_rst_n,
    input              i_write_A, i_write_B, i_write_C, i_write_D, start_pwm,
    input [7:0]        i_wr_data_A, i_wr_data_B, i_wr_data_C, i_wr_data_D, ow_rd_data_E,
    output reg         o_wr_full_A, o_wr_full_B, o_wr_full_C, o_wr_full_D,
    output reg         i_read_E
);

logic        i_write_E;
logic [7:0]  ow_rd_data_A, ow_rd_data_B, ow_rd_data_C, ow_rd_data_D;
logic [7:0]  i_wr_data_E;
logic        pwm_sig, done;
logic [10:0] count;
logic [N-1:0]  request, grant;

fifo_sync
#(
    .DATA_WIDTH       (8),
    .DEPTH            (40),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_fifo_sync_A")
)
u_fifo_sync_A (
    .i_clk              (i_clk),
    .i_rst_n            (i_rst_n),
    .i_write            (i_write_A),
    .i_wr_data          (i_wr_data_A),
    .o_wr_full         (o_wr_full_A),
    .o_wr_almost_full  (o_wr_almost_full_A),
    .i_read             (i_read_A),
    .ow_rd_data         (ow_rd_data_A),
    .o_rd_empty        (o_rd_empty_A),
    .o_rd_almost_empty (o_rd_almost_empty_A)
);

fifo_sync
#(
    .DATA_WIDTH       (8),
    .DEPTH            (24),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_fifo_sync_B")
)
u_fifo_sync_B (
    .i_clk              (i_clk),
    .i_rst_n            (i_rst_n),
    .i_write            (i_write_B),
    .i_wr_data          (i_wr_data_B),
    .o_wr_full         (o_wr_full_B),
    .o_wr_almost_full  (o_wr_almost_full_B),
    .i_read             (i_read_B),
    .ow_rd_data         (ow_rd_data_B),
    .o_rd_empty        (o_rd_empty_B),
    .o_rd_almost_empty (o_rd_almost_empty_B)
);

fifo_sync
#(
    .DATA_WIDTH       (8),
    .DEPTH            (12),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_fifo_sync_C")
)
u_fifo_sync_C (
    .i_clk              (i_clk),
    .i_rst_n            (i_rst_n),
    .i_write            (i_write_C),
    .i_wr_data          (i_wr_data_C),
    .o_wr_full         (o_wr_full_C),
    .o_wr_almost_full  (o_wr_almost_full_C),
    .i_read             (i_read_C),
    .ow_rd_data         (ow_rd_data_C),
    .o_rd_empty        (o_rd_empty_C),
    .o_rd_almost_empty (o_rd_almost_empty_C)
);

fifo_sync
#(
    .DATA_WIDTH       (4),
    .DEPTH            (6),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_fifo_sync_D")
)
u_fifo_sync_D (
    .i_clk              (i_clk),
    .i_rst_n            (i_rst_n),
    .i_write            (i_write_D),
    .i_wr_data          (i_wr_data_D),
    .o_wr_full         (o_wr_full_D),
    .o_wr_almost_full  (o_wr_almost_full_D),
    .i_read             (i_read_D),
    .ow_rd_data         (ow_rd_data_D),
    .o_rd_empty        (o_rd_empty_D),
    .o_rd_almost_empty (o_rd_almost_empty_D)
);

pwm
#(
    .WIDTH (11),
    .CHANNELS (1)
)
u_pwm(
    .i_clk          (i_clk),
    .i_rst_n        (i_rst_n),
    .i_start        (start_pwm),
    .i_duty         (11'h07F),
    .i_period       (11'h7FF),
    .i_repeat_count (11'h001),
    .ow_done        (done),
    .o_pwm          (pwm_sig)
);

assign i_read_A = grant[0];
assign i_read_B = grant[1];
assign i_read_C = grant[2];
assign i_read_D = grant[3];

assign req_A = !o_rd_empty_A;
assign req_B = !o_rd_empty_B;
assign req_C = !o_rd_empty_C;
assign req_D = !o_rd_empty_D;

assign req_A_mask = !o_rd_empty_A && !o_rd_almost_empty_A;
assign req_B_mask = !o_rd_empty_B && !o_rd_almost_empty_B;
assign req_C_mask = !o_rd_empty_C && !o_rd_almost_empty_C;
assign req_D_mask = !o_rd_empty_D && !o_rd_almost_empty_D;
logic [3:0] req_orig;
logic [3:0] req_mask;

always_comb begin
    req_orig = {req_D, req_C, req_B, req_A};
    req_mask = {req_D_mask, req_C_mask, req_B_mask, req_A_mask};
end

assign request = ($countones(req_orig)>1) ? req_orig : req_mask;

arbiter_weighted_round_robin
#(
    .MAX_THRESH(15),
    .CLIENTS   (4)
)
u_weighted_round_robin (
    .i_clk             (i_clk),
    .i_rst_n           (i_rst_n),
    .i_max_thresh      ({4'b0110, 4'b0100, 4'b0010, 4'b0001}),
    .i_req             (request),
    .i_block_arb       (pwm_sig),
    .ow_grant          (grant)
);

assign i_wr_data_E = grant[3] ? ow_rd_data_D :
                        grant[2] ? ow_rd_data_C :
                        grant[1] ? ow_rd_data_B : ow_rd_data_A;
assign i_write_E = |grant;

fifo_sync
#(
    .DATA_WIDTH       (8),
    .DEPTH            (4),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1),
    .INSTANCE_NAME("u_fifo_sync_E")
)
u_fifo_sync_E (
    .i_clk              (i_clk),
    .i_rst_n            (i_rst_n),
    .i_write            (i_write_E),
    .i_wr_data          (i_wr_data_E),
    .o_wr_full         (o_wr_full_E),
    .o_wr_almost_full  (o_wr_almost_full_E),
    .i_read             (i_read_E),
    .ow_rd_data         (ow_rd_data_E),
    .o_rd_empty        (o_rd_empty_E),
    .o_rd_almost_empty (o_rd_almost_empty_E)
);

assign i_read_E = !o_rd_empty_E;
// always @(posedge i_clk or negedge i_rst_n) begin
//     if (!i_rst_n) i_read_E <= 'b0;
//     else        i_read_E <= !o_rd_empty_E;
// end

// synopsys translate_off
initial begin
    $dumpfile("waves.vcd");
    $dumpvars(0, weighted_round_robin_wrapper);
end
// synopsys translate_on

endmodule
