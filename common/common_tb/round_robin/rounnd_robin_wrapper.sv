`timescale 1ns / 1ps

module round_robin_wrapper #(parameter N=4) (
    input              clk,
    input              rst_n,
    input              write_A, write_B, write_C, write_D, start_pwm;
    input [7:0]        wr_data_A, wr_data_B, wr_data_C, wr_data_D, read_data_E;
    output reg         wr_full_A, wr_full_B, wr_full_C, wr_full_d;
)

logic        write_E, read_E;
logic [7:0]  wr_data_E;
logic        pwm_sig, done;
logic [11:0] count;

sync_fifo 
#(
    .DATA_WIDTH       (8),
    .DEPTH            (16),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1)
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
    .ALMOST_RD_MARGIN (1)
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
    .ALMOST_RD_MARGIN (1)
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
    .ALMOST_RD_MARGIN (1)
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
    .high_count   ('h7FF),
    .low_count    ('h10),
    .repeat_count ('b0 ),
    .start        (start_pwm),
    .done         (done),
    .pwm_sig      (pwm_sig),
    .count        (count)
);

assign read_A = grant[0];
assign read_B = grant[1];
assign read_C = grant[2];
assign read_D = grant[3];

assign request = (pwm_sig)? {4'b0000} : {!rd_empty_D, !rd_empty_C, !rd_empty_B, !rd_empty_A};

round_robin_arbiter 
#(
    .N (4)
)
u_round_robin_arbiter(
    .clk     (clk),
    .rst_n   (rst_n),
    .request (request),
    .grant   (grant)
);

assign wr_data_E = grant[3] ? read_data_D : grant[2] ? read_data_C : grant[1] ? read_data_B : read_data_A;

sync_fifo 
#(
    .DATA_WIDTH       (8),
    .DEPTH            (4),
    .ALMOST_WR_MARGIN (1),
    .ALMOST_RD_MARGIN (1)
)
u_sync_fifo_E (
    .clk             (clk),
    .rst_n           (rst_n),
    .write           (write_E),
    .wr_Eata         (wr_data_E),
    .wr_full         (wr_full_E),
    .wr_almost_full  (wr_almost_full_E),
    .read            (read_E),
    .rd_data         (rd_data_E),
    .rd_empty        (rd_empty_E),
    .rd_almost_empty (rd_almost_empty_E)
);

assign read_E = !rd_empty_E;

endmodule