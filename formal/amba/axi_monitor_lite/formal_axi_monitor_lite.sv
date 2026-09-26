// Formal harness for axi_monitor_lite (amba/monitor-lite TASK-001): a read monitor with a
// 4-slot table under UNCONSTRAINED taps. The monitor watches traffic it does
// not control, so the properties are about the monitor's own promises, not
// about the bus being well-behaved:
//   - active_count never exceeds the table (the popcount is bounded by N);
//   - a synchronous clear empties the table on the next cycle;
//   - the monbus keeps valid/ready: a packet offered and not taken is still
//     there, unchanged, the next cycle;
//   - covers: a completion, an error, a timeout and a threshold packet are
//     each reachable, so the proof is not vacuous.
`include "reset_defs.svh"
module formal_axi_monitor_lite (
    input logic clk,
    input logic rst_n
);
    localparam int N  = 4;
    localparam int AW = 16;
    localparam int IW = 2;

    (* anyseq *) reg              clear;
    (* anyseq *) reg [63:0]       mon_time;
    (* anyseq *) reg [AW-1:0]     cmd_addr;
    (* anyseq *) reg [IW-1:0]     cmd_id;
    (* anyseq *) reg [7:0]        cmd_len;
    (* anyseq *) reg              cmd_valid, cmd_ready;
    (* anyseq *) reg [IW-1:0]     data_id;
    (* anyseq *) reg              data_last;
    (* anyseq *) reg [1:0]        data_resp;
    (* anyseq *) reg              data_valid, data_ready;
    (* anyseq *) reg [3:0]        cfg_freq_sel;
    (* anyseq *) reg [15:0]       cfg_timeout_cnt;
    (* anyseq *) reg              monbus_ready;

    wire         monbus_valid;
    wire [127:0] monbus_packet;
    wire [63:0]  monbus_timestamp;
    wire [7:0]   active_count;
    wire         busy;
    wire [15:0]  perf_completed_count, perf_error_count, dropped_count, refused_count;

    axi_monitor_lite #(
        .MAX_TRANSACTIONS (N),
        .ADDR_WIDTH       (AW),
        .ID_WIDTH         (IW),
        .IS_READ          (1'b1),
        .IS_AXI           (1'b1),
        .CFI_MIN_FREQ_MHZ (5),
        .CFI_MAX_FREQ_MHZ (20),
        .CFI_NUM_FREQ_ENTRIES (4)
    ) dut (
        .aclk (clk), .aresetn (rst_n), .clear (clear), .i_mon_time (mon_time),
        .cmd_addr (cmd_addr), .cmd_id (cmd_id), .cmd_len (cmd_len), .cmd_valid (cmd_valid), .cmd_ready (cmd_ready),
        .data_id (data_id), .data_last (data_last), .data_resp (data_resp), .data_valid (data_valid), .data_ready (data_ready),
        .resp_id ('0), .resp_code ('0), .resp_valid (1'b0), .resp_ready (1'b0),
        .cfg_freq_sel (cfg_freq_sel[1:0]), .cfg_timeout_cnt (cfg_timeout_cnt),
        .cfg_error_enable (1'b1), .cfg_compl_enable (1'b1), .cfg_timeout_enable (1'b1), .cfg_threshold_enable (1'b1),
        .cfg_active_trans_threshold (16'd2), .cfg_axi_pkt_mask (16'h0),
        .monbus_valid (monbus_valid), .monbus_ready (monbus_ready), .monbus_packet (monbus_packet), .monbus_timestamp (monbus_timestamp),
        .active_count (active_count), .busy (busy),
        .perf_completed_count (perf_completed_count), .perf_error_count (perf_error_count),
        .dropped_count (dropped_count), .refused_count (refused_count)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // the table is bounded
    always @(posedge clk) if (rst_n)
        ap_count_bounded: assert (active_count <= N);

    // clear empties the table
    always @(posedge clk) if (f_past_valid > 1 && rst_n && $past(rst_n) && $past(clear))
        ap_clear_empties: assert (active_count == 8'd0);

    // valid/ready: a packet not taken stays put, unchanged
    always @(posedge clk) if (f_past_valid > 1 && rst_n && $past(rst_n) && $past(monbus_valid) && !$past(monbus_ready)) begin
        ap_hold_valid:  assert (monbus_valid);
        ap_hold_packet: assert (monbus_packet == $past(monbus_packet));
    end

    // covers: every packet class the lite emits is reachable
    always @(posedge clk) if (rst_n && monbus_valid) begin
        cp_compl:   cover (monbus_packet[127:124] == 4'h1);
        cp_error:   cover (monbus_packet[127:124] == 4'h0);
        cp_timeout: cover (monbus_packet[127:124] == 4'h3);
        cp_thresh:  cover (monbus_packet[127:124] == 4'h2);
        cp_full:    cover (active_count == N);
    end
endmodule
