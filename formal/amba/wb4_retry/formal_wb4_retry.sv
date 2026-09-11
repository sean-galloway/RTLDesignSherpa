// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for wb4_retry. The in-RTL `ifdef FORMAL` assertions ride
// along through sv2v --define=FORMAL; this file adds the port-level
// contract with a free FUB and a free master:
//
//   P1: open commands (accepted - answered) never exceed INFLIGHT, and a
//       FUB response only appears with something open
//   P2: the master never sees more than INFLIGHT commands unanswered
//   P3: (INFLIGHT=1) every command the master sees while a FUB command is
//       open carries that command's payload -- a retry re-issues the same
//       request, and nothing else reaches the bus meanwhile
//   P4: (INFLIGHT=1) the master sees exactly 1 + retries issues per FUB
//       command, retries <= cfg_max_retries, and the FUB gets RTY only
//       when the budget was spent (or is zero); ACK/ERR pass straight back
//   P5: (INFLIGHT=1) a re-issue happens no sooner than cfg_retry_delay
//       clocks after the RTY
//
// Covers: a retry that then ACKs; RTY handed to the FUB after the budget;
// pass-through with cfg_max_retries = 0; (INFLIGHT=2) two open at once.

module formal_wb4_retry #(
    parameter int INFLIGHT = 1
) (
    input logic clk,
    input logic rst_n
);
    localparam int AW = 8;
    localparam int DW = 16;
    localparam int SW = DW / 8;
    localparam int CTW = 3;    // WB4_CTI_WIDTH
    localparam int BTW = 2;    // WB4_BTE_WIDTH

    (* anyseq *) reg [7:0]     cfg_max_retries;
    (* anyseq *) reg [15:0]    cfg_retry_delay;
    (* anyseq *) reg           cmd_valid;
    (* anyseq *) reg           cmd_we;
    (* anyseq *) reg [AW-1:0]  cmd_adr;
    (* anyseq *) reg [DW-1:0]  cmd_dat;
    (* anyseq *) reg [SW-1:0]  cmd_sel;
    (* anyseq *) reg [CTW-1:0] cmd_cti;
    (* anyseq *) reg [BTW-1:0] cmd_bte;
    (* anyseq *) reg           rsp_ready;
    (* anyseq *) reg           mst_cmd_ready;
    (* anyseq *) reg           mst_rsp_valid;
    (* anyseq *) reg [1:0]     mst_rsp_status;
    (* anyseq *) reg [DW-1:0]  mst_rsp_dat;

    wire           cmd_ready, rsp_valid, mst_cmd_valid, mst_cmd_we, mst_rsp_ready;
    wire [1:0]     rsp_status;
    wire [DW-1:0]  rsp_dat, mst_cmd_dat;
    wire [AW-1:0]  mst_cmd_adr;
    wire [SW-1:0]  mst_cmd_sel;
    wire [CTW-1:0] mst_cmd_cti;
    wire [BTW-1:0] mst_cmd_bte;
    wire [31:0]    retry_count;
    wire [7:0]     active_count;

    wb4_retry #(.ADDR_WIDTH (AW), .DATA_WIDTH (DW), .INFLIGHT (INFLIGHT)) dut (
        .clk (clk), .aresetn (rst_n),
        .cfg_max_retries (cfg_max_retries), .cfg_retry_delay (cfg_retry_delay),
        .cmd_valid (cmd_valid), .cmd_ready (cmd_ready), .cmd_we (cmd_we), .cmd_adr (cmd_adr),
        .cmd_dat (cmd_dat), .cmd_sel (cmd_sel),
        .cmd_cti (cmd_cti), .cmd_bte (cmd_bte),
        .rsp_valid (rsp_valid), .rsp_ready (rsp_ready), .rsp_status (rsp_status), .rsp_dat (rsp_dat),
        .mst_cmd_valid (mst_cmd_valid), .mst_cmd_ready (mst_cmd_ready), .mst_cmd_we (mst_cmd_we),
        .mst_cmd_adr (mst_cmd_adr), .mst_cmd_dat (mst_cmd_dat), .mst_cmd_sel (mst_cmd_sel),
        .mst_cmd_cti (mst_cmd_cti), .mst_cmd_bte (mst_cmd_bte),
        .mst_rsp_valid (mst_rsp_valid), .mst_rsp_ready (mst_rsp_ready),
        .mst_rsp_status (mst_rsp_status), .mst_rsp_dat (mst_rsp_dat),
        .retry_count (retry_count), .active_count (active_count)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // Config stable; small budgets keep the proof depth useful.
    always @(posedge clk) if (f_past_valid > 0) begin
        assume (cfg_max_retries == $past(cfg_max_retries));
        assume (cfg_retry_delay == $past(cfg_retry_delay));
    end
    always @(*) begin
        assume (cfg_max_retries <= 2);
        assume (cfg_retry_delay <= 3);
        assume (mst_rsp_status != 2'b11);          // not an encoding
    end
    // Held valids (queues in front and behind hold their payload).
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(cmd_valid && !cmd_ready))
            assume (cmd_valid && cmd_we == $past(cmd_we) && cmd_adr == $past(cmd_adr) &&
                    cmd_dat == $past(cmd_dat) && cmd_sel == $past(cmd_sel));
        if ($past(mst_rsp_valid && !mst_rsp_ready))
            assume (mst_rsp_valid && mst_rsp_status == $past(mst_rsp_status) && mst_rsp_dat == $past(mst_rsp_dat));
    end

    wire f_cmd_hs = cmd_valid && cmd_ready;
    wire f_rsp_hs = rsp_valid && rsp_ready;
    wire f_mc_hs  = mst_cmd_valid && mst_cmd_ready;
    wire f_mr_hs  = mst_rsp_valid && mst_rsp_ready;

    // A well-behaved master answers only what it was given.
    reg [7:0] f_bus_open;
    initial f_bus_open = 0;
    always @(posedge clk) if (!rst_n) f_bus_open <= 0; else f_bus_open <= f_bus_open + f_mc_hs - f_mr_hs;
    always @(*) if (rst_n) assume (!mst_rsp_valid || f_bus_open != 0);

    reg [7:0] f_open;
    initial f_open = 0;
    always @(posedge clk) if (!rst_n) f_open <= 0; else f_open <= f_open + f_cmd_hs - f_rsp_hs;

    always @(posedge clk) if (rst_n) begin
        ap_open_bound:     assert (f_open <= INFLIGHT);
        ap_rsp_when_open:  assert (!rsp_valid || f_open != 0);
        ap_bus_bound:      assert (f_bus_open <= INFLIGHT);
        ap_active_matches: assert (active_count == f_open);
    end

    // ---- INFLIGHT = 1: payload equality and the retry budget -------------
    generate if (INFLIGHT == 1) begin : g_one
        reg           f_pend_we;
        reg [AW-1:0]  f_pend_adr;
        reg [DW-1:0]  f_pend_dat;
        reg [SW-1:0]  f_pend_sel;
        // The burst hints are part of the payload a re-issue must reproduce.
        // They were NOT here until 2026-09-11, and their absence is why the
        // wrapper could route them around the buffer unnoticed: every other
        // field was proven identical on re-issue while CTI/BTE came off the
        // live FUB pins, so a retried transfer carried a neighbour's hint.
        reg [CTW-1:0] f_pend_cti;
        reg [BTW-1:0] f_pend_bte;
        reg [7:0]     f_issues;      // master issues for the open command
        reg [7:0]     f_rtys;        // RTYs received for it
        reg [7:0]     f_since_rty;   // clocks since the last RTY (saturating)
        reg           f_last_was_rty;
        initial begin f_issues = 0; f_rtys = 0; f_since_rty = 8'hFF; f_last_was_rty = 0; end
        always @(posedge clk) begin
            if (!rst_n) begin
                f_issues <= 0; f_rtys <= 0; f_since_rty <= 8'hFF; f_last_was_rty <= 0;
            end else begin
                if (f_cmd_hs) begin
                    f_pend_we <= cmd_we; f_pend_adr <= cmd_adr; f_pend_dat <= cmd_dat; f_pend_sel <= cmd_sel;
                    f_pend_cti <= cmd_cti; f_pend_bte <= cmd_bte;
                    f_issues <= 1; f_rtys <= 0; f_last_was_rty <= 0;
                end else if (f_mc_hs)
                    f_issues <= f_issues + 1;
                if (f_mr_hs) begin
                    f_last_was_rty <= (mst_rsp_status == 2'd2);
                    if (mst_rsp_status == 2'd2) begin f_rtys <= f_rtys + 1; f_since_rty <= 0; end
                end else if (f_since_rty != 8'hFF)
                    f_since_rty <= f_since_rty + 1;
            end
        end
        always @(posedge clk) if (rst_n && f_open != 0) begin
            // P3
            ap_retry_same: assert (!(f_mc_hs) || (mst_cmd_we == f_pend_we && mst_cmd_adr == f_pend_adr &&
                                                 mst_cmd_dat == f_pend_dat && mst_cmd_sel == f_pend_sel &&
                                                 mst_cmd_cti == f_pend_cti && mst_cmd_bte == f_pend_bte));
            // P4: a re-issue only after an RTY within budget
            ap_reissue_budget: assert (!(f_mc_hs && f_issues != 0) || (f_rtys <= cfg_max_retries && f_rtys == f_issues));
            ap_issues_bound:   assert (f_issues <= 8'(cfg_max_retries) + 1);
            // P5: no re-issue sooner than the delay
            ap_delay: assert (!(f_mc_hs && f_issues != 0) || (f_since_rty >= 8'(cfg_retry_delay)));
        end
        always @(posedge clk) if (rst_n && rsp_valid) begin
            // RTY reaches the FUB only once the budget is spent
            ap_rty_only_exhausted: assert (rsp_status != 2'd2 || f_rtys == 8'(cfg_max_retries) + 1);
            // ACK/ERR came from the last termination
            ap_status_is_last: assert (rsp_status == 2'd2 || !f_last_was_rty);
        end
        always @(posedge clk) if (rst_n) begin
            cp_retry_then_ack: cover (f_rsp_hs && rsp_status == 2'd0 && f_rtys == 1);
            cp_rty_exhausted:  cover (f_rsp_hs && rsp_status == 2'd2 && cfg_max_retries == 1);
            cp_passthrough:    cover (f_rsp_hs && rsp_status == 2'd2 && cfg_max_retries == 0 && f_issues == 1);
            cp_delayed_retry:  cover (f_mc_hs && f_issues == 1 && cfg_retry_delay == 2);
            cp_err_direct:     cover (f_rsp_hs && rsp_status == 2'd1 && f_issues == 1);
        end
    end else begin : g_many
        always @(posedge clk) if (rst_n) begin
            cp_two_open:  cover (f_open == INFLIGHT);
            cp_retry_pipe: cover (f_open == INFLIGHT && retry_count != 0);
            cp_drain:     cover (f_past_valid > 8 && f_open == 0 && retry_count != 0);
        end
    end endgenerate
endmodule
