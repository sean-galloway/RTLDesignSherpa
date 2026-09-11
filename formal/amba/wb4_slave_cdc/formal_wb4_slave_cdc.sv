// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for wb4_slave_cdc. Single-clock model (wb_clk = aclk =
// clk, both resets = rst_n), as the apb4_slave_cdc harness does: the
// crossing FIFOs are exercised as FIFOs, and the port-level contract of
// the slave is checked through them.
//   P1: after reset: no termination, no command
//   P2: terminations only for accepted requests (never over-terminate)
//   P3: commands to the FUB never exceed accepted requests; responses from
//       the FUB never exceed commands handed out
//   P4: one-hot terminations
//   P5: payload integrity through both crossings (single-outstanding case)
// Covers: an accept, a command handed to the FUB, a termination, two
// requests open across the crossing.
module formal_wb4_slave_cdc (
    input logic clk,
    input logic rst_n
);
    localparam int AW = 8;
    localparam int DW = 16;
    localparam int SW = DW / 8;

    (* anyseq *) reg            s_wb_CYC, s_wb_STB, s_wb_WE, cmd_ready, rsp_valid;
    (* anyseq *) reg [AW-1:0]   s_wb_ADR;
    (* anyseq *) reg [DW-1:0]   s_wb_DAT_W, rsp_dat;
    (* anyseq *) reg [SW-1:0]   s_wb_SEL;
    // The burst hints are part of the request. Leaving them unconnected
    // pins them at CLASSIC/LINEAR, so every property here would have
    // been proved for one hint value only.
    (* anyseq *) reg [2:0]      s_wb_CTI;
    (* anyseq *) reg [1:0]      s_wb_BTE;
    (* anyseq *) reg [1:0]      rsp_status;

    wire s_wb_STALL, s_wb_ACK, s_wb_ERR, s_wb_RTY, cmd_valid, cmd_we, rsp_ready;
    wire [DW-1:0] s_wb_DAT_R, cmd_dat;
    wire [AW-1:0] cmd_adr;
    wire [SW-1:0] cmd_sel;

    wb4_slave_cdc #(.ADDR_WIDTH (AW), .DATA_WIDTH (DW), .CMD_DEPTH (2), .RSP_DEPTH (2),
                    .MAX_OUTSTANDING (2), .CDC_DEPTH (4)) dut (
        .wb_clk (clk), .wb_resetn (rst_n), .aclk (clk), .aresetn (rst_n),
        .s_wb_CYC (s_wb_CYC), .s_wb_STB (s_wb_STB), .s_wb_WE (s_wb_WE), .s_wb_ADR (s_wb_ADR),
        .s_wb_DAT_W (s_wb_DAT_W), .s_wb_SEL (s_wb_SEL),
        .s_wb_CTI (s_wb_CTI), .s_wb_BTE (s_wb_BTE), .s_wb_STALL (s_wb_STALL),
        .s_wb_ACK (s_wb_ACK), .s_wb_ERR (s_wb_ERR), .s_wb_RTY (s_wb_RTY), .s_wb_DAT_R (s_wb_DAT_R),
        .cmd_valid (cmd_valid), .cmd_ready (cmd_ready), .cmd_we (cmd_we), .cmd_adr (cmd_adr),
        .cmd_dat (cmd_dat), .cmd_sel (cmd_sel),
        .rsp_valid (rsp_valid), .rsp_ready (rsp_ready), .rsp_status (rsp_status), .rsp_dat (rsp_dat)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);
    wire w_accept = s_wb_CYC && s_wb_STB && !s_wb_STALL;
    wire w_term   = s_wb_ACK || s_wb_ERR || s_wb_RTY;
    wire w_fub    = cmd_valid && cmd_ready;
    wire w_rsp    = rsp_valid && rsp_ready;
    reg [7:0] f_open, f_cmds, f_fub_open;
    always @(posedge clk) if (!rst_n) begin f_open <= 0; f_cmds <= 0; f_fub_open <= 0; end
        else begin
            f_open <= f_open + w_accept - w_term;
            f_cmds <= f_cmds + w_accept - w_fub;
            f_fub_open <= f_fub_open + w_fub - w_rsp;
        end

    always @(*) begin
        assume (!s_wb_STB || s_wb_CYC);
        assume (rsp_status != 2'b11);
    end
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(s_wb_STB && s_wb_STALL)) begin
            assume (s_wb_CYC && s_wb_STB);
            assume ($stable(s_wb_WE) && $stable(s_wb_ADR) && $stable(s_wb_DAT_W) && $stable(s_wb_SEL));
        end
        if ($past(rsp_valid && !rsp_ready)) begin
            assume (rsp_valid);
            assume ($stable(rsp_status) && $stable(rsp_dat));
        end
        // The master keeps the cycle open until everything terminates
        // (abort is the base slave's business, proven there).
        if ($past(s_wb_CYC) && ($past(f_open) != 0 || $past(w_accept))) assume (s_wb_CYC);
    end

    always @(*) if (rst_n && f_fub_open == 0) assume (!rsp_valid);

    always @(posedge clk) if (f_past_valid > 0 && $past(!rst_n)) begin
        ap_reset_quiet: assert (!w_term);
        ap_reset_cmd:   assert (!cmd_valid);
    end
    // Payload integrity through the crossings, checked on the single-
    // outstanding case where the head is unambiguous.
    reg           f_we;
    reg [AW-1:0]  f_adr;
    reg [DW-1:0]  f_dat, f_rdat;
    reg [SW-1:0]  f_sel;
    reg [1:0]     f_status;
    always @(posedge clk) if (w_accept) begin
        f_we <= s_wb_WE; f_adr <= s_wb_ADR; f_dat <= s_wb_DAT_W; f_sel <= s_wb_SEL;
    end
    always @(posedge clk) if (w_rsp) begin
        f_status <= rsp_status; f_rdat <= rsp_dat;
    end
    always @(posedge clk) if (rst_n && f_cmds == 1 && cmd_valid && !w_accept) begin
        ap_cmd_payload: assert (cmd_we == f_we && cmd_adr == f_adr && cmd_dat == f_dat && cmd_sel == f_sel);
    end
    always @(posedge clk) if (rst_n && w_term && f_open == 1 && f_fub_open == 0 && !w_rsp) begin
        ap_rsp_payload: assert ((s_wb_ACK == (f_status == 2'd0)) && (s_wb_ERR == (f_status == 2'd1)) &&
                                (s_wb_RTY == (f_status == 2'd2)) && (s_wb_ACK && !f_we ? s_wb_DAT_R == f_rdat : 1'b1));
    end

    always @(posedge clk) if (rst_n) begin
        ap_no_overterm:  assert (!w_term || f_open != 0);
        ap_cmds_bounded: assert (!cmd_valid || f_cmds != 0);
        ap_onehot:       assert ((s_wb_ACK + s_wb_ERR + s_wb_RTY) <= 1);
        ap_open_bound:   assert (f_open <= 2);
    end
    always @(posedge clk) if (rst_n) begin
        cp_accept:   cover (w_accept);
        cp_cmd:      cover (w_fub);
        cp_term:     cover (w_term);
        cp_two_open: cover (f_open == 2);
        cp_rty:      cover (s_wb_RTY);
    end
endmodule
