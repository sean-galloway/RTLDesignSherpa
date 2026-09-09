// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for wb4_slave. The properties live IN the RTL under
// `ifdef FORMAL. The environment here is a FREE Wishbone master -- CYC may
// drop with transfers outstanding (the abort case a sim loop against
// wb4_master can never reach) -- and a free FUB on cmd_*/rsp_*.

module formal_wb4_slave #(
    parameter int AW = 8,
    parameter int DW = 16,
    parameter int MAX_OUTSTANDING = 3
) (
    input logic clk,
    input logic rst_n,
    // free master
    input logic          s_wb_CYC,
    input logic          s_wb_STB,
    input logic          s_wb_WE,
    input logic [AW-1:0] s_wb_ADR,
    input logic [DW-1:0] s_wb_DAT_W,
    input logic [DW/8-1:0] s_wb_SEL,
    // free FUB
    input logic          cmd_ready,
    input logic          rsp_valid,
    input logic [1:0]    rsp_status,
    input logic [DW-1:0] rsp_dat
);
    logic s_wb_STALL, s_wb_ACK, s_wb_ERR, s_wb_RTY, cmd_valid, cmd_we, rsp_ready;
    logic [DW-1:0] s_wb_DAT_R, cmd_dat;
    logic [AW-1:0] cmd_adr;
    logic [DW/8-1:0] cmd_sel;

    wb4_slave #(.ADDR_WIDTH(AW), .DATA_WIDTH(DW), .CMD_DEPTH(2), .RSP_DEPTH(2),
                .MAX_OUTSTANDING(MAX_OUTSTANDING)) dut (
        .clk(clk), .aresetn(rst_n),
        .s_wb_CYC(s_wb_CYC), .s_wb_STB(s_wb_STB), .s_wb_WE(s_wb_WE),
        .s_wb_ADR(s_wb_ADR), .s_wb_DAT_W(s_wb_DAT_W), .s_wb_SEL(s_wb_SEL),
        .s_wb_STALL(s_wb_STALL), .s_wb_ACK(s_wb_ACK), .s_wb_ERR(s_wb_ERR),
        .s_wb_RTY(s_wb_RTY), .s_wb_DAT_R(s_wb_DAT_R),
        .cmd_valid(cmd_valid), .cmd_ready(cmd_ready), .cmd_we(cmd_we),
        .cmd_adr(cmd_adr), .cmd_dat(cmd_dat), .cmd_sel(cmd_sel),
        .rsp_valid(rsp_valid), .rsp_ready(rsp_ready),
        .rsp_status(rsp_status), .rsp_dat(rsp_dat)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // ---- Master model: STB implies CYC; a stalled request is held ----
    always @(*) assume (!s_wb_STB || s_wb_CYC);
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(s_wb_CYC && s_wb_STB && s_wb_STALL)) begin
            assume (s_wb_CYC && s_wb_STB);
            assume ($stable(s_wb_WE) && $stable(s_wb_ADR) && $stable(s_wb_DAT_W) && $stable(s_wb_SEL));
        end
    end
    // FUB: a response, once offered, is held until taken.
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(rsp_valid && !rsp_ready)) begin
            assume (rsp_valid);
            assume ($stable(rsp_status) && $stable(rsp_dat));
        end
    end

    // ---- Port-level properties ----
    logic w_accept;
    assign w_accept = s_wb_CYC && s_wb_STB && !s_wb_STALL;
    reg [7:0] f_open;   // the master's view of accepted-not-terminated
    always @(posedge clk) begin
        if (!rst_n || !s_wb_CYC) f_open <= 0;
        else f_open <= f_open + w_accept - (s_wb_ACK || s_wb_ERR || s_wb_RTY);
    end
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        // Command side honours valid/ready: sticky valid, stable payload.
        if ($past(cmd_valid && !cmd_ready)) begin
            ap_cmd_sticky: assert (cmd_valid);
            ap_cmd_stable: assert ($stable(cmd_we) && $stable(cmd_adr) &&
                                   $stable(cmd_dat) && $stable(cmd_sel));
        end
        // The master never sees more terminations than it had accepted.
        ap_no_overterm: assert (!(s_wb_ACK || s_wb_ERR || s_wb_RTY) || $past(f_open) != 0 || $past(w_accept));
        // Reset leaves the bus quiet.
        if ($past(!rst_n)) ap_quiet: assert (!s_wb_ACK && !s_wb_ERR && !s_wb_RTY);
    end

    // ---- Covers ----
    always @(posedge clk) if (rst_n) begin
        cp_ack:       cover (s_wb_ACK);
        cp_err:       cover (s_wb_ERR);
        cp_rty:       cover (s_wb_RTY);
        cp_stall_full: cover (s_wb_STALL && s_wb_STB);
        cp_abort:     cover (f_past_valid > 3 && $past(s_wb_CYC) && !s_wb_CYC && $past(f_open) != 0);
        cp_backtoback: cover ($past(w_accept) && w_accept);
    end
endmodule
