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
    parameter int MAX_OUTSTANDING = 3,
    parameter int CLASSIC = 0
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
    input logic [2:0]      s_wb_CTI,
    input logic [1:0]      s_wb_BTE,
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
                .MAX_OUTSTANDING(MAX_OUTSTANDING), .CLASSIC(CLASSIC)) dut (
        .clk(clk), .aresetn(rst_n),
        .s_wb_CYC(s_wb_CYC), .s_wb_STB(s_wb_STB), .s_wb_WE(s_wb_WE),
        .s_wb_ADR(s_wb_ADR), .s_wb_DAT_W(s_wb_DAT_W), .s_wb_SEL(s_wb_SEL),
        .s_wb_CTI(s_wb_CTI), .s_wb_BTE(s_wb_BTE),
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

    // ---- Master model: STB implies CYC; a stalled request is held.
    // Classic: the request is held on STB until the termination.
    logic w_term_o;
    assign w_term_o = s_wb_ACK || s_wb_ERR || s_wb_RTY;
    always @(*) assume (!s_wb_STB || s_wb_CYC);
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if (CLASSIC == 0) begin
            if ($past(s_wb_CYC && s_wb_STB && s_wb_STALL)) begin
                assume (s_wb_CYC && s_wb_STB);
                assume ($stable(s_wb_WE) && $stable(s_wb_ADR) && $stable(s_wb_DAT_W) && $stable(s_wb_SEL));
            end
        end else begin
            if ($past(s_wb_CYC && s_wb_STB) && !$past(w_term_o)) begin
                assume (s_wb_CYC && s_wb_STB);
                assume ($stable(s_wb_WE) && $stable(s_wb_ADR) && $stable(s_wb_DAT_W) && $stable(s_wb_SEL));
            end
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
    reg [7:0] f_open;   // the master's view of accepted-not-terminated
    generate if (CLASSIC != 0) begin : g_cm
        // Classic: a presentation opens one request; it stays open until terminated.
        assign w_accept = s_wb_CYC && s_wb_STB && (f_open == 0);
    end else begin : g_pm
        assign w_accept = s_wb_CYC && s_wb_STB && !s_wb_STALL;
    end endgenerate
    always @(posedge clk) begin
        if (!rst_n || !s_wb_CYC) f_open <= 0;
        else f_open <= f_open + w_accept - w_term_o;
    end
    // Responses still owed for transfers the master abandoned (harness view).
    reg [7:0] f_abandoned;
    always @(posedge clk) begin
        if (!rst_n) f_abandoned <= 0;
        else if (!s_wb_CYC) f_abandoned <= f_abandoned + f_open - ((rsp_valid && rsp_ready && f_abandoned != 0) ? 1 : 0);
        else f_abandoned <= f_abandoned - ((rsp_valid && rsp_ready && f_abandoned != 0) ? 1 : 0);
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
        // Classic: the held request is terminated exactly once, STALL never rises.
        if (CLASSIC != 0) begin
            ap_classic_stall: assert (!s_wb_STALL);
            ap_classic_once: assert (!w_term_o || $past(f_open) == 1 || $past(w_accept));
        end
    end

    // ---- Covers ----
    always @(posedge clk) if (rst_n) begin
        cp_ack:       cover (s_wb_ACK);
        cp_err:       cover (s_wb_ERR);
        cp_rty:       cover (s_wb_RTY);
        cp_abort:     cover (f_past_valid > 3 && $past(s_wb_CYC) && !s_wb_CYC && $past(f_open) != 0);
        // A response owed to an aborted transfer is taken off rsp_* while a
        // NEW cycle already has a request open (port-level: no hierarchical
        // reference into the DUT, which yosys would not resolve).
        if (CLASSIC == 0)   // the classic master model holds its request until terminated, so it never aborts mid-request
            cp_abandoned_late: cover (f_abandoned != 0 && rsp_valid && rsp_ready && f_open != 0 && s_wb_CYC);
        if (CLASSIC == 0) begin
            cp_stall_full: cover (s_wb_STALL && s_wb_STB);
            cp_backtoback: cover ($past(w_accept) && w_accept);
        end else begin
            cp_classic_b2b:  cover ($past(w_term_o) && w_accept);
            cp_classic_wait: cover (f_past_valid > 4 && s_wb_STB && $past(s_wb_STB) && $past(s_wb_STB, 2) && !$past(w_term_o) && !$past(w_term_o, 2));
        end
    end
endmodule
