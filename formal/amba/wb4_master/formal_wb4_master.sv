// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for wb4_master. The properties live IN the RTL under
// `ifdef FORMAL (flattened in with --define=FORMAL); this file supplies the
// environment: a free FUB on cmd_*/rsp_*, and a slave that stalls freely and
// terminates only transfers it accepted, one per clock. The slave model keeps
// its OWN accepted-minus-terminated count so no hierarchical reference into
// the DUT is needed (a nonexistent hierarchical net elaborates as a free
// wire and proves nothing).

module formal_wb4_master #(
    parameter int AW = 8,
    parameter int DW = 16,
    parameter int RSP_DEPTH = 3
) (
    input logic clk,
    input logic rst_n,
    // free FUB
    input logic          cmd_valid,
    input logic          cmd_we,
    input logic [AW-1:0] cmd_adr,
    input logic [DW-1:0] cmd_dat,
    input logic [DW/8-1:0] cmd_sel,
    input logic          rsp_ready,
    // free slave
    input logic          m_wb_STALL,
    input logic          m_wb_ACK,
    input logic          m_wb_ERR,
    input logic          m_wb_RTY,
    input logic [DW-1:0] m_wb_DAT_R
);
    logic m_wb_CYC, m_wb_STB, m_wb_WE, cmd_ready, rsp_valid;
    logic [AW-1:0] m_wb_ADR;
    logic [DW-1:0] m_wb_DAT_W, rsp_dat;
    logic [DW/8-1:0] m_wb_SEL;
    logic [1:0] rsp_status;

    wb4_master #(.ADDR_WIDTH(AW), .DATA_WIDTH(DW), .CMD_DEPTH(2), .RSP_DEPTH(RSP_DEPTH)) dut (
        .clk(clk), .aresetn(rst_n),
        .m_wb_CYC(m_wb_CYC), .m_wb_STB(m_wb_STB), .m_wb_WE(m_wb_WE),
        .m_wb_ADR(m_wb_ADR), .m_wb_DAT_W(m_wb_DAT_W), .m_wb_SEL(m_wb_SEL),
        .m_wb_STALL(m_wb_STALL), .m_wb_ACK(m_wb_ACK), .m_wb_ERR(m_wb_ERR),
        .m_wb_RTY(m_wb_RTY), .m_wb_DAT_R(m_wb_DAT_R),
        .cmd_valid(cmd_valid), .cmd_ready(cmd_ready), .cmd_we(cmd_we),
        .cmd_adr(cmd_adr), .cmd_dat(cmd_dat), .cmd_sel(cmd_sel),
        .rsp_valid(rsp_valid), .rsp_ready(rsp_ready),
        .rsp_status(rsp_status), .rsp_dat(rsp_dat)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // ---- Slave model: terminate only what was accepted, one per clock ----
    logic       w_accept, w_term;
    reg  [7:0]  f_open;      // accepted, not yet terminated (slave's view)
    assign w_accept = m_wb_CYC && m_wb_STB && !m_wb_STALL;
    assign w_term   = m_wb_ACK || m_wb_ERR || m_wb_RTY;
    always @(posedge clk) begin
        if (!rst_n) f_open <= 0;
        else        f_open <= f_open + w_accept - w_term;
    end
    always @(*) begin
        assume ((m_wb_ACK + m_wb_ERR + m_wb_RTY) <= 1);
        // A termination needs an accepted transfer; a same-clock accept
        // cannot terminate in the same clock (registered slave).
        if (f_open == 0) assume (!w_term);
        if (!m_wb_CYC)   assume (!w_term);
    end

    // ---- FUB model: valid/ready contract on the command side ----
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(cmd_valid && !cmd_ready)) begin
            assume (cmd_valid);
            assume ($stable(cmd_we) && $stable(cmd_adr) && $stable(cmd_dat) && $stable(cmd_sel));
        end
    end

    // ---- Port-level properties (the internal ones are in the RTL) ----
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        // Response side honours valid/ready: sticky valid, stable payload.
        if ($past(rsp_valid && !rsp_ready)) begin
            ap_rsp_sticky: assert (rsp_valid);
            ap_rsp_stable: assert ($stable(rsp_status) && $stable(rsp_dat));
        end
        // A termination is visible on rsp_* the very next clock (skid latency
        // one) unless the queue already held earlier responses.
        if ($past(w_term) && $past(m_wb_CYC))
            ap_term_visible: assert (rsp_valid);
    end

    // ---- Covers: the pipelined mode is reachable, every status appears ----
    reg [7:0] f_seen_depth = 0;
    always @(posedge clk) if (rst_n && f_open > f_seen_depth) f_seen_depth <= f_open;
    always @(posedge clk) if (rst_n) begin
        cp_pipelined:  cover (f_open == RSP_DEPTH);
        cp_backtoback: cover ($past(w_accept) && w_accept);
        cp_rsp_err:    cover (rsp_valid && rsp_status == 2'd1);
        cp_rsp_rty:    cover (rsp_valid && rsp_status == 2'd2);
        cp_cyc_drop:   cover (f_past_valid > 3 && $past(m_wb_CYC) && !m_wb_CYC);
    end
endmodule
