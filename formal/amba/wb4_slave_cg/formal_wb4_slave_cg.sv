// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for wb4_slave_cg: the clock-gate wrapper's contract with
// a constrained master (the wb4_slave harness's model) and a free FUB.
//   P1: after reset: no gating, no termination on the bus
//   P2: gating clears by the third clock of an open cycle (bounded wake), and
//       STALL is high while gated so no request is taken meanwhile
//   P3: never gated while a command is visible to the FUB (the mask)
//   P4: never gated with cfg_cg_enable low
//   P5: no termination while gated (a gated slave cannot answer)
// Covers: gating; an ungated accept; a termination; gating re-engaging.
module formal_wb4_slave_cg (
    input logic clk,
    input logic rst_n
);
    localparam int AW = 8;
    localparam int DW = 16;
    localparam int SW = DW / 8;
    localparam int ICW = 3;

    (* anyseq *) reg            cfg_cg_enable;
    (* anyseq *) reg [ICW-1:0]  cfg_cg_idle_count;
    (* anyseq *) reg            s_wb_CYC, s_wb_STB, s_wb_WE, cmd_ready, rsp_valid;
    (* anyseq *) reg [AW-1:0]   s_wb_ADR;
    (* anyseq *) reg [DW-1:0]   s_wb_DAT_W, rsp_dat;
    (* anyseq *) reg [SW-1:0]   s_wb_SEL;
    (* anyseq *) reg [1:0]      rsp_status;

    wire s_wb_STALL, s_wb_ACK, s_wb_ERR, s_wb_RTY, cmd_valid, cmd_we, rsp_ready, cg_gating, cg_idle;
    wire [DW-1:0] s_wb_DAT_R, cmd_dat;
    wire [AW-1:0] cmd_adr;
    wire [SW-1:0] cmd_sel;

    wb4_slave_cg #(.ADDR_WIDTH (AW), .DATA_WIDTH (DW), .CMD_DEPTH (2), .RSP_DEPTH (2),
                   .MAX_OUTSTANDING (2), .CG_IDLE_COUNT_WIDTH (ICW)) dut (
        .clk (clk), .aresetn (rst_n),
        .cfg_cg_enable (cfg_cg_enable), .cfg_cg_idle_count (cfg_cg_idle_count),
        .s_wb_CYC (s_wb_CYC), .s_wb_STB (s_wb_STB), .s_wb_WE (s_wb_WE), .s_wb_ADR (s_wb_ADR),
        .s_wb_DAT_W (s_wb_DAT_W), .s_wb_SEL (s_wb_SEL), .s_wb_STALL (s_wb_STALL),
        .s_wb_ACK (s_wb_ACK), .s_wb_ERR (s_wb_ERR), .s_wb_RTY (s_wb_RTY), .s_wb_DAT_R (s_wb_DAT_R),
        .cmd_valid (cmd_valid), .cmd_ready (cmd_ready), .cmd_we (cmd_we), .cmd_adr (cmd_adr),
        .cmd_dat (cmd_dat), .cmd_sel (cmd_sel),
        .rsp_valid (rsp_valid), .rsp_ready (rsp_ready), .rsp_status (rsp_status), .rsp_dat (rsp_dat),
        .cg_gating (cg_gating), .cg_idle (cg_idle)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);
    always @(posedge clk) if (f_past_valid > 0) begin
        assume (cfg_cg_enable == $past(cfg_cg_enable));
        assume (cfg_cg_idle_count == $past(cfg_cg_idle_count));
    end
    always @(*) begin
        assume (cfg_cg_idle_count <= 3);
        assume (!s_wb_STB || s_wb_CYC);
        assume (rsp_status != 2'b11);
    end
    // Master holds a stalled request; FUB holds a response until taken
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(s_wb_STB && s_wb_STALL)) begin
            assume (s_wb_CYC && s_wb_STB);
            assume ($stable(s_wb_WE) && $stable(s_wb_ADR) && $stable(s_wb_DAT_W) && $stable(s_wb_SEL));
        end
        if ($past(rsp_valid && !rsp_ready)) begin
            assume (rsp_valid);
            assume ($stable(rsp_status) && $stable(rsp_dat));
        end
    end
    // The FUB answers only what it was given (responses <= accepted requests)
    reg [7:0] f_open;
    wire w_accept = s_wb_CYC && s_wb_STB && !s_wb_STALL;
    wire w_term   = s_wb_ACK || s_wb_ERR || s_wb_RTY;
    wire w_fub    = cmd_valid && cmd_ready;
    wire w_rsp    = rsp_valid && rsp_ready;
    reg [7:0] f_fub_open;
    always @(posedge clk) if (!rst_n) f_fub_open <= 0; else f_fub_open <= f_fub_open + w_fub - w_rsp;
    always @(*) if (rst_n && f_fub_open == 0) assume (!rsp_valid);

    always @(posedge clk) if (f_past_valid > 0 && $past(!rst_n)) begin
        ap_reset_no_gate: assert (!cg_gating);
        ap_reset_quiet:   assert (!w_term);
    end
    always @(posedge clk) if (rst_n) begin
        // A master may raise CYC while the clock is gated; the wake is
        // registered once in the controller, so gating may persist for a
        // clock or two. STALL is high meanwhile (ap_stall_gated), so no
        // request can be taken. Bounded: the third clock of CYC runs.
        ap_wake_bounded:     assert (!(s_wb_CYC && $past(s_wb_CYC) && $past(s_wb_CYC, 2)) || !cg_gating);
        ap_no_gate_cmd:      assert (!cg_gating || !cmd_valid);
        ap_disabled_no_gate: assert (cfg_cg_enable || !cg_gating);
        ap_no_term_gated:    assert (!cg_gating || !w_term);
        ap_stall_gated:      assert (!cg_gating || s_wb_STALL);
        ap_no_rsp_gated:     assert (!cg_gating || !rsp_ready);
    end
    always @(posedge clk) if (rst_n) begin
        cp_gating:   cover (cg_gating);
        cp_accept:   cover (w_accept && !cg_gating);
        cp_term:     cover (w_term);
        cp_regate:   cover (f_past_valid > 6 && cg_gating && $past(!cg_gating, 2) && $past(w_term, 4));
    end
endmodule

// Formal model of the integrated clock-gate cell: the gated clock is the
// free clock. A derived clock is not provable in this repo's single-clock
// flow (formal/amba/apb4_slave_cg/KNOWN_BUG.md), so this harness proves
// the wrapper's GLUE contract -- when the controller gates, what the wake
// terms cover, what the masks hold -- and the cocotb test proves the
// behaviour of the actually stopped clock. icg.sv is left out of the
// flattened DUT on purpose (see the Makefile DEPS).
module icg (
    input  logic en,
    input  logic clk,
    output logic gclk
);
    assign gclk = clk;
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_en;
    assign unused_en = en;
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
