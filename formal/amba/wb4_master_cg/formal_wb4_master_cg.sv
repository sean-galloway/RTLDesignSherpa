// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for wb4_master_cg: the clock-gate wrapper's contract with
// a free FUB and a constrained slave (the wb4_master harness's model).
//   P1: after reset: no gating, no cycle on the bus
//   P2: never gated while a cycle is open on the bus
//   P3: never gated while a response is visible to the FUB (the mask)
//   P4: never gated with cfg_cg_enable low
//   P5: a FUB command offered is taken with the clock running (cmd_ready
//       implies !cg_gating) and wakes the clock by its third clock
// Covers: gating; an ungated transfer; a response handed back; gating
// re-engaging after a transfer.
module formal_wb4_master_cg (
    input logic clk,
    input logic rst_n
);
    localparam int AW = 8;
    localparam int DW = 16;
    localparam int SW = DW / 8;
    localparam int ICW = 3;

    (* anyseq *) reg            cfg_cg_enable;
    (* anyseq *) reg [ICW-1:0]  cfg_cg_idle_count;
    (* anyseq *) reg            cmd_valid, cmd_we, rsp_ready;
    (* anyseq *) reg [AW-1:0]   cmd_adr;
    (* anyseq *) reg [DW-1:0]   cmd_dat, m_wb_DAT_R;
    (* anyseq *) reg [SW-1:0]   cmd_sel;
    (* anyseq *) reg            m_wb_STALL, m_wb_ACK, m_wb_ERR, m_wb_RTY;

    wire cmd_ready, rsp_valid, m_wb_CYC, m_wb_STB, m_wb_WE, cg_gating, cg_idle;
    wire [1:0]    rsp_status;
    wire [DW-1:0] rsp_dat, m_wb_DAT_W;
    wire [AW-1:0] m_wb_ADR;
    wire [SW-1:0] m_wb_SEL;

    wb4_master_cg #(.ADDR_WIDTH (AW), .DATA_WIDTH (DW), .CMD_DEPTH (2), .RSP_DEPTH (2),
                    .CG_IDLE_COUNT_WIDTH (ICW)) dut (
        .clk (clk), .aresetn (rst_n),
        .cfg_cg_enable (cfg_cg_enable), .cfg_cg_idle_count (cfg_cg_idle_count),
        .m_wb_CYC (m_wb_CYC), .m_wb_STB (m_wb_STB), .m_wb_WE (m_wb_WE), .m_wb_ADR (m_wb_ADR),
        .m_wb_DAT_W (m_wb_DAT_W), .m_wb_SEL (m_wb_SEL), .m_wb_STALL (m_wb_STALL),
        .m_wb_ACK (m_wb_ACK), .m_wb_ERR (m_wb_ERR), .m_wb_RTY (m_wb_RTY), .m_wb_DAT_R (m_wb_DAT_R),
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
    always @(*) assume (cfg_cg_idle_count <= 3);

    // Slave model: terminations only for accepted requests, one per clock,
    // inside the cycle.
    reg  [7:0] f_open;
    wire w_accept = m_wb_CYC && m_wb_STB && !m_wb_STALL;
    wire w_term   = m_wb_ACK || m_wb_ERR || m_wb_RTY;
    always @(posedge clk) if (!rst_n) f_open <= 0; else f_open <= f_open + w_accept - w_term;
    always @(*) begin
        assume ((m_wb_ACK + m_wb_ERR + m_wb_RTY) <= 1);
        if (!m_wb_CYC || f_open == 0) assume (!w_term);
    end
    // FUB holds a command until taken
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n))
        if ($past(cmd_valid && !cmd_ready)) begin
            assume (cmd_valid);
            assume ($stable(cmd_we) && $stable(cmd_adr) && $stable(cmd_dat) && $stable(cmd_sel));
        end

    always @(posedge clk) if (f_past_valid > 0 && $past(!rst_n)) begin
        ap_reset_no_gate: assert (!cg_gating);
        ap_reset_no_cyc:  assert (!m_wb_CYC);
    end
    always @(posedge clk) if (rst_n) begin
        ap_no_gate_in_cycle: assert (!cg_gating || !m_wb_CYC);
        ap_no_gate_rsp:      assert (!cg_gating || !rsp_valid);
        ap_disabled_no_gate: assert (cfg_cg_enable || !cg_gating);
        ap_ready_awake:      assert (!cmd_ready || !cg_gating);
        // A FUB command offered while gated wakes the clock within two clocks.
        ap_wake_bounded:     assert (!(cmd_valid && $past(cmd_valid) && $past(cmd_valid, 2)) || !cg_gating);
    end
    always @(posedge clk) if (rst_n) begin
        cp_gating:     cover (cg_gating);
        cp_transfer:   cover (w_accept && !cg_gating);
        cp_rsp:        cover (rsp_valid && rsp_ready);
        cp_regate:     cover (f_past_valid > 6 && cg_gating && $past(!cg_gating, 2) && $past(w_term, 4));
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
