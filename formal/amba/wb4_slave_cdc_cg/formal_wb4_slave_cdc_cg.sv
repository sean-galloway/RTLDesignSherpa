// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal harness for wb4_slave_cdc_cg -- the one wb4 block that had no proof.
//
// Every APB family proves all three of <x>_slave_cdc, <x>_slave_cg and
// <x>_slave_cdc_cg. wb4 proved the first two and stopped, and nothing
// recorded the gap: it was not in FORMAL_PRIORITY, not in FORMAL_TODO, not in
// a task page. Found 2026-09-11 by walking rtl/amba/wb4 against formal/amba.
//
// TWO MODELS, both of which the siblings already use:
//   * Single clock. wb_clk = aclk = clk, as formal/amba/wb4_slave_cdc does.
//     The crossing's Gray-pointer correctness is not what this harness is
//     about; the wrapper's glue is.
//   * Clock-enable icg. The gated clock is the free clock (see the icg model
//     at the bottom, and the Makefile, which leaves rtl/common/icg.sv out of
//     the flattened DUT). A derived clock is not provable in this flow.
//
// P1: after reset, no gating and nothing driven on the bus
// P2: bounded wake -- the third clock of an open CYC runs
// P3: STALL is high while gated, so no request can be accepted meanwhile
// P4: no termination while gated (a stopped slave cannot answer)
// P5: never gated with cfg_cg_enable low
// P6: the aclk side is NOT masked -- cmd_valid may be high while the
//     Wishbone side is gated, which is the whole point of gating one domain
//     (see vault/handbook/design/clock-gating-activity-terms.md)
module formal_wb4_slave_cdc_cg (
    input logic clk,
    input logic rst_n
);
    localparam int AW  = 8;
    localparam int DW  = 16;
    localparam int SW  = DW / 8;
    localparam int CTW = 3;
    localparam int BTW = 2;
    localparam int ICW = 3;

    (* anyseq *) reg            cfg_cg_enable;
    (* anyseq *) reg [ICW-1:0]  cfg_cg_idle_count;
    (* anyseq *) reg            s_wb_CYC, s_wb_STB, s_wb_WE;
    (* anyseq *) reg [AW-1:0]   s_wb_ADR;
    (* anyseq *) reg [DW-1:0]   s_wb_DAT_W, rsp_dat;
    (* anyseq *) reg [SW-1:0]   s_wb_SEL;
    (* anyseq *) reg [CTW-1:0]  s_wb_CTI;
    (* anyseq *) reg [BTW-1:0]  s_wb_BTE;
    (* anyseq *) reg            cmd_ready, rsp_valid;
    (* anyseq *) reg [1:0]      rsp_status;

    wire s_wb_STALL, s_wb_ACK, s_wb_ERR, s_wb_RTY;
    wire cmd_valid, cmd_we, rsp_ready, cg_gating, cg_idle;
    wire [DW-1:0] s_wb_DAT_R, cmd_dat;
    wire [AW-1:0] cmd_adr;
    wire [SW-1:0] cmd_sel;
    wire [CTW-1:0] cmd_cti;
    wire [BTW-1:0] cmd_bte;

    wb4_slave_cdc_cg #(
        .ADDR_WIDTH (AW), .DATA_WIDTH (DW), .CMD_DEPTH (2), .RSP_DEPTH (2),
        .MAX_OUTSTANDING (2), .CDC_DEPTH (4), .CG_IDLE_COUNT_WIDTH (ICW),
        .USE_BURST_HINTS (1)
    ) dut (
        .wb_clk (clk), .wb_resetn (rst_n), .aclk (clk), .aresetn (rst_n),
        .cfg_cg_enable (cfg_cg_enable), .cfg_cg_idle_count (cfg_cg_idle_count),
        .s_wb_CYC (s_wb_CYC), .s_wb_STB (s_wb_STB), .s_wb_WE (s_wb_WE),
        .s_wb_ADR (s_wb_ADR), .s_wb_DAT_W (s_wb_DAT_W), .s_wb_SEL (s_wb_SEL),
        .s_wb_CTI (s_wb_CTI), .s_wb_BTE (s_wb_BTE),
        .s_wb_STALL (s_wb_STALL), .s_wb_ACK (s_wb_ACK), .s_wb_ERR (s_wb_ERR),
        .s_wb_RTY (s_wb_RTY), .s_wb_DAT_R (s_wb_DAT_R),
        .cmd_valid (cmd_valid), .cmd_ready (cmd_ready), .cmd_we (cmd_we),
        .cmd_adr (cmd_adr), .cmd_dat (cmd_dat), .cmd_sel (cmd_sel),
        .cmd_cti (cmd_cti), .cmd_bte (cmd_bte),
        .rsp_valid (rsp_valid), .rsp_ready (rsp_ready),
        .rsp_status (rsp_status), .rsp_dat (rsp_dat),
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
        assume (!s_wb_STB || s_wb_CYC);   // STB only inside a cycle
        assume (rsp_status != 2'b11);     // no reserved status
    end

    // A B4 master holds a stalled request unchanged; a FUB holds a response
    // until it is taken. Same constraints the wb4_slave harness uses.
    always @(posedge clk) if (f_past_valid > 0 && rst_n && $past(rst_n)) begin
        if ($past(s_wb_STB && s_wb_STALL)) begin
            assume (s_wb_CYC && s_wb_STB);
            assume ($stable(s_wb_WE) && $stable(s_wb_ADR) && $stable(s_wb_DAT_W)
                    && $stable(s_wb_SEL) && $stable(s_wb_CTI) && $stable(s_wb_BTE));
        end
        if ($past(rsp_valid && !rsp_ready)) begin
            assume (rsp_valid);
            assume ($stable(rsp_status) && $stable(rsp_dat));
        end
    end

    // The FUB answers only what it was handed.
    wire w_term = s_wb_ACK || s_wb_ERR || s_wb_RTY;
    wire w_fub  = cmd_valid && cmd_ready;
    wire w_rsp  = rsp_valid && rsp_ready;
    reg [7:0] f_fub_open;
    always @(posedge clk) if (!rst_n) f_fub_open <= 0;
                          else        f_fub_open <= f_fub_open + w_fub - w_rsp;
    always @(*) if (rst_n && f_fub_open == 0) assume (!rsp_valid);

    always @(posedge clk) if (f_past_valid > 0 && $past(!rst_n)) begin
        ap_reset_no_gate: assert (!cg_gating);
        ap_reset_quiet:   assert (!w_term);
    end

    always @(posedge clk) if (rst_n) begin
        // The wake is registered in the controller, so gating can survive a
        // clock or two of CYC. STALL is high meanwhile, so nothing is taken.
        ap_wake_bounded:     assert (!(s_wb_CYC && $past(s_wb_CYC) && $past(s_wb_CYC, 2))
                                     || !cg_gating);
        ap_stall_gated:      assert (!cg_gating || s_wb_STALL);
        ap_no_term_gated:    assert (!cg_gating || !w_term);
        ap_disabled_no_gate: assert (cfg_cg_enable || !cg_gating);
    end

    always @(posedge clk) if (rst_n) begin
        cp_gating:     cover (cg_gating);
        cp_term:       cover (w_term);
        cp_accept:     cover (s_wb_CYC && s_wb_STB && !s_wb_STALL && !cg_gating);
        // The single-domain gate: the FUB side keeps working while the
        // Wishbone side is stopped. If this is unreachable the wrapper is
        // gating both domains, which is the bug the wake-term note warns of.
        cp_fub_live_while_gated: cover (cg_gating && cmd_valid);
    end
endmodule

// Formal model of the integrated clock-gate cell: the gated clock IS the free
// clock. A derived clock is not provable in this repo's single-clock flow, so
// this harness proves the wrapper's glue -- when it gates, what the masks hold
// -- and the cocotb test proves the behaviour of an actually stopped clock.
// rtl/common/icg.sv is left out of the flattened DUT on purpose (Makefile).
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
