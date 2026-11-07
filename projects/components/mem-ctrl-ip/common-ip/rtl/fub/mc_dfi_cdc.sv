// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_dfi_cdc
// Purpose: THE single clock-domain crossing of the DFI 2.1 plane. All traffic
//          between the controller domain (ctl_clk: AXI IFC + scheduler + CAMs)
//          and the PHY DFI domain (dfi_clk: phase-packer + PHY) crosses here,
//          and ONLY through gaxi_fifo_async (Gray-pointer) FIFOs — no
//          hand-rolled synchronizers, no open-loop bit crossings.
//
//          Extracted from pumice_dfi_cdc during Phase 2 common-plane reorg
//          (2026-10-10).
//
//   ctl -> phy : cmd, wrdata, init_start(token)
//   phy -> ctl : rddata, init_complete(token)
//
// Level signals (init_start / init_complete) cross as EVENT TOKENS: a rising
// edge on the source side pushes a 1-bit token; the sink pops it and sets a
// sticky latch. init is monotonic (once); leveling re-runs are future work.
// Payloads are opaque buses — the DFI top packs/unpacks {op,...}/{data,...}.
//
// Documentation: docs/uarch/PUMICE_DFI_PLANE_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_dfi_cdc #(
    parameter int CMD_DW       = 32,   // {op,rank,bank,row,col,ap} packed
    parameter int WD_DW        = 72,   // {data,strb,last}
    parameter int RD_DW        = 66,   // {data,resp,last}
    // Depths are powers of two, which is what the default Gray pointer
    // encoding requires ("even" was stale language from fifo_async_div2).
    parameter int CMD_DEPTH    = 8,
    parameter int WD_DEPTH     = 16,
    parameter int RD_DEPTH     = 16,
    parameter int TOK_DEPTH    = 4,
    parameter int N_FLOP_CROSS = 2,
    // Async-FIFO pointer encoding for all five CDC FIFOs below: 0 = Gray
    // (power-of-2 depth only), 1 = Johnson (any depth, DEPTH-bit pointers).
    // Gray by default -- Johnson is opt-in because its pointers cost DEPTH
    // bits in both domains and every synchronizer stage.
    parameter int USE_JOHNSON  = 0,
    // 1 = ctl_clk and dfi_clk are independent: five Gray-pointer async FIFOs
    //     cross them (the contract above).
    // 0 = ctl_clk and dfi_clk are THE SAME CLOCK (the Nexys A7 boards tie
    //     dfi_clk to mc_clk): the same FIFOs as synchronous gaxi_fifo_sync at
    //     the same depths, the init tokens as plain sticky levels. Same
    //     ports, same valid/ready contract, no pointer synchronizers; each
    //     crossing loses its N_FLOP_CROSS + 1 cycles of latency. The data /
    //     staged-token coupling is unchanged, so the write-staged invariant
    //     (data never behind its WR at the PHY) holds as before. Only legal
    //     when the two clock inputs are one net: the dfi-side flops below
    //     are clocked by dfi_clk and read ctl-domain signals directly.
    parameter bit DFI_CDC_EN   = 1'b1,
    // 1 (same-clock form only) = CMD_FALLTHRU: a command that finds the cmd
    // FIFO EMPTY is also offered to the command path in its own cycle; taken
    // there it is never written, otherwise it is written as before. One cycle
    // less from the scheduler to the DFI pins (granite TASK-003, 2026-10-31).
    // Order holds (only into an empty FIFO); a WR whose data is not staged is
    // refused by the command path's gate and simply queues.
    parameter bit CMD_FALLTHRU = 1'b0
) (
    //=========================================================================
    // Controller domain (aclk)
    //=========================================================================
    input  logic              ctl_clk,
    input  logic              ctl_rstn,

    // cmd  ctl -> phy
    input  logic              cmd_valid_i,
    output logic              cmd_ready_o,
    input  logic [CMD_DW-1:0] cmd_data_i,
    // wrdata ctl -> phy. wd_last_i marks the final DFI word of a burst: it is
    // what pushes the "burst staged" token below (the payload stays opaque).
    input  logic              wd_valid_i,
    output logic              wd_ready_o,
    input  logic [WD_DW-1:0]  wd_data_i,
    input  logic              wd_last_i,
    // init start (level) ctl -> phy
    input  logic              init_start_i,
    // rddata phy -> ctl
    output logic              rd_valid_o,
    input  logic              rd_ready_i,
    output logic [RD_DW-1:0]  rd_data_o,
    // init complete (level) phy -> ctl (sticky latch)
    output logic              init_complete_o,

    //=========================================================================
    // PHY DFI domain (dfi_clk)
    //=========================================================================
    input  logic              dfi_clk,
    input  logic              dfi_rstn,

    // cmd out (phy)
    output logic              pcmd_valid_o,
    input  logic              pcmd_ready_i,
    output logic [CMD_DW-1:0] pcmd_data_o,
    // wrdata out (phy)
    output logic              pwd_valid_o,
    input  logic              pwd_ready_i,
    output logic [WD_DW-1:0]  pwd_data_o,
    // write-burst-staged tokens (phy): one per COMPLETE burst that has crossed
    // into the wrdata FIFO. The command path pops one per WR it accepts, so a
    // WR command can never reach the PHY ahead of its data (the write analog
    // of the read aligner's op_ready backpressure). The token crosses in its
    // OWN async FIFO, on its own Gray pointer and synchronizer, so it is pushed
    // one ctl cycle AFTER the burst's last data word: launched together, two
    // independent synchronizers can resolve a dfi cycle apart and the token
    // could lead the data (memory-controllers BUG-002); launched a cycle later
    // it never can.
    // With the controller's rate-matched commit + CMD_DELAY this gate is an
    // INVARIANT (never holds); the counters in pumice_dfi_cmd_path prove it.
    output logic              pwr_staged_valid_o,
    input  logic              pwr_staged_pop_i,
    // init start (level) phy (sticky latch)
    output logic              pinit_start_o,
    // rddata in (phy)
    input  logic              prd_valid_i,
    output logic              prd_ready_o,
    input  logic [RD_DW-1:0]  prd_data_i,
    // init complete (level) phy -> crosses to ctl
    input  logic              pinit_complete_i
);

    generate if (DFI_CDC_EN) begin : g_async

    // ---- cmd : ctl -> phy ---------------------------------------------------
    gaxi_fifo_async #(
        .DATA_WIDTH  (CMD_DW),
        .DEPTH       (CMD_DEPTH),
        .USE_JOHNSON (USE_JOHNSON),
        .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_cmd_fifo (
        .axi_wr_aclk   (ctl_clk),
        .axi_wr_aresetn(ctl_rstn),
        .axi_rd_aclk   (dfi_clk),
        .axi_rd_aresetn(dfi_rstn),
        .wr_valid      (cmd_valid_i),
        .wr_ready      (cmd_ready_o),
        .wr_data       (cmd_data_i),
        .rd_ready      (pcmd_ready_i),
        .rd_valid      (pcmd_valid_o),
        .rd_data       (pcmd_data_o)
    );

    // ---- wrdata : ctl -> phy ------------------------------------------------
    // The data word is accepted when both FIFOs have room. The staged token
    // for a burst's LAST word is pushed one ctl cycle later (BUG-002, above):
    // the data pointer's crossing then always settles no later than the
    // token's. Tokens in flight (queued + the one pending push) never exceed
    // the bursts still in the data FIFO plus one, so at 2 x WD_DEPTH the token
    // FIFO never fills and the delayed push always lands.
    logic w_wd_data_ready, w_wtok_ready, w_wd_take;
    logic r_wtok_push;
    assign wd_ready_o = w_wd_data_ready && w_wtok_ready;
    assign w_wd_take  = wd_valid_i && wd_ready_o;
    `ALWAYS_FF_RST(ctl_clk, ctl_rstn,
        if (`RST_ASSERTED(ctl_rstn)) r_wtok_push <= 1'b0;
        else                         r_wtok_push <= w_wd_take && wd_last_i;
    )

    gaxi_fifo_async #(
        .DATA_WIDTH  (WD_DW),
        .DEPTH       (WD_DEPTH),
        .USE_JOHNSON (USE_JOHNSON),
        .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_wd_fifo (
        .axi_wr_aclk   (ctl_clk),
        .axi_wr_aresetn(ctl_rstn),
        .axi_rd_aclk   (dfi_clk),
        .axi_rd_aresetn(dfi_rstn),
        .wr_valid      (wd_valid_i && w_wtok_ready),
        .wr_ready      (w_wd_data_ready),
        .wr_data       (wd_data_i),
        .rd_ready      (pwd_ready_i),
        .rd_valid      (pwd_valid_o),
        .rd_data       (pwd_data_o)
    );

    // 2 x WD_DEPTH: see above (one token per burst, plus the delayed push).
    gaxi_fifo_async #(
        .DATA_WIDTH  (1),
        .DEPTH       (2 * WD_DEPTH),
        .USE_JOHNSON (USE_JOHNSON),
        .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_wtok_fifo (
        .axi_wr_aclk   (ctl_clk),
        .axi_wr_aresetn(ctl_rstn),
        .axi_rd_aclk   (dfi_clk),
        .axi_rd_aresetn(dfi_rstn),
        .wr_valid      (r_wtok_push),
        .wr_ready      (w_wtok_ready),
        .wr_data       (1'b1),
        .rd_ready      (pwr_staged_pop_i),
        .rd_valid      (pwr_staged_valid_o),
        .rd_data       ()
    );

    // ---- rddata : phy -> ctl ------------------------------------------------
    gaxi_fifo_async #(
        .DATA_WIDTH  (RD_DW),
        .DEPTH       (RD_DEPTH),
        .USE_JOHNSON (USE_JOHNSON),
        .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_rd_fifo (
        .axi_wr_aclk   (dfi_clk),
        .axi_wr_aresetn(dfi_rstn),
        .axi_rd_aclk   (ctl_clk),
        .axi_rd_aresetn(ctl_rstn),
        .wr_valid      (prd_valid_i),
        .wr_ready      (prd_ready_o),
        .wr_data       (prd_data_i),
        .rd_ready      (rd_ready_i),
        .rd_valid      (rd_valid_o),
        .rd_data       (rd_data_o)
    );

    // ---- init_start : ctl -> phy (level -> token -> sticky latch) ----------
    logic r_istart_d, w_istart_push;
    `ALWAYS_FF_RST(ctl_clk, ctl_rstn,
        if (`RST_ASSERTED(ctl_rstn)) r_istart_d <= 1'b0;
        else                         r_istart_d <= init_start_i;
    )
    assign w_istart_push = init_start_i && !r_istart_d;   // rising edge

    logic w_istok_valid;
    gaxi_fifo_async #(
        .DATA_WIDTH  (1),
        .DEPTH       (TOK_DEPTH),
        .USE_JOHNSON (USE_JOHNSON),
        .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_istart_tok (
        .axi_wr_aclk   (ctl_clk),
        .axi_wr_aresetn(ctl_rstn),
        .axi_rd_aclk   (dfi_clk),
        .axi_rd_aresetn(dfi_rstn),
        .wr_valid      (w_istart_push),
        .wr_ready      (),
        .wr_data       (1'b1),
        .rd_ready      (1'b1),
        .rd_valid      (w_istok_valid),
        .rd_data       ()
    );
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) pinit_start_o <= 1'b0;
        else if (w_istok_valid)      pinit_start_o <= 1'b1;   // sticky
    )

    // ---- init_complete : phy -> ctl (level -> token -> sticky latch) -------
    logic r_icmp_d, w_icmp_push;
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) r_icmp_d <= 1'b0;
        else                         r_icmp_d <= pinit_complete_i;
    )
    assign w_icmp_push = pinit_complete_i && !r_icmp_d;   // rising edge

    logic w_icmptok_valid;
    gaxi_fifo_async #(
        .DATA_WIDTH  (1),
        .DEPTH       (TOK_DEPTH),
        .USE_JOHNSON (USE_JOHNSON),
        .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_icmp_tok (
        .axi_wr_aclk   (dfi_clk),
        .axi_wr_aresetn(dfi_rstn),
        .axi_rd_aclk   (ctl_clk),
        .axi_rd_aresetn(ctl_rstn),
        .wr_valid      (w_icmp_push),
        .wr_ready      (),
        .wr_data       (1'b1),
        .rd_ready      (1'b1),
        .rd_valid      (w_icmptok_valid),
        .rd_data       ()
    );
    `ALWAYS_FF_RST(ctl_clk, ctl_rstn,
        if (`RST_ASSERTED(ctl_rstn)) init_complete_o <= 1'b0;
        else if (w_icmptok_valid)    init_complete_o <= 1'b1;   // sticky
    )

    end else begin : g_sync
    // =====================================================================
    // Same-clock form (DFI_CDC_EN = 0): ctl_clk == dfi_clk by contract.
    // The FIFOs keep their depths (they still decouple the scheduler from
    // the command path's hold, stage write bursts ahead of their WR, and
    // absorb read return) but are synchronous: binary pointers, no Gray
    // encoding, no crossing synchronizers. Clocked on ctl_clk; the phy-side
    // consumers run on dfi_clk, which is the same net.
    // =====================================================================

    // ---- cmd : ctl -> phy ---------------------------------------------------
    logic              w_cq_valid, w_cq_rd_ready, w_cft, w_cft_take;
    logic [CMD_DW-1:0] w_cq_data;
    gaxi_fifo_sync #(
        .DATA_WIDTH (CMD_DW),
        .DEPTH      (CMD_DEPTH)
    ) u_cmd_fifo (
        .axi_aclk    (ctl_clk),
        .axi_aresetn (ctl_rstn),
        .wr_valid    (cmd_valid_i && !w_cft_take),
        .wr_ready    (cmd_ready_o),
        .wr_data     (cmd_data_i),
        .rd_ready    (w_cq_rd_ready),
        .count       (),
        .rd_valid    (w_cq_valid),
        .rd_data     (w_cq_data)
    );
    // CMD_FALLTHRU: the FIFO is empty, so the offered command is its would-be head
    assign w_cft         = CMD_FALLTHRU && !w_cq_valid && cmd_valid_i;
    assign w_cft_take    = w_cft && pcmd_ready_i;
    assign pcmd_valid_o  = w_cq_valid || w_cft;
    assign pcmd_data_o   = w_cq_valid ? w_cq_data : cmd_data_i;
    assign w_cq_rd_ready = pcmd_ready_i && w_cq_valid;

    // ---- wrdata + staged token : ctl -> phy (same coupling as g_async) ------
    logic w_wd_data_ready, w_wtok_ready, w_wtok_push;
    assign wd_ready_o  = w_wd_data_ready && w_wtok_ready;
    assign w_wtok_push = wd_valid_i && wd_last_i && w_wd_data_ready;

    gaxi_fifo_sync #(
        .DATA_WIDTH (WD_DW),
        .DEPTH      (WD_DEPTH)
    ) u_wd_fifo (
        .axi_aclk    (ctl_clk),
        .axi_aresetn (ctl_rstn),
        .wr_valid    (wd_valid_i && w_wtok_ready),
        .wr_ready    (w_wd_data_ready),
        .wr_data     (wd_data_i),
        .rd_ready    (pwd_ready_i),
        .count       (),
        .rd_valid    (pwd_valid_o),
        .rd_data     (pwd_data_o)
    );

    gaxi_fifo_sync #(
        .DATA_WIDTH (1),
        .DEPTH      (WD_DEPTH)
    ) u_wtok_fifo (
        .axi_aclk    (ctl_clk),
        .axi_aresetn (ctl_rstn),
        .wr_valid    (w_wtok_push),
        .wr_ready    (w_wtok_ready),
        .wr_data     (1'b1),
        .rd_ready    (pwr_staged_pop_i),
        .count       (),
        .rd_valid    (pwr_staged_valid_o),
        .rd_data     ()
    );

    // ---- rddata : phy -> ctl ------------------------------------------------
    gaxi_fifo_sync #(
        .DATA_WIDTH (RD_DW),
        .DEPTH      (RD_DEPTH)
    ) u_rd_fifo (
        .axi_aclk    (ctl_clk),
        .axi_aresetn (ctl_rstn),
        .wr_valid    (prd_valid_i),
        .wr_ready    (prd_ready_o),
        .wr_data     (prd_data_i),
        .rd_ready    (rd_ready_i),
        .count       (),
        .rd_valid    (rd_valid_o),
        .rd_data     (rd_data_o)
    );

    // ---- init_start / init_complete : sticky levels, no tokens --------------
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) pinit_start_o <= 1'b0;
        else if (init_start_i)       pinit_start_o <= 1'b1;   // sticky
    )
    `ALWAYS_FF_RST(ctl_clk, ctl_rstn,
        if (`RST_ASSERTED(ctl_rstn)) init_complete_o <= 1'b0;
        else if (pinit_complete_i)   init_complete_o <= 1'b1;   // sticky
    )

    wire _unused_sync = &{1'b0, dfi_rstn, N_FLOP_CROSS[0], USE_JOHNSON[0], TOK_DEPTH[0]};
    end endgenerate

endmodule : mc_dfi_cdc
