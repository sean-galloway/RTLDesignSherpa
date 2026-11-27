// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_tetrad_rig
// Purpose: everything of the build-tetrad board below its clock: UART ->
//          AXI4-Lite, split on addr[18] between gatling_mem_bram (programs,
//          run control, per-context status) and gatling_tetrad_harness (the
//          cells' seams), and gatling_tetrad itself.  The board top adds the
//          MMCM, reset and LEDs; the UART-equivalence sim instantiates this
//          directly, so the two cannot drift.
//
// Documentation: projects/fpga-systems/NexysA7/riscv-ip/gatling/README.md
// Subsystem: fpga-systems / riscv-ip
//
// Created: 2026-11-26
//
// Host address map:
//   0x0_0000 - 0x3_FFFF  gatling_mem_bram (its own map: banks, CTRL, status)
//   0x4_0000 - 0x4_0FFF  gatling_tetrad_harness
//
// Parameters:
//   - CLKS_PER_BIT: UART bit time in clocks
//   - ALU_EN_*: alu-infer row families; the board build sets all to 0 (the
//     bf16 profile): four full ALUs do not fit the xc7a100t (alu-infer
//     TASK-012)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gatling_tetrad_rig #(
    parameter int CLKS_PER_BIT  = 41,
    parameter bit ALU_EN_INT8   = 1'b0,
    parameter bit ALU_EN_FP32   = 1'b0,
    parameter bit ALU_EN_FP8    = 1'b0,
    parameter bit ALU_EN_REDUCE = 1'b0,
    parameter bit ALU_EN_PWL    = 1'b0,
    parameter bit ALU_EN_ACT    = 1'b0,
    parameter bit ALU_EN_CVT    = 1'b0
) (
    input  logic       aclk,
    input  logic       aresetn,
    input  logic       i_uart_rx,
    output logic       o_uart_tx,
    output logic [3:0] o_run,
    output logic [3:0] o_halted,
    output logic [3:0] o_done,
    output logic       o_axil_req,
    output logic       o_axil_rsp
);

    localparam int N = 4;

    // -------------------------------------------------------------------------
    // UART -> AXI4-Lite
    // -------------------------------------------------------------------------
    logic [31:0] axil_awaddr, axil_araddr, axil_wdata, axil_rdata;
    logic [2:0]  axil_awprot, axil_arprot;
    logic [3:0]  axil_wstrb;
    logic [1:0]  axil_bresp, axil_rresp;
    logic        axil_awvalid, axil_awready, axil_wvalid, axil_wready, axil_bvalid, axil_bready;
    logic        axil_arvalid, axil_arready, axil_rvalid, axil_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(32), .CLKS_PER_BIT(CLKS_PER_BIT)
    ) u_uart_bridge (
        .aclk(aclk), .aresetn(aresetn),
        .i_uart_rx(i_uart_rx), .o_uart_tx(o_uart_tx),
        .m_axil_awaddr(axil_awaddr), .m_axil_awprot(axil_awprot),
        .m_axil_awvalid(axil_awvalid), .m_axil_awready(axil_awready),
        .m_axil_wdata(axil_wdata), .m_axil_wstrb(axil_wstrb),
        .m_axil_wvalid(axil_wvalid), .m_axil_wready(axil_wready),
        .m_axil_bresp(axil_bresp), .m_axil_bvalid(axil_bvalid), .m_axil_bready(axil_bready),
        .m_axil_araddr(axil_araddr), .m_axil_arprot(axil_arprot),
        .m_axil_arvalid(axil_arvalid), .m_axil_arready(axil_arready),
        .m_axil_rdata(axil_rdata), .m_axil_rresp(axil_rresp),
        .m_axil_rvalid(axil_rvalid), .m_axil_rready(axil_rready));

    assign o_axil_req = axil_awvalid || axil_arvalid;
    assign o_axil_rsp = axil_rvalid  || axil_bvalid;

    // -------------------------------------------------------------------------
    // Split: addr[18] = 0 memory system, 1 harness
    // -------------------------------------------------------------------------
    logic [31:0] m_awaddr, m_araddr, m_wdata;
    logic [2:0]  m_awprot, m_arprot;
    logic [3:0]  m_wstrb;
    logic [1:0]  m_awvalid, m_awready, m_wvalid, m_wready, m_bvalid, m_bready;
    logic [1:0]  m_arvalid, m_arready, m_rvalid, m_rready;
    logic [1:0]  m_bresp [2];
    logic [1:0]  m_rresp [2];
    logic [31:0] m_rdata [2];

    gatling_tetrad_axil_split #(.AW(32), .SEL_BIT(18)) u_split (
        .aclk(aclk), .aresetn(aresetn),
        .s_awaddr(axil_awaddr), .s_awprot(axil_awprot),
        .s_awvalid(axil_awvalid), .s_awready(axil_awready),
        .s_wdata(axil_wdata), .s_wstrb(axil_wstrb),
        .s_wvalid(axil_wvalid), .s_wready(axil_wready),
        .s_bresp(axil_bresp), .s_bvalid(axil_bvalid), .s_bready(axil_bready),
        .s_araddr(axil_araddr), .s_arprot(axil_arprot),
        .s_arvalid(axil_arvalid), .s_arready(axil_arready),
        .s_rdata(axil_rdata), .s_rresp(axil_rresp),
        .s_rvalid(axil_rvalid), .s_rready(axil_rready),
        .m_awaddr(m_awaddr), .m_awprot(m_awprot),
        .m_awvalid(m_awvalid), .m_awready(m_awready),
        .m_wdata(m_wdata), .m_wstrb(m_wstrb),
        .m_wvalid(m_wvalid), .m_wready(m_wready),
        .m_bresp(m_bresp), .m_bvalid(m_bvalid), .m_bready(m_bready),
        .m_araddr(m_araddr), .m_arprot(m_arprot),
        .m_arvalid(m_arvalid), .m_arready(m_arready),
        .m_rdata(m_rdata), .m_rresp(m_rresp),
        .m_rvalid(m_rvalid), .m_rready(m_rready));

    // -------------------------------------------------------------------------
    // gatling_mem_bram: programs, run control, per-context status
    // -------------------------------------------------------------------------
    logic [1:0]      imem_ctx, dmem_ctx, rvfi_ctx;
    logic [31:0]     imem_addr, imem_rdata, dmem_addr, dmem_rdata, dmem_wdata;
    logic            dmem_req, rvfi_valid;
    logic [3:0]      dmem_wstrb, hart_run, halted, done;
    logic [3:0][3:0] halt_cause;
    logic [4:0]      rvfi_rd_addr;
    logic [31:0]     rvfi_rd_wdata;

    gatling_mem_bram u_mem (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr(m_awaddr[17:0]), .s_axil_awprot(m_awprot),
        .s_axil_awvalid(m_awvalid[0]), .s_axil_awready(m_awready[0]),
        .s_axil_wdata(m_wdata), .s_axil_wstrb(m_wstrb),
        .s_axil_wvalid(m_wvalid[0]), .s_axil_wready(m_wready[0]),
        .s_axil_bresp(m_bresp[0]), .s_axil_bvalid(m_bvalid[0]), .s_axil_bready(m_bready[0]),
        .s_axil_araddr(m_araddr[17:0]), .s_axil_arprot(m_arprot),
        .s_axil_arvalid(m_arvalid[0]), .s_axil_arready(m_arready[0]),
        .s_axil_rdata(m_rdata[0]), .s_axil_rresp(m_rresp[0]),
        .s_axil_rvalid(m_rvalid[0]), .s_axil_rready(m_rready[0]),
        .imem_ctx(imem_ctx), .imem_addr(imem_addr), .imem_rdata(imem_rdata),
        .dmem_req(dmem_req), .dmem_ctx(dmem_ctx), .dmem_addr(dmem_addr),
        .dmem_rdata(dmem_rdata), .dmem_wstrb(dmem_wstrb), .dmem_wdata(dmem_wdata),
        .hart_run(hart_run),
        .halted(halted), .halt_cause(halt_cause),
        .rvfi_valid(rvfi_valid), .rvfi_ctx(rvfi_ctx),
        .rvfi_rd_addr(rvfi_rd_addr), .rvfi_rd_wdata(rvfi_rd_wdata),
        .o_run(o_run), .o_halted(o_halted));

    // -------------------------------------------------------------------------
    // gatling_tetrad and its harness
    // -------------------------------------------------------------------------
    logic [8:0]  cfg_func_sel     [N];
    logic [1:0]  cfg_op_lines     [N];
    logic [15:0] cfg_threshold    [N];
    logic [31:0] cfg_credit_batch [N];
    logic        min_wr_valid [N], min_wr_ready [N], line_consumed [N];
    logic [4:0]  min_wr_addr  [N];
    logic [31:0] min_wr_data  [N];
    logic [5:0]  min_occupancy [N];
    logic        mout_rd_valid [N];
    logic [4:0]  mout_rd_addr  [N];
    logic [31:0] mout_rd_data  [N];
    logic [5:0]  mout_occupancy [N];
    logic        flush_valid [N], flush_ready [N];
    logic [14:0] flush_dest  [N];
    logic [3:0]  flush_tag   [N];
    logic        kick_valid  [N];
    logic [31:0] kick_value  [N];
    logic [3:0]  event_flags, ctx_stalled;
    logic [2:0]  ctx_stall_op [N];
    logic        alu_err_opcode [N];

    gatling_tetrad #(
        .NUM_HARTS(N), .RESET_ADDR(32'h0), .IN_DEPTH(32), .OUT_DEPTH(32),
        .ALU_EN_INT8(ALU_EN_INT8), .ALU_EN_FP32(ALU_EN_FP32), .ALU_EN_FP8(ALU_EN_FP8),
        .ALU_EN_REDUCE(ALU_EN_REDUCE), .ALU_EN_PWL(ALU_EN_PWL), .ALU_EN_ACT(ALU_EN_ACT),
        .ALU_EN_CVT(ALU_EN_CVT)
    ) u_tetrad (
        .clk(aclk), .rst_n(aresetn), .hart_run(hart_run),
        .imem_ctx(imem_ctx), .imem_addr(imem_addr), .imem_rdata(imem_rdata),
        .dmem_req(dmem_req), .dmem_ctx(dmem_ctx), .dmem_addr(dmem_addr),
        .dmem_rdata(dmem_rdata), .dmem_wstrb(dmem_wstrb), .dmem_wdata(dmem_wdata),
        .halted(halted), .halt_cause(halt_cause), .done(done),
        .cfg_func_sel(cfg_func_sel), .cfg_op_lines(cfg_op_lines),
        .cfg_threshold(cfg_threshold), .cfg_credit_batch(cfg_credit_batch),
        .min_wr_valid(min_wr_valid), .min_wr_ready(min_wr_ready),
        .min_wr_addr(min_wr_addr), .min_wr_data(min_wr_data),
        .min_occupancy(min_occupancy), .line_consumed(line_consumed),
        .mout_rd_valid(mout_rd_valid), .mout_rd_addr(mout_rd_addr),
        .mout_rd_data(mout_rd_data), .mout_occupancy(mout_occupancy),
        .flush_valid(flush_valid), .flush_ready(flush_ready),
        .flush_dest(flush_dest), .flush_tag(flush_tag),
        .kick_valid(kick_valid), .kick_value(kick_value),
        .event_flags(event_flags), .ctx_stalled(ctx_stalled),
        .ctx_stall_op(ctx_stall_op), .alu_err_opcode(alu_err_opcode),
        .rvfi_valid(rvfi_valid), .rvfi_ctx(rvfi_ctx), .rvfi_order(),
        .rvfi_pc_rdata(), .rvfi_pc_wdata(), .rvfi_insn(), .rvfi_trap(),
        .rvfi_rs1_addr(), .rvfi_rs2_addr(), .rvfi_rs1_rdata(), .rvfi_rs2_rdata(),
        .rvfi_rd_addr(rvfi_rd_addr), .rvfi_rd_wdata(rvfi_rd_wdata),
        .rvfi_mem_addr(), .rvfi_mem_rmask(), .rvfi_mem_wmask(),
        .rvfi_mem_rdata(), .rvfi_mem_wdata());

    gatling_tetrad_harness #(
        .NUM_HARTS(N), .IN_DEPTH(32), .OUT_DEPTH(32)
    ) u_harness (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr(m_awaddr[11:0]), .s_axil_awprot(m_awprot),
        .s_axil_awvalid(m_awvalid[1]), .s_axil_awready(m_awready[1]),
        .s_axil_wdata(m_wdata), .s_axil_wstrb(m_wstrb),
        .s_axil_wvalid(m_wvalid[1]), .s_axil_wready(m_wready[1]),
        .s_axil_bresp(m_bresp[1]), .s_axil_bvalid(m_bvalid[1]), .s_axil_bready(m_bready[1]),
        .s_axil_araddr(m_araddr[11:0]), .s_axil_arprot(m_arprot),
        .s_axil_arvalid(m_arvalid[1]), .s_axil_arready(m_arready[1]),
        .s_axil_rdata(m_rdata[1]), .s_axil_rresp(m_rresp[1]),
        .s_axil_rvalid(m_rvalid[1]), .s_axil_rready(m_rready[1]),
        .cfg_func_sel(cfg_func_sel), .cfg_op_lines(cfg_op_lines),
        .cfg_threshold(cfg_threshold), .cfg_credit_batch(cfg_credit_batch),
        .min_wr_valid(min_wr_valid), .min_wr_ready(min_wr_ready),
        .min_wr_addr(min_wr_addr), .min_wr_data(min_wr_data),
        .min_occupancy(min_occupancy), .line_consumed(line_consumed),
        .mout_rd_valid(mout_rd_valid), .mout_rd_addr(mout_rd_addr),
        .mout_rd_data(mout_rd_data), .mout_occupancy(mout_occupancy),
        .flush_valid(flush_valid), .flush_ready(flush_ready),
        .flush_dest(flush_dest), .flush_tag(flush_tag),
        .kick_valid(kick_valid), .kick_value(kick_value),
        .event_flags(event_flags), .ctx_stalled(ctx_stalled),
        .ctx_stall_op(ctx_stall_op), .alu_err_opcode(alu_err_opcode),
        .done(done));

    assign o_done = done;

endmodule : gatling_tetrad_rig
