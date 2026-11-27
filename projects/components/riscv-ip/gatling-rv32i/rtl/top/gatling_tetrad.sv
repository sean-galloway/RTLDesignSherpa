// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_tetrad
// Purpose: gatling sequencing its tetrad's cells (gatling PRD 1, owner ruling
//          2026-10-19): gatling_core with Xcell built, the Xcell unit, and per
//          context the three cell blocks the Xcell instructions drive -- the
//          cell's input memory (cell_mem_in), its alu-infer ALU
//          (alu_infer_top) and its result memory (cell_mem_out).
//
//          What is not here is the rest of the cell, which does not exist
//          yet (compute-eng-ip cell TASK-001/002): the delta node and rx demux
//          that fill the input memory, the packetizer that drains the result
//          memory, the credit block and the cfg registers.  Their seams are
//          this module's ports: the input-memory write port, the
//          result-memory read port, the drain command (flush_*), the
//          consumed-line pulses (line_consumed) and the cell configuration
//          (cfg_*).  The program memory is outside too, on the core's
//          imem / dmem ports, as in every gatling build.
//
// Parameters:
//   - NUM_HARTS:  contexts = cells (default 4, the tetrad)
//   - RESET_ADDR: every context's reset PC
//   - IN_DEPTH:   input-memory lines per cell
//   - OUT_DEPTH:  result-memory lines per cell
//   - ALU_EN_*:   alu-infer's build-out switches (EN_INT8 .. EN_CVT), passed
//                 through; default 1, the full ALU.  The bf16 base rows are
//                 always built.
//
// Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32i
//
// Author: sean galloway
// Created: 2026-11-26

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gatling_tetrad #(
    parameter int          NUM_HARTS  = 4,
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000,
    parameter int          IN_DEPTH   = 32,
    parameter int          OUT_DEPTH  = 32,
    parameter bit          ALU_EN_INT8   = 1'b1,
    parameter bit          ALU_EN_FP32   = 1'b1,
    parameter bit          ALU_EN_FP8    = 1'b1,
    parameter bit          ALU_EN_REDUCE = 1'b1,
    parameter bit          ALU_EN_PWL    = 1'b1,
    parameter bit          ALU_EN_ACT    = 1'b1,
    parameter bit          ALU_EN_CVT    = 1'b1,
    parameter int          HART_W     = $clog2(NUM_HARTS),
    parameter int          IN_AW      = $clog2(IN_DEPTH),
    parameter int          OUT_AW     = $clog2(OUT_DEPTH),
    parameter int          IN_OCC_W   = $clog2(IN_DEPTH + 1),
    parameter int          OUT_OCC_W  = $clog2(OUT_DEPTH + 1)
) (
    input  logic                       clk,
    input  logic                       rst_n,
    input  logic [NUM_HARTS-1:0]       hart_run,

    // Program memory (registered read), as gatling_core
    output logic [HART_W-1:0]          imem_ctx,
    output logic [31:0]                imem_addr,
    input  logic [31:0]                imem_rdata,
    output logic                       dmem_req,
    output logic [HART_W-1:0]          dmem_ctx,
    output logic [31:0]                dmem_addr,
    input  logic [31:0]                dmem_rdata,
    output logic [3:0]                 dmem_wstrb,
    output logic [31:0]                dmem_wdata,

    // Context state
    output logic [NUM_HARTS-1:0]       halted,
    output logic [NUM_HARTS-1:0][3:0]  halt_cause,
    output logic [NUM_HARTS-1:0]       done,

    // Cell configuration, per cell
    input  logic [8:0]                 cfg_func_sel     [NUM_HARTS],
    input  logic [1:0]                 cfg_op_lines     [NUM_HARTS],
    input  logic [15:0]                cfg_threshold    [NUM_HARTS],
    input  logic [31:0]                cfg_credit_batch [NUM_HARTS],

    // Input-memory fill (the rx demux's seam), per cell
    input  logic                       min_wr_valid     [NUM_HARTS],
    output logic                       min_wr_ready     [NUM_HARTS],
    input  logic [IN_AW-1:0]           min_wr_addr      [NUM_HARTS],
    input  logic [31:0]                min_wr_data      [NUM_HARTS],
    output logic [IN_OCC_W-1:0]        min_occupancy    [NUM_HARTS],
    output logic                       line_consumed    [NUM_HARTS],

    // Result-memory drain (the packetizer's seam), per cell
    input  logic                       mout_rd_valid    [NUM_HARTS],
    input  logic [OUT_AW-1:0]          mout_rd_addr     [NUM_HARTS],
    output logic [31:0]                mout_rd_data     [NUM_HARTS],
    output logic [OUT_OCC_W-1:0]       mout_occupancy   [NUM_HARTS],

    // FLUSH drain command, KICK events, status
    output logic                       flush_valid      [NUM_HARTS],
    input  logic                       flush_ready      [NUM_HARTS],
    output logic [14:0]                flush_dest       [NUM_HARTS],
    output logic [3:0]                 flush_tag        [NUM_HARTS],
    output logic                       kick_valid       [NUM_HARTS],
    output logic [31:0]                kick_value       [NUM_HARTS],
    output logic [NUM_HARTS-1:0]       event_flags,
    output logic [NUM_HARTS-1:0]       ctx_stalled,
    output logic [2:0]                 ctx_stall_op     [NUM_HARTS],
    output logic                       alu_err_opcode   [NUM_HARTS],

    // RVFI, as gatling_core
    output logic                       rvfi_valid,
    output logic [HART_W-1:0]          rvfi_ctx,
    output logic [63:0]                rvfi_order,
    output logic [31:0]                rvfi_pc_rdata,
    output logic [31:0]                rvfi_pc_wdata,
    output logic [31:0]                rvfi_insn,
    output logic                       rvfi_trap,
    output logic [4:0]                 rvfi_rs1_addr,
    output logic [4:0]                 rvfi_rs2_addr,
    output logic [31:0]                rvfi_rs1_rdata,
    output logic [31:0]                rvfi_rs2_rdata,
    output logic [4:0]                 rvfi_rd_addr,
    output logic [31:0]                rvfi_rd_wdata,
    output logic [31:0]                rvfi_mem_addr,
    output logic [3:0]                 rvfi_mem_rmask,
    output logic [3:0]                 rvfi_mem_wmask,
    output logic [31:0]                rvfi_mem_rdata,
    output logic [31:0]                rvfi_mem_wdata
);

    localparam int LINE_W = 32;

    // The cell blocks and the Xcell unit take a synchronized reset; the core
    // synchronizes its own.
    logic w_aresetn;

    reset_sync #(
        .N             (3),
        .KEEP_ATTRS    (1'b1),
        .IN_ACTIVE_LOW (1'b1),
        .OUT_ACTIVE_LOW(1'b1),
        .ASYNC_ASSERT  (1'b1)
    ) u_reset_sync (
        .clk        (clk),
        .rst_n      (rst_n),
        .sync_rst_n (w_aresetn)
    );

    // =========================================================================
    // Core and Xcell unit
    // =========================================================================
    logic              xc_req, xc_reg0, xc_ok;
    logic [HART_W-1:0] xc_ctx;
    logic [2:0]        xc_funct3;
    logic [31:0]       xc_rs1, xc_rdata;
    logic [11:0]       xc_imm;

    gatling_core #(
        .NUM_HARTS  (NUM_HARTS),
        .RESET_ADDR (RESET_ADDR),
        .XCELL_EN   (1'b1)
    ) u_core (
        .clk            (clk),
        .rst_n          (rst_n),
        .hart_run       (hart_run),
        .imem_ctx       (imem_ctx),
        .imem_addr      (imem_addr),
        .imem_rdata     (imem_rdata),
        .dmem_req       (dmem_req),
        .dmem_ctx       (dmem_ctx),
        .dmem_addr      (dmem_addr),
        .dmem_rdata     (dmem_rdata),
        .dmem_wstrb     (dmem_wstrb),
        .dmem_wdata     (dmem_wdata),
        .halted         (halted),
        .halt_cause     (halt_cause),
        .done           (done),
        .xc_req         (xc_req),
        .xc_ctx         (xc_ctx),
        .xc_funct3      (xc_funct3),
        .xc_reg0        (xc_reg0),
        .xc_rs1         (xc_rs1),
        .xc_imm         (xc_imm),
        .xc_ok          (xc_ok),
        .xc_rdata       (xc_rdata),
        .rvfi_valid     (rvfi_valid),
        .rvfi_ctx       (rvfi_ctx),
        .rvfi_order     (rvfi_order),
        .rvfi_pc_rdata  (rvfi_pc_rdata),
        .rvfi_pc_wdata  (rvfi_pc_wdata),
        .rvfi_insn      (rvfi_insn),
        .rvfi_trap      (rvfi_trap),
        .rvfi_rs1_addr  (rvfi_rs1_addr),
        .rvfi_rs2_addr  (rvfi_rs2_addr),
        .rvfi_rs1_rdata (rvfi_rs1_rdata),
        .rvfi_rs2_rdata (rvfi_rs2_rdata),
        .rvfi_rd_addr   (rvfi_rd_addr),
        .rvfi_rd_wdata  (rvfi_rd_wdata),
        .rvfi_mem_addr  (rvfi_mem_addr),
        .rvfi_mem_rmask (rvfi_mem_rmask),
        .rvfi_mem_wmask (rvfi_mem_wmask),
        .rvfi_mem_rdata (rvfi_mem_rdata),
        .rvfi_mem_wdata (rvfi_mem_wdata)
    );

    logic                min_rd_valid     [NUM_HARTS];
    logic [IN_AW-1:0]    min_rd_addr      [NUM_HARTS];
    logic [LINE_W-1:0]   min_rd_data      [NUM_HARTS];
    logic                mout_wr_valid    [NUM_HARTS];
    logic [OUT_AW-1:0]   mout_wr_addr     [NUM_HARTS];
    logic [LINE_W-1:0]   mout_wr_data     [NUM_HARTS];
    logic                mout_full        [NUM_HARTS];
    logic                alu_valid        [NUM_HARTS];
    logic                alu_ready        [NUM_HARTS];
    logic [LINE_W-1:0]   alu_op_line_a    [NUM_HARTS];
    logic [LINE_W-1:0]   alu_op_line_b    [NUM_HARTS];
    logic [8:0]          alu_func_sel     [NUM_HARTS];
    logic [1:0]          alu_acc_ctrl     [NUM_HARTS];
    logic [15:0]         alu_threshold    [NUM_HARTS];
    logic                alu_result_valid [NUM_HARTS];
    logic                alu_result_ready [NUM_HARTS];
    logic [LINE_W-1:0]   alu_result_line  [NUM_HARTS];
    logic [LINE_W-1:0]   alu_result_flags [NUM_HARTS];

    gatling_xcell #(
        .NUM_HARTS (NUM_HARTS),
        .LINE_W    (LINE_W),
        .IN_DEPTH  (IN_DEPTH),
        .OUT_DEPTH (OUT_DEPTH)
    ) u_xcell (
        .clk              (clk),
        .aresetn          (w_aresetn),
        .xc_req           (xc_req),
        .xc_ctx           (xc_ctx),
        .xc_funct3        (xc_funct3),
        .xc_reg0          (xc_reg0),
        .xc_rs1           (xc_rs1),
        .xc_imm           (xc_imm),
        .xc_ok            (xc_ok),
        .xc_rdata         (xc_rdata),
        .hart_run         (hart_run),
        .done             (done),
        .cfg_func_sel     (cfg_func_sel),
        .cfg_op_lines     (cfg_op_lines),
        .cfg_threshold    (cfg_threshold),
        .cfg_credit_batch (cfg_credit_batch),
        .min_rd_valid     (min_rd_valid),
        .min_rd_addr      (min_rd_addr),
        .min_rd_data      (min_rd_data),
        .min_occupancy    (min_occupancy),
        .line_consumed    (line_consumed),
        .mout_wr_valid    (mout_wr_valid),
        .mout_wr_addr     (mout_wr_addr),
        .mout_wr_data     (mout_wr_data),
        .mout_full        (mout_full),
        .alu_valid        (alu_valid),
        .alu_ready        (alu_ready),
        .alu_op_line_a    (alu_op_line_a),
        .alu_op_line_b    (alu_op_line_b),
        .alu_func_sel     (alu_func_sel),
        .alu_acc_ctrl     (alu_acc_ctrl),
        .alu_threshold    (alu_threshold),
        .alu_result_valid (alu_result_valid),
        .alu_result_ready (alu_result_ready),
        .alu_result_line  (alu_result_line),
        .alu_result_flags (alu_result_flags),
        .flush_valid      (flush_valid),
        .flush_ready      (flush_ready),
        .flush_dest       (flush_dest),
        .flush_tag        (flush_tag),
        .kick_valid       (kick_valid),
        .kick_value       (kick_value),
        .event_flags      (event_flags),
        .ctx_stalled      (ctx_stalled),
        .ctx_stall_op     (ctx_stall_op)
    );

    // =========================================================================
    // The cells: input memory, ALU, result memory per context
    // =========================================================================
    for (genvar c = 0; c < NUM_HARTS; c++) begin : g_cell
        logic min_empty_unused, min_full_unused, min_rd_ready_unused;
        logic mout_empty_unused, mout_wr_ready_unused, mout_rd_ready_unused;
        logic [cell_pkg::COORD_BITS-1:0] src_coord_unused;

        cell_mem_in #(
            .LINE_W   (LINE_W),
            .IN_DEPTH (IN_DEPTH)
        ) u_mem_in (
            .aclk         (clk),
            .aresetn      (w_aresetn),
            .wr_valid     (min_wr_valid[c]),
            .wr_ready     (min_wr_ready[c]),
            .wr_addr      (min_wr_addr[c]),
            .wr_data      (min_wr_data[c]),
            .wr_src_coord ('0),
            .rd_valid     (min_rd_valid[c]),
            .rd_ready     (min_rd_ready_unused),
            .rd_addr      (min_rd_addr[c]),
            .rd_data      (min_rd_data[c]),
            .rd_src_coord (src_coord_unused),
            .o_empty      (min_empty_unused),
            .o_full       (min_full_unused),
            .o_occupancy  (min_occupancy[c])
        );

        alu_infer_top #(
            .LINE_W    (LINE_W),
            .EN_INT8   (ALU_EN_INT8),
            .EN_FP32   (ALU_EN_FP32),
            .EN_FP8    (ALU_EN_FP8),
            .EN_REDUCE (ALU_EN_REDUCE),
            .EN_PWL    (ALU_EN_PWL),
            .EN_ACT    (ALU_EN_ACT),
            .EN_CVT    (ALU_EN_CVT)
        ) u_alu (
            .clk           (clk),
            .aresetn       (w_aresetn),
            .op_line_a     (alu_op_line_a[c]),
            .op_line_b     (alu_op_line_b[c]),
            .threshold_imm (alu_threshold[c]),
            .func_sel      (alu_func_sel[c]),
            .acc_ctrl      (alu_acc_ctrl[c]),
            .valid         (alu_valid[c]),
            .ready         (alu_ready[c]),
            .result_valid  (alu_result_valid[c]),
            .result_ready  (alu_result_ready[c]),
            .result_line   (alu_result_line[c]),
            .result_flags  (alu_result_flags[c]),
            .err_opcode    (alu_err_opcode[c])
        );

        cell_mem_out #(
            .LINE_W    (LINE_W),
            .OUT_DEPTH (OUT_DEPTH)
        ) u_mem_out (
            .aclk        (clk),
            .aresetn     (w_aresetn),
            .wr_valid    (mout_wr_valid[c]),
            .wr_ready    (mout_wr_ready_unused),
            .wr_addr     (mout_wr_addr[c]),
            .wr_data     (mout_wr_data[c]),
            .rd_valid    (mout_rd_valid[c]),
            .rd_ready    (mout_rd_ready_unused),
            .rd_addr     (mout_rd_addr[c]),
            .rd_data     (mout_rd_data[c]),
            .o_empty     (mout_empty_unused),
            .o_full      (mout_full[c]),
            .o_occupancy (mout_occupancy[c])
        );
    end

endmodule : gatling_tetrad
