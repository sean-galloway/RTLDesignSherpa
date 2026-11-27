// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_tetrad_tb_top
// Purpose: cocotb top for gatling_tetrad.  The program memory is the same
//          per-context backdoor-loaded array as gatling_tb_top; every per-cell
//          seam of gatling_tetrad (cfg, input-memory fill, result-memory read,
//          FLUSH, KICK, status) is flattened into packed vectors, cell c in
//          bits [c*W +: W], so the TB drives and samples them as integers.
//          Per-cell consumed-line counters count line_consumed pulses (the
//          credit block's input) for the ledger check.
//
// Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32i
//
// Created: 2026-11-26

`timescale 1ns / 1ps

module gatling_tetrad_tb_top #(
    parameter int          NUM_HARTS  = 4,
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000,
    parameter int          MEM_WORDS  = 4096,           // 16 KB per context
    parameter int          IN_DEPTH   = 32,
    parameter int          OUT_DEPTH  = 32,
    // The ALU families the tetrad tests do not use are left out of the DV
    // build (alu-infer's own suite covers them); 1 builds the full ALU.
    parameter bit          ALU_FULL   = 1'b0,
    parameter int          HART_W     = $clog2(NUM_HARTS),
    parameter int          IN_AW      = $clog2(IN_DEPTH),
    parameter int          OUT_AW     = $clog2(OUT_DEPTH),
    parameter int          IN_OCC_W   = $clog2(IN_DEPTH + 1),
    parameter int          OUT_OCC_W  = $clog2(OUT_DEPTH + 1)
) (
    input  logic                          clk,
    input  logic                          rst_n,
    input  logic [NUM_HARTS-1:0]          hart_run,
    output logic [NUM_HARTS-1:0]          halted,
    output logic [NUM_HARTS*4-1:0]        halt_cause,
    output logic [NUM_HARTS-1:0]          done,

    // Program-memory backdoor
    input  logic                          tb_mem_we,
    input  logic [HART_W-1:0]             tb_mem_ctx,
    input  logic [31:0]                   tb_mem_addr,
    input  logic [31:0]                   tb_mem_wdata,

    // Cell configuration
    input  logic [NUM_HARTS*9-1:0]        cfg_func_sel,
    input  logic [NUM_HARTS*2-1:0]        cfg_op_lines,
    input  logic [NUM_HARTS*16-1:0]       cfg_threshold,
    input  logic [NUM_HARTS*32-1:0]       cfg_credit_batch,

    // Input-memory fill
    input  logic [NUM_HARTS-1:0]          min_wr_valid,
    output logic [NUM_HARTS-1:0]          min_wr_ready,
    input  logic [NUM_HARTS*IN_AW-1:0]    min_wr_addr,
    input  logic [NUM_HARTS*32-1:0]       min_wr_data,
    output logic [NUM_HARTS*IN_OCC_W-1:0] min_occupancy,
    output logic [NUM_HARTS*16-1:0]       consumed_cnt,

    // Result-memory read
    input  logic [NUM_HARTS-1:0]          mout_rd_valid,
    input  logic [NUM_HARTS*OUT_AW-1:0]   mout_rd_addr,
    output logic [NUM_HARTS*32-1:0]       mout_rd_data,
    output logic [NUM_HARTS*OUT_OCC_W-1:0] mout_occupancy,

    // FLUSH / KICK / status
    output logic [NUM_HARTS-1:0]          flush_valid,
    input  logic [NUM_HARTS-1:0]          flush_ready,
    output logic [NUM_HARTS*15-1:0]       flush_dest,
    output logic [NUM_HARTS*4-1:0]        flush_tag,
    output logic [NUM_HARTS-1:0]          kick_valid,
    output logic [NUM_HARTS*32-1:0]       kick_value,
    output logic [NUM_HARTS-1:0]          event_flags,
    output logic [NUM_HARTS-1:0]          ctx_stalled,
    output logic [NUM_HARTS*3-1:0]        ctx_stall_op,
    output logic [NUM_HARTS-1:0]          alu_err_opcode,

    // RVFI
    output logic                          rvfi_valid,
    output logic [HART_W-1:0]             rvfi_ctx,
    output logic [63:0]                   rvfi_order,
    output logic [31:0]                   rvfi_pc_rdata,
    output logic [31:0]                   rvfi_pc_wdata,
    output logic [31:0]                   rvfi_insn,
    output logic                          rvfi_trap,
    output logic [4:0]                    rvfi_rs1_addr,
    output logic [4:0]                    rvfi_rs2_addr,
    output logic [31:0]                   rvfi_rs1_rdata,
    output logic [31:0]                   rvfi_rs2_rdata,
    output logic [4:0]                    rvfi_rd_addr,
    output logic [31:0]                   rvfi_rd_wdata,
    output logic [31:0]                   rvfi_mem_addr,
    output logic [3:0]                    rvfi_mem_rmask,
    output logic [3:0]                    rvfi_mem_wmask,
    output logic [31:0]                   rvfi_mem_rdata,
    output logic [31:0]                   rvfi_mem_wdata,
    output logic                          dmem_req,
    output logic [HART_W-1:0]             dmem_ctx,
    output logic [31:0]                   dmem_addr,
    output logic [3:0]                    dmem_wstrb,
    output logic [31:0]                   dmem_wdata
);

    localparam int IDX_W = $clog2(MEM_WORDS);

    // Program memory: one bank per context, registered read
    logic [31:0] mem [NUM_HARTS*MEM_WORDS];
    logic [31:0] imem_rdata, dmem_rdata;
    logic [HART_W-1:0] imem_ctx;
    logic [31:0] imem_addr;

    initial begin
        for (int i = 0; i < NUM_HARTS * MEM_WORDS; i++) mem[i] = '0;
    end

    always_ff @(posedge clk) begin
        imem_rdata <= mem[{imem_ctx, imem_addr[IDX_W+1:2]}];
        if (dmem_req) begin
            for (int b = 0; b < 4; b++)
                if (dmem_wstrb[b])
                    mem[{dmem_ctx, dmem_addr[IDX_W+1:2]}][b*8 +: 8] <= dmem_wdata[b*8 +: 8];
            dmem_rdata <= mem[{dmem_ctx, dmem_addr[IDX_W+1:2]}];
        end
        if (tb_mem_we) mem[{tb_mem_ctx, tb_mem_addr[IDX_W+1:2]}] <= tb_mem_wdata;
    end

    // Unpacked views of the per-cell seams
    logic [8:0]           u_func_sel [NUM_HARTS];
    logic [1:0]           u_op_lines [NUM_HARTS];
    logic [15:0]          u_thr      [NUM_HARTS];
    logic [31:0]          u_cb       [NUM_HARTS];
    logic                 u_wr_valid [NUM_HARTS];
    logic                 u_wr_ready [NUM_HARTS];
    logic [IN_AW-1:0]     u_wr_addr  [NUM_HARTS];
    logic [31:0]          u_wr_data  [NUM_HARTS];
    logic [IN_OCC_W-1:0]  u_min_occ  [NUM_HARTS];
    logic                 u_consumed [NUM_HARTS];
    logic                 u_rd_valid [NUM_HARTS];
    logic [OUT_AW-1:0]    u_rd_addr  [NUM_HARTS];
    logic [31:0]          u_rd_data  [NUM_HARTS];
    logic [OUT_OCC_W-1:0] u_mout_occ [NUM_HARTS];
    logic                 u_fvalid   [NUM_HARTS];
    logic                 u_fready   [NUM_HARTS];
    logic [14:0]          u_fdest    [NUM_HARTS];
    logic [3:0]           u_ftag     [NUM_HARTS];
    logic                 u_kvalid   [NUM_HARTS];
    logic [31:0]          u_kvalue   [NUM_HARTS];
    logic [2:0]           u_stall_op [NUM_HARTS];
    logic                 u_err      [NUM_HARTS];
    logic [15:0]          r_consumed [NUM_HARTS];
    logic [NUM_HARTS-1:0][3:0] w_cause;

    assign halt_cause = w_cause;

    for (genvar c = 0; c < NUM_HARTS; c++) begin : g_flat
        assign u_func_sel[c] = cfg_func_sel[c*9 +: 9];
        assign u_op_lines[c] = cfg_op_lines[c*2 +: 2];
        assign u_thr[c]      = cfg_threshold[c*16 +: 16];
        assign u_cb[c]       = cfg_credit_batch[c*32 +: 32];
        assign u_wr_valid[c] = min_wr_valid[c];
        assign min_wr_ready[c] = u_wr_ready[c];
        assign u_wr_addr[c]  = min_wr_addr[c*IN_AW +: IN_AW];
        assign u_wr_data[c]  = min_wr_data[c*32 +: 32];
        assign min_occupancy[c*IN_OCC_W +: IN_OCC_W] = u_min_occ[c];
        assign consumed_cnt[c*16 +: 16] = r_consumed[c];
        assign u_rd_valid[c] = mout_rd_valid[c];
        assign u_rd_addr[c]  = mout_rd_addr[c*OUT_AW +: OUT_AW];
        assign mout_rd_data[c*32 +: 32] = u_rd_data[c];
        assign mout_occupancy[c*OUT_OCC_W +: OUT_OCC_W] = u_mout_occ[c];
        assign flush_valid[c] = u_fvalid[c];
        assign u_fready[c]    = flush_ready[c];
        assign flush_dest[c*15 +: 15] = u_fdest[c];
        assign flush_tag[c*4 +: 4]    = u_ftag[c];
        assign kick_valid[c]          = u_kvalid[c];
        assign kick_value[c*32 +: 32] = u_kvalue[c];
        assign ctx_stall_op[c*3 +: 3] = u_stall_op[c];
        assign alu_err_opcode[c]      = u_err[c];

        always_ff @(posedge clk or negedge rst_n) begin
            if (!rst_n)              r_consumed[c] <= '0;
            else if (u_consumed[c])  r_consumed[c] <= r_consumed[c] + 1'b1;
        end
    end

    gatling_tetrad #(
        .NUM_HARTS  (NUM_HARTS),
        .RESET_ADDR (RESET_ADDR),
        .IN_DEPTH   (IN_DEPTH),
        .OUT_DEPTH  (OUT_DEPTH),
        .ALU_EN_INT8   (ALU_FULL),
        .ALU_EN_FP32   (ALU_FULL),
        .ALU_EN_FP8    (ALU_FULL),
        .ALU_EN_REDUCE (ALU_FULL),
        .ALU_EN_PWL    (ALU_FULL),
        .ALU_EN_ACT    (ALU_FULL),
        .ALU_EN_CVT    (ALU_FULL)
    ) u_tetrad (
        .clk              (clk),
        .rst_n            (rst_n),
        .hart_run         (hart_run),
        .imem_ctx         (imem_ctx),
        .imem_addr        (imem_addr),
        .imem_rdata       (imem_rdata),
        .dmem_req         (dmem_req),
        .dmem_ctx         (dmem_ctx),
        .dmem_addr        (dmem_addr),
        .dmem_rdata       (dmem_rdata),
        .dmem_wstrb       (dmem_wstrb),
        .dmem_wdata       (dmem_wdata),
        .halted           (halted),
        .halt_cause       (w_cause),
        .done             (done),
        .cfg_func_sel     (u_func_sel),
        .cfg_op_lines     (u_op_lines),
        .cfg_threshold    (u_thr),
        .cfg_credit_batch (u_cb),
        .min_wr_valid     (u_wr_valid),
        .min_wr_ready     (u_wr_ready),
        .min_wr_addr      (u_wr_addr),
        .min_wr_data      (u_wr_data),
        .min_occupancy    (u_min_occ),
        .line_consumed    (u_consumed),
        .mout_rd_valid    (u_rd_valid),
        .mout_rd_addr     (u_rd_addr),
        .mout_rd_data     (u_rd_data),
        .mout_occupancy   (u_mout_occ),
        .flush_valid      (u_fvalid),
        .flush_ready      (u_fready),
        .flush_dest       (u_fdest),
        .flush_tag        (u_ftag),
        .kick_valid       (u_kvalid),
        .kick_value       (u_kvalue),
        .event_flags      (event_flags),
        .ctx_stalled      (ctx_stalled),
        .ctx_stall_op     (u_stall_op),
        .alu_err_opcode   (u_err),
        .rvfi_valid       (rvfi_valid),
        .rvfi_ctx         (rvfi_ctx),
        .rvfi_order       (rvfi_order),
        .rvfi_pc_rdata    (rvfi_pc_rdata),
        .rvfi_pc_wdata    (rvfi_pc_wdata),
        .rvfi_insn        (rvfi_insn),
        .rvfi_trap        (rvfi_trap),
        .rvfi_rs1_addr    (rvfi_rs1_addr),
        .rvfi_rs2_addr    (rvfi_rs2_addr),
        .rvfi_rs1_rdata   (rvfi_rs1_rdata),
        .rvfi_rs2_rdata   (rvfi_rs2_rdata),
        .rvfi_rd_addr     (rvfi_rd_addr),
        .rvfi_rd_wdata    (rvfi_rd_wdata),
        .rvfi_mem_addr    (rvfi_mem_addr),
        .rvfi_mem_rmask   (rvfi_mem_rmask),
        .rvfi_mem_wmask   (rvfi_mem_wmask),
        .rvfi_mem_rdata   (rvfi_mem_rdata),
        .rvfi_mem_wdata   (rvfi_mem_wdata)
    );

endmodule : gatling_tetrad_tb_top
