// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_xcell
// Purpose: The Xcell unit (gatling PRD 3.1).  It answers gatling_core's xc_*
//          port for the seven custom-0 instructions and drives, per context,
//          that context's cell: the input memory's read port, the result
//          memory's write port and the alu-infer issue / retire handshakes
//          (cell MAS 4: "POP reads operand line(s) ... and presents them to the
//          ALU issue handshake; PUSH retires result line(s) from the ALU").
//
//          The core presents one instruction per cycle in X (xc_req, xc_ctx =
//          k); this block answers xc_ok in the same cycle.  xc_ok = 0 stalls
//          the context, which retries on its next slot.  POP rd and CFG rd
//          return their value on xc_rdata one cycle later (the core's W).
//
//          Register field x0 is the ALU port (MAS decision, owner 2026-11-26):
//
//            POP x0     pop cfg_op_lines[k] (1 or 2) lines and issue them to
//                       the ALU with cfg_func_sel[k], cfg_threshold[k] and
//                       acc_ctrl = insn[21:20] (xc_imm[1:0]; 00 = HOLD, the
//                       encoding's zero field).  Stalls until the context's
//                       issue stager is empty and the memory holds the lines.
//            POP rd     pop one line into rd.  Stalls while the memory is
//                       empty.
//            PUSH x0    retire one ALU result into the result memory:
//                       result_line | result_flags (exactly one of them is
//                       non-zero: the compare row returns its mask on flags,
//                       every other row its line).  Stalls until a result is
//                       offered and the result memory has room.
//            PUSH rs1   write rs1 into the result memory.  Stalls while it is
//                       full.
//            CFG rd, i  rd <- 0: element mode (func_sel[8:7]), 1: credit batch
//                       N, anything else 0 (index 2, the context ID, is
//                       implicit -- PRD 7 item 2).  Never stalls.
//            ECTX       never stalls; the core halts the context (done[]).
//            FLUSH rs1  latch {tag = rs1[18:15], dest = rs1[14:0]} as the
//                       context's drain command, offered on flush_valid until
//                       flush_ready.  Stalls while an earlier command is still
//                       waiting.
//            KICK rs1   set the context's event bit and post rs1 on kick_*.
//                       Never stalls.
//            WAIT rs1   stall until every context k' in rs1[NUM_HARTS-1:0] has
//                       kicked or is done.  A one-shot barrier (owner
//                       2026-11-26): an event bit clears only when its context
//                       is held (hart_run low).
//
//          The issue stager.  The input memory has one registered read port,
//          so a two-line POP reads line A in X and line B the next cycle, and
//          presents both to the ALU the cycle after that, holding valid and
//          the operands until ready.  The read and head pointers belong to
//          this block: each read advances the context's head and pulses
//          line_consumed[k] (one consumed line, for the cell's credit block).
//          No other context touches a cell's memories, and a context's next
//          instruction is NUM_HARTS cycles behind its last, so the stager's
//          second read never meets a POP of its own context.
//
// Parameters:
//   - NUM_HARTS:  contexts = cells, >= 4, <= 32 (the WAIT mask is rs1)
//   - LINE_W:     line width; 32 (one register holds one line)
//   - IN_DEPTH:   input-memory lines per cell, >= 2
//   - OUT_DEPTH:  result-memory lines per cell, >= 2
//
// Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32i
//
// Author: sean galloway
// Created: 2026-11-26

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gatling_xcell #(
    parameter int NUM_HARTS = 4,
    parameter int LINE_W    = 32,
    parameter int IN_DEPTH  = 32,
    parameter int OUT_DEPTH = 32,
    parameter int HART_W    = $clog2(NUM_HARTS),
    parameter int IN_AW     = $clog2(IN_DEPTH),
    parameter int OUT_AW    = $clog2(OUT_DEPTH),
    parameter int IN_OCC_W  = $clog2(IN_DEPTH + 1)
) (
    input  logic                     clk,
    input  logic                     aresetn,

    // gatling_core's Xcell port and context state
    input  logic                     xc_req,
    input  logic [HART_W-1:0]        xc_ctx,
    input  logic [2:0]               xc_funct3,
    input  logic                     xc_reg0,
    input  logic [31:0]              xc_rs1,
    input  logic [11:0]              xc_imm,
    output logic                     xc_ok,
    output logic [31:0]              xc_rdata,
    input  logic [NUM_HARTS-1:0]     hart_run,
    input  logic [NUM_HARTS-1:0]     done,

    // Cell configuration, per context (in-band cfg registers in the cell)
    input  logic [8:0]               cfg_func_sel     [NUM_HARTS],
    input  logic [1:0]               cfg_op_lines     [NUM_HARTS],   // 2 = two lines, else one
    input  logic [15:0]              cfg_threshold    [NUM_HARTS],
    input  logic [31:0]              cfg_credit_batch [NUM_HARTS],

    // Input memory read port, per cell (cell_mem_in: registered read)
    output logic                     min_rd_valid     [NUM_HARTS],
    output logic [IN_AW-1:0]         min_rd_addr      [NUM_HARTS],
    input  logic [LINE_W-1:0]        min_rd_data      [NUM_HARTS],
    input  logic [IN_OCC_W-1:0]      min_occupancy    [NUM_HARTS],
    output logic                     line_consumed    [NUM_HARTS],

    // Result memory write port, per cell (cell_mem_out)
    output logic                     mout_wr_valid    [NUM_HARTS],
    output logic [OUT_AW-1:0]        mout_wr_addr     [NUM_HARTS],
    output logic [LINE_W-1:0]        mout_wr_data     [NUM_HARTS],
    input  logic                     mout_full        [NUM_HARTS],

    // alu-infer issue / retire, per cell
    output logic                     alu_valid        [NUM_HARTS],
    input  logic                     alu_ready        [NUM_HARTS],
    output logic [LINE_W-1:0]        alu_op_line_a    [NUM_HARTS],
    output logic [LINE_W-1:0]        alu_op_line_b    [NUM_HARTS],
    output logic [8:0]               alu_func_sel     [NUM_HARTS],
    output logic [1:0]               alu_acc_ctrl     [NUM_HARTS],
    output logic [15:0]              alu_threshold    [NUM_HARTS],
    input  logic                     alu_result_valid [NUM_HARTS],
    output logic                     alu_result_ready [NUM_HARTS],
    input  logic [LINE_W-1:0]        alu_result_line  [NUM_HARTS],
    input  logic [LINE_W-1:0]        alu_result_flags [NUM_HARTS],

    // FLUSH drain command, per cell (to the packetizer's drain controller)
    output logic                     flush_valid      [NUM_HARTS],
    input  logic                     flush_ready      [NUM_HARTS],
    output logic [14:0]              flush_dest       [NUM_HARTS],
    output logic [3:0]               flush_tag        [NUM_HARTS],

    // KICK events and per-context status (for the tetrad MonBus)
    output logic                     kick_valid       [NUM_HARTS],
    output logic [31:0]              kick_value       [NUM_HARTS],
    output logic [NUM_HARTS-1:0]     event_flags,
    output logic [NUM_HARTS-1:0]     ctx_stalled,
    output logic [2:0]               ctx_stall_op     [NUM_HARTS]
);

    initial begin : param_check
        if (LINE_W != 32)
            $error("gatling_xcell: LINE_W must be 32 (one register holds one line), got %0d", LINE_W);
        if (NUM_HARTS < 4 || NUM_HARTS > 32)
            $error("gatling_xcell: NUM_HARTS must be in [4,32], got %0d", NUM_HARTS);
        if (IN_DEPTH < 2 || OUT_DEPTH < 2)
            $error("gatling_xcell: IN_DEPTH and OUT_DEPTH must be >= 2");
    end

    localparam logic [2:0] XC_POP   = 3'b000;
    localparam logic [2:0] XC_PUSH  = 3'b001;
    localparam logic [2:0] XC_FLUSH = 3'b011;
    localparam logic [2:0] XC_KICK  = 3'b100;
    localparam logic [2:0] XC_WAIT  = 3'b101;

    localparam logic [11:0] CFG_ELEM_MODE    = 12'd0;
    localparam logic [11:0] CFG_CREDIT_BATCH = 12'd1;

    // =========================================================================
    // Per-context state
    // =========================================================================
    logic [IN_AW-1:0]   ip_q [NUM_HARTS];         // input-memory head
    logic [OUT_AW-1:0]  op_q [NUM_HARTS];         // result-memory tail
    logic [NUM_HARTS-1:0] stg_cap_a_q;            // stager: line A on min_rd_data (B read now if two)
    logic [NUM_HARTS-1:0] stg_cap_b_q;            // stager: line B on min_rd_data
    logic [NUM_HARTS-1:0] stg_two_q;              // the invocation takes two lines
    logic [NUM_HARTS-1:0] op_v_q;                 // operands offered to the ALU
    logic [NUM_HARTS-1:0] flush_pend_q;
    logic [NUM_HARTS-1:0] event_q;
    logic [NUM_HARTS-1:0] stall_q;
    logic [2:0]           stall_op_q [NUM_HARTS];

    logic [LINE_W-1:0]  op_a_q   [NUM_HARTS];
    logic [LINE_W-1:0]  op_b_q   [NUM_HARTS];
    logic [8:0]         func_q   [NUM_HARTS];
    logic [1:0]         acc_q    [NUM_HARTS];
    logic [15:0]        thr_q    [NUM_HARTS];
    logic [14:0]        fdest_q  [NUM_HARTS];
    logic [3:0]         ftag_q   [NUM_HARTS];
    logic [31:0]        kval_q   [NUM_HARTS];
    logic [NUM_HARTS-1:0] kvalid_q;

    // =========================================================================
    // X-stage answer for the context in X
    // =========================================================================
    logic             k_stg_idle, k_need_two, k_lines_ok, k_wait_ok;
    logic [NUM_HARTS-1:0] wait_mask;
    logic             fire;

    assign k_stg_idle = ~stg_cap_a_q[xc_ctx] & ~stg_cap_b_q[xc_ctx] & ~op_v_q[xc_ctx];
    assign k_need_two = (cfg_op_lines[xc_ctx] == 2'd2);
    assign k_lines_ok = (min_occupancy[xc_ctx] >= (k_need_two ? IN_OCC_W'(2) : IN_OCC_W'(1)));
    assign wait_mask  = xc_rs1[NUM_HARTS-1:0];
    assign k_wait_ok  = &((event_q | done) | ~wait_mask);

    always_comb begin
        unique case (xc_funct3)
            XC_POP:   xc_ok = xc_reg0 ? (k_stg_idle & k_lines_ok)
                                      : (min_occupancy[xc_ctx] != '0);
            XC_PUSH:  xc_ok = ~mout_full[xc_ctx] & (~xc_reg0 | alu_result_valid[xc_ctx]);
            XC_FLUSH: xc_ok = ~flush_pend_q[xc_ctx];
            XC_WAIT:  xc_ok = k_wait_ok;
            default:  xc_ok = 1'b1;                   // ECTX, KICK, CFG
        endcase
    end

    assign fire = xc_req & xc_ok;

    // One-hot of the context in X, and the per-context fire decode
    logic [NUM_HARTS-1:0] in_x, f_pop_alu, f_pop_reg, f_push, f_push_alu, f_flush, f_kick;

    always_comb begin
        for (int c = 0; c < NUM_HARTS; c++) begin
            in_x[c]       = xc_req & (xc_ctx == HART_W'(c));
            f_pop_alu[c]  = fire & in_x[c] & (xc_funct3 == XC_POP) &  xc_reg0;
            f_pop_reg[c]  = fire & in_x[c] & (xc_funct3 == XC_POP) & ~xc_reg0;
            f_push[c]     = fire & in_x[c] & (xc_funct3 == XC_PUSH);
            f_push_alu[c] = f_push[c] & xc_reg0;
            f_flush[c]    = fire & in_x[c] & (xc_funct3 == XC_FLUSH);
            f_kick[c]     = fire & in_x[c] & (xc_funct3 == XC_KICK);
        end
    end

    // =========================================================================
    // Memory and ALU ports
    // =========================================================================
    always_comb begin
        for (int c = 0; c < NUM_HARTS; c++) begin
            // Every read is at the head; the head advances on every read.
            min_rd_valid[c]  = f_pop_alu[c] | f_pop_reg[c] | (stg_cap_a_q[c] & stg_two_q[c]);
            min_rd_addr[c]   = ip_q[c];
            line_consumed[c] = min_rd_valid[c];

            mout_wr_valid[c] = f_push[c];
            mout_wr_addr[c]  = op_q[c];
            mout_wr_data[c]  = xc_reg0 ? (alu_result_line[c] | alu_result_flags[c]) : xc_rs1;
            alu_result_ready[c] = f_push_alu[c];

            alu_valid[c]     = op_v_q[c];
            alu_op_line_a[c] = op_a_q[c];
            alu_op_line_b[c] = op_b_q[c];
            alu_func_sel[c]  = func_q[c];
            alu_acc_ctrl[c]  = acc_q[c];
            alu_threshold[c] = thr_q[c];

            flush_valid[c]   = flush_pend_q[c];
            flush_dest[c]    = fdest_q[c];
            flush_tag[c]     = ftag_q[c];

            kick_valid[c]    = kvalid_q[c];
            kick_value[c]    = kval_q[c];
            ctx_stall_op[c]  = stall_op_q[c];
        end
    end

    assign event_flags = event_q;
    assign ctx_stalled = stall_q;

    // =========================================================================
    // Control state
    // =========================================================================
    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int c = 0; c < NUM_HARTS; c++) begin
                ip_q[c] <= '0;
                op_q[c] <= '0;
            end
            stg_cap_b_q  <= '0;
            stg_cap_a_q  <= '0;
            stg_two_q    <= '0;
            op_v_q       <= '0;
            flush_pend_q <= '0;
            event_q      <= '0;
            stall_q      <= '0;
            kvalid_q     <= '0;
        end else begin
            for (int c = 0; c < NUM_HARTS; c++) begin
                if (min_rd_valid[c])
                    ip_q[c] <= (ip_q[c] == IN_AW'(IN_DEPTH - 1)) ? '0 : ip_q[c] + 1'b1;
                if (f_push[c])
                    op_q[c] <= (op_q[c] == OUT_AW'(OUT_DEPTH - 1)) ? '0 : op_q[c] + 1'b1;

                // Stager: A is read in X and captured the next cycle, in
                // which B is read if the invocation takes two; B is captured
                // the cycle after.  Operands are offered from the last capture.
                stg_cap_a_q[c] <= f_pop_alu[c];
                if (f_pop_alu[c]) stg_two_q[c] <= k_need_two;
                stg_cap_b_q[c] <= stg_cap_a_q[c] & stg_two_q[c];
                if (alu_valid[c] && alu_ready[c])
                    op_v_q[c] <= 1'b0;
                else if ((stg_cap_a_q[c] && !stg_two_q[c]) || stg_cap_b_q[c])
                    op_v_q[c] <= 1'b1;

                if (flush_valid[c] && flush_ready[c]) flush_pend_q[c] <= 1'b0;
                else if (f_flush[c])                  flush_pend_q[c] <= 1'b1;

                kvalid_q[c] <= f_kick[c];

                if (!hart_run[c])  event_q[c] <= 1'b0;
                else if (f_kick[c]) event_q[c] <= 1'b1;

                if (!hart_run[c])                  stall_q[c] <= 1'b0;
                else if (in_x[c] && !xc_ok)        stall_q[c] <= 1'b1;
                else if (in_x[c])                  stall_q[c] <= 1'b0;
            end
        end
    )

    // Datapath registers: no reset (each is qualified by a control bit above)
    always_ff @(posedge clk) begin
        for (int c = 0; c < NUM_HARTS; c++) begin
            if (f_pop_alu[c]) begin
                func_q[c] <= cfg_func_sel[c];
                acc_q[c]  <= xc_imm[1:0];
                thr_q[c]  <= cfg_threshold[c];
            end
            if (stg_cap_a_q[c]) begin
                op_a_q[c] <= min_rd_data[c];
                op_b_q[c] <= '0;
            end
            if (stg_cap_b_q[c]) op_b_q[c] <= min_rd_data[c];
            if (f_flush[c]) begin
                fdest_q[c] <= xc_rs1[14:0];
                ftag_q[c]  <= xc_rs1[18:15];
            end
            if (f_kick[c])               kval_q[c]     <= xc_rs1;
            if (in_x[c] && !xc_ok)       stall_op_q[c] <= xc_funct3;
        end
    end

    // =========================================================================
    // W-stage return value: POP rd reads the memory's registered output,
    // CFG a value registered here.
    // =========================================================================
    logic              w_from_mem;
    logic [HART_W-1:0] w_k;
    logic [31:0]       cfg_q;

    always_ff @(posedge clk) begin
        w_from_mem <= (xc_funct3 == XC_POP);
        w_k        <= xc_ctx;
        unique case (xc_imm)
            CFG_ELEM_MODE:    cfg_q <= {30'd0, cfg_func_sel[xc_ctx][8:7]};
            CFG_CREDIT_BATCH: cfg_q <= cfg_credit_batch[xc_ctx];
            default:          cfg_q <= 32'd0;
        endcase
    end

    assign xc_rdata = w_from_mem ? min_rd_data[w_k] : cfg_q;

endmodule : gatling_xcell
