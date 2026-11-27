// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: formal_gatling_xcell_live
// Purpose: bounded liveness of the Xcell interlock (gatling-rv32i TASK-005).
//          The real gatling_core (XCELL_EN = 1) and gatling_xcell, wired as
//          gatling_tetrad wires them, against an abstract cell: the input
//          memory, result memory, ALU and FLUSH acceptor are counters whose
//          every wait is FAIR (bounded by K cycles).  Under the program
//          contract below, every context retires an instruction at least
//          once every BOUND cycles: no interlock term can wait forever on
//          state that only the waiting context could change.
//
//          ISOLATE = 1 drops the fairness of context 0's input memory, so
//          context 0 may starve on POP forever; contexts 1..3 must still
//          retire every BOUND cycles (a stalled context never blocks the
//          rotation).
//
// Program contract (the free instruction stream is constrained to it):
//   - ADDI and the Xcell POP, PUSH, FLUSH, KICK, CFG; no ECTX (it halts),
//     no WAIT (its release is a program property: every masked context must
//     KICK or ECTX), no loads/stores/branches (no halts, no misalignment).
//   - PUSH x0 only with an invocation outstanding (POP x0 retired and not
//     yet PUSHed): otherwise nothing will ever arrive.
//   - POP x0 only with at most ALU_D invocations outstanding: the ALU holds
//     ALU_D and the issue stager one more, so the (ALU_D+2)th POP x0 would
//     wait for a PUSH x0 of its own context.  For alu-infer, ALU_D is
//     PIPE_DEPTH.
//   - A refetch of the same PC returns the same word (a program memory).
//
// Abstract environment, per context c:
//   occ   lines in the input memory;   fill  free, fair while occ < 2
//   mcnt  lines in the result memory;  drain free, fair while mcnt > 0
//   acnt  invocations in the ALU;      alu_ready free & acnt < ALU_D, fair
//                                      result_valid free & acnt > 0, fair,
//                                      and HELD until taken (valid/ready:
//                                      alu-infer's is occupancy != 0 &&
//                                      mb_arrived[head]).  A model that may
//                                      drop it can time every offer to miss
//                                      the context's one X slot in four.
//   flush_ready free, fair while flush_valid
//
// sv2v packs each per-context unpacked array with context 0 in the HIGH
// slice: element c is [(N-1-c)*W +: W].
//
// Created: 2026-11-26

module formal_gatling_xcell_live #(
    parameter ISOLATE = 0
) (
    input wire clk
);
    localparam N      = 4;
    localparam IN_D   = 4;
    localparam OUT_D  = 4;
    localparam IN_AW  = 2;
    localparam OUT_AW = 2;
    localparam OCC_W  = 3;
    localparam ALU_D  = 2;
    localparam K      = 4;        // fairness bound (cycles)
    localparam BOUND  = 72;       // retirement bound (cycles), see the .sby

    // ------------------------------------------------------------------
    // Reset: low for the first two cycles, high after
    // ------------------------------------------------------------------
    reg [1:0] rcnt = 2'd0;
    always @(posedge clk) if (rcnt != 2'd3) rcnt <= rcnt + 2'd1;
    wire rst_n = (rcnt >= 2'd2);

    // ------------------------------------------------------------------
    // DUT
    // ------------------------------------------------------------------
    wire [1:0]   imem_ctx;
    wire [31:0]  imem_addr;
    reg  [31:0]  imem_rdata;
    wire         dmem_req;
    wire [1:0]   dmem_ctx;
    wire [31:0]  dmem_addr, dmem_wdata;
    wire [3:0]   dmem_wstrb;
    wire [N-1:0] halted, done;
    wire [4*N-1:0] halt_cause;
    wire         xc_req, xc_reg0, xc_ok;
    wire [1:0]   xc_ctx;
    wire [2:0]   xc_funct3;
    wire [31:0]  xc_rs1, xc_rdata;
    wire [11:0]  xc_imm;
    wire         rvfi_valid, rvfi_trap;
    wire [1:0]   rvfi_ctx;

    (* anyseq *) wire [31:0] dmem_rdata;

    gatling_core #(
        .NUM_HARTS  (N),
        .RESET_ADDR (32'h0),
        .XCELL_EN   (1'b1)
    ) u_core (
        .clk (clk), .rst_n (rst_n), .hart_run ({N{1'b1}}),
        .imem_ctx (imem_ctx), .imem_addr (imem_addr), .imem_rdata (imem_rdata),
        .dmem_req (dmem_req), .dmem_ctx (dmem_ctx), .dmem_addr (dmem_addr),
        .dmem_rdata (dmem_rdata), .dmem_wstrb (dmem_wstrb), .dmem_wdata (dmem_wdata),
        .halted (halted), .halt_cause (halt_cause), .done (done),
        .xc_req (xc_req), .xc_ctx (xc_ctx), .xc_funct3 (xc_funct3),
        .xc_reg0 (xc_reg0), .xc_rs1 (xc_rs1), .xc_imm (xc_imm),
        .xc_ok (xc_ok), .xc_rdata (xc_rdata),
        .rvfi_valid (rvfi_valid), .rvfi_ctx (rvfi_ctx), .rvfi_order (),
        .rvfi_pc_rdata (), .rvfi_pc_wdata (), .rvfi_insn (), .rvfi_trap (rvfi_trap),
        .rvfi_rs1_addr (), .rvfi_rs2_addr (), .rvfi_rs1_rdata (), .rvfi_rs2_rdata (),
        .rvfi_rd_addr (), .rvfi_rd_wdata (), .rvfi_mem_addr (), .rvfi_mem_rmask (),
        .rvfi_mem_wmask (), .rvfi_mem_rdata (), .rvfi_mem_wdata ()
    );

    // Xcell ports, packed (context 0 high)
    wire [N-1:0]       min_rd_valid, line_consumed, mout_wr_valid;
    wire [N-1:0]       alu_valid, alu_result_ready, flush_valid, kick_valid;
    wire [N*IN_AW-1:0] min_rd_addr;
    wire [N*OUT_AW-1:0] mout_wr_addr;
    wire [N*32-1:0]    mout_wr_data, alu_op_line_a, alu_op_line_b, kick_value;
    wire [N*9-1:0]     alu_func_sel;
    wire [N*2-1:0]     alu_acc_ctrl;
    wire [N*16-1:0]    alu_threshold;
    wire [N*15-1:0]    flush_dest;
    wire [N*4-1:0]     flush_tag;
    wire [N*3-1:0]     ctx_stall_op;
    wire [N-1:0]       event_flags, ctx_stalled;

    reg  [N*OCC_W-1:0] min_occupancy;
    reg  [N-1:0]       mout_full, alu_ready, alu_result_valid, flush_ready;

    (* anyconst *) wire [N*9-1:0]  cfg_func_sel;
    (* anyconst *) wire [N*2-1:0]  cfg_op_lines;
    (* anyconst *) wire [N*16-1:0] cfg_threshold;
    (* anyconst *) wire [N*32-1:0] cfg_credit_batch;
    (* anyseq *)   wire [N*32-1:0] min_rd_data;
    (* anyseq *)   wire [N*32-1:0] alu_result_line, alu_result_flags;

    gatling_xcell #(
        .NUM_HARTS (N), .LINE_W (32), .IN_DEPTH (IN_D), .OUT_DEPTH (OUT_D)
    ) u_xcell (
        .clk (clk), .aresetn (rst_n),
        .xc_req (xc_req), .xc_ctx (xc_ctx), .xc_funct3 (xc_funct3),
        .xc_reg0 (xc_reg0), .xc_rs1 (xc_rs1), .xc_imm (xc_imm),
        .xc_ok (xc_ok), .xc_rdata (xc_rdata),
        .hart_run ({N{1'b1}}), .done (done),
        .cfg_func_sel (cfg_func_sel), .cfg_op_lines (cfg_op_lines),
        .cfg_threshold (cfg_threshold), .cfg_credit_batch (cfg_credit_batch),
        .min_rd_valid (min_rd_valid), .min_rd_addr (min_rd_addr),
        .min_rd_data (min_rd_data), .min_occupancy (min_occupancy),
        .line_consumed (line_consumed),
        .mout_wr_valid (mout_wr_valid), .mout_wr_addr (mout_wr_addr),
        .mout_wr_data (mout_wr_data), .mout_full (mout_full),
        .alu_valid (alu_valid), .alu_ready (alu_ready),
        .alu_op_line_a (alu_op_line_a), .alu_op_line_b (alu_op_line_b),
        .alu_func_sel (alu_func_sel), .alu_acc_ctrl (alu_acc_ctrl),
        .alu_threshold (alu_threshold),
        .alu_result_valid (alu_result_valid), .alu_result_ready (alu_result_ready),
        .alu_result_line (alu_result_line), .alu_result_flags (alu_result_flags),
        .flush_valid (flush_valid), .flush_ready (flush_ready),
        .flush_dest (flush_dest), .flush_tag (flush_tag),
        .kick_valid (kick_valid), .kick_value (kick_value),
        .event_flags (event_flags), .ctx_stalled (ctx_stalled),
        .ctx_stall_op (ctx_stall_op)
    );

    // ------------------------------------------------------------------
    // Program: a free word per fetch, constrained to the contract.  The
    // program memory is registered (the word is in D the cycle after F).
    // ------------------------------------------------------------------
    (* anyseq *) wire [31:0] w_word;
    always @(posedge clk) imem_rdata <= w_word;

    wire [6:0] w_op = w_word[6:0];
    wire [2:0] w_f3 = w_word[14:12];
    wire       w_x0 = (w_word[11:7] == 5'd0);
    wire w_addi  = (w_op == 7'h13) && (w_f3 == 3'd0);
    wire w_xc    = (w_op == 7'h0B) &&
                   ((w_f3 == 3'd0) || (w_f3 == 3'd1) || (w_f3 == 3'd3) ||
                    (w_f3 == 3'd4) || (w_f3 == 3'd6));
    wire w_popa  = (w_op == 7'h0B) && (w_f3 == 3'd0) && w_x0;
    wire w_pusha = (w_op == 7'h0B) && (w_f3 == 3'd1) && w_x0;

    // Outstanding invocations per context: POP x0 retired minus PUSH x0
    // retired.  Only the context itself changes its own count, and it has
    // one instruction in flight, so the count is current at its fetch.
    wire fire = xc_req & xc_ok;
    reg [3:0]  pend  [0:N-1];
    reg        lastv [0:N-1];
    reg [31:0] lasta [0:N-1];
    reg [31:0] lastw [0:N-1];

    integer i;
    initial for (i = 0; i < N; i = i + 1) begin
        pend[i] = 4'd0; lastv[i] = 1'b0; lasta[i] = 32'd0; lastw[i] = 32'd0;
    end

    always @(posedge clk) begin
        for (i = 0; i < N; i = i + 1) begin
            if (!rst_n) begin
                pend[i]  <= 4'd0;
                lastv[i] <= 1'b0;
            end else begin
                if (fire && xc_ctx == i && xc_reg0 && xc_funct3 == 3'd0)
                    pend[i] <= pend[i] + 4'd1;
                else if (fire && xc_ctx == i && xc_reg0 && xc_funct3 == 3'd1)
                    pend[i] <= pend[i] - 4'd1;
                if (imem_ctx == i) begin
                    lastv[i] <= 1'b1;
                    lasta[i] <= imem_addr;
                    lastw[i] <= w_word;
                end
            end
        end
    end

    always @(*) begin
        assume (w_addi || w_xc);
        if (w_pusha) assume (pend[imem_ctx] != 4'd0);
        if (w_popa)  assume (pend[imem_ctx] <= ALU_D);
        if (lastv[imem_ctx] && imem_addr == lasta[imem_ctx])
            assume (w_word == lastw[imem_ctx]);
    end

    // ------------------------------------------------------------------
    // Abstract cell, per context
    // ------------------------------------------------------------------
    (* anyseq *) wire [N-1:0] fill, drain, ar, rv, fr;

    reg [OCC_W-1:0] occ  [0:N-1];
    reg [2:0]       mcnt [0:N-1];
    reg [1:0]       acnt [0:N-1];
    reg [3:0]       w_fill [0:N-1], w_drain [0:N-1], w_ar [0:N-1],
                    w_rv [0:N-1], w_fr [0:N-1];
    reg [7:0]       since [0:N-1];
    reg [N-1:0]     rv_hold;              // a result offered and not yet taken

    initial for (i = 0; i < N; i = i + 1) begin
        occ[i] = 0; mcnt[i] = 0; acnt[i] = 0;
        w_fill[i] = 0; w_drain[i] = 0; w_ar[i] = 0; w_rv[i] = 0; w_fr[i] = 0;
        since[i] = 0;
    end
    initial rv_hold = '0;

    // Port views (context c's slice, context 0 high)
    wire [N-1:0] lc, mwv, av, arr, fv;
    genvar g;
    generate for (g = 0; g < N; g = g + 1) begin : gv
        assign lc[g]  = line_consumed[N-1-g];
        assign mwv[g] = mout_wr_valid[N-1-g];
        assign av[g]  = alu_valid[N-1-g];
        assign arr[g] = alu_result_ready[N-1-g];
        assign fv[g]  = flush_valid[N-1-g];
    end endgenerate

    always @(*) begin
        for (i = 0; i < N; i = i + 1) begin
            min_occupancy[(N-1-i)*OCC_W +: OCC_W] = occ[i];
            mout_full[N-1-i]        = (mcnt[i] == OUT_D);
            alu_ready[N-1-i]        = ar[i] && (acnt[i] < ALU_D);
            alu_result_valid[N-1-i] = (rv[i] || rv_hold[i]) && (acnt[i] != 2'd0);
            flush_ready[N-1-i]      = fr[i];
        end
    end

    wire [N-1:0] do_fill, do_drain, acc, ret;
    generate for (g = 0; g < N; g = g + 1) begin : gm
        assign do_fill[g]  = fill[g] && (occ[g] < IN_D);
        assign do_drain[g] = drain[g] && (mcnt[g] != 3'd0);
        assign acc[g]      = av[g] && alu_ready[N-1-g];
        assign ret[g]      = alu_result_valid[N-1-g] && arr[g];
    end endgenerate

    always @(posedge clk) begin
        for (i = 0; i < N; i = i + 1) begin
            if (!rst_n) begin
                occ[i] <= 0; mcnt[i] <= 0; acnt[i] <= 0;
                w_fill[i] <= 0; w_drain[i] <= 0; w_ar[i] <= 0; w_rv[i] <= 0; w_fr[i] <= 0;
                since[i] <= 0;
                rv_hold[i] <= 1'b0;
            end else begin
                occ[i]  <= occ[i]  + do_fill[i]  - lc[i];
                mcnt[i] <= mcnt[i] + mwv[i]      - do_drain[i];
                acnt[i] <= acnt[i] + acc[i]      - ret[i];
                w_fill[i]  <= (occ[i] < 2 && !fill[i])             ? w_fill[i]  + 1 : 0;
                w_drain[i] <= (mcnt[i] != 0 && !drain[i])          ? w_drain[i] + 1 : 0;
                w_ar[i]    <= (av[i] && acnt[i] < ALU_D && !ar[i]) ? w_ar[i]    + 1 : 0;
                w_rv[i]    <= (acnt[i] != 0 && !alu_result_valid[N-1-i]) ? w_rv[i] + 1 : 0;
                rv_hold[i] <= alu_result_valid[N-1-i] && !arr[i];
                w_fr[i]    <= (fv[i] && !fr[i])                    ? w_fr[i]    + 1 : 0;
                since[i]   <= (rvfi_valid && rvfi_ctx == i) ? 8'd0
                            : (since[i] == 8'hFF) ? since[i] : since[i] + 8'd1;
            end
        end
    end

    // Fairness
    always @(*) begin
        for (i = 0; i < N; i = i + 1) begin
            if (!(ISOLATE && i == 0)) assume (w_fill[i] < K);
            assume (w_drain[i] < K);
            assume (w_ar[i] < K);
            assume (w_rv[i] < K);
            assume (w_fr[i] < K);
        end
    end

    // ------------------------------------------------------------------
    // Properties
    // ------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst_n) begin
            for (i = 0; i < N; i = i + 1) begin
                // Liveness (bounded): every context retires every BOUND
                // cycles; under ISOLATE, every context but 0.
                if (!(ISOLATE && i == 0)) assert (since[i] < BOUND);
                // The contract keeps the core out of every halt.
                assert (!halted[i]);
                // Safety on the cell seams
                if (lc[i])  assert (occ[i] != 0);          // never read an empty input memory
                if (mwv[i]) assert (mcnt[i] != OUT_D);     // never write a full result memory
                if (arr[i]) assert (alu_result_valid[N-1-i]); // PUSH x0 takes a real result
            end
            if (rvfi_valid) assert (!rvfi_trap);
        end
    end

    // Reachability: an ALU result reaches PUSH x0 (cover), including a
    // two-line invocation and one with the ALU full behind the stager
    always @(posedge clk) begin
        if (rst_n) begin
            cover (ret[0]);
            cover (ret[3] && cfg_op_lines[1:0] == 2'd2);
            cover (pend[1] == ALU_D + 1);
        end
    end
endmodule
