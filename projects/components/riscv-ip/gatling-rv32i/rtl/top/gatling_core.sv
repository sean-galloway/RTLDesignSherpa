// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_core
// Purpose: Barrel RV32I core (gatling PRD 4).  One datapath -- the
//          common-rv32i decode, immediate generator and ALU, shared with
//          kestrel -- time-shared by NUM_HARTS hardware contexts (harts),
//          each with its own PC and register file, interleaved through a
//          four-stage F/D/X/W rotation.
//
//          The rotation.  A counter 0..NUM_HARTS-1 names the context in F;
//          the contexts in D, X and W are the three before it.  Every cycle
//          each stage holds a DIFFERENT context, so a context has exactly
//          one instruction in flight: its next fetch is NUM_HARTS cycles
//          after its last, by which time that instruction has written its
//          PC (end of X) and its register (end of W).  No hazard, no
//          forwarding, no branch penalty; every context retires one
//          instruction per NUM_HARTS-cycle window, and the core retires one
//          per clock with all contexts running.
//
//          NUM_HARTS (default 4, the tetrad) is a parameter of this module
//          and of gatling_regfile / gatling_mem_bram, which size their
//          context arrays from it.  It must be at least the pipeline depth
//          (4): fewer contexts than stages would put two instructions of
//          one context in flight and bring back the hazards.  More
//          contexts than stages is legal (a context then owns 1/NUM_HARTS
//          of the datapath).  The rotation counter wraps explicitly, so
//          NUM_HARTS need not be a power of two.
//
//            F  imem address = pc[ctx]                  (registered read)
//            D  insn = imem word; decode + immediates; register read issued
//            X  operands arrive; ALU, branch, next PC, halt; data access
//               issued; pc[ctx] written
//            W  load data arrives; align/extend; register write; RVFI beat
//
//          Every memory the barrel touches is a registered-read block RAM
//          whose latency is exactly one stage: fetch (F -> D), register read
//          (D -> X), load (X -> W).  There is no wait signal.
//
//          ISA and halt contract are kestrel's (PRD 3: same opcode map, same
//          trap/halt contract) and come from the same fubs: ecall, ebreak,
//          illegal, misaligned control-flow target and misaligned load/store
//          halt with rv32i_pkg's causes; FENCE/FENCE.I are NOPs; MRET
//          falls through; the SYSTEM CSR class reads zero.  Halts are
//          PER CONTEXT (PRD 7 item 4, context-lock, owner 2026-10-21): the
//          halting instruction retires as an RVFI trap beat, that context
//          stops fetching, and the other three keep running.  The Xcell
//          custom-0 opcode is not built yet, so it decodes as illegal and
//          locks its context the same way.
//
//          Context run control.  hart_run[c] = 0 holds context c at
//          RESET_ADDR with its halt cleared and kills any of its instructions
//          in flight; 1 lets it fetch.  The memory system drives it, one bit
//          per hart, so one context can be reloaded while the others run.
//          Context visibility is implicit (PRD 7 item 2, owner 2026-10-21):
//          software cannot tell the contexts apart.
//
// Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32i
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gatling_core #(
    parameter int          NUM_HARTS  = 4,                 // contexts; >= 4 (the pipeline depth)
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000
) (
    input  logic                         clk,
    input  logic                         rst_n,
    input  logic [NUM_HARTS-1:0]         hart_run,       // per context: 1 = run, 0 = hold at RESET_ADDR

    // Instruction port: address in F, word expected in D (registered read)
    output logic [$clog2(NUM_HARTS)-1:0] imem_ctx,
    output logic [31:0]      imem_addr,
    input  logic [31:0]      imem_rdata,

    // Data port: request in X, read word expected in W (registered read)
    output logic             dmem_req,
    output logic [$clog2(NUM_HARTS)-1:0] dmem_ctx,
    output logic [31:0]      dmem_addr,
    input  logic [31:0]      dmem_rdata,
    output logic [3:0]       dmem_wstrb,
    output logic [31:0]      dmem_wdata,

    // Per-context halt state
    output logic [NUM_HARTS-1:0]         halted,
    output logic [NUM_HARTS-1:0][3:0]    halt_cause,     // [ctx]

    // RVFI: at most one retirement per cycle, from W; rvfi_ctx names the
    // context and rvfi_order counts that context's retirements.
    output logic             rvfi_valid,
    output logic [$clog2(NUM_HARTS)-1:0] rvfi_ctx,
    output logic [63:0]      rvfi_order,
    output logic [31:0]      rvfi_pc_rdata,
    output logic [31:0]      rvfi_pc_wdata,
    output logic [31:0]      rvfi_insn,
    output logic             rvfi_trap,
    output logic [4:0]       rvfi_rs1_addr,
    output logic [4:0]       rvfi_rs2_addr,
    output logic [31:0]      rvfi_rs1_rdata,
    output logic [31:0]      rvfi_rs2_rdata,
    output logic [4:0]       rvfi_rd_addr,
    output logic [31:0]      rvfi_rd_wdata,
    output logic [31:0]      rvfi_mem_addr,
    output logic [3:0]       rvfi_mem_rmask,
    output logic [3:0]       rvfi_mem_wmask,
    output logic [31:0]      rvfi_mem_rdata,
    output logic [31:0]      rvfi_mem_wdata
);

    import rv32i_pkg::*;

    localparam int HART_W         = $clog2(NUM_HARTS);
    localparam int PIPELINE_DEPTH = 4;                 // F, D, X, W

    // Elaboration-time parameter validation
    initial begin : param_check
        if (NUM_HARTS < PIPELINE_DEPTH)
            $error("gatling_core: NUM_HARTS (%0d) must be >= the pipeline depth (%0d) -- fewer contexts than stages puts two instructions of one context in flight",
                   NUM_HARTS, PIPELINE_DEPTH);
    end

    localparam logic [31:0] PC_INCR         = 32'd4;
    localparam logic [31:0] JALR_ALIGN_MASK = 32'hFFFF_FFFE;
    localparam logic [6:0]  OPCODE_LUI      = 7'b0110111;

    // funct3 encodings selecting the branch condition
    localparam logic [2:0] F3_BEQ  = 3'b000;
    localparam logic [2:0] F3_BNE  = 3'b001;
    localparam logic [2:0] F3_BLT  = 3'b100;
    localparam logic [2:0] F3_BGE  = 3'b101;
    localparam logic [2:0] F3_BLTU = 3'b110;
    localparam logic [2:0] F3_BGEU = 3'b111;

    localparam logic [3:0] STRB_BYTE = 4'b0001;
    localparam logic [3:0] STRB_HALF = 4'b0011;
    localparam logic [3:0] STRB_WORD = 4'b1111;

    // Boundary reset synchronization, as kestrel_core: rst_n is an
    // asynchronous-assert input of unknown deassert quality.
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
    // Architectural state: per-context PC, halt, retirement order
    // =========================================================================
    logic [NUM_HARTS-1:0][31:0] pc_q;
    logic [NUM_HARTS-1:0]       halted_q;
    logic [NUM_HARTS-1:0][3:0]  cause_q;
    logic [NUM_HARTS-1:0][63:0] order_q;

    // The rotation: the context in F.  Wraps at NUM_HARTS-1 explicitly, so
    // the context count need not be a power of two.
    logic [HART_W-1:0] sel_q;

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn))           sel_q <= '0;
        else if (sel_q == HART_W'(NUM_HARTS-1)) sel_q <= '0;
        else                                    sel_q <= sel_q + 1'b1;
    )

    // =========================================================================
    // F: fetch at the context's PC
    // =========================================================================
    logic f_valid;

    assign f_valid   = w_aresetn & hart_run[sel_q] & ~halted_q[sel_q];
    assign imem_ctx  = sel_q;
    assign imem_addr = pc_q[sel_q];

    // F -> D
    logic              d_valid;
    logic [HART_W-1:0] d_ctx;
    logic [31:0]       d_pc;

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) d_valid <= 1'b0;
        else                          d_valid <= f_valid;
    )

    always_ff @(posedge clk) begin
        d_ctx <= sel_q;
        d_pc  <= pc_q[sel_q];
    end

    // =========================================================================
    // D: decode the fetched word, build immediates, issue the register read
    // =========================================================================
    logic [31:0] d_insn;
    logic        d_live;

    assign d_insn = imem_rdata;
    assign d_live = d_valid & hart_run[d_ctx];

    alu_op_e    dec_alu_op;
    logic       dec_src_a_pc, dec_src_b_imm, dec_rd_wen, dec_dmem_req, dec_dmem_we;
    logic       dec_branch, dec_jump, dec_jalr, dec_csr_stub;
    logic [3:0] dec_halt_cause;
    logic [31:0] d_imm;

    rv32i_decode u_decode (
        .insn          (d_insn),
        .alu_op        (dec_alu_op),
        .imm_sel       (),               // imm_gen selects by opcode itself
        .alu_src_a_pc  (dec_src_a_pc),
        .alu_src_b_imm (dec_src_b_imm),
        .rd_wen        (dec_rd_wen),
        .dmem_req      (dec_dmem_req),
        .dmem_we       (dec_dmem_we),
        .dmem_size     (),               // funct3[1:0] is the size
        .branch        (dec_branch),
        .jump          (dec_jump),
        .jalr          (dec_jalr),
        .halt_cause    (dec_halt_cause),
        .csr_stub      (dec_csr_stub)
    );

    rv32i_imm_gen u_imm_gen (
        .insn (d_insn),
        .imm  (d_imm)
    );

    // Register file: read issued here, data in X.  Written from W.
    logic [31:0]       x_rs1, x_rs2;
    logic              rf_wen;
    logic [HART_W-1:0] rf_wctx;
    logic [4:0]        rf_waddr;
    logic [31:0]       rf_wdata;

    gatling_regfile #(
        .NUM_HARTS (NUM_HARTS)
    ) u_regfile (
        .clk      (clk),
        .rs_ctx   (d_ctx),
        .rs1_addr (d_insn[19:15]),
        .rs2_addr (d_insn[24:20]),
        .rs1_data (x_rs1),
        .rs2_data (x_rs2),
        .rd_ctx   (rf_wctx),
        .rd_addr  (rf_waddr),
        .rd_data  (rf_wdata),
        .rd_wen   (rf_wen)
    );

    // D -> X.  The PC-relative target and the link value are formed here,
    // off the X path: PC and immediate are both known in D.
    logic              x_valid;
    logic [HART_W-1:0] x_ctx;
    logic [31:0]       x_pc, x_pc_imm, x_pc4, x_insn, x_imm;
    alu_op_e           x_alu_op;
    logic              x_src_a_pc, x_src_b_imm, x_rd_wen, x_dmem_req, x_dmem_we;
    logic              x_branch, x_jump, x_jalr, x_csr_stub, x_lui;
    logic [3:0]        x_dec_cause;

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) x_valid <= 1'b0;
        else                          x_valid <= d_live;
    )

    always_ff @(posedge clk) begin
        x_ctx       <= d_ctx;
        x_pc        <= d_pc;
        x_pc_imm    <= d_pc + d_imm;
        x_pc4       <= d_pc + PC_INCR;
        x_insn      <= d_insn;
        x_imm       <= d_imm;
        x_alu_op    <= dec_alu_op;
        x_src_a_pc  <= dec_src_a_pc;
        x_src_b_imm <= dec_src_b_imm;
        x_rd_wen    <= dec_rd_wen;
        x_dmem_req  <= dec_dmem_req;
        x_dmem_we   <= dec_dmem_we;
        x_branch    <= dec_branch;
        x_jump      <= dec_jump;
        x_jalr      <= dec_jalr;
        x_csr_stub  <= dec_csr_stub;
        x_lui       <= (d_insn[6:0] == OPCODE_LUI);
        x_dec_cause <= dec_halt_cause;
    end

    // =========================================================================
    // X: execute, resolve the next PC and any halt, issue the data access
    // =========================================================================
    logic        x_live;
    logic [2:0]  x_funct3;
    logic [4:0]  x_rd;

    assign x_live   = x_valid & hart_run[x_ctx];
    assign x_funct3 = x_insn[14:12];
    assign x_rd     = x_insn[11:7];

    logic [31:0] alu_a, alu_b, alu_y;

    assign alu_a = x_src_a_pc  ? x_pc  : x_rs1;
    assign alu_b = x_src_b_imm ? x_imm : x_rs2;

    rv32i_alu u_alu (
        .op  (x_alu_op),
        .a   (alu_a),
        .b   (alu_b),
        .y   (alu_y),
        .eq  (),
        .lt  (),
        .ltu ()
    );

    // Branch comparator: one magnitude compare for signed and unsigned, as
    // kestrel_core.
    logic cmp_eq, cmp_lt, cmp_signed, branch_cond, branch_taken;

    assign cmp_signed = ~x_funct3[1];
    assign cmp_eq     = (x_rs1 == x_rs2);
    assign cmp_lt     = ($signed({cmp_signed & x_rs1[31], x_rs1})
                         < $signed({cmp_signed & x_rs2[31], x_rs2}));

    always_comb begin
        unique case (x_funct3)
            F3_BEQ:  branch_cond = cmp_eq;
            F3_BNE:  branch_cond = ~cmp_eq;
            F3_BLT:  branch_cond = cmp_lt;
            F3_BGE:  branch_cond = ~cmp_lt;
            F3_BLTU: branch_cond = cmp_lt;
            F3_BGEU: branch_cond = ~cmp_lt;
            default: branch_cond = 1'b0;
        endcase
    end

    assign branch_taken = x_branch & branch_cond;

    logic [31:0] next_pc;

    always_comb begin
        if (x_jalr)                       next_pc = (x_rs1 + x_imm) & JALR_ALIGN_MASK;
        else if (x_jump || branch_taken)  next_pc = x_pc_imm;
        else                              next_pc = x_pc4;
    end

    // Load/store: naturally aligned, byte-lane rotation within the word;
    // the offset comes from its own two-bit add, off the carry chain.
    logic        ls_active, ls_load, ls_store, ls_misalign, ls_ok;
    logic [1:0]  ls_offset;
    logic [3:0]  ls_size_mask;
    logic [31:0] ls_data_mask;

    assign ls_active = x_live & x_dmem_req;
    assign ls_load   = ls_active & ~x_dmem_we;
    assign ls_store  = ls_active &  x_dmem_we;
    assign ls_offset = x_rs1[1:0] + x_imm[1:0];

    always_comb begin
        unique case (x_funct3[1:0])
            2'b00:   begin ls_size_mask = STRB_BYTE; ls_data_mask = 32'h0000_00FF; end
            2'b01:   begin ls_size_mask = STRB_HALF; ls_data_mask = 32'h0000_FFFF; end
            default: begin ls_size_mask = STRB_WORD; ls_data_mask = 32'hFFFF_FFFF; end
        endcase
    end

    assign ls_misalign = ls_active & ((x_funct3[1:0] == 2'b01) ? ls_offset[0]
                                    : (x_funct3[1:0] == 2'b10) ? (ls_offset != 2'b00)
                                    : 1'b0);
    assign ls_ok       = ls_active & ~ls_misalign;

    assign dmem_req   = ls_active;
    assign dmem_ctx   = x_ctx;
    assign dmem_addr  = {alu_y[31:2], 2'b00};
    assign dmem_wdata = x_rs2 << {ls_offset, 3'b000};
    assign dmem_wstrb = (ls_store & ~ls_misalign) ? (ls_size_mask << ls_offset) : 4'b0000;

    // Halt: decode's causes, a misaligned control-flow target (IALIGN=32),
    // a misaligned access.  The target's low bits come from two-bit adds.
    logic [1:0] tgt_lo_jalr;
    logic       misalign_target;
    logic [3:0] halt_cause_eff;
    logic       halt_now;

    assign tgt_lo_jalr     = (x_rs1[1:0] + x_imm[1:0]) & 2'b10;
    assign misalign_target = ((x_jump | branch_taken) & (x_pc_imm[1:0] != 2'b00))
                           | (x_jalr & (tgt_lo_jalr != 2'b00));
    assign halt_cause_eff  = x_dec_cause
                           | (misalign_target ? HALT_IALIGN : HALT_NONE)
                           | (ls_misalign ? (x_dmem_we ? HALT_SALIGN : HALT_LALIGN)
                                          : HALT_NONE);
    assign halt_now        = x_live & (|halt_cause_eff);

    // Writeback value for everything but a load, formed here: LUI takes the
    // immediate, JAL/JALR the link, the CSR stub zero, the rest the ALU.
    logic        x_rd_wb;
    logic [31:0] x_wb;

    assign x_rd_wb = x_rd_wen & (x_rd != 5'd0) & ~halt_now;
    assign x_wb    = x_csr_stub          ? 32'd0 :
                     x_lui               ? x_imm :
                     (x_jump || x_jalr)  ? x_pc4 : alu_y;

    // Per-context state updates.  hart_run low wins: the context is held at
    // RESET_ADDR with its halt and retirement order cleared.
    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            for (int c = 0; c < NUM_HARTS; c++) begin
                pc_q[c]     <= RESET_ADDR;
                halted_q[c] <= 1'b0;
                cause_q[c]  <= HALT_NONE;
            end
        end else begin
            for (int c = 0; c < NUM_HARTS; c++) begin
                if (!hart_run[c]) begin
                    pc_q[c]     <= RESET_ADDR;
                    halted_q[c] <= 1'b0;
                    cause_q[c]  <= HALT_NONE;
                end else if (x_live && (x_ctx == HART_W'(c))) begin
                    if (halt_now) begin
                        halted_q[c] <= 1'b1;
                        cause_q[c]  <= halt_cause_eff;
                    end else begin
                        pc_q[c] <= next_pc;
                    end
                end
            end
        end
    )

    assign halted     = halted_q;
    assign halt_cause = cause_q;

    // X -> W
    logic              w_valid;
    logic [HART_W-1:0] w_ctx;
    logic [31:0]       w_pc, w_pc_wdata, w_insn, w_wb;
    logic              w_trap, w_rd_wb, w_load;
    logic [2:0]        w_funct3;
    logic [1:0]        w_offset;
    logic [4:0]        w_rs1_addr, w_rs2_addr, w_rd;
    logic [31:0]       w_rs1, w_rs2;
    logic [31:0]       w_mem_addr, w_mem_wdata;
    logic [3:0]        w_mem_rmask, w_mem_wmask;

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) w_valid <= 1'b0;
        else                          w_valid <= x_live;
    )

    always_ff @(posedge clk) begin
        w_ctx       <= x_ctx;
        w_pc        <= x_pc;
        w_pc_wdata  <= next_pc;
        w_insn      <= x_insn;
        w_trap      <= halt_now;
        w_rd_wb     <= x_rd_wb;
        w_rd        <= x_rd;
        w_wb        <= x_wb;
        w_load      <= ls_load & ~ls_misalign;
        w_funct3    <= x_funct3;
        w_offset    <= ls_offset;
        w_rs1_addr  <= x_insn[19:15];
        w_rs2_addr  <= x_insn[24:20];
        w_rs1       <= x_rs1;
        w_rs2       <= x_rs2;
        w_mem_addr  <= ls_ok ? dmem_addr : 32'd0;
        w_mem_rmask <= (ls_ok & ~x_dmem_we) ? (ls_size_mask << ls_offset) : 4'd0;
        w_mem_wmask <= (ls_ok &  x_dmem_we) ? (ls_size_mask << ls_offset) : 4'd0;
        w_mem_wdata <= (ls_ok &  x_dmem_we) ? ((x_rs2 & ls_data_mask) << {ls_offset, 3'b000})
                                            : 32'd0;
    end

    // =========================================================================
    // W: load data arrives; align, extend, write back, retire
    // =========================================================================
    logic        w_live;
    logic [31:0] ld_shifted, ld_data, w_rd_wdata;

    assign w_live     = w_valid & hart_run[w_ctx];
    assign ld_shifted = dmem_rdata >> {w_offset, 3'b000};

    always_comb begin
        unique case (w_funct3)
            3'b000:  ld_data = {{24{ld_shifted[7]}},  ld_shifted[7:0]};    // LB
            3'b100:  ld_data = {24'b0,                ld_shifted[7:0]};    // LBU
            3'b001:  ld_data = {{16{ld_shifted[15]}}, ld_shifted[15:0]};   // LH
            3'b101:  ld_data = {16'b0,                ld_shifted[15:0]};   // LHU
            default: ld_data = dmem_rdata;                                 // LW
        endcase
    end

    assign w_rd_wdata = w_load ? ld_data : w_wb;

    assign rf_wen   = w_live & w_rd_wb;
    assign rf_wctx  = w_ctx;
    assign rf_waddr = w_rd;
    assign rf_wdata = w_rd_wdata;

    // Retirement order, per context; cleared while the context is held.
    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            for (int c = 0; c < NUM_HARTS; c++) order_q[c] <= '0;
        end else begin
            for (int c = 0; c < NUM_HARTS; c++) begin
                if (!hart_run[c])                            order_q[c] <= '0;
                else if (w_live && (w_ctx == HART_W'(c)))    order_q[c] <= order_q[c] + 64'd1;
            end
        end
    )

    // RVFI: rd fields are zero when nothing is written (no rd, x0, or the
    // trap beat); memory fields follow RISCV_FORMAL_ALIGNED_MEM and are zero
    // on a misaligned (halting) access, as kestrel_core.
    assign rvfi_valid     = w_live;
    assign rvfi_ctx       = w_ctx;
    assign rvfi_order     = order_q[w_ctx];
    assign rvfi_pc_rdata  = w_pc;
    assign rvfi_pc_wdata  = w_pc_wdata;
    assign rvfi_insn      = w_insn;
    assign rvfi_trap      = w_trap;
    assign rvfi_rs1_addr  = w_rs1_addr;
    assign rvfi_rs2_addr  = w_rs2_addr;
    assign rvfi_rs1_rdata = w_rs1;
    assign rvfi_rs2_rdata = w_rs2;
    assign rvfi_rd_addr   = w_rd_wb ? w_rd       : 5'd0;
    assign rvfi_rd_wdata  = w_rd_wb ? w_rd_wdata : 32'd0;
    assign rvfi_mem_addr  = w_mem_addr;
    assign rvfi_mem_rmask = w_mem_rmask;
    assign rvfi_mem_wmask = w_mem_wmask;
    assign rvfi_mem_rdata = (w_mem_rmask != 4'd0) ? dmem_rdata : 32'd0;
    assign rvfi_mem_wdata = w_mem_wdata;

endmodule : gatling_core
