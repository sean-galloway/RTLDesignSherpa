// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: merlin_core
// Purpose: 5-stage pipelined RV32I core (IF / ID / EX / MEM / WB).
//
//          This is kestrel's ISA pipelined: the same decode, immediate
//          generator, ALU, register file, halt contract, and RVFI retire
//          interface, extended with pipeline registers, operand forwarding,
//          a load-use interlock, control-hazard flushes, and a CSR stub that
//          forces alu_y to 0 so the EX/MEM forward path stays architectural.
//
//          Memory timing contract: both instruction and data memories are
//          registered-read (block-RAM) slaves.  `imem_addr` is the address
//          driven in the current cycle; a registered-read instruction memory
//          returns the word at that address one cycle later, so the IF/ID
//          register captures the RAM output.  The data memory address is
//          driven in the MEM stage and the load data is assembled in the WB
//          stage from the registered dmem_rdata port -- exactly the block-RAM
//          read latency.  The memory system must hold dmem_rdata stable while
//          dmem_req is deasserted (read-enable semantics) so a load stalled in
//          WB by mem_wait keeps its data.  `mem_wait` is a global hold: all
//          pipeline registers stall, the data request deasserts while held and
//          replays when released, and no instruction retires while the memories
//          are not ready.
//
//          Halt contract: decode raises ecall/ebreak/illegal; EX raises
//          instruction-address-misaligned on a taken branch/jump to a
//          non-4-byte-aligned target and load/store-address-misaligned on
//          a naturally misaligned access.  The halt cause is carried to WB
//          where it latches `halt_q`, freezes the PC, and flushes all younger
//          in-flight instructions.  The halting instruction itself retires as
//          the final RVFI beat (rvfi_trap = 1).
//
// Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
// Subsystem: riscv-ip/merlin-rv32i
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

`include "reset_defs.svh"

module merlin_core #(
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        mem_wait,       // 1: memories not ready -- hold all state
    output logic [31:0] imem_addr,
    output logic [31:0] imem_addr_next, // PC after this edge (registered-read fetch)
    input  logic [31:0] imem_rdata,
    output logic        dmem_req,
    output logic [31:0] dmem_addr,
    input  logic [31:0] dmem_rdata,
    output logic [3:0]  dmem_wstrb,
    output logic [31:0] dmem_wdata,
    output logic        halt,
    output logic [3:0]  halt_cause,
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [31:0] rvfi_insn,
    output logic        rvfi_trap,
    output logic [4:0]  rvfi_rs1_addr,
    output logic [4:0]  rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [4:0]  rvfi_rd_addr,
    output logic [31:0] rvfi_rd_wdata,
    output logic [31:0] rvfi_mem_addr,
    output logic [3:0]  rvfi_mem_rmask,
    output logic [3:0]  rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata
);

    import rv32i_pkg::*;
    import merlin_pkg::*;

    localparam logic [31:0] PC_INCR          = 32'd4;
    localparam logic [31:0] JALR_ALIGN_MASK  = 32'hFFFF_FFFE;
    localparam logic [6:0]  OPCODE_LOAD      = 7'b0000011;
    localparam logic [6:0]  OPCODE_STORE     = 7'b0100011;
    localparam logic [6:0]  OPCODE_LUI       = 7'b0110111;

    // funct3 encodings selecting the branch condition
    localparam logic [2:0] F3_BEQ       = 3'b000;
    localparam logic [2:0] F3_BNE       = 3'b001;
    localparam logic [2:0] F3_BLT       = 3'b100;
    localparam logic [2:0] F3_BGE       = 3'b101;
    localparam logic [2:0] F3_BLTU      = 3'b110;
    localparam logic [2:0] F3_BGEU      = 3'b111;

    // Load/store byte-lane masks (kept identical to kestrel_core)
    localparam logic [3:0] STRB_BYTE = 4'b0001;
    localparam logic [3:0] STRB_HALF = 4'b0011;
    localparam logic [3:0] STRB_WORD = 4'b1111;

    // Boundary reset synchronization.  The port rst_n is treated as an
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

    // -----------------------------------------------------------------
    // IF stage: PC register and fetch address mux
    // -----------------------------------------------------------------
    logic [31:0] pc;
    logic [31:0] pc_d;
    logic [31:0] ex_target;
    logic [31:0] ex_next_pc;
    logic        ex_taken;
    logic        ex_flush;
    logic        stall_ifid;
    logic        flush_ifid;
    logic        flush_idex;
    logic        if_id_flush_eff;
    logic        id_ex_flush_eff;
    logic        ex_mem_flush_eff;

    assign imem_addr      = pc;
    assign imem_addr_next = w_aresetn ? pc_d : RESET_ADDR;

    always_comb begin
        if (halt) begin
            pc_d = pc;                       // freeze on any halt
        end else if (mem_wait) begin
            pc_d = pc;                       // hold while memories wait
        end else if (ex_flush) begin
            pc_d = ex_target;                // EX redirect (branch/jump)
        end else if (stall_ifid) begin
            pc_d = pc;                       // load-use interlock
        end else begin
            pc_d = pc + PC_INCR;             // sequential fetch
        end
    end

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            pc <= RESET_ADDR;
        end else begin
            pc <= pc_d;
        end
    )

    // -----------------------------------------------------------------
    // IF/ID pipeline register
    // -----------------------------------------------------------------
    if_id_t if_id_d, if_id_q;

    assign if_id_d.pc    = pc;
    assign if_id_d.insn  = imem_rdata;
    assign if_id_d.valid = 1'b1;

    merlin_if_id u_if_id (
        .clk   (clk),
        .rst_n (w_aresetn),
        .stall (stall_ifid | mem_wait),
        .flush (if_id_flush_eff),
        .d_i   (if_id_d),
        .q_o   (if_id_q)
    );

    // -----------------------------------------------------------------
    // ID stage: decode, immediate generation, register-file read
    // -----------------------------------------------------------------
    logic [31:0] id_insn;
    logic [ 6:0] id_opcode;
    logic [ 2:0] id_funct3;

    alu_op_e    id_alu_op;
    logic       id_alu_src_a_pc;
    logic       id_alu_src_b_imm;
    logic       id_rd_wen;
    logic       id_dmem_req;
    logic       id_dmem_we;
    logic       id_branch;
    logic       id_jump;
    logic       id_jalr;
    logic [3:0] id_halt_cause;
    logic       id_csr_stub;

    logic [31:0] id_imm;
    logic [31:0] id_rs1_data;
    logic [31:0] id_rs2_data;
    logic [31:0] id_rs1_data_eff;
    logic [31:0] id_rs2_data_eff;

    assign id_insn   = if_id_q.insn;
    assign id_opcode = id_insn[6:0];
    assign id_funct3 = id_insn[14:12];

    rv32i_decode u_decode (
        .insn          (id_insn),
        .alu_op        (id_alu_op),
        .imm_sel       (),
        .alu_src_a_pc  (id_alu_src_a_pc),
        .alu_src_b_imm (id_alu_src_b_imm),
        .rd_wen        (id_rd_wen),
        .dmem_req      (id_dmem_req),
        .dmem_we       (id_dmem_we),
        .dmem_size     (),
        .branch        (id_branch),
        .jump          (id_jump),
        .jalr          (id_jalr),
        .halt_cause    (id_halt_cause),
        .csr_stub      (id_csr_stub)
    );

    rv32i_imm_gen u_imm_gen (
        .insn (id_insn),
        .imm  (id_imm)
    );

    // Register file: two combinational read ports, one synchronous write
    // port.  x0 is kept zero by the writeback value being forced to zero
    // and by writing zero to x0 during reset (kept by kestrel_regfile).
    logic [31:0] wb_rd_wdata;
    logic        wb_rd_wen_eff;
    logic [ 4:0] wb_rd_addr;

    // WB-to-ID bypass: an instruction entering ID while its producer is in
    // WB must see the written value, because the plain kestrel_regfile
    // reads the array before the synchronous write updates it.
    assign id_rs1_data_eff = ((wb_rd_addr == id_insn[19:15]) && (id_insn[19:15] != 5'd0) && wb_rd_wen_eff)
                             ? wb_rd_wdata : id_rs1_data;
    assign id_rs2_data_eff = ((wb_rd_addr == id_insn[24:20]) && (id_insn[24:20] != 5'd0) && wb_rd_wen_eff)
                             ? wb_rd_wdata : id_rs2_data;

    kestrel_regfile u_regfile (
        .clk      (clk),
        .rs1_addr (id_insn[19:15]),
        .rs1_data (id_rs1_data),
        .rs2_addr (id_insn[24:20]),
        .rs2_data (id_rs2_data),
        .rd_addr  (wb_rd_addr),
        .rd_data  (wb_rd_wdata),
        .rd_wen   (wb_rd_wen_eff)
    );

    // ID/EX input assembly
    id_ex_t id_ex_d;

    assign id_ex_d.pc            = if_id_q.pc;
    assign id_ex_d.rs1_data      = id_rs1_data_eff;
    assign id_ex_d.rs2_data      = id_rs2_data_eff;
    assign id_ex_d.imm           = id_imm;
    assign id_ex_d.rs1_addr      = id_insn[19:15];
    assign id_ex_d.rs2_addr      = id_insn[24:20];
    assign id_ex_d.rd_addr       = id_insn[11:7];
    assign id_ex_d.funct3        = id_funct3;
    assign id_ex_d.alu_op        = id_alu_op;
    assign id_ex_d.alu_src_a_pc  = id_alu_src_a_pc;
    assign id_ex_d.alu_src_b_imm = id_alu_src_b_imm;
    assign id_ex_d.rd_wen        = id_rd_wen;
    assign id_ex_d.wb_sel        = (id_opcode == OPCODE_LOAD) ? WB_LOAD :
                                   (id_opcode == OPCODE_LUI)  ? WB_LUI  :
                                   (id_jump || id_jalr)       ? WB_LINK :
                                                                WB_ALU;
    assign id_ex_d.dmem_req      = id_dmem_req;
    assign id_ex_d.dmem_we       = id_dmem_we;
    assign id_ex_d.branch        = id_branch;
    assign id_ex_d.jump          = id_jump;
    assign id_ex_d.jalr          = id_jalr;
    assign id_ex_d.halt_cause    = id_halt_cause;
    assign id_ex_d.csr_stub      = id_csr_stub;
    assign id_ex_d.valid         = if_id_q.valid & ~halt;
    assign id_ex_d.insn          = id_insn;

    id_ex_t id_ex_q;

    merlin_id_ex u_id_ex (
        .clk   (clk),
        .rst_n (w_aresetn),
        .stall (mem_wait),
        .flush (id_ex_flush_eff),
        .d_i   (id_ex_d),
        .q_o   (id_ex_q)
    );

    // -----------------------------------------------------------------
    // Hazard / forwarding unit and load-use interlock
    // -----------------------------------------------------------------
    logic idex_is_load;

    assign idex_is_load = id_ex_q.dmem_req & ~id_ex_q.dmem_we;

    // The hazard unit is used for load-use stall detection and for the
    // branch flush broadcast.  The actual operand forwarding muxes are
    // recomputed in EX (below) against the instruction currently in EX,
    // using the same EX/MEM-priority rule the unit encodes.
    merlin_hazard u_hazard (
        .id_rs1_addr  (id_ex_d.rs1_addr),
        .id_rs2_addr  (id_ex_d.rs2_addr),
        .idex_rd_addr (id_ex_q.rd_addr),
        .idex_rd_wen  (id_ex_q.rd_wen & id_ex_q.valid),
        .idex_is_load (idex_is_load),
        .exmem_rd_addr(ex_mem_q.rd_addr),
        .exmem_rd_wen (ex_mem_q.rd_wen & ex_mem_q.valid),
        .memwb_rd_addr(mem_wb_q.rd_addr),
        .memwb_rd_wen (mem_wb_q.rd_wen & mem_wb_q.valid),
        .ex_flush     (ex_flush),
        .fwd_a        (),
        .fwd_b        (),
        .stall_ifid   (stall_ifid),
        .flush_ifid   (flush_ifid),
        .flush_idex   (flush_idex)
    );

    // Effective flushes: kill young instructions on a taken control-flow
    // change or when a halting instruction reaches WB.  Flushes are
    // suppressed while the memories are waiting so the same event replays
    // cleanly after the wait ends.

    // Halt detection in WB is defined below; declare here for flush wiring.
    logic halt_now;

    assign if_id_flush_eff  = ((flush_ifid | halt_now) & ~mem_wait);
    // stall_ifid must also flush ID/EX so the consumer is not latched twice
    // and retried after the load-use bubble; the flush injects valid=0.
    assign id_ex_flush_eff  = ((flush_idex | stall_ifid | halt_now) & ~mem_wait);
    assign ex_mem_flush_eff = halt_now & ~mem_wait;

    // -----------------------------------------------------------------
    // EX stage: ALU, branch comparator, load/store align check
    // -----------------------------------------------------------------
    logic [1:0] ex_fwd_a, ex_fwd_b;
    logic [31:0] ex_rs1_fwd;
    logic [31:0] ex_rs2_fwd;

    // Forwarding priority: EX/MEM is the newer producer.
    always_comb begin
        if ((ex_mem_q.rd_addr != 5'd0) && ex_mem_q.rd_wen && ex_mem_q.valid &&
            (ex_mem_q.rd_addr == id_ex_q.rs1_addr))
            ex_fwd_a = FWD_EXMEM;
        else if ((mem_wb_q.rd_addr != 5'd0) && mem_wb_q.rd_wen && mem_wb_q.valid &&
                 (mem_wb_q.rd_addr == id_ex_q.rs1_addr))
            ex_fwd_a = FWD_MEMWB;
        else
            ex_fwd_a = FWD_IDEX;
    end

    always_comb begin
        if ((ex_mem_q.rd_addr != 5'd0) && ex_mem_q.rd_wen && ex_mem_q.valid &&
            (ex_mem_q.rd_addr == id_ex_q.rs2_addr))
            ex_fwd_b = FWD_EXMEM;
        else if ((mem_wb_q.rd_addr != 5'd0) && mem_wb_q.rd_wen && mem_wb_q.valid &&
                 (mem_wb_q.rd_addr == id_ex_q.rs2_addr))
            ex_fwd_b = FWD_MEMWB;
        else
            ex_fwd_b = FWD_IDEX;
    end

    assign ex_rs1_fwd = (ex_fwd_a == FWD_EXMEM) ? ex_mem_q.alu_y :
                        (ex_fwd_a == FWD_MEMWB) ? wb_rd_wdata     :
                                                  id_ex_q.rs1_data;
    assign ex_rs2_fwd = (ex_fwd_b == FWD_EXMEM) ? ex_mem_q.alu_y :
                        (ex_fwd_b == FWD_MEMWB) ? wb_rd_wdata     :
                                                  id_ex_q.rs2_data;

    // ALU operand muxes
    logic [31:0] alu_a;
    logic [31:0] alu_b;
    logic [31:0] alu_y;
    logic [31:0] alu_y_raw;

    // LUI must ignore its rs1 field; forcing alu_a to zero is required even
    // though forwarding would otherwise deliver a stale rs1 value.  (FWD_EXMEM
    // forwards alu_y, so a LUI with a non-zero rs1 encoding would otherwise
    // pick up the previous EX/MEM alu_y and corrupt the immediate.)
    assign alu_a = id_ex_q.alu_src_a_pc  ? id_ex_q.pc       :
                   (id_ex_q.insn[6:0] == OPCODE_LUI) ? 32'd0 :
                   ex_rs1_fwd;
    assign alu_b = id_ex_q.alu_src_b_imm ? id_ex_q.imm      : ex_rs2_fwd;

    rv32i_alu u_alu (
        .op  (id_ex_q.alu_op),
        .a   (alu_a),
        .b   (alu_b),
        .y   (alu_y_raw),
        .eq  (),
        .lt  (),
        .ltu ()
    );

    // CSR-stub instructions write 0 to rd.  Force their ALU result to 0 so
    // the EX/MEM forward path broadcasts the architectural writeback value
    // instead of the garbage alu_y_raw that the ALU produced from the CSR
    // encoding, preventing dependent instructions from seeing stale data.
    assign alu_y = id_ex_q.csr_stub ? 32'd0 : alu_y_raw;

    // Dedicated branch comparator on the forwarded operands.
    logic        cmp_signed;
    logic        cmp_eq;
    logic        cmp_lt;
    logic        branch_cond;
    logic        branch_taken;

    assign cmp_signed = ~id_ex_q.funct3[1];
    assign cmp_eq     = (ex_rs1_fwd == ex_rs2_fwd);
    assign cmp_lt     = ($signed({cmp_signed & ex_rs1_fwd[31], ex_rs1_fwd})
                         < $signed({cmp_signed & ex_rs2_fwd[31], ex_rs2_fwd}));

    always_comb begin
        unique case (id_ex_q.funct3)
            F3_BEQ:  branch_cond = cmp_eq;
            F3_BNE:  branch_cond = ~cmp_eq;
            F3_BLT:  branch_cond = cmp_lt;
            F3_BGE:  branch_cond = ~cmp_lt;
            F3_BLTU: branch_cond = cmp_lt;
            F3_BGEU: branch_cond = ~cmp_lt;
            default: branch_cond = 1'b0;
        endcase
    end

    assign branch_taken = id_ex_q.branch & branch_cond;

    // Resolved next-PC target and flush signal.
    assign ex_target = id_ex_q.jalr ? ((ex_rs1_fwd + id_ex_q.imm) & JALR_ALIGN_MASK) : alu_y;
    assign ex_taken  = id_ex_q.valid & (id_ex_q.jump | id_ex_q.jalr | branch_taken);
    assign ex_flush  = ex_taken;
    assign ex_next_pc = ex_taken ? ex_target : (id_ex_q.pc + PC_INCR);

    // Instruction-address misalignment (IALIGN=32) on taken control flow.
    logic [1:0] tgt_lo_pc;
    logic [1:0] tgt_lo_jalr;
    logic       misalign_link;
    logic       misalign_branch;
    logic       misalign_target;

    assign tgt_lo_pc     = id_ex_q.pc[1:0] + id_ex_q.imm[1:0];
    assign tgt_lo_jalr   = (ex_rs1_fwd[1:0] + id_ex_q.imm[1:0]) & 2'b10;
    assign misalign_link = (id_ex_q.jump & (tgt_lo_pc != 2'b00)) |
                           (id_ex_q.jalr & (tgt_lo_jalr != 2'b00));
    assign misalign_branch = branch_taken & (tgt_lo_pc != 2'b00);
    assign misalign_target = misalign_link | misalign_branch;

    // Load/store address misalignment, computed off the low bits of the
    // offset adder so it does not wait for the full 32-bit ALU result.
    logic [1:0] ls_offset;
    logic       ls_active;
    logic       ls_misalign;

    assign ls_active  = id_ex_q.dmem_req & id_ex_q.valid;
    assign ls_offset  = ex_rs1_fwd[1:0] + id_ex_q.imm[1:0];
    assign ls_misalign = ls_active &
                         ((id_ex_q.funct3[1:0] == 2'b01) ? ls_offset[0] :
                          (id_ex_q.funct3[1:0] == 2'b10) ? (ls_offset != 2'b00) :
                          1'b0);

    // EX/MEM input assembly
    ex_mem_t ex_mem_d;

    assign ex_mem_d.pc          = id_ex_q.pc;
    assign ex_mem_d.next_pc     = ex_next_pc;
    assign ex_mem_d.alu_y       = alu_y;
    assign ex_mem_d.store_data  = ex_rs2_fwd;
    assign ex_mem_d.rd_addr     = id_ex_q.rd_addr;
    assign ex_mem_d.rd_wen      = id_ex_q.rd_wen;
    assign ex_mem_d.wb_sel      = id_ex_q.wb_sel;
    assign ex_mem_d.funct3      = id_ex_q.funct3;
    assign ex_mem_d.dmem_req    = id_ex_q.dmem_req;
    assign ex_mem_d.dmem_we     = id_ex_q.dmem_we;
    assign ex_mem_d.ls_misalign = ls_misalign;
    assign ex_mem_d.halt_cause  = id_ex_q.halt_cause
                                | (misalign_target ? HALT_IALIGN : HALT_NONE)
                                | (ls_misalign ? (id_ex_q.dmem_we ? HALT_SALIGN : HALT_LALIGN)
                                               : HALT_NONE);
    assign ex_mem_d.csr_stub    = id_ex_q.csr_stub;
    assign ex_mem_d.valid       = id_ex_q.valid;
    assign ex_mem_d.insn        = id_ex_q.insn;
    assign ex_mem_d.imm         = id_ex_q.imm;
    assign ex_mem_d.rs1_rdata   = ex_rs1_fwd;
    assign ex_mem_d.rs2_rdata   = ex_rs2_fwd;

    ex_mem_t ex_mem_q;

    merlin_ex_mem u_ex_mem (
        .clk   (clk),
        .rst_n (w_aresetn),
        .stall (mem_wait),
        .flush (ex_mem_flush_eff),
        .d_i   (ex_mem_d),
        .q_o   (ex_mem_q)
    );

    // -----------------------------------------------------------------
    // MEM stage: data memory request and store rotation
    // -----------------------------------------------------------------
    logic [1:0]  mem_ls_offset;
    logic [3:0]  mem_ls_size_mask;
    logic        mem_ls_ok;

    assign mem_ls_offset = ex_mem_q.alu_y[1:0];

    always_comb begin
        unique case (ex_mem_q.funct3[1:0])
            2'b00:   mem_ls_size_mask = STRB_BYTE;
            2'b01:   mem_ls_size_mask = STRB_HALF;
            default: mem_ls_size_mask = STRB_WORD;
        endcase
    end

    assign mem_ls_ok        = ex_mem_q.dmem_req & ex_mem_q.valid & ~ex_mem_q.ls_misalign & ~halt;
    assign dmem_req         = mem_ls_ok & ~mem_wait;   // deassert during wait, replay after
    assign dmem_addr        = {ex_mem_q.alu_y[31:2], 2'b00};
    assign dmem_wdata       = ex_mem_q.store_data << {mem_ls_offset, 3'b000};
    assign dmem_wstrb       = (ex_mem_q.dmem_we & mem_ls_ok) ? (mem_ls_size_mask << mem_ls_offset)
                                                             : 4'b0000;

    // MEM/WB input assembly.  Load data is NOT assembled here: dmem_rdata in
    // the MEM cycle is the previous access's data.  The registered memory
    // returns this load's word during the WB cycle, where it is assembled.
    mem_wb_t mem_wb_d;

    assign mem_wb_d.pc        = ex_mem_q.pc;
    assign mem_wb_d.next_pc   = ex_mem_q.next_pc;
    assign mem_wb_d.alu_y     = ex_mem_q.alu_y;
    assign mem_wb_d.rd_addr   = ex_mem_q.rd_addr;
    assign mem_wb_d.rd_wen    = ex_mem_q.rd_wen;
    assign mem_wb_d.wb_sel    = ex_mem_q.wb_sel;
    assign mem_wb_d.funct3    = ex_mem_q.funct3;
    assign mem_wb_d.csr_stub  = ex_mem_q.csr_stub;
    assign mem_wb_d.halt_cause= ex_mem_q.halt_cause;
    assign mem_wb_d.valid     = ex_mem_q.valid;
    assign mem_wb_d.insn      = ex_mem_q.insn;
    assign mem_wb_d.imm       = ex_mem_q.imm;
    assign mem_wb_d.rs1_rdata = ex_mem_q.rs1_rdata;
    assign mem_wb_d.rs2_rdata = ex_mem_q.rs2_rdata;

    mem_wb_t mem_wb_q;

    merlin_mem_wb u_mem_wb (
        .clk   (clk),
        .rst_n (w_aresetn),
        .stall (mem_wait),
        .flush (1'b0),
        .d_i   (mem_wb_d),
        .q_o   (mem_wb_q)
    );

    // -----------------------------------------------------------------
    // WB stage: load assembly, writeback mux, halt holding register, RVFI retire
    // -----------------------------------------------------------------
    logic        halt_q;
    logic [3:0]  halt_cause_q;
    logic [63:0] retire_count;

    // Assemble the load data in WB from the registered memory read port.  At
    // this point dmem_rdata holds the word for the address presented when this
    // instruction was in MEM.
    logic [1:0]  wb_ls_offset;
    logic [31:0] wb_ls_rdata_shifted;
    logic [31:0] wb_load_data;

    assign wb_ls_offset       = mem_wb_q.alu_y[1:0];
    assign wb_ls_rdata_shifted = dmem_rdata >> {wb_ls_offset, 3'b000};

    always_comb begin
        unique case (mem_wb_q.funct3)
            3'b000:  wb_load_data = {{24{wb_ls_rdata_shifted[7]}},  wb_ls_rdata_shifted[7:0]};   // LB
            3'b100:  wb_load_data = {24'b0,                      wb_ls_rdata_shifted[7:0]};   // LBU
            3'b001:  wb_load_data = {{16{wb_ls_rdata_shifted[15]}}, wb_ls_rdata_shifted[15:0]};  // LH
            3'b101:  wb_load_data = {16'b0,                      wb_ls_rdata_shifted[15:0]};  // LHU
            default: wb_load_data = dmem_rdata;                                            // LW
        endcase
    end

    assign wb_rd_wdata = (mem_wb_q.csr_stub || (mem_wb_q.rd_addr == 5'd0)) ? 32'd0 :
                         (mem_wb_q.wb_sel == WB_LUI)  ? mem_wb_q.imm       :
                         (mem_wb_q.wb_sel == WB_LOAD) ? wb_load_data       :
                         (mem_wb_q.wb_sel == WB_LINK) ? (mem_wb_q.pc + PC_INCR) :
                                                        mem_wb_q.alu_y;

    // Halt becomes architecturally visible in WB.  It is masked by mem_wait
    // so that a wait cycle does not prematurely latch halt; the same halting
    // instruction remains in WB and retires one cycle after the wait ends.
    assign halt_now     = mem_wb_q.valid & (mem_wb_q.halt_cause != HALT_NONE) & ~mem_wait;

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            halt_q       <= 1'b0;
            halt_cause_q <= HALT_NONE;
        end else begin
            if (halt_now) begin
                halt_q       <= 1'b1;
                halt_cause_q <= mem_wb_q.halt_cause;
            end
        end
    )

    assign halt       = halt_q | halt_now;
    assign halt_cause = halt_q ? halt_cause_q : (halt_now ? mem_wb_q.halt_cause : HALT_NONE);

    // Register-file write port.  During reset the destination is forced to
    // x0 and the write is enabled every cycle so x0 is initialized to zero.
    assign wb_rd_addr     = w_aresetn ? mem_wb_q.rd_addr : 5'd0;
    assign wb_rd_wen_eff  = (~w_aresetn) |
                            (w_aresetn & mem_wb_q.rd_wen & mem_wb_q.valid &
                             ~mem_wait & ~halt);

    // Retirement order counter.
    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            retire_count <= '0;
        end else begin
            if (rvfi_valid) begin
                retire_count <= retire_count + 64'd1;
            end
        end
    )

    // RVFI aggregation at WB retire.
    logic       rd_wb;
    logic [1:0] rvfi_ls_offset;
    logic [3:0] rvfi_ls_size_mask;
    logic [31:0] rvfi_ls_data_mask;
    logic        rvfi_mem_active;

    assign rd_wb          = mem_wb_q.rd_wen & (mem_wb_q.rd_addr != 5'd0) & ~halt;
    assign rvfi_valid     = w_aresetn & mem_wb_q.valid & ~halt_q & ~mem_wait;
    assign rvfi_order     = retire_count;
    assign rvfi_pc_rdata  = mem_wb_q.pc;
    assign rvfi_pc_wdata  = mem_wb_q.next_pc;
    assign rvfi_insn      = mem_wb_q.insn;
    assign rvfi_trap      = halt_now;
    assign rvfi_rs1_addr  = mem_wb_q.insn[19:15];
    assign rvfi_rs2_addr  = mem_wb_q.insn[24:20];
    assign rvfi_rs1_rdata = mem_wb_q.rs1_rdata;
    assign rvfi_rs2_rdata = mem_wb_q.rs2_rdata;
    assign rvfi_rd_addr   = rd_wb ? mem_wb_q.rd_addr : 5'd0;
    assign rvfi_rd_wdata  = rd_wb ? wb_rd_wdata      : 32'd0;

    // RVFI memory fields follow RISCV_FORMAL_ALIGNED_MEM.  They are reported
    // only for aligned load/store instructions; misaligned accesses halt and
    // perform no memory operation.
    assign rvfi_ls_offset = mem_wb_q.alu_y[1:0];

    always_comb begin
        unique case (mem_wb_q.insn[13:12])
            2'b00:   rvfi_ls_size_mask = STRB_BYTE;
            2'b01:   rvfi_ls_size_mask = STRB_HALF;
            default: rvfi_ls_size_mask = STRB_WORD;
        endcase
    end

    assign rvfi_ls_data_mask = (mem_wb_q.insn[13:12] == 2'b00) ? 32'h0000_00FF :
                               (mem_wb_q.insn[13:12] == 2'b01) ? 32'h0000_FFFF :
                                                                  32'hFFFF_FFFF;

    assign rvfi_mem_active = mem_wb_q.valid & (mem_wb_q.halt_cause == HALT_NONE) &
                             ((mem_wb_q.insn[6:0] == OPCODE_LOAD) |
                              (mem_wb_q.insn[6:0] == OPCODE_STORE));

    assign rvfi_mem_addr  = rvfi_mem_active ? {mem_wb_q.alu_y[31:2], 2'b00} : 32'd0;
    assign rvfi_mem_rmask = (rvfi_mem_active & (mem_wb_q.insn[6:0] == OPCODE_LOAD))
                            ? (rvfi_ls_size_mask << rvfi_ls_offset) : 4'd0;
    assign rvfi_mem_wmask = (rvfi_mem_active & (mem_wb_q.insn[6:0] == OPCODE_STORE))
                            ? (rvfi_ls_size_mask << rvfi_ls_offset) : 4'd0;
    assign rvfi_mem_rdata = (rvfi_mem_active & (mem_wb_q.insn[6:0] == OPCODE_LOAD))
                            ? dmem_rdata : 32'd0;
    assign rvfi_mem_wdata = (rvfi_mem_active & (mem_wb_q.insn[6:0] == OPCODE_STORE))
                            ? ((mem_wb_q.rs2_rdata & rvfi_ls_data_mask) << {rvfi_ls_offset, 3'b000})
                            : 32'd0;

endmodule : merlin_core
