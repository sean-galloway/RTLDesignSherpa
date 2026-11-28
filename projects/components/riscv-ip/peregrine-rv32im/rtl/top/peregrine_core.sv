// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_core
// Purpose: peregrine, the falcon-suite rung-3 core: merlin's 5-stage
//          pipeline (IF / ID / EX / MEM / WB) with machine-mode traps.
//
//          Stage 1 of riscv-ip/peregrine-rv32im TASK-001: the CSR file and
//          precise traps on the cacheless build (PRD §4.3, P6, P12).
//          Stage 2: the M unit (PRD §4.4, P3, P8).  Stage 3: the branch
//          predictor (PRD §4.2, P2, P5).  Stage 4: CACHE_EN, fence.i and
//          the D-side request contract for peregrine_top (PRD §4.5).
//
//          What is merlin's, unchanged: the pipeline registers, the
//          forwarding unit (EX/MEM over MEM/WB, select computed in ID), the
//          load-use bubble, the load-to-branch interlock, branch resolution
//          in EX with a 2-bubble flush, the WB-to-ID regfile bypass, and the
//          registered-read memory contract with the `mem_wait` global hold.
//          With BP_EN=0 the fetch path is merlin's exactly (predict not
//          taken, every taken branch flushes).
//
//          What is new:
//          - Traps replace the halt contract.  An exception is detected in
//            ID (ecall/ebreak/illegal) or EX (misaligned target or access,
//            a CSR that does not exist or is read-only) and rides with its
//            instruction to MEM.  MEM is the commit point: memory is
//            written there and the regfile only in WB, so an instruction
//            trapping in MEM has every older instruction committed (the one
//            in WB retires) and nothing younger has touched state.  The
//            trap writes mepc/mcause/mtval, clears mstatus.MIE, redirects
//            to mtvec and flushes IF/ID, ID/EX and the instruction leaving
//            EX.  The trapping instruction retires on RVFI with rvfi_trap.
//          - Interrupts are sampled at the same point: a pending, enabled
//            interrupt attaches to the valid instruction entering MEM,
//            which traps instead of executing (precise at the oldest
//            uncommitted instruction).  The exception is an M instruction:
//            it reaches MEM only with its result done, and it is not
//            interruptible there, so the interrupt is taken on the next
//            instruction.  Without that, an interrupt re-raised faster
//            than the M unit's 33 cycles discards the M instruction on
//            every pass and it never retires (a measured livelock,
//            TASK-001 stage 2).
//          - mret redirects to mepc from MEM, the same way.
//          - CSR instructions read the CSR file in EX (the old value is
//            rd's result and forwards like any ALU result) and write it in
//            MEM.  A CSR instruction in ID waits while an older one is in
//            ID/EX or EX/MEM, so its EX read sees every older write.
//          - The M extension runs on one iterative unit, peregrine_mdu,
//            started from EX.  The M instruction holds in EX until its
//            result is ready (hold-in-EX, owner 2026-11-23): the PC, IF/ID
//            and ID/EX hold and EX/MEM takes bubbles, so the result writes
//            back in program order and RVFI stays exact.  The unit starts
//            on the first EX cycle without mem_wait, when the forwarded
//            operands are valid, and latches them: the forwarding selects
//            go stale while the producers drain.  A MEM-stage trap or mret
//            kills the M instruction in EX and cancels the unit.
//          - Branch prediction (peregrine_bpred): the fetch PC looks up a
//            BTB and a 2-bit BHT, and IF fetches the predicted next PC.
//            The guess rides with the instruction to EX, which resolves
//            it.  A mispredict (wrong direction, or a wrong target on a
//            taken prediction) redirects to the resolved next PC and
//            flushes IF/ID and ID/EX: 2 bubbles.  A correctly predicted
//            taken branch costs 0.  The predictor is written once per
//            resolved instruction, when it leaves EX: not under mem_wait,
//            not while an M instruction holds, and not when a MEM redirect
//            kills it.  Every instruction that leaves EX retires (as an
//            ordinary or a trap beat), so the state is a function of the
//            retire stream.
//            An instruction held in EX (the M unit) mispredicts only when
//            it leaves: an earlier flush would kill it in ID/EX.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-23
//
// Parameters:
//   - RESET_ADDR: first fetch address.
//   - MUL_DSP: 0 (default) iterative multiply, 33 stall cycles; 1 one
//     registered DSP multiply, 2 stall cycles (PRD P8).  Divide is
//     iterative either way.
//   - BP_EN: 1 (default) BTB + 2-bit BHT prediction; 0 predict not taken
//     (merlin's fetch), the PRD P5 A/B build.
//   - BTB_ENTRIES, BHT_ENTRIES: predictor sizes (PRD P5: 32 and 256).
//   - CACHE_EN: 0 (default) the cacheless build (PRD P12): fence.i commits
//     in MEM and redirects to pc + 4, flushing the younger instructions
//     fetched before it (owner 2026-11-25, so the cacheless build passes
//     Zifencei too); there is no cache to clean and fencei_req stays 0.
//     Otherwise the core is the stage-3 core.  1 the cached build
//     inside peregrine_top (TASK-001 stage 4):
//     - fence.i in MEM raises fencei_req and waits (the wrapper holds
//       mem_wait) while the wrapper cleans the D$ and invalidates the I$;
//       then it commits like an ordinary instruction and redirects to
//       pc + 4, flushing everything younger (it was fetched before the
//       invalidate);
//     - a load, store or fence.i that has presented its request to the
//       memory side while mem_wait held is not interruptible on the cycle
//       mem_wait drops (the interrupt goes to the next instruction).  The
//       D-side request (dmem_req_pre) therefore never drops before its
//       handshake, which the GAXI / AXI contract behind the wrapper
//       requires;
//     - bus errors (TASK-005).  An instruction fetch whose I$ fill was
//       answered SLVERR / DECERR arrives with imem_fault: IF/ID carries the
//       fault (and a zero instruction word, so decode raises nothing of its
//       own), ID turns it into EXC_IFAULT, and it traps at MEM like any
//       other exception (mcause 1, mtval = its PC).  A load or store whose
//       D-side response was an error is known only when the response
//       arrives, which the registered-read contract puts in WB: the
//       wrapper holds the core on the error response, then presents
//       dmem_fault with the instruction in WB.  That cycle the WB
//       instruction retires as a trap beat (mcause 5 / 7, mtval = its
//       address, no rd write), and the instruction in MEM -- held there
//       through the error response, so it has not committed -- is killed
//       with everything younger.  Precise: everything older retired,
//       nothing younger wrote memory, the regfile or a CSR.  The one
//       exception to "every instruction that leaves EX retires": the
//       instruction killed in MEM had already updated the predictor;
//     - mip.16 / mbuserr (TASK-005): amber's sticky write-back error is
//       platform interrupt 16 (irq_buserr), taken at MEM on the ordinary
//       interrupt path; the custom CSR mbuserr (0x7C0) reads buserr_info
//       and a write to it pulses buserr_clear.
//     The cacheless build has neither: imem_fault, dmem_fault and
//     irq_buserr are ignored and mbuserr does not exist.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_core #(
    parameter logic [31:0] RESET_ADDR  = 32'h0000_0000,
    parameter bit          MUL_DSP     = 1'b0,
    parameter bit          BP_EN       = 1'b1,
    parameter int          BTB_ENTRIES = 32,
    parameter int          BHT_ENTRIES = 256,
    parameter bit          CACHE_EN    = 1'b0
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        mem_wait,       // 1: memories not ready -- hold all state
    output logic [31:0] imem_addr,
    output logic [31:0] imem_addr_next, // PC after this edge (registered-read fetch)
    output logic [31:0] imem_addr_next_nw, // the same, as if mem_wait were low
    input  logic [31:0] imem_rdata,
    output logic        dmem_req,
    output logic [31:0] dmem_addr,
    input  logic [31:0] dmem_rdata,
    output logic [3:0]  dmem_wstrb,
    output logic [31:0] dmem_wdata,
    // CACHE_EN=1 only (peregrine_top); 0 when CACHE_EN=0.
    output logic        dmem_req_pre,   // the MEM access, before the mem_wait gate
    output logic        fencei_req,     // fence.i in MEM: clean D$, invalidate I$
    // Bus errors (TASK-005), CACHE_EN=1 only; tie 0 when CACHE_EN=0.
    input  logic        imem_fault,     // the fetch at imem_addr faulted (with imem_rdata)
    input  logic        dmem_fault,     // WB's load/store response was an error (with dmem_rdata)
    input  logic        irq_buserr,     // amber's sticky write-back error (mip.16)
    input  logic [31:0] buserr_info,    // what mbuserr (0x7C0) reads
    output logic        buserr_clear,   // a write to mbuserr committed
    input  logic        irq_software,
    input  logic        irq_timer,
    input  logic        irq_external,
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
    output logic [31:0] rvfi_mem_wdata,
    // Trap observation (TB and the trap directed suite): mcause of the
    // trap committed with this retire beat, valid with rvfi_trap.
    output logic [31:0] rvfi_trap_cause,
    // Predictor observation, valid with rvfi_valid: the guess this
    // instruction was fetched with, and whether EX found it wrong.
    output logic        rvfi_bp_pred_taken,
    output logic [31:0] rvfi_bp_pred_target,
    output logic        rvfi_bp_mispredict
);

    import rv32i_pkg::*;
    import peregrine_pkg::*;

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

    // CSR funct3 low bits (bit 2 selects the zimm source)
    localparam logic [1:0] CSR_RW = 2'b01;
    localparam logic [1:0] CSR_RS = 2'b10;
    localparam logic [1:0] CSR_RC = 2'b11;

    // Load/store byte-lane masks (kept identical to kestrel_core)
    localparam logic [3:0] STRB_BYTE = 4'b0001;
    localparam logic [3:0] STRB_HALF = 4'b0011;
    localparam logic [3:0] STRB_WORD = 4'b1111;

    // Boundary reset synchronization.
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
    logic [31:0] pc_d_nw;     // pc_d as if mem_wait were low
    logic [31:0] ex_target;
    logic [31:0] ex_next_pc;
    logic        ex_taken;
    logic        ex_flush;
    logic        if_pred_taken;
    logic [31:0] if_pred_target;
    logic        ex_mispredict;
    logic        stall_ifid;
    logic        stall_lu;
    logic        flush_ifid;
    logic        flush_idex;
    logic        if_id_flush_eff;
    logic        id_ex_flush_eff;
    logic        ex_mem_flush_eff;

    // MEM-stage redirect (trap entry or mret), declared here for the PC mux.
    logic        mem_redirect;
    logic        mem_redirect_nw;   // mem_redirect before its ~mem_wait gate
    logic [31:0] mem_redirect_pc;

    // An M instruction holding in EX until its result is ready.
    logic        ex_m_stall;

    assign imem_addr      = pc;
    assign imem_addr_next    = w_aresetn ? pc_d    : RESET_ADDR;
    assign imem_addr_next_nw = w_aresetn ? pc_d_nw : RESET_ADDR;

    // The next PC without the hold, so a fetch memory can take mem_wait as
    // its read enable instead of through the address (TASK-001 stage 7):
    // mem_wait is the late signal, and the hold arm is the only use of it.
    always_comb begin
        if (mem_redirect_nw) begin
            pc_d_nw = mem_redirect_pc;       // trap entry / mret (oldest wins)
        end else if (ex_flush) begin
            pc_d_nw = ex_next_pc;            // EX redirect: a mispredict
        end else if (stall_ifid | ex_m_stall) begin
            pc_d_nw = pc;                    // interlock / M unit busy
        end else if (if_pred_taken) begin
            pc_d_nw = if_pred_target;        // predicted taken
        end else begin
            pc_d_nw = pc + PC_INCR;          // sequential fetch
        end
    end
    assign pc_d = mem_wait ? pc : pc_d_nw;   // hold while memories wait

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

    // A faulted fetch (TASK-005) carries a zero word: decode sees an
    // illegal instruction with no side effects, and ID replaces the cause.
    logic w_ifault;
    assign w_ifault            = CACHE_EN & imem_fault;
    assign if_id_d.pc          = pc;
    assign if_id_d.insn        = w_ifault ? 32'd0 : imem_rdata;
    assign if_id_d.pred_taken  = if_pred_taken;
    assign if_id_d.pred_target = if_pred_target;
    assign if_id_d.ifault      = w_ifault;
    assign if_id_d.valid       = 1'b1;

    peregrine_if_id u_if_id (
        .clk   (clk),
        .rst_n (w_aresetn),
        .stall (stall_ifid | mem_wait | ex_m_stall),
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
    logic [3:0] id_exc_cause;
    logic       id_csr_op;
    logic       id_mret;
    logic       id_m_op;

    logic [31:0] id_imm;
    logic [31:0] id_rs1_data;
    logic [31:0] id_rs2_data;
    logic [31:0] id_rs1_data_eff;
    logic [31:0] id_rs2_data_eff;

    assign id_insn   = if_id_q.insn;
    assign id_opcode = id_insn[6:0];
    assign id_funct3 = id_insn[14:12];

    rv32i_decode #(
        .M_EXT (1'b1),
        .ZICSR (1'b1)
    ) u_decode (
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
        .halt_cause    (id_exc_cause),
        .csr_stub      (),
        .m_op          (id_m_op),
        .csr_op        (id_csr_op),
        .mret          (id_mret)
    );

    rv32i_imm_gen u_imm_gen (
        .insn (id_insn),
        .imm  (id_imm)
    );

    logic [31:0] wb_rd_wdata;
    logic        wb_rd_wen_eff;
    logic [ 4:0] wb_rd_addr;

    // WB-to-ID bypass (merlin's).
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
    assign id_ex_d.exc_cause     = if_id_q.ifault ? EXC_IFAULT : id_exc_cause;
    assign id_ex_d.csr_op        = id_csr_op;
    assign id_ex_d.mret          = id_mret;
    assign id_ex_d.m_op          = id_m_op;
    assign id_ex_d.pred_taken    = if_id_q.pred_taken;
    assign id_ex_d.pred_target   = if_id_q.pred_target;
    // A branch or JAL target does not depend on a register: compute it and
    // its compare against the guess here, so EX's mispredict test does not
    // sit behind the forwarding mux and the ALU (TASK-001 stage 7).
    logic [31:0] id_br_target;
    assign id_br_target          = if_id_q.pc + id_imm;
    assign id_ex_d.br_target     = id_br_target;
    assign id_ex_d.br_tgt_hit    = (if_id_q.pred_target == id_br_target);
    assign id_ex_d.jalr_x        = if_id_q.pred_target - id_imm;
    assign id_ex_d.valid         = if_id_q.valid;
    assign id_ex_d.insn          = id_insn;

    id_ex_t id_ex_q;

    peregrine_id_ex u_id_ex (
        .clk   (clk),
        .rst_n (w_aresetn),
        .stall (mem_wait | ex_m_stall),
        .flush (id_ex_flush_eff),
        .d_i   (id_ex_d),
        .q_o   (id_ex_q)
    );

    // -----------------------------------------------------------------
    // Hazard / forwarding unit and interlocks
    // -----------------------------------------------------------------
    ex_mem_t ex_mem_q;
    mem_wb_t mem_wb_q;

    logic idex_is_load;
    logic [1:0] ex_fwd_a, ex_fwd_b;

    assign idex_is_load = id_ex_q.dmem_req & ~id_ex_q.dmem_we & id_ex_q.valid;

    logic [1:0] id_fwd_a, id_fwd_b;

    peregrine_hazard u_hazard (
        .id_rs1_addr  (id_ex_d.rs1_addr),
        .id_rs2_addr  (id_ex_d.rs2_addr),
        .fwd_rs1_addr (id_ex_d.rs1_addr),
        .fwd_rs2_addr (id_ex_d.rs2_addr),
        .idex_rd_addr (id_ex_q.rd_addr),
        .idex_is_load (idex_is_load),
        .exmem_rd_addr(id_ex_q.rd_addr),
        .exmem_rd_wen (id_ex_q.rd_wen & id_ex_q.valid),
        .memwb_rd_addr(ex_mem_q.rd_addr),
        .memwb_rd_wen (ex_mem_q.rd_wen & ex_mem_q.valid),
        .ex_flush     (ex_flush),
        .fwd_a        (id_fwd_a),
        .fwd_b        (id_fwd_b),
        .stall_ifid   (stall_lu),
        .flush_ifid   (flush_ifid),
        .flush_idex   (flush_idex)
    );

    // Load interlock, second cycle. merlin's load-to-branch interlock
    // (riscv-ip common-rv32i ISSUE-001 row 3) widened to every consumer
    // (peregrine TASK-006, the 75 MHz build): an ID instruction whose
    // operand is a load now in MEM waits one more cycle and reads the load
    // through the WB->ID bypass. No load is forwarded WB->EX, so the D$
    // response -> load align -> ALU path is gone; a load-use costs two
    // bubbles instead of one.
    logic exmem_is_load;
    logic stall_ldbr;

    assign exmem_is_load = ex_mem_q.dmem_req & ~ex_mem_q.dmem_we & ex_mem_q.valid;
    assign stall_ldbr    = if_id_q.valid & exmem_is_load &
                           ((id_fwd_a == FWD_MEMWB) | (id_fwd_b == FWD_MEMWB));

    // CSR serialization: a CSR instruction in ID waits while an older CSR
    // instruction is in ID/EX or EX/MEM, so its EX-stage read of the CSR
    // file sees every older CSR write (written at MEM).
    logic stall_csr;

    assign stall_csr = if_id_q.valid & id_csr_op &
                       ((id_ex_q.valid & id_ex_q.csr_op) |
                        (ex_mem_q.valid & ex_mem_q.csr_op));

    assign stall_ifid = stall_lu | stall_ldbr | stall_csr;

    // The select register: same stall and flush as ID/EX.
    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            ex_fwd_a <= FWD_IDEX;
            ex_fwd_b <= FWD_IDEX;
        end else if (id_ex_flush_eff) begin
            ex_fwd_a <= FWD_IDEX;
            ex_fwd_b <= FWD_IDEX;
        end else if (!mem_wait && !ex_m_stall) begin
            ex_fwd_a <= id_fwd_a;
            ex_fwd_b <= id_fwd_b;
        end
    )

    // Effective flushes.  A MEM redirect (trap or mret) kills everything
    // younger: IF/ID, ID/EX, and the instruction leaving EX.  Flushes are
    // suppressed while the memories wait so the event replays after.
    // While an M instruction holds in EX, ID/EX holds it (the ID interlock
    // bubble must not overwrite it) and EX/MEM takes the bubble instead.
    assign if_id_flush_eff  = ((flush_ifid | mem_redirect_nw) & ~mem_wait);
    assign id_ex_flush_eff  = ((flush_idex | (stall_ifid & ~ex_m_stall) | mem_redirect_nw)
                               & ~mem_wait);
    assign ex_mem_flush_eff = (mem_redirect_nw | ex_m_stall) & ~mem_wait;

    // -----------------------------------------------------------------
    // EX stage: ALU, branch comparator, alignment checks, CSR read
    // -----------------------------------------------------------------
    logic [31:0] wb_fwd_data;
    logic [31:0] ex_rs1_fwd;
    logic [31:0] ex_rs2_fwd;

    // The MEM/WB arm is the non-load writeback value: stall_ldbr keeps a
    // load in WB from ever being forwarded into EX (TASK-006).
    assign ex_rs1_fwd = (ex_fwd_a == FWD_EXMEM) ? ex_mem_q.alu_y :
                        (ex_fwd_a == FWD_MEMWB) ? mem_wb_q.alu_y  :
                                                  id_ex_q.rs1_data;
    assign ex_rs2_fwd = (ex_fwd_b == FWD_EXMEM) ? ex_mem_q.alu_y :
                        (ex_fwd_b == FWD_MEMWB) ? mem_wb_q.alu_y  :
                                                  id_ex_q.rs2_data;

    logic [31:0] alu_a;
    logic [31:0] alu_b;
    logic [31:0] alu_y_raw;

    // LUI ignores its rs1 field (merlin's note).
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

    // CSR read and write-data generation.  The CSR's old value is rd's
    // result, so it replaces the ALU result and forwards from EX/MEM.
    logic [11:0] ex_csr_addr;
    logic [31:0] ex_csr_rdata;
    logic        ex_csr_exists;
    logic [31:0] ex_csr_src;
    logic        ex_csr_wen;
    logic [31:0] ex_csr_wdata;
    logic        ex_csr_ill;

    assign ex_csr_addr = id_ex_q.insn[31:20];
    assign ex_csr_src  = id_ex_q.funct3[2] ? {27'd0, id_ex_q.insn[19:15]} : ex_rs1_fwd;
    // csrrw/csrrwi always write; csrrs/csrrc (and their immediates) write
    // only when the rs1/zimm field is non-zero.
    assign ex_csr_wen  = id_ex_q.csr_op &
                         ((id_ex_q.funct3[1:0] == CSR_RW) | (id_ex_q.insn[19:15] != 5'd0));

    always_comb begin
        unique case (id_ex_q.funct3[1:0])
            CSR_RS:  ex_csr_wdata = ex_csr_rdata | ex_csr_src;
            CSR_RC:  ex_csr_wdata = ex_csr_rdata & ~ex_csr_src;
            default: ex_csr_wdata = ex_csr_src;
        endcase
    end

    // Illegal: no such CSR, or a write to a read-only one (addr[11:10]=11).
    assign ex_csr_ill = id_ex_q.csr_op &
                        (~ex_csr_exists | (ex_csr_wen & (ex_csr_addr[11:10] == 2'b11)));

    // M unit (PRD §4.4).  It starts on the first EX cycle without mem_wait
    // and latches the forwarded operands; RVFI reports those latched
    // values, because the forwarding selects go stale during the hold.
    logic        ex_m_valid;
    logic        mdu_start;
    logic        mdu_idle;
    logic        mdu_done;
    logic [31:0] mdu_result;
    logic [31:0] ex_m_rs1;
    logic [31:0] ex_m_rs2;

    assign ex_m_valid = id_ex_q.valid & id_ex_q.m_op;
    assign mdu_start  = ex_m_valid & mdu_idle & ~mem_wait & ~mem_redirect_nw;
    assign ex_m_stall = ex_m_valid & ~mdu_done;

    peregrine_mdu #(
        .MUL_DSP (MUL_DSP)
    ) u_mdu (
        .clk     (clk),
        .rst_n   (w_aresetn),
        .start   (mdu_start),
        .cancel  (mem_redirect),
        .consume (~mem_wait),
        .funct3  (id_ex_q.funct3),
        .a       (ex_rs1_fwd),
        .b       (ex_rs2_fwd),
        .idle    (mdu_idle),
        .done    (mdu_done),
        .result  (mdu_result)
    );

    always_ff @(posedge clk) begin
        if (mdu_start) begin
            ex_m_rs1 <= ex_rs1_fwd;
            ex_m_rs2 <= ex_rs2_fwd;
        end
    end

    logic [31:0] alu_y;
    assign alu_y = id_ex_q.csr_op ? ex_csr_rdata :
                   id_ex_q.m_op   ? mdu_result   : alu_y_raw;

    // Branch / JALR operands (merlin's: the MEM/WB arm is the non-load
    // writeback value).
    logic [31:0] br_rs1;
    logic [31:0] br_rs2;

    assign br_rs1 = (ex_fwd_a == FWD_EXMEM) ? ex_mem_q.alu_y :
                    (ex_fwd_a == FWD_MEMWB) ? mem_wb_q.alu_y :
                                              id_ex_q.rs1_data;
    assign br_rs2 = (ex_fwd_b == FWD_EXMEM) ? ex_mem_q.alu_y :
                    (ex_fwd_b == FWD_MEMWB) ? mem_wb_q.alu_y :
                                              id_ex_q.rs2_data;

    logic        cmp_signed;
    logic        cmp_eq;
    logic        cmp_lt;
    logic        branch_cond;
    logic        branch_taken;

    assign cmp_signed = ~id_ex_q.funct3[1];
    assign cmp_eq     = (br_rs1 == br_rs2);
    assign cmp_lt     = ($signed({cmp_signed & br_rs1[31], br_rs1})
                         < $signed({cmp_signed & br_rs2[31], br_rs2}));

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

    // JALR's target needs rs1; a branch's or JAL's comes from ID (pc + imm,
    // what the ALU computes for them).
    logic [31:0] ex_jalr_target;
    logic        ex_tgt_miss;
    assign ex_jalr_target = (br_rs1 + id_ex_q.imm) & JALR_ALIGN_MASK;
    assign ex_target   = id_ex_q.jalr ? ex_jalr_target : id_ex_q.br_target;
    // A JALR guess is checked without the target adder: a taken guess is
    // word aligned (the BTB stores PC[31:2]), so (rs1 + imm) & ~1 equals it
    // exactly when rs1 is pred_target - imm or one more (jalr_x, from ID).
    // A not-taken guess mispredicts on its direction alone.
    logic [31:0] ex_jalr_x1;
    logic        ex_jalr_hit;
    assign ex_jalr_x1  = id_ex_q.jalr_x + 32'd1;
    assign ex_jalr_hit = (br_rs1 == id_ex_q.jalr_x) | (br_rs1 == ex_jalr_x1);
    assign ex_tgt_miss = id_ex_q.jalr ? ~ex_jalr_hit : ~id_ex_q.br_tgt_hit;
    assign ex_taken  = id_ex_q.valid & (id_ex_q.jump | id_ex_q.jalr | branch_taken);
    logic [31:0] ex_pc_incr;
    assign ex_pc_incr = id_ex_q.pc + PC_INCR;
    assign ex_next_pc = ex_taken ? ex_target : ex_pc_incr;

    // Mispredict: the guess the instruction was fetched with disagrees
    // with the resolved next PC -- the direction, or the target of a taken
    // guess.  With BP_EN=0 the guess is always "not taken", so this is
    // merlin's "every taken branch flushes".
    assign ex_mispredict = id_ex_q.valid &
                           ((id_ex_q.pred_taken != ex_taken) |
                            (ex_taken & ex_tgt_miss));
    // An instruction held in EX redirects only as it leaves (an earlier
    // flush would kill it in ID/EX, flush beating stall).
    assign ex_flush  = ex_mispredict & ~ex_m_stall;

    // Predictor: looked up by the fetch PC, written once per resolved
    // instruction as it leaves EX (not under mem_wait, not while an M
    // instruction holds, not when a MEM redirect kills it).
    logic ex_leaves;
    assign ex_leaves = id_ex_q.valid & ~mem_wait & ~ex_m_stall & ~mem_redirect_nw;

    peregrine_bpred #(
        .BP_EN       (BP_EN),
        .BTB_ENTRIES (BTB_ENTRIES),
        .BHT_ENTRIES (BHT_ENTRIES)
    ) u_bpred (
        .clk            (clk),
        .rst_n          (w_aresetn),
        .lookup_pc      (pc),
        .pred_taken     (if_pred_taken),
        .pred_target    (if_pred_target),
        .upd_valid      (ex_leaves),
        .upd_pc         (id_ex_q.pc),
        .upd_cond       (id_ex_q.branch),
        .upd_uncond     (id_ex_q.jump | id_ex_q.jalr),
        .upd_taken      (ex_taken),
        .upd_target     (ex_target),
        .upd_pred_taken (id_ex_q.pred_taken)
    );

    // Instruction-address misalignment (IALIGN=32) on taken control flow.
    // The redirect still happens in EX; the trap at MEM one cycle later
    // flushes whatever it fetched.
    logic [1:0] tgt_lo_pc;
    logic [1:0] tgt_lo_jalr;
    logic       misalign_target;

    assign tgt_lo_pc       = id_ex_q.pc[1:0] + id_ex_q.imm[1:0];
    assign tgt_lo_jalr     = (br_rs1[1:0] + id_ex_q.imm[1:0]) & 2'b10;
    assign misalign_target = (id_ex_q.jump & (tgt_lo_pc != 2'b00)) |
                             (id_ex_q.jalr & (tgt_lo_jalr != 2'b00)) |
                             (branch_taken & (tgt_lo_pc != 2'b00));

    // Load/store address misalignment, off the low bits of the offset adder.
    logic [1:0] ls_offset;
    logic       ls_misalign;

    assign ls_offset   = ex_rs1_fwd[1:0] + id_ex_q.imm[1:0];
    assign ls_misalign = id_ex_q.dmem_req & id_ex_q.valid &
                         ((id_ex_q.funct3[1:0] == 2'b01) ? ls_offset[0] :
                          (id_ex_q.funct3[1:0] == 2'b10) ? (ls_offset != 2'b00) :
                          1'b0);

    // EX/MEM input assembly
    ex_mem_t ex_mem_d;

    assign ex_mem_d.pc          = id_ex_q.pc;
    assign ex_mem_d.next_pc     = ex_next_pc;
    assign ex_mem_d.alu_y       = (id_ex_q.jump | id_ex_q.jalr) ? ex_pc_incr : alu_y;
    assign ex_mem_d.store_data  = ex_rs2_fwd;
    assign ex_mem_d.rd_addr     = id_ex_q.rd_addr;
    assign ex_mem_d.rd_wen      = id_ex_q.rd_wen;
    assign ex_mem_d.wb_sel      = id_ex_q.wb_sel;
    assign ex_mem_d.funct3      = id_ex_q.funct3;
    assign ex_mem_d.dmem_req    = id_ex_q.dmem_req;
    assign ex_mem_d.dmem_we     = id_ex_q.dmem_we;
    assign ex_mem_d.ls_misalign = ls_misalign;
    // One exception per instruction; decode's (ecall/ebreak/illegal) comes
    // first because such an instruction does nothing else.
    assign ex_mem_d.exc_cause   = (id_ex_q.exc_cause != EXC_NONE) ? id_ex_q.exc_cause :
                                  ex_csr_ill                       ? EXC_ILL           :
                                  misalign_target                  ? EXC_IALIGN        :
                                  ls_misalign                      ? (id_ex_q.dmem_we ? EXC_SALIGN
                                                                                      : EXC_LALIGN) :
                                                                     EXC_NONE;
    assign ex_mem_d.csr_op      = id_ex_q.csr_op;
    assign ex_mem_d.csr_wen     = ex_csr_wen;
    assign ex_mem_d.csr_wdata   = ex_csr_wdata;
    assign ex_mem_d.mret        = id_ex_q.mret;
    assign ex_mem_d.m_op        = id_ex_q.m_op;
    assign ex_mem_d.bp_pred_taken  = id_ex_q.pred_taken;
    assign ex_mem_d.bp_pred_target = id_ex_q.pred_target;
    assign ex_mem_d.bp_mispredict  = ex_mispredict;
    assign ex_mem_d.valid       = id_ex_q.valid;
    assign ex_mem_d.insn        = id_ex_q.insn;
    assign ex_mem_d.imm         = id_ex_q.imm;
    assign ex_mem_d.rs1_rdata   = id_ex_q.m_op ? ex_m_rs1 : ex_rs1_fwd;
    assign ex_mem_d.rs2_rdata   = id_ex_q.m_op ? ex_m_rs2 : ex_rs2_fwd;

    peregrine_ex_mem u_ex_mem (
        .clk   (clk),
        .rst_n (w_aresetn),
        .stall (mem_wait),
        .flush (ex_mem_flush_eff),
        .d_i   (ex_mem_d),
        .q_o   (ex_mem_q)
    );

    // -----------------------------------------------------------------
    // MEM stage: the commit point -- traps, mret, CSR write, data access
    // -----------------------------------------------------------------
    logic [31:0] csr_mtvec;
    logic [31:0] csr_mepc;
    logic        csr_irq_pending;
    logic [31:0] csr_irq_cause;

    logic        mem_exc;
    logic        mem_irq;
    logic        mem_trap;
    logic        mem_valid;     // MEM's instruction, unless WB's bus fault kills it
    logic        wb_fault;      // WB's load/store got an error response (TASK-005)
    logic        wb_trap;
    logic [31:0] wb_fault_cause;
    logic        mem_mret;
    logic        mem_csr_wen;
    logic [31:0] mem_trap_cause;
    logic [31:0] mem_trap_tval;

    // A bus fault on the instruction in WB (CACHE_EN): the wrapper raises
    // dmem_fault only for WB's own access; is_mem is the belt to its
    // braces.  It traps WB and kills MEM: every MEM-stage commit below
    // (trap, mret, CSR write, fence.i, the move to WB) is qualified by
    // ~wb_fault.  The one exception is the data request (mem_ls_ok, and
    // so dmem_req_pre), the core -> amber accept cone that limits the
    // 75 MHz build: it stays as it was, and the wrapper, which raised the
    // fault from its own flop, does not present or wait for MEM's request
    // that cycle (TASK-005; gating it here cost a logic level and 0.3 ns).
    assign wb_fault  = CACHE_EN & dmem_fault & mem_wb_q.valid & mem_wb_q.is_mem;
    assign wb_trap   = wb_fault & ~mem_wait;
    assign mem_valid = ex_mem_q.valid & ~wb_fault;

    assign mem_exc  = ex_mem_q.valid & (ex_mem_q.exc_cause != EXC_NONE);
    // An M instruction is not interruptible (see the header): its work is
    // done, and discarding it can starve it forever.
    // CACHE_EN: not on the cycle after a hold in which this instruction
    // presented a memory request (see the header).
    logic        r_mem_irq_lock;
    logic        mem_fencei_pend;
    logic        mem_fencei;
    logic        mem_ls_ok;

    assign mem_irq  = ex_mem_q.valid & ~ex_mem_q.m_op & csr_irq_pending & ~r_mem_irq_lock;
    assign mem_trap = (mem_exc | mem_irq) & ~wb_fault & ~mem_wait;
    assign mem_mret = mem_valid & ex_mem_q.mret & ~mem_exc & ~mem_irq & ~mem_wait;
    assign mem_csr_wen = mem_valid & ex_mem_q.csr_wen & ~mem_exc & ~mem_irq & ~mem_wait;

    // fence.i: a redirect to the next instruction, flushing what was fetched
    // before it.  CACHE_EN: held in MEM by the wrapper (fencei_req) until the
    // D$ clean and the I$ invalidate are done.
    assign mem_fencei_pend = mem_valid & ~mem_exc & ~mem_irq &
                             (ex_mem_q.insn[6:0] == 7'b0001111) &
                             (ex_mem_q.insn[14:12] == 3'b001);
    assign mem_fencei      = mem_fencei_pend & ~mem_wait;
    assign fencei_req      = CACHE_EN & mem_fencei_pend;

    if (CACHE_EN) begin : g_irq_lock
        `ALWAYS_FF_RST(clk, w_aresetn,
            if (`RST_ASSERTED(w_aresetn)) begin
                r_mem_irq_lock <= 1'b0;
            end else begin
                r_mem_irq_lock <= mem_wait & (r_mem_irq_lock | mem_ls_ok | mem_fencei_pend);
            end
        )
    end else begin : g_no_irq_lock
        assign r_mem_irq_lock = 1'b0;
    end

    assign mem_redirect    = wb_trap | mem_trap | mem_mret | mem_fencei;
    // The same decision without the ~mem_wait term, for the consumers that
    // gate on mem_wait themselves (the PC mux, the flushes, the M-unit
    // start, the predictor write): mem_wait then feeds them once, not
    // through the redirect as well (TASK-001 stage 7).  Same function.
    logic mem_trap_nw;
    logic mem_mret_nw;
    assign mem_trap_nw     = (mem_exc | mem_irq) & ~wb_fault;
    assign mem_mret_nw     = mem_valid & ex_mem_q.mret & ~mem_exc & ~mem_irq;
    assign mem_redirect_nw = wb_fault | mem_trap_nw | mem_mret_nw | mem_fencei_pend;
    assign mem_redirect_pc = (wb_fault | mem_trap_nw) ? csr_mtvec :
                             mem_mret_nw              ? csr_mepc  : ex_mem_q.next_pc;

    // mcause and mtval.  An interrupt wins: the instruction never executed.
    always_comb begin
        mem_trap_tval = 32'd0;
        if (mem_irq) begin
            mem_trap_cause = csr_irq_cause;
        end else begin
            unique case (ex_mem_q.exc_cause)
                EXC_ECALL:  mem_trap_cause = {1'b0, MCAUSE_ECALL_M};
                EXC_EBREAK: begin
                    mem_trap_cause = {1'b0, MCAUSE_EBREAK};
                    mem_trap_tval  = ex_mem_q.pc;
                end
                EXC_IALIGN: begin
                    mem_trap_cause = {1'b0, MCAUSE_IALIGN};
                    mem_trap_tval  = ex_mem_q.next_pc;
                end
                EXC_LALIGN: begin
                    mem_trap_cause = {1'b0, MCAUSE_LALIGN};
                    mem_trap_tval  = ex_mem_q.alu_y;
                end
                EXC_SALIGN: begin
                    mem_trap_cause = {1'b0, MCAUSE_SALIGN};
                    mem_trap_tval  = ex_mem_q.alu_y;
                end
                EXC_IFAULT: begin
                    mem_trap_cause = {1'b0, MCAUSE_IFAULT};
                    mem_trap_tval  = ex_mem_q.pc;
                end
                default: begin
                    mem_trap_cause = {1'b0, MCAUSE_ILL};
                    mem_trap_tval  = ex_mem_q.insn;
                end
            endcase
        end
    end

    // WB's bus fault (TASK-005): the trap the CSR file enters is WB's when
    // there is one (MEM's instruction is killed that cycle).  mtval is the
    // access's byte address.
    logic        csr_trap_take;
    logic [31:0] csr_trap_cause;
    logic [31:0] csr_trap_epc;
    logic [31:0] csr_trap_tval;
    assign wb_fault_cause = {1'b0, (mem_wb_q.insn[6:0] == OPCODE_STORE) ? MCAUSE_SFAULT
                                                                         : MCAUSE_LFAULT};
    assign csr_trap_take  = wb_trap | mem_trap;
    assign csr_trap_cause = wb_fault ? wb_fault_cause : mem_trap_cause;
    assign csr_trap_epc   = wb_fault ? mem_wb_q.pc    : ex_mem_q.pc;
    assign csr_trap_tval  = wb_fault ? mem_wb_q.alu_y : mem_trap_tval;

    peregrine_csr #(
        .M_EXT     (1'b1),
        .BUSERR_EN (CACHE_EN)
    ) u_csr (
        .clk          (clk),
        .rst_n        (w_aresetn),
        .raddr        (ex_csr_addr),
        .rdata        (ex_csr_rdata),
        .r_exists     (ex_csr_exists),
        .wen          (mem_csr_wen),
        .waddr        (ex_mem_q.insn[31:20]),
        .wdata        (ex_mem_q.csr_wdata),
        .trap_take    (csr_trap_take),
        .trap_cause   (csr_trap_cause),
        .trap_epc     (csr_trap_epc),
        .trap_tval    (csr_trap_tval),
        .mret_take    (mem_mret),
        .irq_software (irq_software),
        .irq_timer    (irq_timer),
        .irq_external (irq_external),
        .irq_buserr   (irq_buserr),
        .buserr_info  (buserr_info),
        .buserr_clear (buserr_clear),
        .mtvec        (csr_mtvec),
        .mepc         (csr_mepc),
        .irq_pending  (csr_irq_pending),
        .irq_cause    (csr_irq_cause)
    );

    // Data access: only for an instruction that commits here.
    logic [1:0]  mem_ls_offset;
    logic [3:0]  mem_ls_size_mask;

    assign mem_ls_offset = ex_mem_q.alu_y[1:0];

    always_comb begin
        unique case (ex_mem_q.funct3[1:0])
            2'b00:   mem_ls_size_mask = STRB_BYTE;
            2'b01:   mem_ls_size_mask = STRB_HALF;
            default: mem_ls_size_mask = STRB_WORD;
        endcase
    end

    // Not gated by wb_fault (see mem_valid): the wrapper blocks it then.
    assign mem_ls_ok  = ex_mem_q.dmem_req & ex_mem_q.valid & ~mem_exc & ~mem_irq;
    assign dmem_req   = mem_ls_ok & ~mem_wait;
    assign dmem_req_pre = CACHE_EN & mem_ls_ok;
    assign dmem_addr  = {ex_mem_q.alu_y[31:2], 2'b00};
    assign dmem_wdata = ex_mem_q.store_data << {mem_ls_offset, 3'b000};
    assign dmem_wstrb = (ex_mem_q.dmem_we & mem_ls_ok) ? (mem_ls_size_mask << mem_ls_offset)
                                                       : 4'b0000;

    // MEM/WB input assembly.  A trapping instruction writes no rd and
    // reports its trap target as the next PC.
    mem_wb_t mem_wb_d;
    logic    mem_trap_any;

    assign mem_trap_any       = mem_exc | mem_irq;
    assign mem_wb_d.pc        = ex_mem_q.pc;
    assign mem_wb_d.next_pc   = mem_trap_any  ? csr_mtvec :
                                ex_mem_q.mret ? csr_mepc  : ex_mem_q.next_pc;
    assign mem_wb_d.alu_y     = ex_mem_q.alu_y;
    assign mem_wb_d.rd_addr   = ex_mem_q.rd_addr;
    assign mem_wb_d.rd_wen    = ex_mem_q.rd_wen & ~mem_trap_any;
    assign mem_wb_d.wb_sel    = ex_mem_q.wb_sel;
    assign mem_wb_d.funct3    = ex_mem_q.funct3;
    assign mem_wb_d.trap      = mem_trap_any;
    assign mem_wb_d.is_mem    = ex_mem_q.dmem_req & ~mem_trap_any;
    assign mem_wb_d.exc_cause = ex_mem_q.exc_cause;
    assign mem_wb_d.bp_pred_taken  = ex_mem_q.bp_pred_taken;
    assign mem_wb_d.bp_pred_target = ex_mem_q.bp_pred_target;
    assign mem_wb_d.bp_mispredict  = ex_mem_q.bp_mispredict;
    assign mem_wb_d.valid     = mem_valid;
    assign mem_wb_d.insn      = ex_mem_q.insn;
    assign mem_wb_d.imm       = ex_mem_q.imm;
    assign mem_wb_d.rs1_rdata = ex_mem_q.rs1_rdata;
    assign mem_wb_d.rs2_rdata = ex_mem_q.rs2_rdata;

    // The trap cause rides beside MEM/WB for RVFI observation only.
    logic [31:0] wb_trap_cause;

    always_ff @(posedge clk) begin
        if (!mem_wait) wb_trap_cause <= mem_trap_cause;
    end

    peregrine_mem_wb u_mem_wb (
        .clk   (clk),
        .rst_n (w_aresetn),
        .stall (mem_wait),
        .flush (1'b0),
        .d_i   (mem_wb_d),
        .q_o   (mem_wb_q)
    );

    // -----------------------------------------------------------------
    // WB stage: load assembly, writeback mux, RVFI retire
    // -----------------------------------------------------------------
    logic [63:0] retire_count;
    logic [1:0]  wb_ls_offset;
    logic [31:0] wb_ls_rdata_shifted;
    logic [31:0] wb_load_data;

    assign wb_ls_offset        = mem_wb_q.alu_y[1:0];
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

    // The forwarded WB value; the x0 guard reads wb_rd_addr (reset-forced).
    assign wb_fwd_data = (wb_rd_addr == 5'd0)          ? 32'd0        :
                         (mem_wb_q.wb_sel == WB_LOAD)  ? wb_load_data :
                                                         mem_wb_q.alu_y;
    assign wb_rd_wdata = wb_fwd_data;

    // Register-file write port.  During reset the destination is forced to
    // x0 and the write is enabled every cycle so x0 is initialized to zero.
    assign wb_rd_addr    = w_aresetn ? mem_wb_q.rd_addr : 5'd0;
    assign wb_rd_wen_eff = (~w_aresetn) |
                           (w_aresetn & mem_wb_q.rd_wen & mem_wb_q.valid & ~mem_wait &
                            ~wb_fault);

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            retire_count <= '0;
        end else if (rvfi_valid) begin
            retire_count <= retire_count + 64'd1;
        end
    )

    // RVFI aggregation at WB retire.
    logic        rd_wb;
    logic [1:0]  rvfi_ls_offset;
    logic [3:0]  rvfi_ls_size_mask;
    logic [31:0] rvfi_ls_data_mask;
    logic        rvfi_mem_active;
    logic        wb_is_load;
    logic        wb_is_store;

    // A bus-faulted load or store (wb_fault) retires as a trap beat: no rd,
    // no memory access, its trap target as the next PC.
    assign rd_wb           = mem_wb_q.rd_wen & (mem_wb_q.rd_addr != 5'd0) & ~wb_fault;
    assign rvfi_valid      = w_aresetn & mem_wb_q.valid & ~mem_wait;
    assign rvfi_order      = retire_count;
    assign rvfi_pc_rdata   = mem_wb_q.pc;
    assign rvfi_pc_wdata   = wb_fault ? csr_mtvec : mem_wb_q.next_pc;
    assign rvfi_insn       = mem_wb_q.insn;
    assign rvfi_trap       = mem_wb_q.trap | wb_fault;
    assign rvfi_trap_cause = wb_fault      ? wb_fault_cause :
                             mem_wb_q.trap ? wb_trap_cause  : 32'd0;
    assign rvfi_bp_pred_taken  = mem_wb_q.bp_pred_taken;
    assign rvfi_bp_pred_target = mem_wb_q.bp_pred_target;
    assign rvfi_bp_mispredict  = mem_wb_q.bp_mispredict;
    assign rvfi_rs1_addr   = mem_wb_q.insn[19:15];
    assign rvfi_rs2_addr   = mem_wb_q.insn[24:20];
    assign rvfi_rs1_rdata  = mem_wb_q.rs1_rdata;
    assign rvfi_rs2_rdata  = mem_wb_q.rs2_rdata;
    assign rvfi_rd_addr    = rd_wb ? mem_wb_q.rd_addr : 5'd0;
    assign rvfi_rd_wdata   = rd_wb ? wb_rd_wdata      : 32'd0;

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

    assign wb_is_load      = mem_wb_q.insn[6:0] == OPCODE_LOAD;
    assign wb_is_store     = mem_wb_q.insn[6:0] == OPCODE_STORE;
    assign rvfi_mem_active = mem_wb_q.valid & mem_wb_q.is_mem & ~wb_fault;

    assign rvfi_mem_addr  = rvfi_mem_active ? {mem_wb_q.alu_y[31:2], 2'b00} : 32'd0;
    assign rvfi_mem_rmask = (rvfi_mem_active & wb_is_load)
                            ? (rvfi_ls_size_mask << rvfi_ls_offset) : 4'd0;
    assign rvfi_mem_wmask = (rvfi_mem_active & wb_is_store)
                            ? (rvfi_ls_size_mask << rvfi_ls_offset) : 4'd0;
    assign rvfi_mem_rdata = (rvfi_mem_active & wb_is_load) ? dmem_rdata : 32'd0;
    assign rvfi_mem_wdata = (rvfi_mem_active & wb_is_store)
                            ? ((mem_wb_q.rs2_rdata & rvfi_ls_data_mask) << {rvfi_ls_offset, 3'b000})
                            : 32'd0;

endmodule : peregrine_core
