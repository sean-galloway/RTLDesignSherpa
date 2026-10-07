// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_core
// Purpose: Single-cycle RV32I core — PC register, decode truth table,
//          immediate generator, ALU, register file, writeback, next-PC mux,
//          halt, and first-class RVFI retire ports.
//
//          Task 7 adds the load/store datapath.  Aligned and in-word
//          misaligned accesses complete in one cycle; cross-word misaligned
//          accesses hold PC for one retry cycle and issue a second beat at
//          the next word.  This follows the plan's Global Constraints
//          spec-silent decision: kestrel handles misaligned L/S in hardware
//          (byte-lane rotation) rather than trapping, so rv32ui-p-ma_data
//          passes without a trap mechanism.
//
//          Task 8 adds the system layer.  Halt is a holding register:
//          any nonzero decode halt_cause latches halt, freezes the PC, and
//          stops retirement; the halting instruction retires as an RVFI
//          trap beat (rvfi_valid=1, rvfi_trap=1) and rvfi_valid stays low
//          thereafter.  FENCE/FENCE.I retire as NOPs; MRET falls through
//          to pc+4 (the riscv-tests p-env always points mepc at the next
//          instruction); the SYSTEM CSR class retires through a zero
//          writeback (kestrel has no CSR state — reads return zero, writes
//          drop), which lets the p-env preamble run; anything else in
//          SYSTEM or MISC-MEM is an illegal-instruction halt (cause 0xF).
//
//          Task 9 adds the instruction-address-misaligned halt.  RV32I
//          (IALIGN=32, no C extension) mandates a trap when taken control
//          flow — a taken branch, JAL, or JALR — targets an address that
//          is not 4-byte aligned, and rvfi.md requires that beat on RVFI.
//          Kestrel has no exception machinery, so like ecall/ebreak/
//          illegal it halts: cause 3 (HALT_IALIGN, encoding in kestrel_pkg)
//          from the halt holding register below, the beat retiring with
//          rvfi_trap=1, the rd writeback suppressed, and the PC frozen.
//          The riscv-formal insn_{beq,bne,blt,bge,bltu,bgeu,jal,jalr}
//          checks prove it.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

`include "reset_defs.svh"

module kestrel_core #(
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000
) (
    input  logic        clk,
    input  logic        rst_n,
    output logic [31:0] imem_addr,
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

    import kestrel_pkg::*;

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

    // The PC register, the RVFI retirement counter, and the Task-8 halt
    // holding register are the only state besides the register file.
    // Task 7 adds one retry bit (control state only) for cross-word L/S.
    logic [31:0] pc;
    logic [31:0] next_pc;
    logic [63:0] retire_count;
    logic        ls_retry;
    logic [31:0] ls_rdata_lo;

    // Fetch
    logic [31:0] insn;
    logic [6:0]  opcode;
    logic [2:0]  funct3;

    assign imem_addr = pc;
    assign insn      = imem_rdata;
    assign opcode    = insn[6:0];
    assign funct3    = insn[14:12];

    // Decode truth table (control bundle only; no state).
    alu_op_e    alu_op;
    imm_sel_e   imm_sel;
    logic       alu_src_a_pc;
    logic       alu_src_b_imm;
    logic       rd_wen;
    logic       dmem_we;
    logic [1:0] dmem_size;
    logic       branch;
    logic       jump;
    logic       jalr;
    logic [3:0] dec_halt_cause;
    logic       csr_stub;

    kestrel_decode u_decode (
        .insn          (insn),
        .alu_op        (alu_op),
        .imm_sel       (imm_sel),
        .alu_src_a_pc  (alu_src_a_pc),
        .alu_src_b_imm (alu_src_b_imm),
        .rd_wen        (rd_wen),
        .dmem_req      (dmem_req),
        .dmem_we       (dmem_we),
        .dmem_size     (dmem_size),
        .branch        (branch),
        .jump          (jump),
        .jalr          (jalr),
        .halt_cause    (dec_halt_cause),
        .csr_stub      (csr_stub)
    );

    // Immediate generator.
    logic [31:0] imm;

    kestrel_imm_gen u_imm_gen (
        .insn (insn),
        .sel  (imm_sel),
        .imm  (imm)
    );

    // Register file: combinational reads, single synchronous write, x0 tied.
    logic [31:0] rs1_data;
    logic [31:0] rs2_data;
    logic [31:0] rd_wdata;
    logic        rd_wen_eff;

    kestrel_regfile u_regfile (
        .clk      (clk),
        .rst_n    (rst_n),
        .rs1_addr (insn[19:15]),
        .rs1_data (rs1_data),
        .rs2_addr (insn[24:20]),
        .rs2_data (rs2_data),
        .rd_addr  (insn[11:7]),
        .rd_data  (rd_wdata),
        .rd_wen   (rd_wen_eff)
    );

    // Source muxes: PC vs rs1, immediate vs rs2.
    logic [31:0] alu_src_a;
    logic [31:0] alu_src_b;

    assign alu_src_a = alu_src_a_pc  ? pc       : rs1_data;
    assign alu_src_b = alu_src_b_imm ? imm      : rs2_data;

    // ALU: datapath arithmetic only. The eq/lt/ltu flags are deliberately
    // left unconnected — with src_a=PC for branches they would compare
    // pc against imm, so branch decisions come from the dedicated
    // comparator below (Task 4 review ruling, SDD ledger).
    logic [31:0] alu_y;

    kestrel_alu u_alu (
        .op  (alu_op),
        .a   (alu_src_a),
        .b   (alu_src_b),
        .y   (alu_y),
        .eq  (),
        .lt  (),
        .ltu ()
    );

    // Load/store datapath: byte-lane rotation with a single retry bit for
    // cross-word accesses.  Aligned and in-word misaligned accesses complete
    // in one cycle; when addr[1:0] + access_size > 4 the PC is held and a
    // second beat is issued at the next word.  The retry bit is control
    // state only — the datapath remains FSM-free.
    localparam logic [3:0] STRB_BYTE = 4'b0001;
    localparam logic [3:0] STRB_HALF = 4'b0011;
    localparam logic [3:0] STRB_WORD = 4'b1111;

    logic        ls_active;
    logic        ls_load;
    logic        ls_store;
    logic [2:0]  ls_size_bytes;
    logic [3:0]  ls_size_mask;
    logic [31:0] ls_data_mask;
    logic [1:0]  ls_offset;
    logic [2:0]  ls_tail_size;
    logic [2:0]  ls_head_size;
    logic        ls_crossing;
    logic        ls_first;
    logic        ls_second;
    logic        ls_single;
    logic [31:0] ls_rdata_shifted;
    logic [31:0] ls_raw_rdata;
    logic [31:0] ls_load_data;
    logic [3:0]  ls_head_strobe;
    logic [31:0] ls_wdata_first;
    logic [31:0] ls_wdata_second;

    assign ls_active  = dmem_req;
    assign ls_load    = dmem_req & ~dmem_we;
    assign ls_store   = dmem_req & dmem_we;
    assign ls_offset  = alu_y[1:0];

    always_comb begin
        unique case (dmem_size)
            2'b00:   ls_size_bytes = 3'd1;
            2'b01:   ls_size_bytes = 3'd2;
            2'b10:   ls_size_bytes = 3'd4;
            default: ls_size_bytes = 3'd1;
        endcase
        ls_size_mask = (ls_size_bytes == 3'd4) ? STRB_WORD :
                       (ls_size_bytes == 3'd2) ? STRB_HALF : STRB_BYTE;
        unique case (ls_size_bytes)
            3'd1:    ls_data_mask = 32'h0000_00FF;
            3'd2:    ls_data_mask = 32'h0000_FFFF;
            default: ls_data_mask = 32'hFFFF_FFFF;
        endcase
    end

    assign ls_tail_size = 3'd4 - {1'b0, ls_offset};
    assign ls_head_size = ls_size_bytes - ls_tail_size;
    assign ls_crossing  = ls_active & ((ls_offset + ls_size_bytes[2:0]) > 4'd4);
    assign ls_second    = ls_retry;
    assign ls_first     = ls_crossing & ~ls_second;
    assign ls_single    = ls_active & ~ls_crossing;

    assign dmem_addr = ls_second ? {alu_y[31:2] + 30'd1, 2'b00}
                                 : {alu_y[31:2], 2'b00};

    assign ls_wdata_first  = rs2_data << {ls_offset, 3'b000};
    assign ls_wdata_second = rs2_data >> {ls_tail_size, 3'b000};
    assign ls_head_strobe  = (ls_head_size == 3'd0) ? 4'b0000 :
                             (ls_head_size == 3'd1) ? 4'b0001 :
                             (ls_head_size == 3'd2) ? 4'b0011 :
                             (ls_head_size == 3'd3) ? 4'b0111 : 4'b1111;

    assign dmem_wdata = ls_second ? ls_wdata_second : ls_wdata_first;
    assign dmem_wstrb = ls_store ? (ls_second ? ls_head_strobe
                                              : (ls_size_mask << ls_offset))
                                 : 4'b0000;

    logic [31:0] ls_tail_mask;
    logic [31:0] ls_head_mask;

    assign ls_tail_mask = (ls_tail_size == 3'd0) ? 32'd0 :
                          (ls_tail_size == 3'd1) ? 32'h0000_00FF :
                          (ls_tail_size == 3'd2) ? 32'h0000_FFFF :
                          (ls_tail_size == 3'd3) ? 32'h00FF_FFFF :
                                                   32'hFFFF_FFFF;
    assign ls_head_mask = (ls_head_size == 3'd0) ? 32'd0 :
                          (ls_head_size == 3'd1) ? 32'h0000_00FF :
                          (ls_head_size == 3'd2) ? 32'h0000_FFFF :
                                                   32'h00FF_FFFF;
    assign ls_rdata_shifted = dmem_rdata >> {ls_offset, 3'b000};
    assign ls_raw_rdata     = ls_second ? (((dmem_rdata & ls_head_mask) << ({ls_tail_size, 3'b000}))
                                            | (ls_rdata_lo & ls_tail_mask))
                                        : (ls_rdata_shifted & ls_data_mask);

    always_comb begin
        unique case (funct3)
            3'b000:  ls_load_data = {{24{ls_raw_rdata[7]}},  ls_raw_rdata[7:0]};   // LB
            3'b100:  ls_load_data = {24'b0,                  ls_raw_rdata[7:0]};   // LBU
            3'b001:  ls_load_data = {{16{ls_raw_rdata[15]}}, ls_raw_rdata[15:0]};  // LH
            3'b101:  ls_load_data = {16'b0,                  ls_raw_rdata[15:0]};  // LHU
            3'b010:  ls_load_data = ls_raw_rdata;                                  // LW
            default: ls_load_data = ls_raw_rdata;
        endcase
    end

    // Writeback: LUI takes its immediate straight from imm_gen; loads take the
    // assembled/sign-extended data; JAL/JALR write pc+4; CSR-stubbed SYSTEM
    // instructions write a hard zero (no CSR state exists); everything else
    // uses the ALU result.  The register-file write is suppressed during the
    // first cycle of a crossing load so the partial word is not committed
    // early, and whenever halt is raised or held (Task 9: the misaligned
    // control-flow halt has decode rd_wen set for JAL/JALR, so the gate is
    // the halt itself, not decode's rd_wen).
    assign rd_wen_eff = rd_wen & ~ls_first & ~halt;
    assign rd_wdata   = csr_stub              ? 32'd0        :
                        (opcode == OPCODE_LUI) ? imm          :
                        ls_load                ? ls_load_data :
                        (jump || jalr)         ? (pc + PC_INCR) : alu_y;

    // Dedicated branch comparator: eq/lt/ltu computed from rs1_data/rs2_data
    // with the funct3 condition select, in parallel with the ALU computing
    // the pc+imm target. Wired now (ruling above); first exercised by the
    // Task 6 branch programs.
    logic cmp_eq;
    logic cmp_lt;
    logic cmp_ltu;
    logic branch_cond;
    logic branch_taken;

    assign cmp_eq  = (rs1_data == rs2_data);
    assign cmp_lt  = ($signed(rs1_data) < $signed(rs2_data));
    assign cmp_ltu = (rs1_data < rs2_data);

    always_comb begin
        unique case (funct3)
            F3_BEQ:  branch_cond = cmp_eq;
            F3_BNE:  branch_cond = ~cmp_eq;
            F3_BLT:  branch_cond = cmp_lt;
            F3_BGE:  branch_cond = ~cmp_lt;
            F3_BLTU: branch_cond = cmp_ltu;
            F3_BGEU: branch_cond = ~cmp_ltu;
            default: branch_cond = 1'b0;
        endcase
    end

    assign branch_taken = branch & branch_cond;

    // Next-PC mux. Branches/jumps are wired now; this slice's programs are
    // straight-line and Task 6 brings their golden vectors.
    always_comb begin
        if (jump || jalr) begin
            next_pc = jalr ? ((rs1_data + imm) & JALR_ALIGN_MASK) : (pc + imm);
        end else if (branch_taken) begin
            next_pc = pc + imm;
        end else begin
            next_pc = pc + PC_INCR;
        end
    end

    // Halt holding register (Task 8): any nonzero decode halt_cause latches
    // halt.  The output also ORs the combinational cause so the first
    // halting cycle is visible immediately — the PC freezes, the halting
    // instruction retires its RVFI trap beat, and rvfi_valid drops on the
    // following cycle (halt_q) and stays low forever.
    //
    // Task 9 adds the instruction-address-misaligned halt: a taken branch
    // or jump whose resolved target is not 4-byte aligned (IALIGN=32, no
    // C extension) must trap per RV32I; kestrel has no exception machinery
    // so it halts with cause 3 (HALT_IALIGN, kestrel_pkg) exactly like the
    // decode halt causes — same trap beat, same rd-writeback suppression
    // via `halt`, same PC freeze.  Decode never sets rd_wen on its own
    // halt causes, but JAL/JALR do, which is why the writeback gate uses
    // `halt` and not decode's rd_wen.
    logic       halt_q;
    logic       misalign_target;
    logic [3:0] halt_cause_eff;
    logic       halt_now;

    assign misalign_target = (jump | jalr | branch_taken)
                           & (next_pc[1:0] != 2'b00);
    assign halt_cause_eff  = dec_halt_cause
                           | (misalign_target ? HALT_IALIGN : HALT_NONE);
    assign halt_now        = |halt_cause_eff;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            halt_q <= 1'b0;
        end else begin
            halt_q <= halt_q | halt_now;
        end
    )

    assign halt       = halt_q | halt_now;
    assign halt_cause = halt_cause_eff;

    // PC register: hold on halt or on the first cycle of a cross-word access.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            pc <= RESET_ADDR;
        end else begin
            pc <= halt ? pc : (ls_first ? pc : next_pc);
        end
    )

    // Cross-word L/S retry bit: control state only, set on the first beat and
    // cleared after the second beat.  No FSM in the datapath.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            ls_retry <= 1'b0;
        end else begin
            ls_retry <= ls_first;
        end
    )

    // Capture the shifted first-word read data for merging on the retry cycle.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            ls_rdata_lo <= '0;
        end else begin
            if (ls_first) begin
                ls_rdata_lo <= ls_rdata_shifted;
            end
        end
    )

    // RVFI retirement order: 0, 1, 2, ... one per retired instruction.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            retire_count <= '0;
        end else begin
            if (rvfi_valid) begin
                retire_count <= retire_count + 64'd1;
            end
        end
    )

    // RVFI aggregation. rd fields are zeroed when decode is not writing a
    // register, when the destination is x0, and whenever halt is raised or
    // held (the Task-9 misaligned control-flow halt retires JAL/JALR
    // encodings whose decode rd_wen is set, so the rvfi view is gated by
    // `halt` like the regfile write) — riscv-formal requires rd_wdata == 0
    // whenever rd_addr == 0, so the discarded write to x0 is not reported
    // (the regfile discards that write architecturally as well); mem fields
    // report the unaligned access address, packed strobes and assembled
    // data on the final cycle of an access and are zero otherwise; rs
    // fields always reflect the register-file read ports (x0 reads return 0
    // naturally).  rvfi_valid is low during the first cycle of a cross-word
    // access, high on the final beat, and — Task 8 — high for exactly one
    // more beat on the halting cycle: the halting instruction (ecall/
    // ebreak/illegal/Task-9 misaligned target) retires as an rvfi_trap beat
    // (rvfi_trap=1, no rd write, no memory fields), after which the latched
    // halt holds rvfi_valid low.
    logic rd_wb;

    assign rd_wb          = rd_wen & (insn[11:7] != 5'd0) & ~halt;
    assign rvfi_valid     = rst_n & ~halt_q & ~ls_first;
    assign rvfi_order     = retire_count;
    assign rvfi_pc_rdata  = pc;
    assign rvfi_pc_wdata  = next_pc;
    assign rvfi_insn      = insn;
    assign rvfi_trap      = halt_now;
    assign rvfi_rs1_addr  = insn[19:15];
    assign rvfi_rs2_addr  = insn[24:20];
    assign rvfi_rs1_rdata = rs1_data;
    assign rvfi_rs2_rdata = rs2_data;
    assign rvfi_rd_addr   = rd_wb ? insn[11:7] : 5'd0;
    assign rvfi_rd_wdata  = rd_wb ? rd_wdata  : 32'd0;
    assign rvfi_mem_addr  = ls_active ? alu_y : 32'd0;
    assign rvfi_mem_rmask = ls_load   ? ls_size_mask : 4'd0;
    assign rvfi_mem_wmask = ls_store  ? ls_size_mask : 4'd0;
    assign rvfi_mem_rdata = ls_load   ? ls_raw_rdata          : 32'd0;
    assign rvfi_mem_wdata = ls_store  ? (rs2_data & ls_data_mask) : 32'd0;

endmodule : kestrel_core
