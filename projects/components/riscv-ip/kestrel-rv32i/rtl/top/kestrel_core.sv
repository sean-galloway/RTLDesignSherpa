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
//          Task 7 adds the load/store datapath: naturally aligned byte,
//          half and word accesses in one cycle, byte-lane rotation within
//          the word.  A misaligned address halts (2026-10-20, owner: the
//          hardware cross-word retry sat on the register-write and PC-hold
//          path): cause 4 for a load, 5 for a store, the access is not
//          performed.  RISC-V permits either hardware or trap handling;
//          kestrel has no exception machinery, so like the other traps it
//          halts.  rv32ui-p-ma_data, which needs hardware support, now halts
//          on its first misaligned load.  RVFI follows riscv-formal's
//          RISCV_FORMAL_ALIGNED_MEM convention (word address, lane masks).
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
//          illegal it halts: cause 3 (HALT_IALIGN, encoding in rv32i_pkg)
//          from the halt holding register below, the beat retiring with
//          rvfi_trap=1, the rd writeback suppressed, and the PC frozen.
//          The riscv-formal insn_{beq,bne,blt,bge,bltu,bgeu,jal,jalr}
//          checks prove it.
//
//          Memory wait (2026-10-20, owner: a registered-read wrapper for
//          block RAM).  `mem_wait` high means the memories have not
//          answered this cycle: every piece of architectural state holds
//          (PC, regfile write, halt latch, retry bits, retire counter), RVFI
//          reports no retirement, and the combinational halt term is masked
//          (insn is not valid yet).  Tied low, the core is exactly the
//          single-cycle core above; kestrel_mem_bram drives it to put
//          synchronous-read memory behind the same ports.
//
//          Next-PC fetch port (2026-10-20).  `imem_addr_next` is the value
//          the PC register takes at the next edge (RESET_ADDR while in
//          reset).  A registered-read instruction memory addressed by it
//          presents the word at `pc` one clock later, so block RAM's own
//          output register stands in for an instruction register and the
//          execute cycle starts at the RAM output.
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

    // Boundary reset synchronization. The port rst_n is treated as an
    // asynchronous-assert input of unknown deassert quality: an N=3
    // reset_sync (rtl/cdc, formally proven) produces the internal reset
    // every block below sees.
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

    // The PC register, the RVFI retirement counter, and the Task-8 halt
    // holding register are the only state besides the register file.
    logic [31:0] pc;
    logic [31:0] pc_d;
    logic        halt_q;
    logic        misalign_link;     // JAL/JALR to a non-4-aligned target
    logic [31:0] next_pc;
    logic [63:0] retire_count;

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
    logic       alu_src_a_pc;
    logic       alu_src_b_imm;
    logic       rd_wen;
    logic       dec_dmem_req;
    logic       dmem_we;
    logic       branch;
    logic       jump;
    logic       jalr;
    logic [3:0] dec_halt_cause;
    logic       csr_stub;

    rv32i_decode u_decode (
        .insn          (insn),
        .alu_op        (alu_op),
        .imm_sel       (),               // imm_gen selects by opcode itself
        .alu_src_a_pc  (alu_src_a_pc),
        .alu_src_b_imm (alu_src_b_imm),
        .rd_wen        (rd_wen),
        .dmem_req      (dec_dmem_req),
        .dmem_we       (dmem_we),
        .dmem_size     (),               // funct3[1:0] is the size
        .branch        (branch),
        .jump          (jump),
        .jalr          (jalr),
        .halt_cause    (dec_halt_cause),
        .csr_stub      (csr_stub)
    );

    // Immediate generator.
    logic [31:0] imm;

    rv32i_imm_gen u_imm_gen (
        .insn (insn),
        .imm  (imm)
    );

    // Register file: plain 2R1W storage with combinational reads.  x0 is
    // kept zero by WRITES, not by a read-side mux (2026-10-20; the idea of
    // a stored zero x0 is from the BRISKI barrel core, done here
    // init-by-write per the house SRAM rule): while the core is in reset it
    // writes zero to x0 (reset_sync holds w_aresetn low for at least three
    // clocks), and any later write that targets x0 writes zero -- that term
    // shares the writeback mux's existing zero row with the CSR stub.  So
    // x0 reads zero with no logic on the register-read path, which is on
    // the critical path.  riscv-formal checks rs*_rdata == 0 for x0.
    logic [31:0] rs1_data;
    logic [31:0] rs2_data;
    logic [31:0] rd_wdata;
    logic        rd_wen_eff;
    logic [4:0]  rf_waddr;
    logic        rf_wen;

    assign rf_waddr = w_aresetn ? insn[11:7] : 5'd0;
    assign rf_wen   = rd_wen_eff | ~w_aresetn;

    kestrel_regfile u_regfile (
        .clk      (clk),
        .rs1_addr (insn[19:15]),
        .rs1_data (rs1_data),
        .rs2_addr (insn[24:20]),
        .rs2_data (rs2_data),
        .rd_addr  (rf_waddr),
        .rd_data  (rd_wdata),
        .rd_wen   (rf_wen)
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

    rv32i_alu u_alu (
        .op  (alu_op),
        .a   (alu_src_a),
        .b   (alu_src_b),
        .y   (alu_y),
        .eq  (),
        .lt  (),
        .ltu ()
    );

    // Load/store datapath: naturally aligned accesses, byte-lane rotation
    // within the word.  The access offset is the low two bits of rs1 + imm
    // (the ALU's own low bits, computed off the carry chain so the
    // misaligned halt and the strobes do not wait for the 32-bit add).  The
    // size is funct3[1:0] (byte 00, half 01, word 10) for loads and stores.
    localparam logic [3:0] STRB_BYTE = 4'b0001;
    localparam logic [3:0] STRB_HALF = 4'b0011;
    localparam logic [3:0] STRB_WORD = 4'b1111;

    logic        ls_active;
    logic        ls_load;
    logic        ls_store;
    logic [1:0]  ls_offset;
    logic        ls_misalign;
    logic        ls_ok;
    logic [3:0]  ls_size_mask;
    logic [31:0] ls_data_mask;
    logic [31:0] ls_rdata_shifted;
    logic [31:0] ls_load_data;

    // Requests are suppressed in reset and once halted (the frozen halting
    // instruction is never a store that should repeat).
    assign dmem_req   = dec_dmem_req & w_aresetn & ~halt_q;
    assign ls_active  = dmem_req;
    assign ls_load    = dmem_req & ~dmem_we;
    assign ls_store   = dmem_req & dmem_we;
    assign ls_offset  = rs1_data[1:0] + imm[1:0];

    always_comb begin
        unique case (funct3[1:0])
            2'b00:   begin ls_size_mask = STRB_BYTE; ls_data_mask = 32'h0000_00FF; end
            2'b01:   begin ls_size_mask = STRB_HALF; ls_data_mask = 32'h0000_FFFF; end
            default: begin ls_size_mask = STRB_WORD; ls_data_mask = 32'hFFFF_FFFF; end
        endcase
    end

    assign ls_misalign = ls_active & ((funct3[1:0] == 2'b01) ? ls_offset[0]
                                    : (funct3[1:0] == 2'b10) ? (ls_offset != 2'b00)
                                    : 1'b0);
    assign ls_ok       = ls_active & ~ls_misalign;

    assign dmem_addr  = {alu_y[31:2], 2'b00};
    assign dmem_wdata = rs2_data << {ls_offset, 3'b000};
    assign dmem_wstrb = (ls_store & ~ls_misalign) ? (ls_size_mask << ls_offset) : 4'b0000;

    assign ls_rdata_shifted = dmem_rdata >> {ls_offset, 3'b000};

    always_comb begin
        unique case (funct3)
            3'b000:  ls_load_data = {{24{ls_rdata_shifted[7]}},  ls_rdata_shifted[7:0]};   // LB
            3'b100:  ls_load_data = {24'b0,                      ls_rdata_shifted[7:0]};   // LBU
            3'b001:  ls_load_data = {{16{ls_rdata_shifted[15]}}, ls_rdata_shifted[15:0]};  // LH
            3'b101:  ls_load_data = {16'b0,                      ls_rdata_shifted[15:0]};  // LHU
            default: ls_load_data = dmem_rdata;                                            // LW
        endcase
    end

    // Writeback: LUI takes its immediate straight from imm_gen; loads take the
    // assembled/sign-extended data; JAL/JALR write pc+4; CSR-stubbed SYSTEM
    // instructions write a hard zero (no CSR state exists); everything else
    // uses the ALU result.  The register-file write is suppressed whenever
    // halt is held, while the memories wait, and on the two halts an
    // rd-writing instruction can raise: a misaligned JAL/JALR target (Task
    // 9) and a misaligned load.  The other halt sources never write rd --
    // decode sets rd_wen on none of its halt rows and branches have none --
    // so the gate leaves them (and the branch comparator behind a taken
    // misaligned branch) off this path; it is equivalent to gating with
    // `halt` (2026-10-20: that was the A7 critical path, register read ->
    // branch compare -> IALIGN halt -> register write enable).
    assign rd_wen_eff = rd_wen & ~halt_q & ~mem_wait & ~misalign_link & ~ls_misalign;
    assign rd_wdata   = (csr_stub || (rf_waddr == 5'd0)) ? 32'd0 :
                        (opcode == OPCODE_LUI) ? imm          :
                        ls_load                ? ls_load_data :
                        (jump || jalr)         ? (pc + PC_INCR) : alu_y;

    // Dedicated branch comparator: eq/lt/ltu computed from rs1_data/rs2_data
    // with the funct3 condition select, in parallel with the ALU computing
    // the pc+imm target. Wired now (ruling above); first exercised by the
    // Task 6 branch programs.
    // One magnitude comparator serves signed and unsigned (2026-10-20; the
    // shared-comparator idea is from the BRISKI barrel core): each operand
    // is extended to 33 bits with its sign bit for BLT/BGE (funct3[1] = 0)
    // and a zero for BLTU/BGEU (funct3[1] = 1), then compared signed.  One
    // carry chain instead of two.
    logic        cmp_eq;
    logic        cmp_lt;
    logic        cmp_signed;
    logic        branch_cond;
    logic        branch_taken;

    assign cmp_signed = ~funct3[1];
    assign cmp_eq     = (rs1_data == rs2_data);
    assign cmp_lt     = ($signed({cmp_signed & rs1_data[31], rs1_data})
                         < $signed({cmp_signed & rs2_data[31], rs2_data}));

    always_comb begin
        unique case (funct3)
            F3_BEQ:  branch_cond = cmp_eq;
            F3_BNE:  branch_cond = ~cmp_eq;
            F3_BLT:  branch_cond = cmp_lt;
            F3_BGE:  branch_cond = ~cmp_lt;
            F3_BLTU: branch_cond = cmp_lt;
            F3_BGEU: branch_cond = ~cmp_lt;
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
    // so it halts with cause 3 (HALT_IALIGN, rv32i_pkg) exactly like the
    // decode halt causes — same trap beat, same rd-writeback suppression
    // via `halt`, same PC freeze.  Decode never sets rd_wen on its own
    // halt causes, but JAL/JALR do, which is why the writeback gate uses
    // `halt` and not decode's rd_wen.
    // The target's low two bits come from their own two-bit adds, not from
    // the 32-bit next-PC adders: pc + imm for JAL and branches, (rs1 + imm)
    // with bit 0 cleared for JALR.
    logic       misalign_target;
    logic       misalign_branch;
    logic [1:0] tgt_lo_pc;
    logic [1:0] tgt_lo_jalr;
    logic [3:0] halt_cause_eff;
    logic       halt_now;

    assign tgt_lo_pc       = pc[1:0] + imm[1:0];
    assign tgt_lo_jalr     = (rs1_data[1:0] + imm[1:0]) & 2'b10;
    assign misalign_link   = (jump & (tgt_lo_pc != 2'b00)) | (jalr & (tgt_lo_jalr != 2'b00));
    assign misalign_branch = branch_taken & (tgt_lo_pc != 2'b00);
    assign misalign_target = misalign_link | misalign_branch;
    assign halt_cause_eff  = dec_halt_cause
                           | (misalign_target ? HALT_IALIGN : HALT_NONE)
                           | (ls_misalign ? (dmem_we ? HALT_SALIGN : HALT_LALIGN)
                                          : HALT_NONE);
    assign halt_now        = (|halt_cause_eff) & ~mem_wait;

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            halt_q <= 1'b0;
        end else begin
            halt_q <= halt_q | halt_now;   // halt_now is masked by mem_wait
        end
    )

    assign halt       = halt_q | halt_now;
    assign halt_cause = mem_wait ? 4'd0 : halt_cause_eff;

    // PC register: hold on halt or while the memories wait.  pc_d is also
    // the registered-read fetch address (RESET_ADDR while in reset, so the
    // first word is already at the RAM output when reset releases).
    assign pc_d           = (halt || mem_wait) ? pc : next_pc;
    assign imem_addr_next = w_aresetn ? pc_d : RESET_ADDR;

    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            pc <= RESET_ADDR;
        end else begin
            pc <= pc_d;
        end
    )

    // RVFI retirement order: 0, 1, 2, ... one per retired instruction.
    `ALWAYS_FF_RST(clk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
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
    // (the regfile discards that write architecturally as well).  Memory
    // fields follow RISCV_FORMAL_ALIGNED_MEM: the word address, the byte
    // lanes the access covers, the raw read word, and the store data
    // shifted into its lanes; they are zero on a misaligned (halting)
    // access, which performs nothing.  rs fields always reflect the
    // register-file read ports (x0 reads return 0 naturally).  rvfi_valid is
    // low while the memories wait and — Task 8 — high for exactly one more
    // beat on the halting cycle: the halting instruction (ecall/ebreak/
    // illegal/misaligned target/misaligned access) retires as an rvfi_trap
    // beat, after which the latched halt holds rvfi_valid low.
    logic rd_wb;

    assign rd_wb          = rd_wen & (insn[11:7] != 5'd0) & ~halt;
    assign rvfi_valid     = w_aresetn & ~halt_q & ~mem_wait;
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
    assign rvfi_mem_addr  = ls_ok ? dmem_addr : 32'd0;
    assign rvfi_mem_rmask = (ls_ok & ~dmem_we) ? (ls_size_mask << ls_offset) : 4'd0;
    assign rvfi_mem_wmask = (ls_ok &  dmem_we) ? (ls_size_mask << ls_offset) : 4'd0;
    assign rvfi_mem_rdata = (ls_ok & ~dmem_we) ? dmem_rdata : 32'd0;
    assign rvfi_mem_wdata = (ls_ok &  dmem_we) ? ((rs2_data & ls_data_mask) << {ls_offset, 3'b000})
                                               : 32'd0;

endmodule : kestrel_core
