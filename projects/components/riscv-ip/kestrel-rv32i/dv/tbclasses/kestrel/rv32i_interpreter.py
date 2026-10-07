# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rv32i_interpreter
# Purpose: Tiny golden RV32I interpreter. Executes the same hex image the
#          kestrel TB loads into imem and produces the RVFI beat trace the
#          cocotb TB diffs against the core's observed trace.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

"""Golden RV32I interpreter for the kestrel lockstep TB.

EXTENSION POINT (Tasks 6-8)
---------------------------
This interpreter intentionally covers ONLY the instructions the current core
implements. ``RV32IInterpreter._exec`` dispatches by opcode; an unimplemented
opcode raises ``NotImplementedError`` naming the extension task:

* Task 6: OPCODE_BRANCH (0x63), OPCODE_JAL (0x6F), OPCODE_JALR (0x67) —
  set ``next_pc`` to the taken target (and pc+4 as JAL/JALR rd data).
* Task 7: OPCODE_LOAD (0x03), OPCODE_STORE (0x23) — model dmem and fill the
  mem_* beat fields (rmask/wmask/rdata/wdata, mem_addr).
* Task 8: OPCODE_FENCE (0x0F) retires as a NOP; OPCODE_SYSTEM already halts
  here (ecall/ebreak), and illegal instructions should halt with cause 0xF
  instead of raising, to mirror decode.

To extend: add a branch of the dispatch in ``_exec``, compute ``rd_val`` /
``next_pc``, and let the shared tail append the retire record. A retire
record must be appended for EVERY retired instruction and NONE for the
halting instruction (the core's rvfi_valid is low the cycle decode raises
halt), so the traces stay index-aligned with the core's.

Hex image format: normalized kestrel images (normalize_hex.py) — one 32-bit
word per line, ``@`` records carry WORD indices, sparse (no zero padding).
``load_verilog_hex`` returns ``{word_index: word}``; fetches of unwritten
words return 0 (matching the tb_top zero-initialized memories).
"""

MASK32 = 0xFFFFFFFF


def sext(value, bits):
    """Sign-extend the low ``bits`` of ``value`` to a Python signed int."""
    sign = 1 << (bits - 1)
    return (value & (sign - 1)) - (value & sign)


def s32(value):
    """Reinterpret an unsigned 32-bit value as signed."""
    return value - (1 << 32) if value & 0x80000000 else value


def load_verilog_hex(path):
    """Parse a normalized word-indexed hex image into {word_index: word}."""
    words = {}
    idx = 0
    with open(path) as fh:
        for line in fh:
            line = line.split("#")[0].strip()
            for tok in line.split():
                if tok.startswith("@"):
                    idx = int(tok[1:], 16)
                else:
                    words[idx] = int(tok, 16) & MASK32
                    idx += 1
    return words


class RV32IInterpreter:
    """Minimal RV32I golden model: imem image in, RVFI retire trace out."""

    def __init__(self, imem_words, reset_addr=0):
        self.imem = dict(imem_words)
        self.regs = [0] * 32
        self.pc = reset_addr
        self.reset_addr = reset_addr
        self.trace = []
        self.halt_cause = None
        self.halt_pc = None

    def run(self, max_insns=100_000):
        """Execute until halt (ecall/ebreak) or the retirement budget expires."""
        for order in range(max_insns):
            next_pc = self._exec(order, self.imem.get(self.pc >> 2, 0))
            if next_pc is None:
                break
            self.pc = next_pc
        else:
            raise RuntimeError(
                f"golden: no halt after {max_insns} retired insns from "
                f"pc=0x{self.reset_addr:x}")
        return self.trace

    def _exec(self, order, insn):
        """Execute one instruction; return next PC or None when halted.

        Dispatch tail contract: compute rd_val (None = no rd write) and
        next_pc, then the shared tail records the beat and updates state.
        """
        x = self.regs
        pc = self.pc
        opcode = insn & 0x7F
        rd = (insn >> 7) & 0x1F
        f3 = (insn >> 12) & 0x7
        rs1 = (insn >> 15) & 0x1F
        rs2 = (insn >> 20) & 0x1F
        f7 = (insn >> 25) & 0x7F
        imm_i = sext(insn >> 20, 12)
        shamt = (insn >> 20) & 0x1F
        a = x[rs1]
        b = x[rs2]
        next_pc = pc + 4
        rd_val = None

        if opcode == 0x13:                        # OP-IMM
            if f3 == 0:
                rd_val = (a + imm_i) & MASK32     # ADDI
            elif f3 == 1:
                rd_val = (a << shamt) & MASK32    # SLLI
            elif f3 == 2:
                rd_val = int(s32(a) < imm_i)      # SLTI
            elif f3 == 3:
                rd_val = int(a < (imm_i & MASK32))  # SLTIU
            elif f3 == 4:
                rd_val = a ^ (imm_i & MASK32)     # XORI
            elif f3 == 5:
                rd_val = ((s32(a) >> shamt) if (insn >> 30) & 1
                          else (a >> shamt)) & MASK32   # SRAI / SRLI
            elif f3 == 6:
                rd_val = a | (imm_i & MASK32)     # ORI
            elif f3 == 7:
                rd_val = a & (imm_i & MASK32)     # ANDI
        elif opcode == 0x33:                      # OP
            if f3 == 0:
                rd_val = ((a - b) if f7 == 0x20 else (a + b)) & MASK32
            elif f3 == 1:
                rd_val = (a << (b & 0x1F)) & MASK32
            elif f3 == 2:
                rd_val = int(s32(a) < s32(b))     # SLT
            elif f3 == 3:
                rd_val = int(a < b)               # SLTU
            elif f3 == 4:
                rd_val = a ^ b                    # XOR
            elif f3 == 5:
                rd_val = ((s32(a) >> (b & 0x1F)) if f7 == 0x20
                          else (a >> (b & 0x1F))) & MASK32  # SRA / SRL
            elif f3 == 6:
                rd_val = a | b                    # OR
            elif f3 == 7:
                rd_val = a & b                    # AND
        elif opcode == 0x37:                      # LUI
            rd_val = insn & 0xFFFFF000
        elif opcode == 0x17:                      # AUIPC
            rd_val = (pc + (insn & 0xFFFFF000)) & MASK32
        elif opcode == 0x73 and f3 == 0:          # SYSTEM: ECALL/EBREAK halt
            self.halt_cause = 1 if ((insn >> 20) & 0xFFF) == 0 else 2
            self.halt_pc = pc
            return None
        else:
            raise NotImplementedError(
                f"golden: opcode 0x{opcode:02x} not implemented "
                f"(Task 5 slice is OP/OP-IMM/LUI/AUIPC; see extension notes)")

        if rd_val is None:
            raise NotImplementedError(
                f"golden: opcode 0x{opcode:02x} funct3 {f3} not implemented")

        # Shared retire tail: append the beat, commit the rd write.
        self.trace.append({
            "order": order,
            "pc": pc,
            "insn": insn,
            "trap": 0,
            "rs1_addr": rs1,
            "rs2_addr": rs2,
            "rs1_rdata": a,
            "rs2_rdata": b,
            "rd_addr": rd,
            # riscv-formal rule: rd_wdata must be zero whenever rd_addr is
            # zero — the discarded architectural write is not reported.
            "rd_wdata": (rd_val & MASK32) if rd != 0 else 0,
            "pc_wdata": next_pc,
            "mem_addr": 0,
            "mem_rmask": 0,
            "mem_wmask": 0,
            "mem_rdata": 0,
            "mem_wdata": 0,
        })
        if rd != 0:
            x[rd] = rd_val & MASK32
        x[0] = 0
        return next_pc
