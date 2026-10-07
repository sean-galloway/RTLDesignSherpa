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

Load/store model (Task 7)
--------------------------
The golden model implements architectural RISC-V misaligned semantics: an
access that crosses a 32-bit word boundary reads/writes both words and
assembles the full value.  Aligned and in-word misaligned accesses touch a
single word.  RVFI mem fields report the unaligned byte address, a packed
strobe starting at bit 0, and the assembled access data.
"""

MASK32 = 0xFFFFFFFF


def sext(value, bits):
    """Sign-extend the low ``bits`` of ``value`` to a Python signed int."""
    sign = 1 << (bits - 1)
    return (value & (sign - 1)) - (value & sign)


def s32(value):
    """Reinterpret an unsigned 32-bit value as signed."""
    return value - (1 << 32) if value & 0x80000000 else value


def _data_mask(size):
    """Bit mask for ``size`` bytes (size = 1/2/4)."""
    return (1 << (size * 8)) - 1


def _store_merge(word, wdata, wstrb):
    """Merge wdata into word using the 4-bit byte strobe."""
    result = word
    for b in range(4):
        if (wstrb >> b) & 1:
            lo = b * 8
            result = (result & ~(0xFF << lo)) | (((wdata >> lo) & 0xFF) << lo)
    return result & MASK32


def _arch_load(dmem, addr, size):
    """Architectural load: return raw little-endian value of ``size`` bytes."""
    offset = addr & 0x3
    if offset + size <= 4:
        word = dmem.get(addr >> 2, 0)
        raw = (word >> (offset * 8)) & _data_mask(size)
    else:
        tail_size = 4 - offset
        head_size = size - tail_size
        word0 = dmem.get(addr >> 2, 0)
        word1 = dmem.get((addr >> 2) + 1, 0)
        tail = (word0 >> (offset * 8)) & _data_mask(tail_size)
        head = word1 & _data_mask(head_size)
        raw = (head << (tail_size * 8)) | tail
    return raw & _data_mask(size)


def _arch_store(dmem, addr, size, value):
    """Architectural store: write ``size`` bytes from ``value`` at ``addr``."""
    offset = addr & 0x3
    value &= _data_mask(size)
    if offset + size <= 4:
        idx = addr >> 2
        wstrb = ((1 << size) - 1) << offset
        wdata = value << (offset * 8)
        dmem[idx] = _store_merge(dmem.get(idx, 0), wdata, wstrb)
    else:
        tail_size = 4 - offset
        head_size = size - tail_size
        idx0 = addr >> 2
        idx1 = idx0 + 1
        tail = value & _data_mask(tail_size)
        head = (value >> (tail_size * 8)) & _data_mask(head_size)
        tail_strobe = ((1 << tail_size) - 1) << offset
        dmem[idx0] = _store_merge(
            dmem.get(idx0, 0), tail << (offset * 8), tail_strobe
        )
        head_strobe = (1 << head_size) - 1
        dmem[idx1] = _store_merge(dmem.get(idx1, 0), head, head_strobe)
    return value


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
        self.dmem = {}
        self.regs = [0] * 32
        self.pc = reset_addr
        self.reset_addr = reset_addr
        self.trace = []
        self.halt_cause = None
        self.halt_pc = None

    def _load(self, addr, size, signed):
        """Return (rd_val, rmask, rvfi_rdata) for an architectural load."""
        raw = _arch_load(self.dmem, addr, size)
        rmask = (1 << size) - 1
        if size == 1:
            val = raw & 0xFF
            if signed:
                val = sext(val, 8)
        elif size == 2:
            val = raw & 0xFFFF
            if signed:
                val = sext(val, 16)
        else:
            val = raw & MASK32
        return val & MASK32, rmask, raw

    def _store(self, addr, size, value):
        """Commit an architectural store; return (wmask, rvfi_wdata)."""
        raw = _arch_store(self.dmem, addr, size, value)
        return (1 << size) - 1, raw

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
        mem_addr = 0
        mem_rmask = 0
        mem_wmask = 0
        mem_rdata = 0
        mem_wdata = 0

        # immediates for branches/jumps (sign-extended, LSB already zero for B/J)
        imm_b = sext(
            ((insn >> 31) & 0x1) << 12
            | ((insn >> 7) & 0x1) << 11
            | ((insn >> 25) & 0x3F) << 5
            | ((insn >> 8) & 0xF) << 1,
            13,
        )
        imm_j = sext(
            ((insn >> 31) & 0x1) << 20
            | ((insn >> 12) & 0xFF) << 12
            | ((insn >> 20) & 0x1) << 11
            | ((insn >> 21) & 0x3FF) << 1,
            21,
        )
        imm_s = sext(
            ((insn >> 25) & 0x7F) << 5
            | ((insn >> 7) & 0x1F),
            12,
        )

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
        elif opcode == 0x63:                      # BRANCH
            taken = False
            if f3 == 0:                            # BEQ
                taken = a == b
            elif f3 == 1:                          # BNE
                taken = a != b
            elif f3 == 4:                          # BLT
                taken = s32(a) < s32(b)
            elif f3 == 5:                          # BGE
                taken = s32(a) >= s32(b)
            elif f3 == 6:                          # BLTU
                taken = a < b
            elif f3 == 7:                          # BGEU
                taken = a >= b
            next_pc = (pc + imm_b) & MASK32 if taken else (pc + 4) & MASK32
            rd = 0                                 # branches do not write rd
        elif opcode == 0x6F:                      # JAL
            rd_val = (pc + 4) & MASK32
            next_pc = (pc + imm_j) & MASK32
        elif opcode == 0x67 and f3 == 0:          # JALR
            rd_val = (pc + 4) & MASK32
            next_pc = ((a + imm_i) & MASK32) & ~1
        elif opcode == 0x03:                      # LOAD
            mem_addr = (a + imm_i) & MASK32
            if f3 == 0:                            # LB
                rd_val, mem_rmask, mem_rdata = self._load(mem_addr, 1, True)
            elif f3 == 1:                          # LH
                rd_val, mem_rmask, mem_rdata = self._load(mem_addr, 2, True)
            elif f3 == 2:                          # LW
                rd_val, mem_rmask, mem_rdata = self._load(mem_addr, 4, False)
            elif f3 == 4:                          # LBU
                rd_val, mem_rmask, mem_rdata = self._load(mem_addr, 1, False)
            elif f3 == 5:                          # LHU
                rd_val, mem_rmask, mem_rdata = self._load(mem_addr, 2, False)
            else:
                raise NotImplementedError(f"golden: load funct3 {f3} not modelled")
        elif opcode == 0x23:                      # STORE
            mem_addr = (a + imm_s) & MASK32
            if f3 == 0:                            # SB
                size = 1
            elif f3 == 1:                          # SH
                size = 2
            elif f3 == 2:                          # SW
                size = 4
            else:
                raise NotImplementedError(f"golden: store funct3 {f3} not modelled")
            mem_wmask, mem_wdata = self._store(mem_addr, size, b)
            rd = 0                                 # stores do not write rd
        elif opcode == 0x73 and f3 == 0:          # SYSTEM: ECALL/EBREAK halt
            self.halt_cause = 1 if ((insn >> 20) & 0xFFF) == 0 else 2
            self.halt_pc = pc
            return None
        else:
            raise NotImplementedError(
                f"golden: opcode 0x{opcode:02x} not implemented "
                f"(Task 5 slice is OP/OP-IMM/LUI/AUIPC; see extension notes)")

        # Shared retire tail: append the beat, commit the rd write.
        rd_wdata = (rd_val & MASK32) if (rd != 0 and rd_val is not None) else 0
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
            "rd_wdata": rd_wdata,
            "pc_wdata": next_pc,
            "mem_addr": mem_addr,
            "mem_rmask": mem_rmask,
            "mem_wmask": mem_wmask,
            "mem_rdata": mem_rdata,
            "mem_wdata": mem_wdata,
        })
        if rd != 0 and rd_val is not None:
            x[rd] = rd_val & MASK32
        x[0] = 0
        return next_pc
