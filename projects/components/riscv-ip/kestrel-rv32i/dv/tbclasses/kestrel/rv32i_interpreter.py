# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: rv32i_interpreter
# Purpose: Tiny golden RV32I interpreter. Executes the same hex image the
#          kestrel TB loads into memory and produces the RVFI beat trace the
#          cocotb TB diffs against the core's observed trace.
#
# Documentation: projects/components/riscv-ip/README.md
# Subsystem: riscv-ip/kestrel-rv32i
#
# Author: sean galloway
# Created: 2026-10-06

"""Golden RV32I interpreter for the kestrel lockstep TB.

The interpreter models exactly what the kestrel core implements — no more,
no less — so a full-field trace diff is meaningful:

* RV32I user instructions (OP/OP-IMM/LOAD/STORE/BRANCH/JAL/JALR/LUI/AUIPC).
* FENCE and FENCE.I retire as NOPs (MISC-MEM funct3 0/1).
* SYSTEM: ECALL/EBREAK halt (causes 1/2); MRET and the CSR class
  (CSRRW/CSRRS/CSRRC and immediate forms) retire through kestrel's
  system stub — no CSR state exists, reads return zero, writes are
  dropped, MRET falls through to pc+4.  This mirrors decode exactly and
  lets the battery's p-env preamble (``csrw mtvec`` etc.) execute.
* Any other encoding — unknown opcodes and RESERVED encodings of
  implemented opcodes (OP/OP-IMM funct7 mismatches, branch funct3 2/3,
  load/store funct3 holes, MISC-MEM funct3 2-7, SYSTEM funct3 100,
  SYSTEM funct3=0 with an unimplemented imm12) — raises
  ``NotImplementedError`` instead of guessing, so the golden can never
  silently agree with a core that halts illegal on it (deferred minor M2).

Task 8 trap beats: the halting instruction (ecall/ebreak) retires as an
RVFI trap beat — ``trap=1``, no rd write, no memory fields, ``pc_wdata``
pc+4 — appended after which ``run()`` stops.  The core emits the matching
beat the cycle decode raises halt, so traces stay index-aligned.

Memory model: unified (von Neumann).  The data memory is seeded with the
image, so self-modifying code (the rv32ui-p-fence_i signature overwrite)
is fetched correctly, matching the tb_top unified array.  Loads/stores
implement architectural RISC-V misaligned semantics: an access crossing a
32-bit word boundary reads/writes both words and assembles the full
value.  RVFI mem fields report the unaligned byte address, a packed
strobe starting at bit 0, and the assembled access data.

Hex image format: normalized kestrel images (normalize_hex.py) — one
32-bit word per line, ``@`` records carry WORD indices, sparse (no zero
padding).  ``load_verilog_hex`` returns ``{word_index: word}``.  Battery
callers key this map by the FULL word address (add the link base >> 2)
because the interpreter runs in the core's address space.
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
    """Minimal RV32I golden model: memory image in, RVFI retire trace out."""

    def __init__(self, imem_words, reset_addr=0):
        # Unified memory: the image seeds the data memory; instruction fetches
        # read the same array (self-modifying code must be visible, matching
        # the tb_top unified memory).
        self.dmem = dict(imem_words)
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
            next_pc = self._exec(order, self.dmem.get(self.pc >> 2, 0))
            if next_pc is None:
                break
            self.pc = next_pc
        else:
            raise RuntimeError(
                f"golden: no halt after {max_insns} retired insns from "
                f"pc=0x{self.reset_addr:x}")
        return self.trace

    def _halt(self, order, insn, cause):
        """Record the RVFI trap beat for the halting instruction, then stop.

        rs fields report the register-file read ports exactly like a normal
        beat (ebreak's imm12 bit overlaps the rs2 field, so they are not in
        general zero); rd and mem fields are architecturally empty.
        """
        rs1 = (insn >> 15) & 0x1F
        rs2 = (insn >> 20) & 0x1F
        self.trace.append({
            "order": order,
            "pc": self.pc,
            "insn": insn,
            "trap": 1,
            "rs1_addr": rs1,
            "rs2_addr": rs2,
            "rs1_rdata": self.regs[rs1],
            "rs2_rdata": self.regs[rs2],
            "rd_addr": 0,
            "rd_wdata": 0,
            "pc_wdata": (self.pc + 4) & MASK32,
            "mem_addr": 0,
            "mem_rmask": 0,
            "mem_wmask": 0,
            "mem_rdata": 0,
            "mem_wdata": 0,
        })
        self.halt_cause = cause
        self.halt_pc = self.pc
        return None

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
                if f7 != 0x00:
                    raise NotImplementedError(    # SLLI funct7 must be 0
                        f"golden: slli funct7 0x{f7:02x} reserved")
                rd_val = (a << shamt) & MASK32    # SLLI
            elif f3 == 2:
                rd_val = int(s32(a) < imm_i)      # SLTI
            elif f3 == 3:
                rd_val = int(a < (imm_i & MASK32))  # SLTIU
            elif f3 == 4:
                rd_val = a ^ (imm_i & MASK32)     # XORI
            elif f3 == 5:
                if f7 == 0x00:
                    rd_val = (a >> shamt) & MASK32        # SRLI
                elif f7 == 0x20:
                    rd_val = (s32(a) >> shamt) & MASK32   # SRAI
                else:
                    raise NotImplementedError(    # SRLI/SRAI funct7 hole
                        f"golden: srli/srai funct7 0x{f7:02x} reserved")
            elif f3 == 6:
                rd_val = a | (imm_i & MASK32)     # ORI
            elif f3 == 7:
                rd_val = a & (imm_i & MASK32)     # ANDI
        elif opcode == 0x33:                      # OP
            if f3 == 0:
                if f7 == 0x00:
                    rd_val = (a + b) & MASK32     # ADD
                elif f7 == 0x20:
                    rd_val = (a - b) & MASK32     # SUB
                else:
                    raise NotImplementedError(
                        f"golden: add/sub funct7 0x{f7:02x} reserved")
            elif f3 == 1:
                if f7 != 0x00:
                    raise NotImplementedError(
                        f"golden: sll funct7 0x{f7:02x} reserved")
                rd_val = (a << (b & 0x1F)) & MASK32
            elif f3 == 2:
                if f7 != 0x00:
                    raise NotImplementedError(
                        f"golden: slt funct7 0x{f7:02x} reserved")
                rd_val = int(s32(a) < s32(b))     # SLT
            elif f3 == 3:
                if f7 != 0x00:
                    raise NotImplementedError(
                        f"golden: sltu funct7 0x{f7:02x} reserved")
                rd_val = int(a < b)               # SLTU
            elif f3 == 4:
                if f7 != 0x00:
                    raise NotImplementedError(
                        f"golden: xor funct7 0x{f7:02x} reserved")
                rd_val = a ^ b                    # XOR
            elif f3 == 5:
                if f7 == 0x00:
                    rd_val = (a >> (b & 0x1F)) & MASK32        # SRL
                elif f7 == 0x20:
                    rd_val = (s32(a) >> (b & 0x1F)) & MASK32   # SRA
                else:
                    raise NotImplementedError(
                        f"golden: srl/sra funct7 0x{f7:02x} reserved")
            elif f3 == 6:
                if f7 != 0x00:
                    raise NotImplementedError(
                        f"golden: or funct7 0x{f7:02x} reserved")
                rd_val = a | b                    # OR
            elif f3 == 7:
                if f7 != 0x00:
                    raise NotImplementedError(
                        f"golden: and funct7 0x{f7:02x} reserved")
                rd_val = a & b                    # AND
        elif opcode == 0x37:                      # LUI
            rd_val = insn & 0xFFFFF000
        elif opcode == 0x17:                      # AUIPC
            rd_val = (pc + (insn & 0xFFFFF000)) & MASK32
        elif opcode == 0x63:                      # BRANCH
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
            else:
                raise NotImplementedError(        # branch funct3 2/3 reserved
                    f"golden: branch funct3 {f3} reserved")
            next_pc = (pc + imm_b) & MASK32 if taken else (pc + 4) & MASK32
            rd = 0                                 # branches do not write rd
        elif opcode == 0x6F:                      # JAL
            rd_val = (pc + 4) & MASK32
            next_pc = (pc + imm_j) & MASK32
        elif opcode == 0x67:                      # JALR
            if f3 != 0:
                raise NotImplementedError(        # JALR requires funct3 0
                    f"golden: jalr funct3 {f3} reserved")
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
                raise NotImplementedError(        # load funct3 3/6/7 reserved
                    f"golden: load funct3 {f3} reserved")
        elif opcode == 0x23:                      # STORE
            mem_addr = (a + imm_s) & MASK32
            if f3 == 0:                            # SB
                size = 1
            elif f3 == 1:                          # SH
                size = 2
            elif f3 == 2:                          # SW
                size = 4
            else:
                raise NotImplementedError(        # store funct3 3-7 reserved
                    f"golden: store funct3 {f3} reserved")
            mem_wmask, mem_wdata = self._store(mem_addr, size, b)
            rd = 0                                 # stores do not write rd
        elif opcode == 0x0F:                      # MISC-MEM
            if f3 > 1:
                raise NotImplementedError(        # MISC-MEM funct3 2-7 reserved
                    f"golden: misc-mem funct3 {f3} reserved")
            # FENCE / FENCE.I retire as NOPs for this core.
        elif opcode == 0x73:                      # SYSTEM
            if f3 == 0:
                sys_imm = (insn >> 20) & 0xFFF
                if sys_imm == 0x000:
                    return self._halt(order, insn, 1)      # ECALL
                if sys_imm == 0x001:
                    return self._halt(order, insn, 2)      # EBREAK
                if sys_imm == 0x302:
                    pass                                   # MRET: stub, fall through
                else:
                    raise NotImplementedError(
                        f"golden: system imm12 0x{sys_imm:03x} not modelled")
            elif f3 == 4:
                raise NotImplementedError(        # SYSTEM funct3 100 reserved
                    f"golden: system funct3 4 reserved")
            else:
                # CSR stub: no CSR state exists; reads return zero (rd write
                # of zero), writes are dropped.  Covers CSRRW/CSRRS/CSRRC and
                # the immediate forms — exactly the core's decode behaviour.
                rd_val = 0
        else:
            raise NotImplementedError(
                f"golden: opcode 0x{opcode:02x} not implemented")

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
