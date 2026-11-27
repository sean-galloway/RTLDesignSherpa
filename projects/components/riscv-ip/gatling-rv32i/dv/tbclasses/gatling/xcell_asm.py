# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: xcell_asm
# Purpose: Hand assembler for gatling programs: the RV32I subset the Xcell
#          tests use and the seven Xcell instructions (custom-0, gatling PRD
#          3.1 as built: CFG on funct3 110, x0 the ALU port).
#
# Documentation: projects/components/riscv-ip/gatling-rv32i/docs/gatling_mas
# Subsystem: riscv-ip/gatling-rv32i
#
# Created: 2026-11-26

"""Encoders for hand-assembled gatling programs.

``Prog`` collects words and resolves branch labels, so a test writes a
program as a short list of calls instead of hex.  The PRD leaves toolchain
support to a later binutils fragment (PRD 7 item 5); until then this is the
assembler.
"""

OPCODE_XCELL = 0x0B
XC_POP, XC_PUSH, XC_ECTX, XC_FLUSH, XC_KICK, XC_WAIT, XC_CFG = 0, 1, 2, 3, 4, 5, 6
XC_NAMES = {XC_POP: "POP", XC_PUSH: "PUSH", XC_ECTX: "ECTX", XC_FLUSH: "FLUSH",
            XC_KICK: "KICK", XC_WAIT: "WAIT", XC_CFG: "CFG"}
ACC_HOLD, ACC_ACCUM, ACC_CLEAR, ACC_DRAIN = 0, 1, 2, 3
HALT_DONE = 0x8
HALT_ILL = 0xF


def _xc(f3: int, reg: int, upper: int = 0) -> int:
    return ((upper & 0xFFF) << 20) | ((f3 & 7) << 12) | ((reg & 0x1F) << 7) | OPCODE_XCELL


def pop(rd: int = 0, acc: int = ACC_HOLD) -> int:
    """POP rd; rd = 0 issues the cell's function, acc_ctrl in insn[21:20]."""
    return _xc(XC_POP, rd, acc & 3)


def push(rs: int = 0) -> int:
    return _xc(XC_PUSH, rs)


def ectx() -> int:
    return _xc(XC_ECTX, 0)


def flush(rs: int) -> int:
    return _xc(XC_FLUSH, rs)


def kick(rs: int) -> int:
    return _xc(XC_KICK, rs)


def wait(rs: int) -> int:
    return _xc(XC_WAIT, rs)


def cfg(rd: int, idx: int) -> int:
    return _xc(XC_CFG, rd, idx)


def xcell_reserved(rd: int = 0) -> int:
    """funct3 111: reserved, an illegal instruction."""
    return _xc(7, rd)


def _i(op: int, rd: int, f3: int, rs1: int, imm: int) -> int:
    return ((imm & 0xFFF) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op


def addi(rd: int, rs1: int, imm: int) -> int:
    return _i(0x13, rd, 0, rs1, imm)


def lui(rd: int, imm20: int) -> int:
    return ((imm20 & 0xFFFFF) << 12) | (rd << 7) | 0x37


def li(rd: int, value: int) -> list:
    """Load a 32-bit constant: ADDI alone when it fits, else LUI + ADDI."""
    value &= 0xFFFF_FFFF
    sv = value - (1 << 32) if value & 0x8000_0000 else value
    if -2048 <= sv < 2048:
        return [addi(rd, 0, sv)]
    lo = value & 0xFFF
    lo_s = lo - 0x1000 if lo & 0x800 else lo
    hi = ((value - lo_s) >> 12) & 0xFFFFF
    return [lui(rd, hi), addi(rd, rd, lo_s)]


def _b(f3: int, rs1: int, rs2: int, off: int) -> int:
    o = off & 0x1FFF
    return ((((o >> 12) & 1) << 31) | (((o >> 5) & 0x3F) << 25) | (rs2 << 20)
            | (rs1 << 15) | (f3 << 12) | (((o >> 1) & 0xF) << 8) | (((o >> 11) & 1) << 7)
            | 0x63)


def sw(rs2: int, rs1: int, imm: int) -> int:
    i = imm & 0xFFF
    return ((i >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (2 << 12) | ((i & 0x1F) << 7) | 0x23


ECALL = 0x0000_0073


class Prog:
    """A program at address 0: ``emit`` words, ``label`` targets, ``bne`` /
    ``beq`` to a label (resolved at ``words()``)."""

    def __init__(self):
        self._items = []          # int word, or (kind, f3, rs1, rs2, label)
        self._labels = {}

    def emit(self, *words) -> "Prog":
        for w in words:
            if isinstance(w, list):
                self._items.extend(w)
            else:
                self._items.append(w)
        return self

    def label(self, name: str) -> "Prog":
        self._labels[name] = len(self._items)
        return self

    def bne(self, rs1: int, rs2: int, label: str) -> "Prog":
        self._items.append(("b", 1, rs1, rs2, label))
        return self

    def beq(self, rs1: int, rs2: int, label: str) -> "Prog":
        self._items.append(("b", 0, rs1, rs2, label))
        return self

    def words(self) -> dict:
        out = {}
        for idx, item in enumerate(self._items):
            if isinstance(item, tuple):
                _, f3, rs1, rs2, label = item
                out[idx] = _b(f3, rs1, rs2, (self._labels[label] - idx) * 4)
            else:
                out[idx] = item & 0xFFFF_FFFF
        return out

    def addr_of(self, label: str) -> int:
        return self._labels[label] * 4
