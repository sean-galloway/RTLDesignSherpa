# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: mext_program
# Purpose: Seeded generator of self-checking RV32IM programs aimed at the
#          peregrine M unit's hazards, plus the RVFI shadow-regfile check
#          the core-level M test applies to the retire trace.
#
# Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
# Subsystem: riscv-ip/peregrine-rv32im
#
# Author: sean galloway
# Created: 2026-11-23

"""Generated M-extension stress programs for peregrine_core.

The generator emits blocks of hazard shapes around M instructions and models
every register write itself, so the program ends by comparing each register
with the value the generator computed (``tohost = (reg << 1) | 1`` names the
first mismatch).  Register use:

* x1..x29: the generator's pool;
* x30: base of the data area (loads and stores);
* x31: the trap handler's only scratch register (saved through mscratch).

The handler services two traps.  An ``ecall`` (planted directly before an M
instruction, so it traps in MEM while that M instruction sits in EX) adds 1
to x29 and returns to mepc + 4; the M instruction after it reads x29, so a
unit that kept the operation the trap killed would return a stale result.  A machine timer interrupt acknowledges itself with a store to
``irq_ack``, which the TB's interrupt source watches.  Timer interrupts are
enabled only when the TB pokes ``irq_enable``: spike runs the same ELF with
the word at 0, so its timer (mtimecmp = 0 at reset) cannot fire.
"""

import random
from dataclasses import dataclass, field

from .mdu_tb import INT_MIN, M_OPS, MASK32, m_ref

POOL = tuple(range(1, 30))
ECALL_REG = 29          # the ecall handler adds 1 to it
BASE_REG = 30
DATA_WORDS = 64
EDGES = (0, 1, MASK32, INT_MIN, 0x7FFF_FFFF, 2, MASK32 - 1, INT_MIN + 1)

OPC_OP = 0x33
OPC_OP_IMM = 0x13
OPC_LOAD = 0x03
OPC_STORE = 0x23
OPC_BRANCH = 0x63
OPC_JALR = 0x67
OPC_SYSTEM = 0x73
F7_MULDIV = 0x01

# Interrupt enable bit the program sets in mie when irq_enable != 0.
MIE_MTIE = 0x80


@dataclass
class MextProgram:
    """Assembly text plus what the generator knows about it."""
    text: str
    m_count: int = 0
    shapes: dict = field(default_factory=dict)


class _Gen:
    def __init__(self, rng: random.Random) -> None:
        self.rng = rng
        self.lines: list = []
        self.regs = {r: 0 for r in POOL}
        self.mem = [0] * DATA_WORDS
        self.labels = 0
        self.m_count = 0
        self.shapes: dict = {}

    # -- helpers ----------------------------------------------------------
    def emit(self, line: str) -> None:
        self.lines.append(f"    {line}")

    def label(self) -> str:
        self.labels += 1
        return f"L{self.labels}"

    def reg(self, exclude=()) -> int:
        return self.rng.choice([r for r in POOL if r not in exclude])

    def operand(self) -> int:
        rng = self.rng
        pick = rng.randrange(4)
        if pick == 0:
            return rng.choice(EDGES)
        if pick == 1:
            return rng.randrange(1 << rng.randrange(1, 33))
        if pick == 2:
            return (-rng.randrange(1, 1 << rng.randrange(1, 32))) & MASK32
        return rng.getrandbits(32)

    def li(self, rd: int, value: int) -> None:
        self.emit(f"li x{rd}, {value & MASK32:#x}")
        self.regs[rd] = value & MASK32

    def m_op(self, rd: int, rs1: int, rs2: int, f3=None) -> int:
        f3 = self.rng.randrange(8) if f3 is None else f3
        self.emit(f"{M_OPS[f3]} x{rd}, x{rs1}, x{rs2}")
        value = m_ref(f3, self.regs.get(rs1, 0) if rs1 else 0,
                      self.regs.get(rs2, 0) if rs2 else 0)
        if rd:
            self.regs[rd] = value
        self.m_count += 1
        return value

    def add(self, rd: int, rs1: int, rs2: int) -> None:
        self.emit(f"add x{rd}, x{rs1}, x{rs2}")
        self.regs[rd] = (self.regs[rs1] + self.regs[rs2]) & MASK32

    def store(self, rs: int, word: int) -> None:
        self.emit(f"sw x{rs}, {4 * word}(x{BASE_REG})")
        self.mem[word] = self.regs[rs]

    def load(self, rd: int, word: int) -> None:
        self.emit(f"lw x{rd}, {4 * word}(x{BASE_REG})")
        self.regs[rd] = self.mem[word]

    # -- hazard shapes ----------------------------------------------------
    def shape_single(self):
        self.m_op(self.reg(), self.reg(), self.reg())

    def shape_dependent_pair(self):
        rd = self.reg()
        self.m_op(rd, self.reg(), self.reg())
        self.m_op(self.reg(), rd, self.reg())

    def shape_independent_pair(self):
        a, b = self.reg(), self.reg()
        self.m_op(a, self.reg(exclude=(a,)), self.reg(exclude=(a,)))
        self.m_op(b, self.reg(exclude=(a,)), self.reg(exclude=(a,)))

    def shape_alu_consumer(self):
        rd = self.reg()
        self.m_op(rd, self.reg(), self.reg())
        self.add(self.reg(), rd, self.reg())

    def shape_branch_consumer(self):
        rd = self.reg()
        self.m_op(rd, self.reg(), self.reg())
        other = self.reg(exclude=(rd,))
        bump = self.reg(exclude=(rd,))
        skip = self.label()
        branch = self.rng.choice(("beq", "bne", "blt", "bgeu"))
        a, b = self.regs[rd], self.regs[other]
        sa = a - (1 << 32) if a & INT_MIN else a
        sb = b - (1 << 32) if b & INT_MIN else b
        taken = {"beq": a == b, "bne": a != b, "blt": sa < sb, "bgeu": a >= b}[branch]
        self.emit(f"{branch} x{rd}, x{other}, {skip}")
        self.emit(f"addi x{bump}, x{bump}, 1")
        if not taken:
            self.regs[bump] = (self.regs[bump] + 1) & MASK32
        self.lines.append(f"{skip}:")

    def shape_store_load(self):
        rd = self.reg()
        word = self.rng.randrange(DATA_WORDS)
        self.m_op(rd, self.reg(), self.reg())
        self.store(rd, word)
        self.load(self.reg(), word)

    def shape_load_into_m(self):
        rs = self.reg()
        self.load(rs, self.rng.randrange(DATA_WORDS))
        self.m_op(self.reg(), rs, self.reg())

    def shape_rd_x0(self):
        self.m_op(0, self.reg(), self.reg())

    def shape_same_reg(self):
        r = self.reg()
        self.m_op(r, r, r)

    def shape_csr_after(self):
        self.m_op(self.reg(), self.reg(), self.reg())
        rd = self.reg()
        self.emit(f"csrr x{rd}, mtvec")
        self.emit(f"csrr x{rd}, mstatus")
        self.emit(f"andi x{rd}, x{rd}, 0")
        self.regs[rd] = 0

    def shape_branch_shadow(self):
        # The M instruction sits in a taken jump's shadow: fetched, flushed,
        # never executed.  A core that executes it corrupts its rd.
        over = self.label()
        self.emit(f"j {over}")
        self.emit(f"{M_OPS[self.rng.randrange(8)]} x{self.reg()}, x{self.reg()}, x{self.reg()}")
        self.lines.append(f"{over}:")

    def shape_ecall_before(self):
        # ecall traps in MEM in the cycle the M instruction is in EX; the
        # handler changes the M instruction's rs1 before it re-executes.
        self.emit("ecall")
        self.regs[ECALL_REG] = (self.regs[ECALL_REG] + 1) & MASK32
        self.m_op(self.reg(), ECALL_REG, self.reg())

    def shape_load_m_branch(self):
        # A load, then an M instruction, then a branch on the load: in the
        # M instruction's first EX cycle the load is in EX/MEM and the
        # branch in ID, so the load-to-branch interlock fires while the M
        # instruction holds.  Its ID/EX bubble must not overwrite it.
        rl = self.reg()
        self.load(rl, self.rng.randrange(DATA_WORDS))
        self.m_op(self.reg(exclude=(rl,)), self.reg(), self.reg())
        bump = self.reg(exclude=(rl,))
        skip = self.label()
        taken = self.regs[rl] == 0
        self.emit(f"beqz x{rl}, {skip}")
        self.emit(f"addi x{bump}, x{bump}, 1")
        if not taken:
            self.regs[bump] = (self.regs[bump] + 1) & MASK32
        self.lines.append(f"{skip}:")

    def shape_csr_around(self):
        # A CSR read, an M instruction, a CSR read: the CSR serialization
        # interlock fires in ID during the M instruction's first EX cycle.
        rd = self.reg()
        self.emit(f"csrr x{rd}, mie")
        self.m_op(self.reg(exclude=(rd,)), self.reg(), self.reg())
        self.emit(f"csrr x{rd}, mtvec")
        self.emit(f"andi x{rd}, x{rd}, 0")
        self.regs[rd] = 0

    def shape_reload(self):
        for _ in range(3):
            self.li(self.reg(), self.rng.choice(EDGES))

    SHAPES = ("single", "dependent_pair", "independent_pair", "alu_consumer",
              "branch_consumer", "store_load", "load_into_m", "rd_x0",
              "same_reg", "csr_after", "branch_shadow", "ecall_before",
              "load_m_branch", "csr_around", "reload")

    # -- program ----------------------------------------------------------
    def build(self, blocks: int) -> MextProgram:
        out = self.lines
        out += [".section .text", ".globl _start", "_start:"]
        self.emit("la x31, trap_handler")
        self.emit("csrw mtvec, x31")
        self.emit(f"la x{BASE_REG}, data")
        self.emit("la x31, irq_enable")
        self.emit("lw x31, 0(x31)")
        self.emit("beqz x31, 1f")
        self.emit(f"li x31, {MIE_MTIE:#x}")
        self.emit("csrs mie, x31")
        self.emit("csrsi mstatus, 8")
        out.append("1:")
        for r in POOL:
            self.li(r, self.operand())
        for _ in range(blocks):
            name = self.rng.choice(self.SHAPES)
            self.shapes[name] = self.shapes.get(name, 0) + 1
            getattr(self, f"shape_{name}")()
        # Epilogue: interrupts off (the handler owns x31), then check every
        # pool register against the model.
        self.emit("csrci mstatus, 8")
        for r in POOL:
            ok = self.label()
            self.emit(f"li x31, {self.regs[r]:#x}")
            self.emit(f"beq x{r}, x31, {ok}")
            self.emit(f"li x31, {(r << 1) | 1}")
            self.emit("j finish")
            out.append(f"{ok}:")
        self.emit("li x31, 1")
        out.append("finish:")
        self.emit(f"la x{BASE_REG}, tohost")
        self.emit(f"sw x31, 0(x{BASE_REG})")
        out.append("2:")
        self.emit("j 2b")
        out += ["trap_handler:"]
        self.emit("csrrw x31, mscratch, x31")
        self.emit("csrr x31, mcause")
        self.emit("bltz x31, 3f")
        self.emit("csrr x31, mepc")
        self.emit("addi x31, x31, 4")
        self.emit("csrw mepc, x31")
        self.emit(f"addi x{ECALL_REG}, x{ECALL_REG}, 1")
        self.emit("j 4f")
        out.append("3:")
        self.emit("la x31, irq_ack")
        self.emit("sw x0, 0(x31)")
        out.append("4:")
        self.emit("csrrw x31, mscratch, x31")
        self.emit("mret")
        out += [".section .data", ".align 3",
                ".globl tohost", "tohost: .dword 0",
                ".globl fromhost", "fromhost: .dword 0",
                ".globl irq_enable", "irq_enable: .word 0",
                ".globl irq_ack", "irq_ack: .word 0",
                ".align 2", "data:"]
        out += ["    .word 0"] * DATA_WORDS
        return MextProgram(text="\n".join(out) + "\n", m_count=self.m_count,
                           shapes=dict(self.shapes))


def generate(seed: int, blocks: int) -> MextProgram:
    """A seeded program of ``blocks`` hazard shapes."""
    return _Gen(random.Random(seed)).build(blocks)


# ---------------------------------------------------------------------------
# RVFI shadow-regfile check
# ---------------------------------------------------------------------------

def _reads(insn: int) -> tuple:
    """(reads rs1, reads rs2) for the instruction's format."""
    opc = insn & 0x7F
    f3 = (insn >> 12) & 0x7
    if opc in (OPC_OP, OPC_STORE, OPC_BRANCH):
        return True, True
    if opc in (OPC_OP_IMM, OPC_LOAD, OPC_JALR):
        return True, False
    if opc == OPC_SYSTEM and f3 in (1, 2, 3):
        return True, False
    return False, False


def is_m_insn(insn: int) -> bool:
    return (insn & 0x7F) == OPC_OP and (insn >> 25) == F7_MULDIV


def shadow_check(trace: list) -> dict:
    """Check every retired beat's operand values against the register values
    RVFI itself reported writing, and every M result against the model.

    Raises AssertionError on the first mismatch; returns counts.
    """
    shadow = {0: 0}
    checked_operands = 0
    checked_m = 0
    for i, beat in enumerate(trace):
        if beat["trap"]:
            continue
        insn = beat["insn"]
        r1, r2 = _reads(insn)
        rs1, rs2 = (insn >> 15) & 0x1F, (insn >> 20) & 0x1F
        for use, reg, val in ((r1, rs1, beat["rs1_rdata"]), (r2, rs2, beat["rs2_rdata"])):
            if use and reg in shadow:
                assert val == shadow[reg], (
                    f"beat {i} pc=0x{beat['pc']:x} insn=0x{insn:08x}: x{reg} read "
                    f"0x{val:08x}, last written 0x{shadow[reg]:08x}")
                checked_operands += 1
        if is_m_insn(insn) and rs1 in shadow and rs2 in shadow:
            f3 = (insn >> 12) & 0x7
            want = m_ref(f3, shadow[rs1], shadow[rs2])
            rd = (insn >> 7) & 0x1F
            got = beat["rd_wdata"] if rd else want
            assert got == want, (
                f"beat {i} pc=0x{beat['pc']:x}: {M_OPS[f3]} x{rd}, "
                f"0x{shadow[rs1]:08x}, 0x{shadow[rs2]:08x} wrote 0x{got:08x}, "
                f"want 0x{want:08x}")
            checked_m += 1
        if beat["rd_addr"]:
            shadow[beat["rd_addr"]] = beat["rd_wdata"]
    return {"operands": checked_operands, "m_results": checked_m}
